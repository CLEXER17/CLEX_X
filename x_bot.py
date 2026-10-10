"""
X (Twitter) automation bot v4 - niche: crypto, tech, airdrops, earnings
- Fresh news only (max age = max_age_min) from crypto RSS feeds + Google News queries
- Categories: news, airdrop, earnings, tech (each with its own image tag + hashtags + daily cap)
- Breaking stories (hack, exploit, ETF approved, lawsuit, crash...) BYPASS the scheduled
  posts-per-day limit and the category caps. They only have their own cap (max_breaking_per_day).
- Claude writes the post, Pillow makes an image card, tweepy posts it
- Replies only to people who comment/mention you on YOUR posts

ENV (Railway Variables) - ONLY these:
    X_API_KEY, X_API_SECRET, X_ACCESS_TOKEN, X_ACCESS_TOKEN_SECRET
    ANTHROPIC_API_KEY
    TELEGRAM_BOT_TOKEN, TELEGRAM_CHAT_ID
    DATA_DIR=/data            (Railway Volume mounted at /data; the volume path is used automatically when attached)

EVERYTHING ELSE is changed from Telegram (saved in DATA_DIR/settings.json, applied live):
    /settings                 show all settings
    /set <key> <value>        change one setting      e.g.  /set posts_per_day 4
    /reset <key>              back to default
    /breaking                 show breaking keywords
    /addbreak <word>          add a breaking keyword
    /delbreak <word>          remove a breaking keyword
    /status  /pause  /resume  /help
    /post                     post the best fresh story RIGHT NOW (ignores daily limits + review)
    /say <text>               post your own text RIGHT NOW (max 280 chars) with an auto image card
    send a PHOTO with caption  /say <text>   -> posts YOUR image with that text
    /sayt <text>              post text only, no image
    /menu                     show the button keyboard
    /golive  /dryrun          switch live / dry-run (go-live asks you to confirm)

First start is DRY_RUN (nothing is posted). Go live with:  /set dry_run 0

Run:
    python x_bot.py            # the bot
    python x_bot.py review     # approve/edit/reject queued posts in terminal (optional)
"""

import difflib
import io
import json
import logging
import os
import random
import queue as pyqueue
import re
import sys
import textwrap
from html import escape as html_escape, unescape
import threading
import time
from calendar import timegm
from datetime import datetime, timedelta, timezone
from pathlib import Path
from urllib.parse import quote, urljoin

import feedparser
import requests
import schedule
import tweepy
from requests_oauthlib import OAuth1   # installed together with tweepy
from anthropic import Anthropic, APIStatusError
from dotenv import load_dotenv
from PIL import Image, ImageDraw, ImageFont

load_dotenv()

# ---------- ENV (secrets + paths only) ----------
# DATA_DIR: set to a persistent volume path on Railway (e.g. /data) so state survives redeploys
# Railway sets RAILWAY_VOLUME_MOUNT_PATH by itself when a Volume is attached - prefer it, so a wrong DATA_DIR can't lose data
_vol = os.getenv("RAILWAY_VOLUME_MOUNT_PATH", "")
DATA_DIR = Path(_vol or os.getenv("DATA_DIR") or str(Path(__file__).parent))
DATA_DIR.mkdir(parents=True, exist_ok=True)
PERSISTENT = bool(_vol) or os.path.ismount(str(DATA_DIR))
STORAGE_NOTE = (
    f"💾 Settings are saved (volume at {DATA_DIR})" if PERSISTENT else
    "⚠️ NO PERSISTENT VOLUME - settings, history and pause state reset on every redeploy.\n"
    "Fix: in Railway open your project, press Ctrl+K, choose Volume, attach it to this service with mount path /data."
)
STATE_FILE = DATA_DIR / "state.json"
CARD_FILE = DATA_DIR / "card.png"
CARDS_DIR = DATA_DIR / "cards"
QUEUE_FILE = DATA_DIR / "review_queue.json"
LOG_FILE = DATA_DIR / "posts_log.json"
KILL_FILE = DATA_DIR / "STOP"
SPEND_FILE = DATA_DIR / "x_spend.json"
SETTINGS_FILE = DATA_DIR / "settings.json"
CARDS_DIR.mkdir(exist_ok=True)
TG_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN", "")
TG_CHAT = os.getenv("TELEGRAM_CHAT_ID", "")
TG_ENABLED = bool(TG_TOKEN and TG_CHAT)


# ---------- SETTINGS (editable from Telegram) ----------
# key: (default, kind, min, max, description)
SETTINGS = {
    "dry_run": (True, "bool", None, None, "1 = print only, 0 = really post to X"),
    "brand": ("CLEXER", "str", None, None, "name printed on image cards"),
    "use_image": (True, "bool", None, None, "attach image card to posts"),
    "use_article_image": (True, "bool", None, None, "use the news article's own image when it has one (else the card)"),
    "bold_keywords": (True, "bool", None, None, "bold CAPITAL key words in posts (Unicode bold letters)"),
    "claude_model": ("claude-sonnet-5-5", "str", None, None, "Claude model used for writing/scoring"),
    "max_age_min": (150, "int", 30, 1440, "ignore news older than this (keep > break_check_minutes)"),
    "break_check_minutes": (120, "int", 5, 720, "how often to look for breaking stories"),
    "posts_per_day": (3, "int", 0, 24, "scheduled posts per day (breaking posts are extra)"),
    "max_breaking_per_day": (5, "int", 0, 50, "safety cap for breaking posts per day (0 = no limit)"),
    "reply_check_minutes": (15, "int", 5, 240, "how often to check comments"),
    "enable_replies": (False, "bool", None, None, "reply to comments on your posts"),
    "max_replies_per_run": (5, "int", 1, 20, "max replies per check"),
    "enable_metrics": (True, "bool", None, None, "log engagement numbers"),
    "use_x_search": (False, "bool", None, None, "small-creator chatter via X search (costs API reads)"),
    "x_search_minutes": (60, "int", 15, 1440, "how often X search runs"),
    "x_search_max_results": (20, "int", 10, 100, "posts per X search (each is billed)"),
    "x_search_budget_usd_day": (1.0, "float", 0, 50, "hard daily $ cap for X search"),
    "x_min_likes": (3, "int", 0, 1000, "total likes across tweets about one $TICKER"),
    "x_min_authors": (2, "int", 1, 50, "distinct accounts mentioning one $TICKER"),
    "x_min_followers": (300, "int", 0, 100000, "ignore tiny/bot-like accounts"),
    "quality_min": (6, "int", 0, 10, "usefulness score needed to post (second Claude pass)"),
    "accuracy_min": (7, "int", 0, 10, "accuracy score needed (every claim must be in the source)"),
    "review_cats": ("airdrop", "str", None, None, "categories needing your approval (comma list, or none)"),
    "review_all": (False, "bool", None, None, "1 = approve every post yourself"),
    "review_expire_min": (180, "int", 10, 1440, "unreviewed items are dropped after this"),
    "tg_notify_posts": (True, "bool", None, None, "Telegram message for each live post"),
    "cap_news": (99, "int", 0, 999, "news posts per day (non-breaking)"),
    "cap_airdrop": (2, "int", 0, 999, "airdrop posts per day (non-breaking)"),
    "cap_earnings": (2, "int", 0, 999, "earnings posts per day (non-breaking)"),
    "cap_tech": (2, "int", 0, 999, "tech posts per day (non-breaking)"),
}
CATS = ("news", "airdrop", "earnings", "tech")
DEFAULT_BREAKING = [
    "hack", "hacked", "exploit", "drained", "stolen", "breach", "rug pull",
    "liquidat", "halts", "suspends", "bankrupt",
    "etf approved", "lawsuit", "crash", "plunge", "record high", "all-time high", "delist", "arrest",
]
BREAKING_EXCLUDE = re.compile(r"hackathon\w*")   # words that contain a keyword but are not news
SCHEDULE_KEYS = {"break_check_minutes", "posts_per_day", "reply_check_minutes"}

_settings_cache = {"m": None, "d": {}}


def _settings_raw():
    try:
        m = SETTINGS_FILE.stat().st_mtime_ns
    except OSError:
        _settings_cache.update(m=None, d={})
        return {}
    if m != _settings_cache["m"]:
        try:
            d = json.loads(SETTINGS_FILE.read_text())
        except Exception:
            d = {}
        _settings_cache.update(m=m, d=d)
    return _settings_cache["d"]


def _save_settings(data):
    tmp = SETTINGS_FILE.with_suffix(".tmp")
    tmp.write_text(json.dumps(data, indent=2))
    os.replace(tmp, SETTINGS_FILE)


def cfg(key):
    default, kind = SETTINGS[key][0], SETTINGS[key][1]
    v = _settings_raw().get(key, default)
    try:
        return {"bool": bool, "int": int, "float": float, "str": str}[kind](v)
    except Exception:
        return default


def review_cats():
    return {c.strip() for c in cfg("review_cats").split(",") if c.strip()}


def breaking_keywords():
    kws = _settings_raw().get("breaking_keywords")
    return kws if isinstance(kws, list) and kws else list(DEFAULT_BREAKING)


def fmt_val(v):
    if isinstance(v, bool):
        return "1" if v else "0"
    return str(v)


def parse_value(key, s):
    default, kind, lo, hi, _ = SETTINGS[key]
    s = s.strip()
    if kind == "bool":
        if s.lower() in ("1", "on", "true", "yes", "y"):
            return True
        if s.lower() in ("0", "off", "false", "no", "n"):
            return False
        raise ValueError("use 1 or 0")
    if kind in ("int", "float"):
        try:
            v = int(s) if kind == "int" else float(s)
        except ValueError:
            raise ValueError(f"needs a {'whole number' if kind == 'int' else 'number'}")
        if (lo is not None and v < lo) or (hi is not None and v > hi):
            raise ValueError(f"allowed range {lo} to {hi}")
        return v
    if not s:
        raise ValueError("value is empty")
    if key == "review_cats":
        if s.lower() == "none":
            return ""
        cats = [c.strip().lower() for c in s.split(",") if c.strip()]
        bad = [c for c in cats if c not in CATS]
        if bad:
            raise ValueError(f"unknown category {bad}; use {', '.join(CATS)} or none")
        return ",".join(cats)
    return s


def settings_text():
    raw = _settings_raw()
    lines = ["SETTINGS (change: /set key value)"]
    for key, (default, *_rest) in SETTINGS.items():
        v = cfg(key)
        mark = "" if key not in raw else f"   (default {fmt_val(default)})"
        lines.append(f"{key} = {fmt_val(v)}{mark}")
    lines.append(f"breaking keywords: {len(breaking_keywords())}  (see /breaking)")
    return "\n".join(lines)


def settings_html():
    """Every setting as its own tap-to-copy line: tap it, change the value, send it back. Several lines can be sent at once."""
    raw = _settings_raw()
    lines = ["SETTINGS - tap a line to copy it, change the value, send it. You can send several lines in one message.", ""]
    for key, (default, *_rest) in SETTINGS.items():
        tail = "" if key not in raw else f"  (default {html_escape(fmt_val(default))})"
        lines.append(f"<code>{html_escape(f'/set {key} = {fmt_val(cfg(key))}')}</code>{tail}")
    lines += ["", f"Breaking keywords: {len(breaking_keywords())}  -  <code>/breaking</code>"]
    return "\n".join(lines)


def apply_setting(kind, a, b):
    """Runs in the main thread. Returns the Telegram reply text."""
    data = dict(_settings_raw())
    if kind in ("set", "reset"):
        key = a
        if key not in SETTINGS:
            near = difflib.get_close_matches(key, list(SETTINGS), n=1, cutoff=0.6)
            hint = f" Did you mean {near[0]}?" if near else ""
            return f"❌ Unknown setting '{key}'.{hint}"
        if kind == "set":
            try:
                val = parse_value(key, b or "")
            except ValueError as e:
                return f"❌ {key}: {e}"
            data[key] = val
            msg = f"✅ {key} = {fmt_val(val)}"
        else:
            data.pop(key, None)
            msg = f"♻️ {key} reset to default ({fmt_val(SETTINGS[key][0])})"
        _save_settings(data)
        _settings_raw()
        if key in SCHEDULE_KEYS:
            apply_schedule()
            msg += "\n⏱ schedule updated"
        if key in ("max_age_min", "break_check_minutes") and cfg("max_age_min") <= cfg("break_check_minutes"):
            msg += "\n⚠️ max_age_min should be larger than break_check_minutes or stories can slip through."
        if key == "dry_run":
            msg += "\n🔴 LIVE: the bot will really post to X." if not cfg("dry_run") else "\n🟡 DRY_RUN: nothing will be posted."
        return msg
    word = (a or "").strip().lower()
    kws = list(breaking_keywords())
    if kind == "addbreak":
        if len(word) < 3:
            return "Keyword must be at least 3 characters."
        if word in kws:
            return f"'{word}' is already a breaking keyword."
        kws.append(word)
        data["breaking_keywords"] = kws
        _save_settings(data)
        _settings_raw()
        return f"✅ Added breaking keyword: {word}"
    if kind == "delbreak":
        if word not in kws:
            return f"'{word}' is not in the list. Send /breaking to see it."
        kws.remove(word)
        if not kws:
            return "Can't remove the last keyword."
        data["breaking_keywords"] = kws
        _save_settings(data)
        _settings_raw()
        return f"🗑 Removed breaking keyword: {word}"
    return "Unknown action."


HELP_TEXT = (
    "Commands:\n"
    "/settings - every setting as a tap-to-copy line; edit the value and send it back\n"
    "/set <key> = <value> - change a setting (several lines in one message work)\n"
    "/reset <key> - back to default\n"
    "/breaking - list breaking keywords\n"
    "/addbreak <word> - add breaking keyword\n"
    "/delbreak <word> - remove breaking keyword\n"
    "/post - post the best fresh story NOW (ignores daily limits and review)\n"
    "/say <text> - post your own text NOW (auto image card)\n"
    "Photo + caption /say <text> - post YOUR image with your text\n"
    "/sayt <text> - text only, no image\n"
    "/menu - show the buttons\n"
    "/golive  /dryrun - switch live / dry-run\n"
    "/status - today's counters\n"
    "/pause  /resume - stop / start all posting\n"
    "Go live: /set dry_run 0"
)


def gnews(q):
    return "https://news.google.com/rss/search?q=" + quote(q) + "&hl=en-IN&gl=IN&ceid=IN:en"


# (url, trusted_feed, category)
SOURCES = [
    ("https://www.coindesk.com/arc/outboundfeeds/rss/", True, "news"),
    ("https://cointelegraph.com/rss", True, "news"),
    ("https://decrypt.co/feed", True, "news"),
    ("https://www.theblock.co/rss.xml", True, "news"),
    (gnews("(bitcoin OR crypto OR ethereum OR exchange hack OR bitget OR binance OR bingx) when:3h"), False, "news"),
    (gnews("(airdrop OR snapshot OR eligibility OR \"token launch\" OR whitelist) crypto when:6h"), False, "airdrop"),
    (gnews("(earnings OR \"quarterly results\") (coinbase OR nvidia OR strategy OR robinhood OR circle OR marathon) when:6h"), False, "earnings"),
    ("https://techcrunch.com/feed/", True, "tech"),
    ("https://www.theverge.com/rss/index.xml", True, "tech"),
]

# Google News results from these sources are user posts / ideas, not news - never post them
BLOCKED_SOURCES = ("tradingview", "reddit", "medium", "substack", "youtube", "facebook",
                   "telegram", "quora", "stocktwits", "x.com", "twitter")

CAT_KEYWORDS = {
    "news": ["bitcoin", "btc", "crypto", "ethereum", "eth", "solana", "altcoin", "etf", "binance",
             "bitget", "bingx", "bybit", "okx", "coinbase", "hack", "exploit", "stablecoin", "defi"],
    "airdrop": ["airdrop", "snapshot", "claim", "eligib", "points", "tge", "token launch"],
    "earnings": ["earnings", "revenue", "quarter", "profit", "results", "yield", "staking"],
    "tech": ["ai", "openai", "nvidia", "chip", "blockchain", "quantum", "semiconductor",
             "bitcoin", "crypto", "stablecoin", "tokeniz"],
}
CAT_PRIORITY = {"news": 0, "airdrop": 1, "earnings": 1, "tech": 2}
CAT_HASHTAGS = {
    "news": "#Crypto #Bitcoin",
    "airdrop": "#Airdrop #Crypto #Web3",
    "earnings": "#Earnings #Crypto",
    "tech": "#Tech #AI",
}
CAT_TAG = {"news": "CRYPTO NEWS", "airdrop": "AIRDROP ALERT", "earnings": "EARNINGS UPDATE", "tech": "TECH"}
CAT_COLOR = {"news": (0, 200, 150), "airdrop": (255, 170, 0), "earnings": (80, 140, 255), "tech": (170, 100, 255)}
DISCLAIMER_CATS = {"airdrop", "earnings"}
OPT_OUT_WORDS = {"stop", "unsubscribe", "opt out", "dont reply", "don't reply", "do not reply"}

PERSONA = (
    "You run a sharp, no-hype crypto and tech X account covering news, airdrops and earnings. "
    "Tone: confident, concise, useful. No financial advice, no price guarantees, no 'to the moon' hype, "
    "max 1 emoji, no links."
)

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
log = logging.getLogger("xbot")

claude = Anthropic()  # uses ANTHROPIC_API_KEY
x = tweepy.Client(
    consumer_key=os.environ["X_API_KEY"],
    consumer_secret=os.environ["X_API_SECRET"],
    access_token=os.environ["X_ACCESS_TOKEN"],
    access_token_secret=os.environ["X_ACCESS_TOKEN_SECRET"],
    wait_on_rate_limit=True,
)
_auth_v1 = tweepy.OAuth1UserHandler(
    os.environ["X_API_KEY"],
    os.environ["X_API_SECRET"],
    os.environ["X_ACCESS_TOKEN"],
    os.environ["X_ACCESS_TOKEN_SECRET"],
)
x_v1 = tweepy.API(_auth_v1)  # image upload only


# ---------- STATE ----------
def load_json(path, default):
    if path.exists():
        try:
            return json.loads(path.read_text())
        except Exception:
            return default
    return default


def load_state():
    base = {"posted": [], "since_id": None, "replied": [], "opted_out": [],
            "day": "", "count": 0, "cat_counts": {}, "reg_count": 0, "brk_count": 0}
    if STATE_FILE.exists():
        base.update(json.loads(STATE_FILE.read_text()))
    return base


def save_state(state):
    state["posted"] = state["posted"][-300:]
    state["replied"] = state["replied"][-1000:]
    STATE_FILE.write_text(json.dumps(state, indent=2))


def roll_day(state):
    today = datetime.now().strftime("%Y-%m-%d")
    if state.get("day") != today:
        state["day"], state["count"], state["cat_counts"] = today, 0, {}
        state["reg_count"], state["brk_count"] = 0, 0


# ---------- TEXT STYLE ----------
def x_len(text):
    """Length the way X counts it: emoji and bold-style letters count as 2, most other characters as 1."""
    n = 0
    for ch in text:
        cp = ord(ch)
        n += 1 if (cp <= 0x10FF or 0x2000 <= cp <= 0x200D or 0x2010 <= cp <= 0x201F or 0x2032 <= cp <= 0x2037) else 2
    return n


def to_bold(s):
    """A-Z / 0-9 -> Unicode sans-serif bold capitals (this is how 'bold' looks on X; real bold is not possible via API)."""
    out = []
    for ch in s.upper():
        if "A" <= ch <= "Z":
            out.append(chr(0x1D5D4 + ord(ch) - 65))
        elif "0" <= ch <= "9":
            out.append(chr(0x1D7EC + ord(ch) - 48))
        else:
            out.append(ch)
    return "".join(out)


def from_bold(s):
    """Reverse of to_bold, so image cards (whose font has no bold-style letters) show normal capitals."""
    out = []
    for ch in s:
        cp = ord(ch)
        if 0x1D5D4 <= cp <= 0x1D5ED:
            out.append(chr(65 + cp - 0x1D5D4))
        elif 0x1D7EC <= cp <= 0x1D7F5:
            out.append(chr(48 + cp - 0x1D7EC))
        else:
            out.append(ch)
    return "".join(out)


def style_text(text):
    """Turn **KEYWORD** markers from the writer into bold capitals (max 4). Plain text if disabled or too long."""
    plain = text.replace("**", "")
    if not cfg("bold_keywords"):
        return plain
    count = [0]

    def _bold(m):
        count[0] += 1
        return to_bold(m.group(1)) if count[0] <= 4 else m.group(1)

    styled = re.sub(r"\*\*(.+?)\*\*", _bold, text).replace("**", "")
    return styled if x_len(styled) <= 280 else plain


# ---------- CLAUDE ----------
_alert_last = {}
_last = {"card": None}   # image card of the most recent run_post draft


def alert_once(key, text, every_min=180):
    """Telegram alert, repeated at most once per `every_min` so a broken key/credit never spams you."""
    now = time.time()
    if now - _alert_last.get(key, 0) < every_min * 60:
        return
    _alert_last[key] = now
    log.error(text)
    tg_send(text)


def ask_claude(system, prompt, max_tokens=300):
    for _attempt in (1, 2):
        try:
            r = claude.messages.create(
                model=cfg("claude_model"),
                max_tokens=max_tokens,
                system=system,
                messages=[{"role": "user", "content": prompt}],
            )
        except APIStatusError as e:
            msg = str(e).lower()
            if e.status_code == 402 or "credit balance" in msg:
                alert_once("claude_credit", "🚨 Claude API credits are finished - the bot cannot write posts until you add credits:\n"
                                            "https://platform.claude.com/settings/billing")
            elif e.status_code == 401:
                alert_once("claude_auth", "🚨 Claude API key was rejected (invalid or deleted). Create a new key at "
                                          "https://platform.claude.com and update ANTHROPIC_API_KEY in Railway.")
            raise
        text = "".join(b.text for b in r.content if b.type == "text").strip()
        if text:
            return text
        log.warning("Claude returned no text (stop_reason=%s, blocks=%s, max_tokens=%d) - retrying with more room",
                    r.stop_reason, [b.type for b in r.content], max_tokens)
        max_tokens = min(max_tokens * 3, 2000)
    return ""


# ---------- NEWS ----------
def _age_min(entry):
    ts = entry.get("published_parsed") or entry.get("updated_parsed")
    if not ts:
        return None
    return (time.time() - timegm(ts)) / 60


def _tokens(t):
    return set(re.findall(r"[a-z0-9$]{3,}", t.lower()))


def is_dup(title, posted):
    a = _tokens(title)
    for p in posted[-60:]:
        b = _tokens(p)
        if a and b and len(a & b) / len(a | b) > 0.5:
            return True
    return False


def has_kw(title, kws):
    t = title.lower()
    for k in kws:
        pattern = r"\b" + re.escape(k) + (r"\b" if len(k) <= 3 else "")
        if re.search(pattern, t):
            return True
    return False


def is_niche(item):
    if item["trusted"] and item["cat"] == "news":
        return True
    return has_kw(item["title"], CAT_KEYWORDS[item["cat"]])


def is_breaking(title):
    """Breaking = title contains a breaking keyword (word start match, so 'liquidat' covers liquidation/liquidated)."""
    t = BREAKING_EXCLUDE.sub("", title.lower())
    return any(re.search(r"\b" + re.escape(k), t) for k in breaking_keywords())


_UA = {"User-Agent": "Mozilla/5.0 (compatible; NewsBot/1.0)"}


def _first_image_url(entry):
    """Picture URL from an RSS entry (media tags, image enclosure, or the first <img> in its HTML)."""
    for key in ("media_content", "media_thumbnail"):
        for m in entry.get(key) or []:
            if m.get("url"):
                return m["url"]
    for ln in entry.get("links") or []:
        if str(ln.get("type", "")).startswith("image/") and ln.get("href"):
            return ln["href"]
    html = (entry["content"][0].get("value", "") if entry.get("content") else "") + entry.get("summary", "")
    m = re.search(r'<img[^>]+src=["\']([^"\']+)', html, re.I)
    return m.group(1) if m else ""


def page_image_url(url):
    """og:image / twitter:image of the article page, '' if none."""
    if not url or "news.google.com" in url:
        return ""
    try:
        r = requests.get(url, timeout=8, headers=_UA)
        if r.status_code != 200:
            return ""
        head = r.text[:200000]
        for pat in (r'<meta[^>]+(?:property|name)=["\'](?:og:image|twitter:image)["\'][^>]*content=["\']([^"\']+)',
                    r'<meta[^>]+content=["\']([^"\']+)["\'][^>]*(?:property|name)=["\'](?:og:image|twitter:image)["\']'):
            m = re.search(pat, head, re.I)
            if m:
                return urljoin(url, unescape(m.group(1)))
    except Exception:
        pass
    return ""


def download_image(img_url, referer=""):
    """Download, check (>= 400x200) and re-save as a JPEG under X's 5 MB limit. Returns the path or None."""
    try:
        r = requests.get(img_url, timeout=10, headers={**_UA, "Referer": referer or ""})
        if r.status_code != 200 or len(r.content) > 15 * 1024 * 1024:
            return None
        img = Image.open(io.BytesIO(r.content))
        img.load()
        if img.width < 400 or img.height < 200:   # logos / thumbnails
            return None
        img = img.convert("RGB")
        img.thumbnail((1600, 1600))
        path = CARDS_DIR / f"art_{int(time.time() * 1000)}.jpg"
        q = 90
        while True:
            img.save(path, "JPEG", quality=q)
            if path.stat().st_size <= 4_500_000 or q <= 60:
                break
            q -= 10
        return str(path)
    except Exception as e:
        log.info("article image skipped (%s): %s", img_url[:80], e)
        return None


def article_image(item):
    """The news article's own picture, or None (then the generated card is used)."""
    for u in (item.get("image"), page_image_url(item.get("link"))):
        if u:
            path = download_image(u, item.get("link"))
            if path:
                return path
    return None


def article_text(url):
    """First paragraphs of the article page, used only as context for the writer. Returns '' on any problem."""
    if not url or "news.google.com" in url:
        return ""
    try:
        r = requests.get(url, timeout=8, headers={"User-Agent": "Mozilla/5.0 (compatible; NewsBot/1.0)"})
        if r.status_code != 200 or "html" not in r.headers.get("content-type", ""):
            return ""
        paras = re.findall(r"<p[^>]*>(.*?)</p>", r.text[:400000], re.S | re.I)
        txt = " ".join(re.sub("<[^>]+>", " ", p) for p in paras)
        return re.sub(r"\s+", " ", unescape(txt)).strip()[:1500]
    except Exception:
        return ""


def fetch_news():
    items = []
    max_age = cfg("max_age_min")
    for url, trusted, cat in SOURCES:
        try:
            feed = feedparser.parse(url)
        except Exception as e:
            log.warning("feed failed %s: %s", url, e)
            continue
        for e in feed.entries:
            age = _age_min(e)
            if age is None or age > max_age:
                continue
            title = e.title.strip()
            if not trusted:
                m = re.search(r"\s+-\s+([^-]+)$", title)
                if m and any(b in m.group(1).lower() for b in BLOCKED_SOURCES):
                    continue
                title = re.sub(r"\s+-\s+[^-]+$", "", title)  # strip " - Source"
            body = e["content"][0].get("value", "") if e.get("content") else ""
            summary = re.sub(r"\s+", " ", unescape(re.sub("<[^>]+>", " ", body or e.get("summary", "")))).strip()[:1200]
            items.append({"title": title, "summary": summary, "age": age, "trusted": trusted, "cat": cat,
                          "link": e.get("link", ""), "image": _first_image_url(e) if trusted else ""})
    items += fetch_x_signals()
    return items


# ---------- X SEARCH (small-creator airdrop / earnings chatter) ----------
# Note: min_faves is NOT supported by the API search, so likes/followers are filtered in code.
X_QUERIES = [
    ("airdrop", '(airdrop OR snapshot OR eligibility OR "points" OR tge OR "token launch" OR whitelist) '
                '(crypto OR solana OR ethereum OR base OR arbitrum) -is:retweet -is:reply lang:en'),
    ("earnings", '(yield OR apy OR staking OR farming OR "passive income") '
                 '(crypto OR defi OR airdrop) -is:retweet -is:reply lang:en'),
]
MAJOR_TICKERS = {"BTC", "ETH", "SOL", "USDT", "USDC", "BNB", "XRP", "DOGE", "ADA", "TON", "AVAX", "LINK"}
SCAM_WORDS = ["dm me", "dm for", "giveaway", "connect your wallet", "connect wallet", "send me",
              "guaranteed", "100x", "1000x", "pump", "free money", "drop your wallet"]
_x_cache = {"t": 0.0, "items": []}


def fetch_x_signals():
    """Group recent tweets by $TICKER; keep tickers mentioned by several real accounts with engagement."""
    if not cfg("use_x_search"):
        return []
    max_age = cfg("max_age_min")
    if time.time() - _x_cache["t"] < cfg("x_search_minutes") * 60:
        fresh = []
        for it in _x_cache["items"]:
            it["age"] = (time.time() - it["ts"]) / 60
            if it["age"] <= max_age:
                fresh.append(it)
        return fresh

    max_results = cfg("x_search_max_results")
    budget = cfg("x_search_budget_usd_day")
    min_followers, min_authors, min_likes = cfg("x_min_followers"), cfg("x_min_authors"), cfg("x_min_likes")
    _x_cache["t"], _x_cache["items"] = time.time(), []
    today = datetime.now().strftime("%Y-%m-%d")
    spend = load_json(SPEND_FILE, {})
    if spend.get("day") != today:
        spend = {"day": today, "usd": 0.0}
    start = datetime.now(timezone.utc) - timedelta(minutes=max_age)
    out = []
    for cat, query in X_QUERIES:
        # worst case per search: every post + its author billed (posts $0.005, users $0.010)
        if spend["usd"] + max_results * 0.015 > budget:
            log.info("X search budget reached for today ($%.2f)", spend["usd"])
            break
        try:
            resp = x.search_recent_tweets(
                user_auth=True,
                query=query,
                max_results=max_results,
                start_time=start,
                tweet_fields=["created_at", "public_metrics", "author_id"],
                expansions=["author_id"],
                user_fields=["public_metrics"],
            )
        except Exception as e:
            log.warning("X search failed (%s): %s", cat, e)
            continue
        users = {u.id: u for u in (resp.includes or {}).get("users", [])}
        spend["usd"] += len(resp.data or []) * 0.005 + len(users) * 0.010
        groups = {}
        for t in resp.data or []:
            low = t.text.lower()
            if any(w in low for w in SCAM_WORDS):
                continue
            u = users.get(t.author_id)
            if not u or u.public_metrics["followers_count"] < min_followers:
                continue
            likes = t.public_metrics["like_count"]
            for tk in {m.upper() for m in re.findall(r"\$([A-Za-z][A-Za-z0-9]{1,9})\b", t.text)}:
                if tk in MAJOR_TICKERS:
                    continue
                groups.setdefault(tk, []).append((t.author_id, likes, t))
        for tk, rows in groups.items():
            authors = {r[0] for r in rows}
            total_likes = sum(r[1] for r in rows)
            if len(authors) < min_authors or total_likes < min_likes:
                continue
            newest = max(r[2].created_at for r in rows).timestamp()
            snippets = " | ".join(
                re.sub(r"https?://\S+", "", r[2].text).strip()[:140] for r in rows[:3]
            )
            out.append({
                "title": f"${tk} {cat}",
                "card": f"${tk} {cat} buzz rising on X",
                "summary": f"{len(authors)} accounts, {total_likes} likes. Snippets: {snippets}"[:400],
                "ts": newest,
                "age": (time.time() - newest) / 60,
                "trusted": False,
                "cat": cat,
                "source": "x",
            })
    SPEND_FILE.write_text(json.dumps(spend))
    log.info("X search spend today (est.): $%.2f / $%.2f", spend["usd"], budget)
    _x_cache["items"] = out
    return out


# ---------- IMAGE CARD ----------
def _font(size):
    for p in [
        "C:/Windows/Fonts/arialbd.ttf",
        "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf",
        "/System/Library/Fonts/Supplemental/Arial Bold.ttf",
        "DejaVuSans-Bold.ttf",
    ]:
        try:
            return ImageFont.truetype(p, size)
        except OSError:
            continue
    return ImageFont.load_default(size)


def make_card(headline, cat, breaking, out=None):
    W, H = 1200, 675
    img = Image.new("RGB", (W, H), (11, 15, 25))
    d = ImageDraw.Draw(img)
    accent = (255, 59, 48) if breaking else CAT_COLOR[cat]
    tag = "BREAKING" if breaking else CAT_TAG[cat]
    d.rectangle([0, 0, 18, H], fill=accent)
    f_tag = _font(40)
    tag_w = int(d.textlength(tag, font=f_tag)) + 60
    d.rounded_rectangle([70, 60, 70 + tag_w, 120], radius=10, fill=accent)
    d.text((100, 66), tag, font=f_tag, fill=(255, 255, 255))
    y = 170
    for ln in textwrap.wrap(headline, width=30)[:5]:
        d.text((70, y), ln, font=_font(60), fill=(255, 255, 255))
        y += 76
    d.text((70, H - 90), cfg("brand"), font=_font(44), fill=accent)
    path = out or str(CARD_FILE)
    img.save(path)
    return path


# ---------- POST ----------
def generate_post(item, breaking):
    cat = item["cat"]
    style = {
        "news": "Lead with the key fact. Add one short line of context ONLY if it is stated in the context. No opinions, advice or predictions.",
        "airdrop": "Say what the airdrop/launch is and what users should check (eligibility, snapshot, official channel). Warn to use only official links.",
        "earnings": "Lead with the key number/result from the headline, then one short takeaway.",
        "tech": "State the key fact, then one line on why it matters, using only what the context says. No predictions.",
    }[cat]
    if breaking:
        style = "Lead with the key fact fast, urgent but factual."
    x_note = ""
    if item.get("source") == "x":
        x_note = (
            "NOTE: this is unverified chatter from small X accounts, not confirmed news. "
            "Do NOT present it as confirmed, do not name or quote any account, use wording like "
            "'buzz' or 'reportedly', and tell readers to verify via the project's official channels.\n"
        )
    prompt = (
        f"Headline: {item['title']}\n"
        f"Context: {item['summary']}\n"
        f"{x_note}\n"
        "Write ONE X post about this.\n"
        "Rules:\n"
        "- Max 250 characters total INCLUDING hashtags\n"
        f"- {style}\n"
        "- State only facts from the headline/context, do not invent numbers, dates or details\n"
        "- NO commentary, warnings, advice, predictions or interpretation: only restate what the headline/context says, "
        "in your own words\n"
        "- Never mention 'the headline', 'the source' or what is missing/unknown - just leave missing details out\n"
        + ("- Wrap the 1-3 most important key words (company, token, event or key number) in **double asterisks**, "
           "written in CAPITALS, e.g. **BINANCE** or **$15M**. Never wrap whole sentences or hashtags\n"
           if cfg("bold_keywords") else "- Do not use asterisks or any markdown\n") +
        "- Name a publication or analyst only if it appears in the headline/context; never write 'according to reports'\n"
        "- Use the concrete numbers, names and dates in the context so the post is specific\n"
        f"- End with 1-3 relevant hashtags (suggested: {CAT_HASHTAGS[cat]})\n"
        "- No links, no quotes around the post, no preamble\n"
        "Output only the post text."
    )
    return ask_claude(PERSONA, prompt).strip('"').strip()


# ---------- SAFETY / QUALITY ----------
def killed():
    """/pause in Telegram creates a STOP file in DATA_DIR; /resume removes it."""
    if KILL_FILE.exists():
        log.info("Paused (STOP file)")
        return True
    return False


def numbers_supported(text, item):
    """Every number in the post must appear in the source headline/context."""
    body = re.sub(r"#\w+", "", text).replace(",", "")
    src = (item["title"] + " " + item["summary"]).replace(",", "")
    return all(n in src for n in re.findall(r"\d+(?:\.\d+)?", body))


def quality_check(item, text):
    """Second Claude pass: score usefulness, accuracy, spam risk. Returns (ok, scores)."""
    prompt = (
        f"Source headline: {item['title']}\n"
        f"Source context: {item['summary']}\n\n"
        f"Draft X post:\n{text}\n\n"
        "Score the draft from 0 to 10 on:\n"
        "- usefulness: states a clear, specific, newsworthy fact for a crypto audience (do NOT penalize a post for "
        "lacking opinion or analysis - none is wanted)\n"
        "- accuracy: every claim is supported by the source; nothing invented\n"
        "- spam_risk: 10 = looks like spam, shilling or a scam promotion\n"
        'Return ONLY JSON: {"usefulness": n, "accuracy": n, "spam_risk": n, "reason": "short"}'
    )
    raw = ask_claude("You are a strict crypto news editor. Reply with the JSON object only, no other text.",
                     prompt, max_tokens=600)
    s = {}
    m = re.search(r"\{.*\}", raw, re.S)
    if m:
        try:
            s = json.loads(m.group(0))
        except Exception:
            s = {}
    for k in ("usefulness", "accuracy", "spam_risk"):  # fallback: pull the numbers out of messy output
        if not isinstance(s.get(k), (int, float)):
            mm = re.search(r'"?' + k + r'"?\s*[:=]\s*"?(\d+(?:\.\d+)?)', raw)
            if mm:
                s[k] = float(mm.group(1))
    if not all(isinstance(s.get(k), (int, float)) for k in ("usefulness", "accuracy", "spam_risk")):
        log.warning("quality check unparseable, raw reply: %r", raw[:300])
        return False, {"reason": "unparseable score"}
    qmin = cfg("quality_min")
    ok = s["usefulness"] >= qmin and s["accuracy"] >= cfg("accuracy_min") and s["spam_risk"] <= 4
    return ok, s


def needs_review(cat):
    return cfg("review_all") or cat in review_cats()


# ---------- ENGAGEMENT LOG ----------
def log_post(tweet_id, cat, text):
    rows = load_json(LOG_FILE, [])
    rows.append({"id": str(tweet_id), "t": time.time(), "cat": cat, "text": text, "m1": None, "m24": None})
    LOG_FILE.write_text(json.dumps(rows[-500:], indent=2))


def update_metrics():
    if not cfg("enable_metrics"):
        return
    rows = load_json(LOG_FILE, [])
    now = time.time()
    due = [r for r in rows
           if (r["m1"] is None and now - r["t"] >= 3600) or (r["m24"] is None and now - r["t"] >= 86400)]
    if not due:
        return
    resp = x.get_tweets(ids=[r["id"] for r in due][:100], tweet_fields=["public_metrics"], user_auth=True)
    metrics = {str(t.id): t.public_metrics for t in (resp.data or [])}
    for r in due:
        m = metrics.get(r["id"])
        if not m:
            continue
        if now - r["t"] >= 86400:
            r["m24"] = m
            r["m1"] = r["m1"] or m
        else:
            r["m1"] = m
    LOG_FILE.write_text(json.dumps(rows, indent=2))


def daily_summary():
    rows = [r for r in load_json(LOG_FILE, []) if time.time() - r["t"] < 86400]
    by_cat = {}
    for r in rows:
        c = by_cat.setdefault(r["cat"], {"posts": 0, "likes": 0, "replies": 0})
        c["posts"] += 1
        m = r["m24"] or r["m1"] or {}
        c["likes"] += m.get("like_count", 0)
        c["replies"] += m.get("reply_count", 0)
    log.info("DAILY SUMMARY (last 24h): %s", json.dumps(by_cat))


# ---------- PUBLISH ----------
def upload_card(card_path):
    """Upload the image card. Tries the v1.1 endpoint (tweepy), then X's v2 upload. Returns a media id or None."""
    errs = []
    try:
        return x_v1.media_upload(filename=card_path).media_id
    except Exception as e:
        errs.append(f"v1.1 upload: {str(e)[:200]}")
    try:
        auth = OAuth1(os.environ["X_API_KEY"], os.environ["X_API_SECRET"],
                      os.environ["X_ACCESS_TOKEN"], os.environ["X_ACCESS_TOKEN_SECRET"])
        with open(card_path, "rb") as f:
            r = requests.post("https://api.x.com/2/media/upload", auth=auth, files={"media": f},
                              data={"media_category": "tweet_image"}, timeout=60)
        if r.ok:
            j = r.json()
            mid = (j.get("data") or {}).get("id") or j.get("media_id_string")
            if mid:
                return str(mid)
        errs.append(f"v2 upload: HTTP {r.status_code} {r.text[:200]}")
    except Exception as e:
        errs.append(f"v2 upload: {str(e)[:200]}")
    alert_once("media_fail", "⚠️ Image upload failed - posted TEXT ONLY.\n" + "\n".join(errs), every_min=60)
    log.warning("Image upload failed: %s", " | ".join(errs))
    return None


def publish(text, title, cat, breaking, card_path, kind="regular"):
    state = load_state()
    roll_day(state)
    dry = cfg("dry_run")
    media_ids = None
    if card_path and not dry:
        mid = upload_card(card_path)
        media_ids = [mid] if mid else None
    log.info("POST [%s%s]: %s", cat, " BREAKING" if breaking else "", text)
    if not dry:
        try:
            r = x.create_tweet(text=text, media_ids=media_ids)
        except tweepy.errors.HTTPException as e:
            if getattr(e.response, "status_code", None) == 402 or "credit" in str(e).lower():
                alert_once("x_credit", "🚨 X API credits are finished - posting is blocked. Add credits at https://console.x.com")
            raise
        log_post(r.data["id"], cat, text)
        if TG_ENABLED and cfg("tg_notify_posts"):
            tg_send(f"✅ Posted [{cat}{' BREAKING' if breaking else ''}]: https://x.com/i/status/{r.data['id']}")
    if dry:   # dry-run drafts must not use up today's real posting slots
        return
    state["count"] += 1
    if kind == "breaking":
        state["brk_count"] += 1
    elif kind == "regular":
        state["reg_count"] += 1
    if kind != "forced":   # /post and /say never use up scheduled / category slots
        state["cat_counts"][cat] = state["cat_counts"].get(cat, 0) + 1
    save_state(state)


def run_post(breaking_only, force=False):
    """force=True (/post): ignore daily limits, category caps and review. Returns the post text if one went out."""
    if killed():
        return None
    state = load_state()
    roll_day(state)
    brk_cap = cfg("max_breaking_per_day")
    brk_full = brk_cap > 0 and state["brk_count"] >= brk_cap
    reg_full = state["reg_count"] >= cfg("posts_per_day")
    if not force and breaking_only and brk_full:
        log.info("Breaking cap reached (%d/day)", brk_cap)
        return None
    if not force and not breaking_only and reg_full:
        log.info("Scheduled posts done for today (%d)", cfg("posts_per_day"))
        return None
    items = []
    for n in fetch_news():
        if not is_niche(n) or is_dup(n["title"], state["posted"]):
            continue
        brk = is_breaking(n["title"])
        if breaking_only and not brk:
            continue
        # breaking stories bypass the category caps (and the scheduled posts/day limit)
        bypass = brk and not brk_full
        if not force and not bypass and state["cat_counts"].get(n["cat"], 0) >= cfg("cap_" + n["cat"]):
            continue
        items.append(n)
    if not items:
        log.info("No fresh %s item", "breaking" if breaking_only else "")
        return None
    items.sort(key=lambda n: (not is_breaking(n["title"]), CAT_PRIORITY[n["cat"]], n["age"]))
    for item in items[:5 if force else 3]:   # try the best few candidates; stop at the first one that passes
        cat = item["cat"]
        breaking = is_breaking(item["title"])
        kind = "forced" if force else ("breaking" if (breaking and not brk_full) else "regular")

        # mark as seen first so a rejected/failed story is never retried every 10 minutes
        state["posted"].append(item["title"])
        save_state(state)

        if len(item["summary"]) < 250 and item.get("link"):
            extra = article_text(item["link"])
            if extra:
                item["summary"] = (item["summary"] + " " + extra).strip()[:1800]
        text = generate_post(item, breaking)
        marked = text                      # keeps **KEYWORD** markers; all checks run on the plain text
        text = text.replace("**", "")
        if len(text.strip()) < 30:
            log.info("SKIP (empty or too short draft): %r", text)
            continue
        if x_len(text) > 280:
            text = ask_claude(PERSONA, f"Shorten to under 260 characters, keep hashtags:\n{text}")
            marked = text = text.replace("**", "")
        if x_len(text) > 280:
            log.warning("Post too long, skipping")
            continue
        if not numbers_supported(text, item):
            log.info("SKIP (number not in source): %s", text)
            continue
        ok, scores = quality_check(item, text)
        if not ok:
            log.info("SKIP (quality %s): %s", scores, text)
            continue
        text = style_text(marked)          # bold capital key words, applied after all checks
        if cat in DISCLAIMER_CATS and x_len(text) + 6 <= 280:
            text += "\nDYOR"

        card = None
        if cfg("use_image"):
            if cfg("use_article_image"):
                card = article_image(item)
            if not card:
                try:
                    card = make_card(item.get("card", item["title"])[:150], cat, breaking,
                                     out=str(CARDS_DIR / f"{int(time.time())}.png"))
                except Exception as e:
                    log.warning("Card failed, text only: %s", e)

        if needs_review(cat) and not force:
            q = load_json(QUEUE_FILE, [])
            q.append({"id": str(int(time.time() * 1000)), "text": text, "title": item["title"],
                      "cat": cat, "breaking": breaking, "card": card, "t": time.time(), "scores": scores,
                      "kind": kind})
            QUEUE_FILE.write_text(json.dumps(q, indent=2))
            log.info("QUEUED for review [%s]: %s", cat, text)
            if TG_ENABLED:
                tg_send_review(q[-1])
            return None
        _last.update(card=card, cat=cat, title=item["title"], breaking=breaking)
        publish(text, item["title"], cat, breaking, card, kind=kind)
        return text
    log.info("No candidate passed the checks this run")
    return None


def review_cli():
    """python x_bot.py review  -> approve / edit / reject queued posts."""
    q = load_json(QUEUE_FILE, [])
    if not q:
        print("Review queue is empty.")
        return
    keep = []
    for it in q:
        age = (time.time() - it["t"]) / 60
        print(f"\n[{it['cat']}{' BREAKING' if it['breaking'] else ''}] queued {age:.0f} min ago | scores {it.get('scores')}")
        print(f"Source: {it['title']}\n---\n{it['text']}\n---")
        a = input("[a]pprove / [e]dit / [r]eject / [s]kip: ").strip().lower()
        if a == "e":
            new = input("New text: ").strip()
            if new:
                it["text"], a = new, "a"
        if a == "a":
            if x_len(it["text"]) > 280:
                print("Too long (>280), skipped.")
                keep.append(it)
                continue
            publish(it["text"], it["title"], it["cat"], it["breaking"], it["card"], kind=it.get("kind", "regular"))
        elif a == "s":
            keep.append(it)
    QUEUE_FILE.write_text(json.dumps(keep, indent=2))


# ---------- REPLIES (comments on my posts only) ----------
_me = {}


def get_me():
    if "d" not in _me:
        _me["d"] = x.get_me().data  # fetched once; every call would be billed
    return _me["d"]


def do_replies():
    if killed() or not cfg("enable_replies"):
        return
    state = load_state()
    me = get_me()
    resp = x.get_users_mentions(
        user_auth=True,
        id=me.id,
        since_id=state["since_id"],
        max_results=10,
        tweet_fields=["author_id", "conversation_id", "text", "in_reply_to_user_id"],
    )
    mentions = resp.data or []
    if not mentions:
        log.info("No new comments")
        return

    mentions = sorted(mentions, key=lambda m: int(m.id))
    state["since_id"] = str(mentions[-1].id)
    count = 0
    max_replies = cfg("max_replies_per_run")
    for m in mentions:
        if count >= max_replies:
            break
        author = str(m.author_id)
        if author == str(me.id) or str(m.id) in state["replied"]:
            continue
        if str(m.in_reply_to_user_id) != str(me.id):
            continue  # not a comment on my post
        body = m.text.lower()
        if any(w in body for w in OPT_OUT_WORDS):
            if author not in state["opted_out"]:
                state["opted_out"].append(author)
            continue
        if author in state["opted_out"]:
            continue
        pair = f"{author}:{m.conversation_id}"
        if pair in state["replied"]:
            continue  # already replied to this person on this post
        prompt = (
            f"Someone commented on your X post:\n\"{m.text}\"\n\n"
            "Write a short, helpful, friendly reply (max 240 characters). Vary the wording. "
            "If it is a genuine question, answer it with one concrete useful insight instead of a generic thanks. "
            "no hashtags, no links, no promotion.\n"
            "If the comment is spam, a scam, abusive, asks for guaranteed signals/financial advice, "
            "or is not worth replying to, output exactly: SKIP\n"
            "Output only the reply text."
        )
        reply = ask_claude(PERSONA, prompt, max_tokens=200).strip('"').strip()
        if reply.upper().startswith("SKIP") or len(reply) > 280:
            continue
        log.info("REPLY to %s: %s", m.id, reply)
        if not cfg("dry_run"):
            try:
                x.create_tweet(text=reply, in_reply_to_tweet_id=m.id)
            except tweepy.errors.TweepyException as e:
                # self-serve API only allows replies to people who @mentioned/quoted you
                log.warning("Reply refused by X (%s): %s", m.id, e)
        state["replied"] += [str(m.id), pair]
        count += 1
        time.sleep(random.randint(20, 60))
    save_state(state)


# ---------- TELEGRAM (approval buttons + settings) ----------
ACTIONS = pyqueue.Queue()  # poll thread -> main thread (only the main thread touches state/queue/settings files)
TG_BASE = f"https://api.telegram.org/bot{TG_TOKEN}"
SETTING_ACTIONS = {"set", "reset", "addbreak", "delbreak"}


def tg(method, files=None, **params):
    try:
        if files:
            r = requests.post(f"{TG_BASE}/{method}", data=params, files=files, timeout=60)
        else:
            r = requests.post(f"{TG_BASE}/{method}", json=params, timeout=40)
        return r.json()
    except Exception as e:
        log.warning("telegram %s failed: %s", method, e)
        return {}


def tg_send(text, markup=None, html=False):
    if TG_ENABLED:
        extra = {"reply_markup": markup} if markup else {}
        if html:
            extra["parse_mode"] = "HTML"
        tg("sendMessage", chat_id=TG_CHAT, text=text[:4000], disable_web_page_preview=True, **extra)


def enqueue_draft(text, card, title, cat, breaking):
    """Keep a dry-run draft in the review queue so it can be posted later (with its image) after going LIVE."""
    q = load_json(QUEUE_FILE, [])
    it = {"id": str(int(time.time() * 1000)), "text": text, "title": title, "cat": cat, "breaking": breaking,
          "card": card, "t": time.time(), "scores": {}, "kind": "forced"}
    q.append(it)
    QUEUE_FILE.write_text(json.dumps(q, indent=2))
    return it


def tg_draft_box(text, card=None, item=None):
    """Dry-run draft: image + monospace '/say ...' box (tap to copy) + Approve/Edit/Reject buttons that post THIS draft
    (same image, same text) once you are LIVE."""
    body = ("🟡 DRY_RUN is on - NOT posted yet.\n"
            "To post THIS draft with its image: tap 🔴 Go LIVE, then ✅ Approve below.\n"
            "Or tap the box to copy it for /say:\n\n<pre>" + html_escape("/say " + text) + "</pre>")
    kb = None
    if item:
        kb = {"inline_keyboard": [[
            {"text": "✅ Approve", "callback_data": f"a:{item['id']}"},
            {"text": "✏️ Edit", "callback_data": f"e:{item['id']}"},
            {"text": "❌ Reject", "callback_data": f"r:{item['id']}"},
        ]]}
    if card and os.path.exists(card):
        with open(card, "rb") as f:
            extra = {"reply_markup": json.dumps(kb)} if kb else {}
            tg("sendPhoto", files={"photo": f}, chat_id=TG_CHAT, caption=body[:1024], parse_mode="HTML", **extra)
    else:
        tg_send(body, kb, html=True)


def tg_download_image(msg):
    """Download the photo (or image file) of a Telegram message into DATA_DIR/cards. Returns the path or None."""
    fid = None
    if msg.get("photo"):
        fid = msg["photo"][-1]["file_id"]            # largest size
    elif msg.get("document") and str(msg["document"].get("mime_type", "")).startswith("image/"):
        fid = msg["document"]["file_id"]
    if not fid:
        return None
    fp = (tg("getFile", file_id=fid).get("result") or {}).get("file_path")
    if not fp:
        return None
    try:
        r = requests.get(f"https://api.telegram.org/file/bot{TG_TOKEN}/{fp}", timeout=60)
        if r.status_code != 200 or len(r.content) > 5 * 1024 * 1024:   # X limit for post images: 5 MB
            return None
        path = CARDS_DIR / f"user_{int(time.time() * 1000)}{os.path.splitext(fp)[1] or '.jpg'}"
        path.write_bytes(r.content)
        return str(path)
    except Exception as e:
        log.warning("image download failed: %s", e)
        return None


def handle_photo_message(msg):
    """A photo sent to the bot: caption '/say your text' posts it with that text."""
    parts = (msg.get("caption") or "").strip().split(None, 1)
    if not parts or parts[0].split("@")[0].lower() != "/say":
        tg_send("To post your own image, send the photo with the caption:  /say your text")
    elif len(parts) < 2:
        tg_send("Add your text in the caption:  /say your text")
    else:
        path = tg_download_image(msg)
        if path:
            ACTIONS.put(("say", parts[1].strip(), path))
        else:
            tg_send("Couldn't use that image (send it as a photo or image file, max 5 MB).")


def card_for_text(text):
    """Image card for a /say post: headline = first sentence without hashtags."""
    if not cfg("use_image"):
        return None
    try:
        head = re.sub(r"#\w+", "", from_bold(text)).replace("\n", " ").strip()
        head = re.split(r"(?<=[.!?])\s", head)[0][:140] or "Crypto update"
        return make_card(head, "news", False, out=str(CARDS_DIR / f"{int(time.time())}.png"))
    except Exception as e:
        log.warning("Card failed, text only: %s", e)
        return None


# persistent button keyboard at the bottom of the chat; each button sends the command on the right
MENU_KB = {"keyboard": [
    [{"text": "📊 Status"}, {"text": "📰 Post now"}],
    [{"text": "⚙️ Settings"}, {"text": "⏸ Pause"}, {"text": "▶️ Resume"}],
    [{"text": "🔴 Go LIVE"}, {"text": "🟡 Dry run"}],
    [{"text": "⚡ Breaking list"}, {"text": "❓ Help"}],
], "resize_keyboard": True, "is_persistent": True}
BUTTONS = {
    "📊 Status": "/status", "📰 Post now": "/post", "⚙️ Settings": "/settings",
    "⏸ Pause": "/pause", "▶️ Resume": "/resume", "🔴 Go LIVE": "/golive",
    "🟡 Dry run": "/dryrun", "⚡ Breaking list": "/breaking", "❓ Help": "/help",
}


def tg_send_review(it):
    sc = it.get("scores") or {}
    caption = (
        f"REVIEW [{it['cat']}{' BREAKING' if it['breaking'] else ''}] | "
        f"useful {sc.get('usefulness', '?')} / accurate {sc.get('accuracy', '?')} / spam {sc.get('spam_risk', '?')}\n"
        f"Source: {it['title'][:150]}\n\n{it['text']}"
    )
    kb = {"inline_keyboard": [[
        {"text": "✅ Approve", "callback_data": f"a:{it['id']}"},
        {"text": "✏️ Edit", "callback_data": f"e:{it['id']}"},
        {"text": "❌ Reject", "callback_data": f"r:{it['id']}"},
    ]]}
    card = it.get("card")
    if card and os.path.exists(card):
        with open(card, "rb") as f:
            tg("sendPhoto", files={"photo": f}, chat_id=TG_CHAT, caption=caption[:1000],
               reply_markup=json.dumps(kb))
    else:
        tg("sendMessage", chat_id=TG_CHAT, text=caption[:4000], reply_markup=kb)


def status_text():
    st = load_json(STATE_FILE, {})
    paused = KILL_FILE.exists()
    brk_cap = cfg("max_breaking_per_day")
    return (
        f"Paused: {paused} | DRY_RUN: {cfg('dry_run')} | Approve every post: {cfg('review_all')}\n"
        f"Scheduled today: {st.get('reg_count', 0)}/{cfg('posts_per_day')}\n"
        f"Breaking today: {st.get('brk_count', 0)}/{brk_cap if brk_cap else 'no limit'}\n"
        f"Per category: {st.get('cat_counts', {})}\n"
        f"Waiting for review: {len(load_json(QUEUE_FILE, []))}"
    )


def handle_command(text):
    """Runs in the poll thread. Read-only commands answer directly; changes go to the main thread."""
    parts = text.split(None, 1)
    cmd, rest = parts[0].split("@")[0].lower(), (parts[1].strip() if len(parts) > 1 else "")
    if cmd == "/pause":
        KILL_FILE.touch()
        tg_send("⏸ Paused. Send /resume to continue.")
    elif cmd == "/resume":
        KILL_FILE.unlink(missing_ok=True)
        tg_send("▶️ Resumed.")
    elif cmd == "/status":
        tg_send(status_text())
    elif cmd in ("/help", "/commands"):
        tg_send(HELP_TEXT)
    elif cmd == "/settings":
        tg_send(settings_html(), html=True)
    elif cmd == "/breaking":
        tg_send("Breaking keywords (these bypass the scheduled posts/day limit):\n" + ", ".join(breaking_keywords()))
    elif cmd == "/menu":
        tg_send("Buttons ready 👇", MENU_KB)
    elif cmd == "/post":
        ACTIONS.put(("postnow", None, None))
    elif cmd == "/say":
        ACTIONS.put(("say", rest, None)) if rest else tg_send("Usage: /say <your post text>   (posts immediately, max 280 chars)")
    elif cmd == "/sayt":
        ACTIONS.put(("say", rest, "none")) if rest else tg_send("Usage: /sayt <text>   (posts text only, no image)")
    elif cmd == "/golive":
        tg("sendMessage", chat_id=TG_CHAT, text="Go LIVE? The bot will post to X for real.",
           reply_markup={"inline_keyboard": [[{"text": "✅ Yes, go LIVE", "callback_data": "c:live"},
                                              {"text": "Cancel", "callback_data": "x:live"}]]})
    elif cmd == "/dryrun":
        ACTIONS.put(("set", "dry_run", "1"))
    elif cmd == "/set":
        m = re.match(r"^(\S+?)\s*[=:]\s*(.+)$", rest, re.S) or re.match(r"^(\S+)\s+(.+)$", rest, re.S)
        if not m:
            tg_send("Usage: /set key = value   e.g. /set posts_per_day = 4\nSend /settings to see all keys.")
        else:
            ACTIONS.put(("set", m.group(1).lower(), m.group(2).strip()))
    elif cmd == "/reset":
        if not rest:
            tg_send("Usage: /reset <key>")
        else:
            ACTIONS.put(("reset", rest.split()[0].lower(), None))
    elif cmd == "/addbreak":
        ACTIONS.put(("addbreak", rest, None)) if rest else tg_send("Usage: /addbreak <word or phrase>")
    elif cmd == "/delbreak":
        ACTIONS.put(("delbreak", rest, None)) if rest else tg_send("Usage: /delbreak <word or phrase>")
    else:
        return False
    return True


COMMAND_WORDS = {"/set", "/reset", "/say", "/sayt", "/post", "/status", "/pause", "/resume", "/settings", "/breaking",
                 "/addbreak", "/delbreak", "/menu", "/golive", "/dryrun", "/help", "/commands"}


def split_commands(text):
    """One message may hold several commands, one per line. Lines that don't start a command belong to the
    previous one, so a multi-line /say text stays in one piece."""
    out = []
    for line in text.split("\n"):
        word = line.strip().split(None, 1)[0].split("@")[0].lower() if line.strip() else ""
        if word in COMMAND_WORDS or not out:
            out.append(line)
        else:
            out[-1] += "\n" + line
    return [c.strip() for c in out if c.strip()]


def tg_poll():
    """Background thread: long-polls Telegram for button taps, edits and commands."""
    offset, pending_edit = None, None
    while True:
        try:
            params = {"timeout": 30, "allowed_updates": json.dumps(["message", "callback_query"])}
            if offset:
                params["offset"] = offset
            data = requests.get(f"{TG_BASE}/getUpdates", params=params, timeout=45).json()
            for u in data.get("result", []):
                offset = u["update_id"] + 1
                cb = u.get("callback_query")
                if cb:
                    if str(cb["from"]["id"]) != TG_CHAT:
                        tg("answerCallbackQuery", callback_query_id=cb["id"], text="Not allowed")
                        continue
                    kind, qid = cb["data"].split(":", 1)
                    tg("answerCallbackQuery", callback_query_id=cb["id"], text="Working...")
                    tg("editMessageReplyMarkup", chat_id=TG_CHAT, message_id=cb["message"]["message_id"],
                       reply_markup={"inline_keyboard": []})  # remove buttons -> no double taps
                    if kind == "c":
                        ACTIONS.put(("set", "dry_run", "0"))
                    elif kind == "x":
                        tg_send("Cancelled - still in DRY_RUN." if cfg("dry_run") else "Cancelled.")
                    elif kind == "e":
                        pending_edit = qid
                        tg_send("Send the new post text now (max 280 characters).")
                    else:
                        ACTIONS.put(("approve" if kind == "a" else "reject", qid, None))
                    continue
                msg = u.get("message")
                if msg and (msg.get("photo") or msg.get("document")) and str(msg["chat"]["id"]) == TG_CHAT:
                    handle_photo_message(msg)
                    continue
                if not msg or not msg.get("text"):
                    continue
                text = BUTTONS.get(msg["text"].strip(), msg["text"].strip())
                chat = str(msg["chat"]["id"])
                if text == "/start":  # helps you find your chat id during setup
                    tg("sendMessage", chat_id=chat, text=f"Your chat id: {chat}")
                    continue
                if chat != TG_CHAT:
                    continue
                if text.startswith("/"):
                    for one in split_commands(text):
                        if not handle_command(one):
                            tg_send("Unknown command. Send /help")
                elif pending_edit:
                    ACTIONS.put(("edit", pending_edit, text))
                    pending_edit = None
        except Exception as e:
            log.warning("telegram poll error: %s", e)
            time.sleep(5)


def process_actions():
    """Runs in the main thread: executes settings changes, approve / edit / reject taps, expires stale review items."""
    if not TG_ENABLED:
        return
    expire = cfg("review_expire_min")
    q = load_json(QUEUE_FILE, [])
    fresh = [i for i in q if (time.time() - i["t"]) / 60 <= expire]
    if len(fresh) != len(q):
        QUEUE_FILE.write_text(json.dumps(fresh, indent=2))
        tg_send(f"⌛ Dropped {len(q) - len(fresh)} review item(s) older than {expire} min.")
    replies = []
    while True:
        try:
            kind, qid, extra = ACTIONS.get_nowait()
        except pyqueue.Empty:
            break
        if kind == "postnow":
            if killed():
                tg_send("⏸ Bot is paused - tap Resume first.")
                continue
            tg_send("⏳ Looking for a story and writing the post...")
            try:
                text = run_post(False, force=True)
            except Exception as e:
                log.exception("forced post failed: %s", e)
                tg_send(f"❌ Post failed: {str(e)[:300]}")
                continue
            if text is None:
                tg_send("😕 No fresh story passed the checks right now. Try again in a few minutes, or use /say your own text.")
            elif cfg("dry_run"):
                tg_draft_box(text, _last.get("card"),
                             enqueue_draft(text, _last.get("card"), _last.get("title", "manual /post"),
                                           _last.get("cat", "news"), _last.get("breaking", False)))
            elif not cfg("tg_notify_posts"):
                tg_send("✅ Posted:\n\n" + text)
            continue
        if kind == "say":
            text = (qid or "").strip()
            if killed():
                tg_send("⏸ Bot is paused - tap Resume first.")
            elif not text or x_len(text) > 280:
                tg_send(f"Text must be 1-280 characters (yours: {x_len(text)}; emoji and bold letters count double).")
            else:
                if extra == "none":
                    card = None
                elif extra and os.path.exists(extra):
                    card = extra               # the photo you sent
                else:
                    card = card_for_text(text)
                if cfg("dry_run"):
                    tg_draft_box(text, card, enqueue_draft(text, card, "manual /say", "news", False))
                    continue
                try:
                    publish(text, "manual", "news", False, card, kind="forced")
                except Exception as e:
                    log.exception("say failed: %s", e)
                    tg_send(f"❌ Post failed: {str(e)[:300]}")
                    continue
                if not cfg("tg_notify_posts"):
                    tg_send("✅ Posted.")
            continue
        if kind in SETTING_ACTIONS:
            try:
                replies.append(apply_setting(kind, qid, extra))
            except Exception as e:
                log.exception("settings change failed: %s", e)
                replies.append(f"❌ Could not apply that: {e}")
            continue
        q = load_json(QUEUE_FILE, [])
        it = next((i for i in q if i["id"] == qid), None)
        if not it:
            tg_send("That item was already handled or expired.")
            continue
        if kind == "reject":
            QUEUE_FILE.write_text(json.dumps([i for i in q if i["id"] != qid], indent=2))
            tg_send("❌ Rejected.")
        elif kind == "edit":
            if x_len(extra) > 280:
                tg_send(f"Too long ({len(extra)} chars). Original kept:")
            else:
                it["text"] = extra
                QUEUE_FILE.write_text(json.dumps(q, indent=2))
            tg_send_review(it)
        elif kind == "approve":
            if killed():
                tg_send("⏸ Bot is paused - /resume first. Item stays in the queue.")
                tg_send_review(it)
                continue
            if cfg("dry_run"):   # keep the draft: approving in dry-run must not throw it away
                tg_send("🟡 DRY_RUN is on - NOT posted. Tap 🔴 Go LIVE, then approve again. The draft stays in the queue.")
                tg_send_review(it)
                continue
            QUEUE_FILE.write_text(json.dumps([i for i in q if i["id"] != qid], indent=2))
            publish(it["text"], it["title"], it["cat"], it["breaking"], it.get("card"), kind=it.get("kind", "regular"))
    if replies:   # one message for a whole batch of /set lines
        tg_send("\n\n".join(replies))


# ---------- SCHEDULER ----------
def safe(fn):
    def wrapper():
        try:
            fn()
        except Exception as e:
            log.exception("job failed: %s", e)
    return wrapper


def apply_schedule():
    """(Re)build the jobs that depend on settings. Called at start and when an interval setting changes."""
    schedule.clear("cfg")
    interval_min = max(60, int(24 * 60 / max(1, cfg("posts_per_day"))))
    schedule.every(cfg("break_check_minutes")).minutes.do(safe(lambda: run_post(True))).tag("cfg")
    # randomized spacing (+/-15%) so posts don't land on a fixed clock
    schedule.every(int(interval_min * 0.85)).to(int(interval_min * 1.15)).minutes.do(
        safe(lambda: run_post(False))).tag("cfg")
    schedule.every(cfg("reply_check_minutes")).minutes.do(safe(do_replies)).tag("cfg")
    log.info("Schedule: breaking every %d min | scheduled posts every ~%d min (%d/day)",
             cfg("break_check_minutes"), interval_min, cfg("posts_per_day"))


def main():
    log.info("Storage: %s | persistent=%s", DATA_DIR, PERSISTENT)
    log.info("Started | dry_run=%s | images=%s | review=%s | telegram=%s", cfg("dry_run"), cfg("use_image"),
             "ALL" if cfg("review_all") else sorted(review_cats()), TG_ENABLED)
    if TG_ENABLED:
        threading.Thread(target=tg_poll, daemon=True).start()
        tg("setMyCommands", commands=[
            {"command": "settings", "description": "show all settings"},
            {"command": "set", "description": "change a setting: /set key value"},
            {"command": "reset", "description": "reset a setting to default"},
            {"command": "breaking", "description": "list breaking keywords"},
            {"command": "addbreak", "description": "add breaking keyword"},
            {"command": "delbreak", "description": "remove breaking keyword"},
            {"command": "post", "description": "post best story now"},
            {"command": "say", "description": "post text now (+ image card)"},
            {"command": "sayt", "description": "post text only, no image"},
            {"command": "menu", "description": "show buttons"},
            {"command": "golive", "description": "go live (asks to confirm)"},
            {"command": "dryrun", "description": "back to dry-run"},
            {"command": "status", "description": "today's counters"},
            {"command": "pause", "description": "stop all posting"},
            {"command": "resume", "description": "resume posting"},
            {"command": "help", "description": "all commands"},
        ])
        tg_send("🤖 Bot started" + (" (DRY_RUN - nothing will be posted. Go live: /set dry_run 0)" if cfg("dry_run") else " (LIVE)")
                + "\n" + STORAGE_NOTE + "\nSend /help for commands", MENU_KB)
    else:
        log.warning("Telegram not configured: settings cannot be changed, defaults apply (DRY_RUN stays on).")
    apply_schedule()
    schedule.every(30).minutes.do(safe(update_metrics))
    schedule.every().day.at("23:55").do(safe(daily_summary))
    schedule.every(5).seconds.do(safe(process_actions))
    safe(lambda: run_post(False))()  # first run immediately
    while True:
        schedule.run_pending()
        time.sleep(5)


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "review":
        review_cli()
    else:
        main()
