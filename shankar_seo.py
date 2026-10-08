#!/usr/bin/env python3
"""
SHANKAR SEO  -  On-page SEO Checker
Paste any website link -> get the 14-point on-page SEO checklist.
Green tick = site follows the rule, Red cross = site does not.

Run:   python shankar_seo.py            (then open http://localhost:8000)
Needs: Python 3.8+  (no extra packages)
"""
import gzip
import json
import re
import ssl
import sys
import threading
import time
import webbrowser
import zlib
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from html.parser import HTMLParser
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.error import HTTPError, URLError
from urllib.parse import parse_qs, urldefrag, urljoin, urlparse
from urllib.request import Request, urlopen
from urllib.robotparser import RobotFileParser

UA = "Mozilla/5.0 (compatible; ShankarSEO/1.0; +https://localhost)"
STOP = set("""a an and are as at be but by for from has have he her his i if in into is it its of on or our she so
that the their them then there these they this to us was we were what when where which who will with you your not
can all any more most other some such than too very just about also how why do does did been being""".split())
SKIP_EXT = (".pdf", ".jpg", ".jpeg", ".png", ".gif", ".webp", ".svg", ".zip", ".rar", ".mp4", ".mp3", ".css",
            ".js", ".xml", ".ico", ".doc", ".docx", ".xls", ".xlsx", ".ppt", ".pptx", ".json", ".txt")
GENERIC_ANCHORS = {"", "click here", "here", "read more", "more", "learn more", "link", "this", "click"}


# --------------------------------------------------------------------------- fetching
def fetch(url, timeout=15, max_bytes=3_000_000):
    headers = {"User-Agent": UA, "Accept": "text/html,application/xhtml+xml,*/*;q=0.8",
               "Accept-Encoding": "gzip, deflate"}
    req = Request(url, headers=headers)
    start = time.time()
    try:
        try:
            resp = urlopen(req, timeout=timeout, context=ssl.create_default_context())
        except URLError as e:
            if isinstance(getattr(e, "reason", None), ssl.SSLError):
                resp = urlopen(req, timeout=timeout, context=ssl._create_unverified_context())
            else:
                raise
    except HTTPError as e:
        resp = e
    raw = resp.read(max_bytes)
    elapsed = time.time() - start
    enc = (resp.headers.get("Content-Encoding") or "").lower()
    try:
        if "gzip" in enc:
            raw = gzip.decompress(raw)
        elif "deflate" in enc:
            raw = zlib.decompress(raw)
    except Exception:
        pass
    ctype = resp.headers.get("Content-Type") or ""
    m = re.search(r"charset=([\w-]+)", ctype, re.I) or re.search(rb"charset=[\"']?([\w-]+)", raw[:3000], re.I)
    charset = (m.group(1).decode() if isinstance(m.group(1), bytes) else m.group(1)) if m else "utf-8"
    try:
        body = raw.decode(charset, errors="replace")
    except LookupError:
        body = raw.decode("utf-8", errors="replace")
    return {"url": resp.geturl() if hasattr(resp, "geturl") else url, "status": getattr(resp, "status", None) or resp.code,
            "headers": resp.headers, "body": body, "elapsed": elapsed, "size": len(raw), "ctype": ctype,
            "encoding": enc}


# --------------------------------------------------------------------------- HTML parsing
class PageParser(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.title = ""
        self.in_title = False
        self.metas = {}
        self.heads = []
        self.cur_head = None
        self.links = []
        self.cur_a = None
        self.imgs = []
        self.scripts = 0
        self.css = 0
        self.jsonld = []
        self.in_jsonld = False
        self.micro = False
        self.text = []
        self.skip = 0
        self.paras = []
        self.cur_p = None
        self.lists = 0
        self.tables = 0
        self.videos = 0
        self.lang = None
        self.canonical = None

    def handle_starttag(self, tag, attrs):
        a = {k.lower(): (v or "") for k, v in attrs}
        if tag == "html":
            self.lang = a.get("lang")
        elif tag == "title":
            self.in_title = True
        elif tag == "meta":
            key = (a.get("name") or a.get("property") or a.get("http-equiv") or "").lower()
            if key:
                self.metas[key] = a.get("content", "")
        elif tag == "link":
            rel = a.get("rel", "").lower()
            if "canonical" in rel:
                self.canonical = a.get("href")
            if "stylesheet" in rel:
                self.css += 1
        elif tag in ("h1", "h2", "h3", "h4", "h5", "h6"):
            self.cur_head = [int(tag[1]), ""]
        elif tag == "a" and a.get("href"):
            self.cur_a = [a["href"], "", a.get("rel", "").lower()]
        elif tag == "img":
            self.imgs.append({"alt": a.get("alt"), "src": a.get("src") or a.get("data-src", ""),
                              "lazy": a.get("loading", "").lower() == "lazy" or "data-src" in a})
            if self.cur_a is not None and a.get("alt"):
                self.cur_a[1] += " " + a["alt"]
        elif tag == "script":
            self.skip += 1
            if a.get("src"):
                self.scripts += 1
            if "ld+json" in a.get("type", "").lower():
                self.in_jsonld = True
                self.jsonld.append("")
        elif tag in ("style", "noscript", "template", "svg"):
            self.skip += 1
        elif tag == "p":
            self.cur_p = ""
        elif tag in ("ul", "ol"):
            self.lists += 1
        elif tag == "table":
            self.tables += 1
        elif tag in ("video", "iframe"):
            self.videos += 1
        if "itemscope" in a or "typeof" in a:
            self.micro = True

    def handle_endtag(self, tag):
        if tag == "title":
            self.in_title = False
        elif tag in ("h1", "h2", "h3", "h4", "h5", "h6") and self.cur_head:
            self.heads.append((self.cur_head[0], " ".join(self.cur_head[1].split())))
            self.cur_head = None
        elif tag == "a" and self.cur_a:
            self.links.append((self.cur_a[0], " ".join(self.cur_a[1].split()), self.cur_a[2]))
            self.cur_a = None
        elif tag == "script":
            self.skip = max(0, self.skip - 1)
            self.in_jsonld = False
        elif tag in ("style", "noscript", "template", "svg"):
            self.skip = max(0, self.skip - 1)
        elif tag == "p" and self.cur_p is not None:
            self.paras.append(" ".join(self.cur_p.split()))
            self.cur_p = None

    def handle_data(self, d):
        if self.in_title:
            self.title += d
        if self.in_jsonld and self.jsonld:
            self.jsonld[-1] += d
        if self.skip:
            return
        if self.cur_head is not None:
            self.cur_head[1] += d
        if self.cur_a is not None:
            self.cur_a[1] += d
        if self.cur_p is not None:
            self.cur_p += d
        self.text.append(d)


# --------------------------------------------------------------------------- helpers
def host_key(u):
    h = urlparse(u).netloc.lower()
    return h[4:] if h.startswith("www.") else h


def normalize_url(u):
    u = u.strip()
    if not re.match(r"^https?://", u, re.I):
        u = "https://" + u
    p = urlparse(u)
    if not p.netloc:
        raise ValueError("Please enter a valid website link")
    return u


def words_of(text):
    return re.findall(r"[^\W\d_]{2,}|\d+", text.lower())


def flesch(text):
    ws = re.findall(r"[A-Za-z']+", text)
    if len(ws) < 50:
        return None
    sents = max(1, len(re.findall(r"[.!?]+", text)))
    syl = sum(max(1, len(re.findall(r"[aeiouy]+", w.lower()))) for w in ws)
    return 206.835 - 1.015 * len(ws) / sents - 84.6 * syl / len(ws)


def detect_keyword(p, words):
    h1 = " ".join(t for l, t in p.heads if l == 1)
    base = f"{p.title} {h1}".lower()
    tw = [w for w in re.findall(r"[^\W\d_]{3,}", base) if w not in STOP]
    body = Counter(w for w in words if w not in STOP)
    joined = " ".join(words)
    best, best_n = None, 0
    for i in range(len(tw) - 1):
        bg = f"{tw[i]} {tw[i + 1]}"
        n = len(re.findall(r"\b" + re.escape(bg) + r"\b", joined))
        if n > best_n:
            best, best_n = bg, n
    if best and best_n >= 2:
        return best
    cands = [(body.get(w, 0), w) for w in tw]
    if cands:
        n, w = max(cands)
        if n:
            return w
    return body.most_common(1)[0][0] if body else ""


ROBOTS, RLOCK = {}, threading.Lock()


def get_robots(origin):
    with RLOCK:
        if origin in ROBOTS:
            return ROBOTS[origin]
    info = {"status": None, "rp": None, "sitemap": False}
    try:
        r = fetch(origin + "/robots.txt", timeout=10, max_bytes=500_000)
        info["status"] = r["status"]
        if r["status"] == 200 and "html" not in r["ctype"].lower():
            rp = RobotFileParser()
            rp.parse(r["body"].splitlines())
            info["rp"] = rp
            info["sitemap"] = bool(re.search(r"^\s*sitemap:", r["body"], re.I | re.M))
    except Exception:
        pass
    with RLOCK:
        ROBOTS[origin] = info
    return info


def check(cid, name, ok, notes, tip):
    return {"id": cid, "name": name, "ok": bool(ok), "notes": notes, "tip": tip}


# --------------------------------------------------------------------------- the 14 checks
def analyze_page(url, user_kw=None, want_links=False):
    r = fetch(url)
    if r["status"] >= 400:
        raise ValueError(f"Page returned HTTP {r['status']}")
    if "html" not in r["ctype"].lower() and "<html" not in r["body"][:2000].lower():
        raise ValueError("This link is not an HTML web page")
    final = r["url"]
    p = PageParser()
    p.feed(r["body"])
    text = " ".join(" ".join(p.text).split())
    words = words_of(text)
    joined = " ".join(words)
    parsed = urlparse(final)
    origin = f"{parsed.scheme}://{parsed.netloc}"

    title = " ".join(p.title.split())
    h1s = [t for l, t in p.heads if l == 1]
    desc = " ".join((p.metas.get("description") or "").split())

    kw_user = (user_kw or "").strip().lower()
    kw = kw_user or detect_keyword(p, words)
    kw_src = "entered by you" if kw_user else "auto-detected from the page"
    toks = re.findall(r"[^\W_]+", kw.lower())

    def has_kw(s):
        s = (s or "").lower()
        return bool(toks) and all(t in s for t in toks)

    slug_text = parsed.path.replace("-", " ").replace("_", " ")
    places = [n for n, s in (("title", title), ("H1", " ".join(h1s)), ("meta description", desc),
                             ("URL", slug_text)) if has_kw(s)]
    checks = []

    # 1 target keywords
    checks.append(check(1, "Identify target keywords", bool(kw) and len(places) >= 2,
                        [f"Target keyword: \u201c{kw}\u201d ({kw_src})",
                         "Found in: " + (", ".join(places) if places else "none of title / H1 / description / URL")],
                        "Pick one main keyword and use it in at least two of: title, H1, meta description, URL."))

    # 2 title tag
    tl = len(title)
    ok2 = 30 <= tl <= 65 and has_kw(title)
    checks.append(check(2, "Optimize the title tag", ok2,
                        [f"Title: \u201c{title[:90]}\u201d" if title else "No <title> tag found",
                         f"Length: {tl} characters (best 30\u201365)", "Contains keyword" if has_kw(title) else "Keyword missing in title"],
                        "Write a unique title of 30\u201365 characters with the main keyword near the start."))

    # 3 H1
    ok3 = len(h1s) == 1 and has_kw(h1s[0])
    checks.append(check(3, "Use an H1 tag for your headline", ok3,
                        [f"H1 tags found: {len(h1s)}"] + ([f"H1: \u201c{h1s[0][:90]}\u201d"] if h1s else []) +
                        (["Contains keyword" if has_kw(h1s[0]) else "Keyword missing in H1"] if h1s else []),
                        "Use exactly one H1 per page and include the main keyword in it."))

    # 4 meta description
    dl = len(desc)
    checks.append(check(4, "Write a meta description that boosts clicks", 70 <= dl <= 160,
                        [f"Description length: {dl} characters (best 70\u2013160)" if desc else "No meta description found"] +
                        ([f"\u201c{desc[:110]}\u2026\u201d"] if desc else []),
                        "Add a 70\u2013160 character description that tells people why to click."))

    # 5 URL slug
    path = parsed.path or "/"
    probs = []
    if path != "/":
        if re.search(r"[A-Z]", path):
            probs.append("has capital letters")
        if "_" in path:
            probs.append("uses underscores (use hyphens)")
        if "%20" in path or " " in path:
            probs.append("has spaces")
        if len(path) > 75:
            probs.append("longer than 75 characters")
    if parsed.query:
        probs.append("has query parameters (?...)")
    checks.append(check(5, "Check the URL slug for SEO-friendliness", not probs,
                        [f"Path: {path}", ("Problems: " + ", ".join(probs)) if probs else
                         ("Homepage URL is clean" if path == "/" else "Short, lowercase and clean")],
                        "Use short lowercase URLs with hyphens, no parameters, and the keyword inside."))

    # 6 keywords in body
    phrase = " ".join(toks)
    count = len(re.findall(r"\b" + re.escape(phrase) + r"\b", joined)) if phrase else 0
    density = (count * max(1, len(toks)) / len(words) * 100) if words else 0
    in_first = bool(phrase) and phrase in " ".join(words[:100])
    sub = [t for l, t in p.heads if l in (2, 3) and has_kw(t)]
    ok6 = count >= 2 and in_first and density <= 3.5
    checks.append(check(6, "Add target keywords to your body content", ok6,
                        [f"Keyword used {count} time(s), density {density:.1f}% (best 0.5\u20133%)",
                         "In the first 100 words" if in_first else "Not in the first 100 words",
                         f"In {len(sub)} subheading(s)"],
                        "Mention the keyword naturally in the first 100 words and a couple more times. Avoid stuffing."))

    # 7 content quality
    wc = len(words)
    fl = flesch(" ".join(p.paras)) if sum(len(x.split()) for x in p.paras) >= 50 else flesch(text)
    ok7 = wc >= 300 and (fl is None or fl >= 40)
    checks.append(check(7, "Review your content quality", ok7,
                        [f"Word count: {wc} (at least 300)",
                         f"Readability score: {fl:.0f} (40+ is easy enough)" if fl is not None else "Readability: not enough English text to score"],
                        "Cover the topic fully (300+ words), use short sentences and plain words."))

    # 8 structure
    h2 = sum(1 for l, _ in p.heads if l == 2)
    levels = [l for l, _ in p.heads]
    skipped = any(b - a > 1 for a, b in zip(levels, levels[1:]))
    plens = [len(x.split()) for x in p.paras if x]
    avg_p = sum(plens) / len(plens) if plens else 0
    ok8 = h2 >= 2 and not skipped and avg_p <= 120
    checks.append(check(8, "Structure your content thoughtfully", ok8,
                        [f"H2 subheadings: {h2} (at least 2)", "Heading order is clean" if not skipped else "Heading levels are skipped (e.g. H1 \u2192 H3)",
                         f"Average paragraph: {avg_p:.0f} words" if plens else "No paragraphs found",
                         f"Lists: {p.lists}, tables: {p.tables}"],
                        "Break content with H2/H3 headings in order, short paragraphs and bullet lists."))

    # 9 internal links
    internal, external, generic, nofollow = {}, set(), 0, 0
    me = host_key(final)
    for href, anchor, rel in p.links:
        href = href.strip()
        if not href or href.startswith(("#", "mailto:", "tel:", "javascript:")):
            continue
        absu = urldefrag(urljoin(final, href))[0]
        if not absu.startswith(("http://", "https://")):
            continue
        if host_key(absu) == me:
            internal.setdefault(absu, anchor)
            if anchor.lower() in GENERIC_ANCHORS:
                generic += 1
        else:
            external.add(absu)
            nofollow += "nofollow" in rel
    ok9 = len(internal) >= 3 and generic <= max(1, 0.3 * len(internal))
    checks.append(check(9, "Improve navigation with internal links", ok9,
                        [f"Internal links: {len(internal)} (at least 3)", f"Weak anchors (\u201cclick here\u201d, empty): {generic}",
                         f"External links: {len(external)}"],
                        "Link to 3+ related pages on your own site with descriptive anchor text."))

    # 10 visuals
    imgs = p.imgs
    noalt = sum(1 for i in imgs if not (i["alt"] or "").strip())
    ok10 = (len(imgs) >= 1 or p.videos > 0) and (len(imgs) == 0 or noalt <= 0.1 * len(imgs))
    checks.append(check(10, "Add engaging visual content", ok10,
                        [f"Images: {len(imgs)}, videos/embeds: {p.videos}", f"Images without alt text: {noalt}",
                         f"Lazy-loaded images: {sum(1 for i in imgs if i['lazy'])}"],
                        "Add relevant images or video, each with descriptive alt text."))

    # 11 schema
    types = []
    for blob in p.jsonld:
        types += re.findall(r'"@type"\s*:\s*"([^"]+)"', blob)
    ok11 = bool(p.jsonld) or p.micro
    checks.append(check(11, "Apply schema markup", ok11,
                        ["JSON-LD found: " + ", ".join(sorted(set(types))[:6]) if types else
                         ("Structured data found" if ok11 else "No structured data found")],
                        "Add JSON-LD schema (Article, Product, FAQ, LocalBusiness, Organization...)."))

    # 12 robots.txt + indexability
    rb = get_robots(origin)
    allowed, rnote = True, ""
    if rb["rp"] is not None:
        allowed = rb["rp"].can_fetch("Googlebot", final) and rb["rp"].can_fetch("*", final)
        rnote = "robots.txt found" + (" with sitemap" if rb["sitemap"] else ", no sitemap line")
    elif rb["status"] == 404:
        rnote = "No robots.txt (crawlers are allowed by default)"
    elif rb["status"] in (401, 403):
        allowed, rnote = False, f"robots.txt blocked (HTTP {rb['status']})"
    else:
        rnote = "Could not read robots.txt"
    robots_meta = (p.metas.get("robots", "") + " " + (r["headers"].get("X-Robots-Tag") or "")).lower()
    noindex = "noindex" in robots_meta
    checks.append(check(12, "Ensure robots.txt allows crawlers to access your pages", allowed and not noindex,
                        [rnote, "This page is allowed for crawlers" if allowed else "This page is BLOCKED by robots.txt",
                         "Page is set to noindex!" if noindex else "No noindex tag"],
                        "Remove Disallow rules and noindex tags for pages you want in Google."))

    # 13 page speed (lab estimate)
    kb = r["size"] / 1024
    ok13 = r["elapsed"] <= 2.0 and kb <= 500 and p.scripts <= 20
    checks.append(check(13, "Increase page speed", ok13,
                        [f"Server response + download: {r['elapsed']:.2f}s (best under 2s)", f"HTML size: {kb:.0f} KB (best under 500 KB)",
                         f"Scripts: {p.scripts}, stylesheets: {p.css}",
                         "Compression: " + (r["encoding"] or "none")],
                        "Compress files, cache, lazy-load images, and remove unused scripts. (Quick estimate, not a full Lighthouse test.)"))

    # 14 mobile
    vp = (p.metas.get("viewport") or "").lower().replace(" ", "")
    ok14 = "width=device-width" in vp and "user-scalable=no" not in vp and "maximum-scale=1" not in vp
    checks.append(check(14, "Make sure your pages are mobile-friendly", ok14,
                        [f"Viewport tag: {vp}" if vp else "No viewport meta tag",
                         "Zoom is allowed" if ("user-scalable=no" not in vp and "maximum-scale=1" not in vp) else "Zoom is blocked"],
                        'Add <meta name="viewport" content="width=device-width, initial-scale=1">.'))

    passed = sum(c["ok"] for c in checks)
    out = {"url": final, "title": title, "keyword": kw, "keyword_source": kw_src, "checks": checks,
           "passed": passed, "total": len(checks), "score": round(passed / len(checks) * 100)}
    if want_links:
        out["_internal"] = list(internal.keys())
        out["internal_count"] = len(internal)
    return out


def analyze_site(url, user_kw, total_pages):
    typed_scheme = bool(re.match(r"^https?://", url.strip(), re.I))
    url = normalize_url(url)
    try:
        main = analyze_page(url, user_kw, want_links=True)
    except URLError:
        if typed_scheme:
            raise
        url = "http://" + url[len("https://"):]
        main = analyze_page(url, user_kw, want_links=True)
    links = [u for u in main.pop("_internal") if not urlparse(u).path.lower().endswith(SKIP_EXT)]
    seen, extra = {urldefrag(main["url"])[0].rstrip("/")}, []
    for u in links:
        k = u.rstrip("/")
        if k not in seen:
            seen.add(k)
            extra.append(u)
        if len(extra) >= total_pages - 1:
            break

    def run(u):
        try:
            res = analyze_page(u)
            res["error"] = None
            return res
        except Exception as e:
            return {"url": u, "title": "", "error": str(e), "checks": [], "score": 0, "passed": 0, "total": 14}

    with ThreadPoolExecutor(max_workers=5) as ex:
        others = list(ex.map(run, extra))
    return {"main": main, "pages": [dict(main, is_main=True)] + others, "found_links": len(links)}


# --------------------------------------------------------------------------- web UI
PAGE = r'''<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>SHANKAR SEO - On-page SEO checker</title>
<link rel="preconnect" href="https://fonts.googleapis.com"><link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Bricolage+Grotesque:opsz,wght@12..96,500;12..96,700;12..96,800&family=Hanken+Grotesk:wght@400;500;600&display=swap" rel="stylesheet">
<style>
:root{--ink:#16143a;--ink2:#4b4a6b;--paper:#eef0f8;--card:#ffffff;--line:#d9dcec;--saf:#ff8f1f;--ok:#0f9d58;--okbg:#e4f6ec;--bad:#d92d20;--badbg:#fdebe9;--r:14px}
*{box-sizing:border-box}html,body{margin:0}
body{background:var(--paper);color:var(--ink);font:16px/1.5 "Hanken Grotesk",system-ui,Segoe UI,Roboto,sans-serif}
h1,h2,h3,.brand{font-family:"Bricolage Grotesque","Hanken Grotesk",system-ui,sans-serif;letter-spacing:-.02em;margin:0}
.top{background:var(--ink);color:#fff;padding:34px 20px 74px}
.wrap{max-width:980px;margin:0 auto}
.brand{font-size:15px;font-weight:700;display:flex;align-items:center;gap:10px}
.brand i{width:22px;height:22px;border-radius:6px;background:var(--saf);display:inline-block}
.top h1{font-size:clamp(34px,6vw,60px);line-height:1.02;margin:26px 0 10px;font-weight:800;max-width:14em}
.top p{margin:0;color:#b9b8dd;max-width:34em}
.form{background:var(--card);border-radius:var(--r);padding:16px;margin-top:-44px;display:grid;grid-template-columns:2fr 1.2fr .8fr auto;gap:10px;box-shadow:0 12px 30px -16px rgba(22,20,58,.45)}
.form label{display:block;font-size:13px;color:var(--ink2);margin:0 0 4px;font-weight:600}
.form input,.form select{width:100%;height:46px;border:1.5px solid var(--line);border-radius:10px;padding:0 12px;font:inherit;color:var(--ink);background:#fff}
.form input:focus,.form select:focus,button:focus-visible,.pg summary:focus-visible{outline:3px solid var(--saf);outline-offset:1px}
.form button{align-self:end;height:46px;padding:0 24px;border:0;border-radius:10px;background:var(--saf);color:#2a1700;font:700 16px "Bricolage Grotesque",sans-serif;cursor:pointer}
.form button:disabled{opacity:.6;cursor:wait}
@media(max-width:760px){.form{grid-template-columns:1fr}}
#out{margin:26px auto 80px}
.msg{padding:18px;border-radius:var(--r);background:var(--card);border:1px solid var(--line)}
.msg.err{background:var(--badbg);border-color:#f3b9b3;color:#7a1810}
.sum{display:flex;gap:22px;align-items:center;background:var(--card);border-radius:var(--r);padding:20px;border:1px solid var(--line);flex-wrap:wrap}
.ring{width:112px;height:112px;flex:none}
.sum h2{font-size:24px}.sum .u{color:var(--ink2);word-break:break-all;font-size:14px}
.pills{display:flex;gap:8px;margin-top:10px;flex-wrap:wrap}
.pill{border-radius:99px;padding:3px 12px;font-weight:600;font-size:14px}.pill.g{background:var(--okbg);color:#0a6b3b}.pill.r{background:var(--badbg);color:#9a1b11}
.list{margin-top:18px;background:var(--card);border:1px solid var(--line);border-radius:var(--r);overflow:hidden}
.row{display:grid;grid-template-columns:44px 1fr;gap:14px;padding:16px 18px;border-top:1px solid var(--line)}
.row:first-child{border-top:0}
.tick{width:36px;height:36px;border-radius:50%;display:grid;place-items:center;color:#fff;font-weight:800;font-size:19px}
.ok .tick{background:var(--ok)}.bad .tick{background:var(--bad)}
.row h3{font-size:18px;font-weight:700}
.row .n{margin:6px 0 0;padding:0;list-style:none;color:var(--ink2);font-size:14.5px}
.row .n li{padding-left:0}
.row.ok{background:linear-gradient(90deg,var(--okbg),#fff 40%)}
.row.bad{background:linear-gradient(90deg,var(--badbg),#fff 40%)}
.tip{margin-top:8px;font-size:14px;color:#8a1a10;font-weight:500}
.bonus{background:var(--ink);color:#fff;padding:10px 18px;font:700 16px "Bricolage Grotesque",sans-serif}
.pages{margin-top:26px}.pages h2{font-size:24px;margin-bottom:4px}.pages>p{margin:0 0 12px;color:var(--ink2)}
.pg{background:var(--card);border:1px solid var(--line);border-radius:12px;margin-bottom:8px;overflow:hidden}
.pg summary{list-style:none;cursor:pointer;display:grid;grid-template-columns:48px 1fr auto;gap:12px;align-items:center;padding:12px 14px}
.pg summary::-webkit-details-marker{display:none}
.sc{font:800 15px "Bricolage Grotesque",sans-serif;border-radius:8px;padding:5px 0;text-align:center}
.sc.g{background:var(--okbg);color:#0a6b3b}.sc.m{background:#fff0dc;color:#8a4b00}.sc.r{background:var(--badbg);color:#9a1b11}
.pu{min-width:0}.pu b{display:block;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;font-weight:600}
.pu span{font-size:13px;color:var(--ink2);display:block;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.dots{display:flex;gap:3px;flex-wrap:wrap;justify-content:flex-end;max-width:150px}
.dots i{width:9px;height:9px;border-radius:50%;display:block}.dots .y{background:var(--ok)}.dots .x{background:var(--bad)}
.pg .body{padding:4px 14px 14px;border-top:1px solid var(--line);display:grid;grid-template-columns:repeat(auto-fill,minmax(250px,1fr));gap:6px 18px}
.pg .body div{font-size:14px;display:flex;gap:8px;align-items:center}
.pg .body b{width:20px;height:20px;border-radius:50%;color:#fff;font-size:12px;display:grid;place-items:center;flex:none}
.pg .body .y b{background:var(--ok)}.pg .body .x b{background:var(--bad)}
.load{display:flex;align-items:center;gap:12px}.spin{width:22px;height:22px;border:3px solid var(--line);border-top-color:var(--saf);border-radius:50%;animation:s .8s linear infinite}
@keyframes s{to{transform:rotate(360deg)}}
@media(prefers-reduced-motion:reduce){.spin{animation-duration:3s}}
</style></head><body>
<header class="top"><div class="wrap">
<div class="brand"><i></i>SHANKAR SEO</div>
<h1>Paste a website link. See what passes and what fails.</h1>
<p>Every point of the 14-step on-page SEO checklist is checked on your page and its other pages. Green means done. Red means fix it.</p>
</div></header>
<main class="wrap">
<div class="form">
 <div><label for="u">Website link</label><input id="u" placeholder="example.com or https://example.com/page" autofocus></div>
 <div><label for="k">Target keyword (optional)</label><input id="k" placeholder="auto-detected if empty"></div>
 <div><label for="n">Pages to scan</label><select id="n"><option>1</option><option selected>6</option><option>10</option><option>15</option></select></div>
 <button id="go">Check SEO</button>
</div>
<div id="out"></div>
</main>
<script>
const $=s=>document.querySelector(s);
const esc=s=>String(s??"").replace(/[&<>"']/g,c=>({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"}[c]));
const cls=s=>s>=75?"g":s>=45?"m":"r";
function ring(score){const c=2*Math.PI*46,col=score>=75?"#0f9d58":score>=45?"#ff8f1f":"#d92d20";
return `<svg class="ring" viewBox="0 0 112 112" role="img" aria-label="Score ${score} out of 100"><circle cx="56" cy="56" r="46" fill="none" stroke="#e6e8f3" stroke-width="12"/><circle cx="56" cy="56" r="46" fill="none" stroke="${col}" stroke-width="12" stroke-linecap="round" stroke-dasharray="${c*score/100} ${c}" transform="rotate(-90 56 56)"/><text x="56" y="63" text-anchor="middle" font-family="Bricolage Grotesque,sans-serif" font-weight="800" font-size="30" fill="#16143a">${score}</text></svg>`}
function row(c){return `<div class="row ${c.ok?"ok":"bad"}"><div class="tick" aria-label="${c.ok?"Passed":"Failed"}">${c.ok?"\u2713":"\u2715"}</div><div><h3>${c.id}. ${esc(c.name)}</h3><ul class="n">${c.notes.map(n=>`<li>${esc(n)}</li>`).join("")}</ul>${c.ok?"":`<div class="tip">How to fix: ${esc(c.tip)}</div>`}</div></div>`}
function render(d){
 const m=d.main,cs=m.checks;
 let h=`<div class="sum">${ring(m.score)}<div><h2>${m.passed} of ${m.total} checks passed</h2><div class="u">${esc(m.url)}</div>
 <div class="pills"><span class="pill g">${m.passed} green</span><span class="pill r">${m.total-m.passed} red</span><span class="pill" style="background:#eceefa">Keyword: ${esc(m.keyword)||"none"}</span></div></div></div>`;
 h+=`<div class="list">`;
 cs.forEach(c=>{if(c.id===12)h+=`<div class="bonus">Bonus: Start on your technical SEO</div>`;h+=row(c)});
 h+=`</div>`;
 h+=`<section class="pages"><h2>Site pages</h2><p>${d.found_links} internal pages found on the home page. Showing ${d.pages.length}. Tap a page to see its ticks.</p>`;
 d.pages.forEach(p=>{
  if(p.error){h+=`<div class="pg"><div style="padding:12px 14px"><b>${esc(p.url)}</b><br><span style="color:#9a1b11">Could not scan: ${esc(p.error)}</span></div></div>`;return}
  h+=`<details class="pg"><summary><div class="sc ${cls(p.score)}">${p.score}</div><div class="pu"><b>${esc(p.title||p.url)}</b><span>${esc(p.url)}</span></div><div class="dots" title="14 checks">${p.checks.map(c=>`<i class="${c.ok?"y":"x"}"></i>`).join("")}</div></summary>
  <div class="body">${p.checks.map(c=>`<div class="${c.ok?"y":"x"}"><b>${c.ok?"\u2713":"\u2715"}</b>${c.id}. ${esc(c.name)}</div>`).join("")}</div></details>`});
 h+=`</section>`;$("#out").innerHTML=h;
}
async function go(){
 let u=$("#u").value.trim();if(!u){$("#u").focus();return}
 const b=$("#go");b.disabled=true;
 $("#out").innerHTML=`<div class="msg load"><div class="spin"></div>Reading ${esc(u)} and its pages\u2026</div>`;
 try{
  const r=await fetch(`/api/analyze?url=${encodeURIComponent(u)}&keyword=${encodeURIComponent($("#k").value)}&pages=${$("#n").value}`);
  const d=await r.json();
  if(d.error)$("#out").innerHTML=`<div class="msg err"><b>Could not check this link.</b><br>${esc(d.error)}</div>`;else render(d);
 }catch(e){$("#out").innerHTML=`<div class="msg err">Lost connection to SHANKAR SEO. Make sure the program is still running.</div>`}
 b.disabled=false;
}
$("#go").onclick=go;["#u","#k"].forEach(s=>$(s).addEventListener("keydown",e=>{if(e.key==="Enter")go()}));
</script></body></html>'''

class Handler(BaseHTTPRequestHandler):
    def log_message(self, *a):
        pass

    def _send(self, code, body, ctype):
        data = body.encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def do_GET(self):
        u = urlparse(self.path)
        if u.path == "/":
            return self._send(200, PAGE, "text/html; charset=utf-8")
        if u.path == "/api/analyze":
            q = parse_qs(u.query)
            try:
                n = max(1, min(20, int((q.get("pages") or ["6"])[0])))
                res = analyze_site((q.get("url") or [""])[0], (q.get("keyword") or [""])[0], n)
                return self._send(200, json.dumps(res), "application/json")
            except Exception as e:
                msg = str(e) if isinstance(e, ValueError) else f"{type(e).__name__}: {e}"
                if isinstance(e, URLError):
                    msg = f"Cannot reach this website ({e.reason}). Check the link and your internet."
                return self._send(200, json.dumps({"error": msg}), "application/json")
        self._send(404, "Not found", "text/plain")


def main():
    port = int(sys.argv[1]) if len(sys.argv) > 1 else 8000
    srv = ThreadingHTTPServer(("127.0.0.1", port), Handler)
    url = f"http://localhost:{port}"
    print(f"\n  SHANKAR SEO is running at {url}\n  Press Ctrl+C to stop.\n")
    threading.Timer(0.8, lambda: webbrowser.open(url)).start()
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        print("\n  Stopped.")


if __name__ == "__main__":
    main()
