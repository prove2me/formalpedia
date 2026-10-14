-- Prove2me | Definitions.Def_IntMul_KappaJainData
-- name    : IntMul_KappaJainData
-- status  : Definition
-- author  : @xuanji
-- created : 2026-10-11T19:55:57.359126+00:00
-- url     : https://prove2.me/theorems/5bd66f3b-cb0b-4635-8cff-5ab7bcca9f57
-- title:
--   Child-width histograms of Jain's round six to eight networks
-- statement:
--   Frozen child-width histograms of the finite interchange networks in S. Jain's conditional witnesses for integer multiplication in time $O(n(\lg n)^{1-\kappa})$. Each list consists of pairs $(w,n_w)$: the network makes $n_w$ recursive child calls of width $w$.
--
--   1. `bitR6`: round six bit network, width $m=529$, $W=148225616$ roles.
--   2. `cxR6`: round six complex network (also used in round seven), width $m=576$, $W=207387136$ roles, rank sum $119453132304$.
--   3. `bitR7`: round seven bit network, witness 1 with the staircase entrance corner, width $529$, $W=108516254$.
--   4. `bitR7plain`: round seven bit network, witness 2 with the round-six entrance corner, width $529$, $W=104719230$; its saving is round eight's $a_{\mathrm{old}}$.
--   5. `bitR8`: round eight bit network (opposite bank orders on witness 2), width $529$, $W=104719230$.
--   6. `cxR8`: round eight complex network (signed reclaim and completed-core sharing), width $576$, $W=12869228$, rank sum $7410813248$.
--
--   These are the inputs of the moment certificates of rounds six to eight; the networks themselves (frames, words, replays) are checked in the source repository by independent Python gates, not here.
--
--   **Formalization Note** Transcribed verbatim from the lists `bitHist`, `cxHist`, `bitplainHist` of `lean/Round6.lean`, `lean/Round7.lean` (commit `c05adfe` for `bitR7`, `5868dc7` for `bitR7plain`) and `lean/Round8.lean`.
-- source:
--   https://github.com/Swapnil-jain/integer-mult-kappa — lean/Round6.lean (commit f2176bc), lean/Round7.lean (commit c05adfe1dfe85326dd6dcf12bfd53f435bd49bf3 for bitHist; commit 5868dc701a9bec375c9dc5391d992ab3b8c35f3f for bitplainHist), lean/Round8.lean (commit 5868dc701a9bec375c9dc5391d992ab3b8c35f3f); frozen data in certificates/round8/bit_hist.json.gz and cx_hist.json.gz

import Mathlib

/-!
# Child-width histograms of S. Jain's round six, seven and eight networks

Frozen data from S. Jain, `integer-mult-kappa`
(https://github.com/Swapnil-jain/integer-mult-kappa), transcribed verbatim from the files
`lean/Round6.lean`, `lean/Round7.lean` and `lean/Round8.lean`.  Each list holds pairs
`(w, n_w)`: the network makes `n_w` recursive child calls of width `w`.
-/

namespace IntMul.Kappa.Jain

/-- Round six bit interchange network (`lean/Round6.lean`, `bitHist`; width `m = 529`, `W = 148225616` roles). -/
def bitR6 : List (ℕ × ℕ) :=
  [(1, 2191713447), (3, 5667200), (5, 11716936), (7, 6970656), (9, 14731178), (11, 4445210), (13, 35572306), (15, 13905892), (17, 4562096), (19, 9740500), (21, 18900112), (23, 141952734), (439, 6272882), (483, 141952734)]

/-- Round six complex interchange network, reused in round seven (`lean/Round6.lean`, `cxHist`; width `m = 576`, `W = 207387136` roles). -/
def cxR6 : List (ℕ × ℕ) :=
  [(1, 184811440), (2, 107199136), (3, 50583808), (4, 53478128), (5, 33031680), (6, 27611408), (7, 14767104), (8, 20195472), (9, 6217728), (10, 14119424), (11, 5051904), (12, 13742960), (13, 4663296), (14, 14864256), (15, 4849504), (16, 13014320), (17, 10196912), (18, 33371712), (19, 13601280), (20, 22774048), (22, 44038192), (23, 16479408), (24, 4048), (529, 8193152), (552, 199193984)]

/-- Round seven bit network, staircase entrance corner, witness 1 (`lean/Round7.lean` at commit `c05adfe`, `bitHist`; width `m = 529`, `W = 108516254` roles). -/
def bitR7 : List (ℕ × ℕ) :=
  [(1, 1690297301), (3, 1356586), (5, 354200), (7, 3580962), (9, 1526602), (11, 5093396), (13, 2164162), (15, 7948248), (17, 8476006), (18, 6272882), (19, 1639946), (21, 6906900), (23, 61280142), (439, 6272882), (483, 61280142), (485, 545468), (487, 173558), (489, 293986), (491, 580888), (493, 14168), (495, 322322), (497, 17710), (499, 1129898), (501, 127512), (503, 410872), (505, 99176), (507, 1186570), (509, 340032), (511, 322322), (513, 106260), (515, 1583274), (517, 626934), (519, 2854852), (521, 13711082), (523, 4629394), (525, 5653032), (527, 6233920)]

/-- Round seven bit network, witness 2 with the round-six entrance corner (`lean/Round7.lean`, `bitplainHist`; width `m = 529`, `W = 104719230` roles). Its saving is the `a_old` of round eight's stopped interchange. -/
def bitR7plain : List (ℕ × ℕ) :=
  [(1, 1792923209), (3, 1438052), (5, 842996), (7, 3357816), (9, 4200812), (11, 2160620), (13, 570262), (15, 13622532), (17, 1009470), (19, 1944558), (21, 6843144), (23, 59760624), (439, 6272882), (483, 59760624), (485, 453376), (487, 173558), (489, 421498), (491, 233772), (493, 205436), (495, 226688), (497, 340032), (499, 602140), (501, 173558), (503, 357742), (505, 283360), (507, 690690), (509, 389620), (511, 102718), (513, 184184), (515, 584430), (517, 350658), (519, 3021326), (521, 13448974), (523, 4558554), (525, 5649490), (527, 6233920)]

/-- Round eight bit network: opposite bank orders on the round-seven witness 2 (`lean/Round8.lean`, `bitHist`; width `m = 529`, `W = 104719230` roles). -/
def bitR8 : List (ℕ × ℕ) :=
  [(1, 221936407), (2, 259926128), (3, 38728228), (4, 49343602), (5, 24609816), (6, 8068676), (7, 3818276), (8, 4785242), (9, 2992990), (10, 1211364), (11, 1445136), (12, 1331792), (13, 1080310), (14, 669438), (15, 2755676), (16, 3860780), (17, 1933932), (18, 364826), (19, 13388760), (20, 587972), (21, 1771000), (22, 116886), (484, 6272882), (506, 59760624), (507, 453376), (508, 173558), (509, 421498), (510, 233772), (511, 205436), (512, 226688), (513, 340032), (514, 602140), (515, 173558), (516, 357742), (517, 283360), (518, 690690), (519, 389620), (520, 102718), (521, 184184), (522, 584430), (523, 350658), (524, 3021326), (525, 13448974), (526, 4558554), (527, 5649490), (528, 6233920)]

/-- Round eight complex network: signed reclaim and completed-core sharing (`lean/Round8.lean`, `cxHist`; width `m = 576`, `W = 12869228` roles). -/
def cxR8 : List (ℕ × ℕ) :=
  [(1, 416381328), (2, 279401056), (3, 72936864), (4, 52437792), (5, 23753664), (6, 11617760), (7, 12322112), (8, 28433152), (9, 4938560), (10, 46070288), (11, 9840688), (12, 3206016), (13, 728640), (14, 910800), (15, 1692064), (16, 615296), (17, 1740640), (18, 2574528), (19, 3971088), (20, 1805408), (23, 8318640), (384, 214992), (529, 8193152)]

end IntMul.Kappa.Jain


