-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B041
-- name    : CK_CKLaneC2R_EpCells_B041
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:13:54.286114+00:00
-- url     : https://prove2.me/theorems/8ef3140d-53e2-4582-8b97-ecdd2411ae5c
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B041` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B041` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B041` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B041 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B041.lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheckT

-- ===== source module CKLaneC2R.EpCells.B041 =====
section

namespace CKLaneC2R.EpCells.B041

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['662793/4096000', '265287/1638400', '1999/2000', '7997/8000']  interval_lower 237217939/1099511627776
noncomputable def e2460 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277428768964,0,true,164908246976,164908247040⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921594486588,0,false,-194081480256,-194081480192⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277542719816,0,true,165006322624,165006322688⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921480535736,0,false,-194217438144,-194217438080⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277339810393,0,true,164831675648,164831675712⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921683445159,0,false,-193975353024,-193975352960⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277475958157,0,true,164948863040,164948863104⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921547297395,0,false,-194137780928,-194137780864⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545631754,0,true,34003392,34003456⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477623798,0,false,-34004544,-34004480⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556997293,0,true,45368576,45368640⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466258259,0,false,-45370496,-45370432⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625903,0,false,-1920,-1856⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626725,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277384285224,0,true,164869958144,164869958208⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921638970328,0,false,-194028410048,-194028409984⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277509347573,0,true,164977600576,164977600640⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921513907979,0,false,-194177619072,-194177619008⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070695935924,0,false,-29200018432,-29200018368⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070736413883,0,false,-29158451840,-29158451776⟩
    { al := (662793/4096000), au := (265287/1638400), zl := (1999/2000), zu := (7997/8000),
      A := ⟨177917141188,178031092040⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164908246976,164908247040⟩ : DyadicInterval 40),(⟨-194081480256,-194081480192⟩ : DyadicInterval 40),(⟨747665093174,747665112504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165006322624,165006322688⟩ : DyadicInterval 40),(⟨-194217438144,-194217438080⟩ : DyadicInterval 40),(⟨747646484700,747646504030⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164831675648,164831675712⟩ : DyadicInterval 40),(⟨-193975353024,-193975352960⟩ : DyadicInterval 40),(⟨747679611941,747679631271⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164948863040,164948863104⟩ : DyadicInterval 40),(⟨-194137780928,-194137780864⟩ : DyadicInterval 40),(⟨747657388505,747657407834⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34003978,45369517⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34003392,34003456⟩ : DyadicInterval 40),(⟨-34004544,-34004480⟩ : DyadicInterval 40),(⟨762123383076,762123402405⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45368576,45368640⟩ : DyadicInterval 40),(⟨-45370496,-45370432⟩ : DyadicInterval 40),(⟨762123382639,762123401968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1920,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177872657448,177997719797⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164869958144,164869958208⟩ : DyadicInterval 40),(⟨-194028410048,-194028409984⟩ : DyadicInterval 40),(⟨747672354210,747672373540⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164977600576,164977600640⟩ : DyadicInterval 40),(⟨-194177619072,-194177619008⟩ : DyadicInterval 40),(⟨747651935738,747651955067⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29200018432,-29158451776⟩ : DyadicInterval 40),(⟨776702609504,776723412096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164908246976,165006322688⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194217438144,-194081480192⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2460_ok : ecellOkT e2460 = true := by decide +kernel
theorem e2460_pos {a z : ℝ} (ha1 : ((662793/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((265287/1638400 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2460 e2460_ok ha1 ha2 hz1 hz2 hz

-- box ['265287/1638400', '331821/2048000', '1999/2000', '7997/8000']  interval_lower 119230553/549755813888
noncomputable def e2461 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277542719815,0,true,165006322624,165006322688⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921480535737,0,false,-194217438144,-194217438080⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277656670667,0,true,165104389568,165104389632⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921366584885,0,false,-194353412800,-194353412736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277453704268,0,true,164929709120,164929709184⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921569551284,0,false,-194111229824,-194111229760⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277589866276,0,true,165046898304,165046898368⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921433389276,0,false,-194273694784,-194273694720⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545654379,0,true,34026048,34026112⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477601173,0,false,-34027136,-34027072⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557027462,0,true,45398720,45398784⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466228090,0,false,-45400640,-45400576⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625901,0,false,-1920,-1856⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626723,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277498207582,0,true,164968012736,164968012800⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921525047970,0,false,-194164327360,-194164327296⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277623277060,0,true,165075651712,165075651776⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921399978492,0,false,-194313563328,-194313563264⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070659036489,0,false,-29237911552,-29237911488⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070699542674,0,false,-29196314624,-29196314560⟩
    { al := (265287/1638400), au := (331821/2048000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨178031092039,178145042891⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165006322624,165006322688⟩ : DyadicInterval 40),(⟨-194217438144,-194217438080⟩ : DyadicInterval 40),(⟨747646484700,747646504030⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165104389568,165104389632⟩ : DyadicInterval 40),(⟨-194353412800,-194353412736⟩ : DyadicInterval 40),(⟨747627864054,747627883383⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164929709120,164929709184⟩ : DyadicInterval 40),(⟨-194111229824,-194111229760⟩ : DyadicInterval 40),(⟨747661022223,747661041552⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165046898304,165046898368⟩ : DyadicInterval 40),(⟨-194273694784,-194273694720⟩ : DyadicInterval 40),(⟨747638781980,747638801310⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34026603,45399686⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34026048,34026112⟩ : DyadicInterval 40),(⟨-34027136,-34027072⟩ : DyadicInterval 40),(⟨762123383042,762123402371⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45398720,45398784⟩ : DyadicInterval 40),(⟨-45400640,-45400576⟩ : DyadicInterval 40),(⟨762123382637,762123401966⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1920,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177986579806,178111649284⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164968012736,164968012800⟩ : DyadicInterval 40),(⟨-194164327360,-194164327296⟩ : DyadicInterval 40),(⟨747653755086,747653774415⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165075651712,165075651776⟩ : DyadicInterval 40),(⟨-194313563328,-194313563264⟩ : DyadicInterval 40),(⟨747633322134,747633341463⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29237911552,-29196314560⟩ : DyadicInterval 40),(⟨776721540896,776742358656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165006322624,165104389632⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194353412800,-194217438080⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2461_ok : ecellOkT e2461 = true := by decide +kernel
theorem e2461_pos {a z : ℝ} (ha1 : ((265287/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((331821/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2461 e2461_ok ha1 ha2 hz1 hz2 hz

-- box ['662793/4096000', '265287/1638400', '7997/8000', '3999/4000']  interval_lower 237040211/1099511627776
noncomputable def e2462 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277428768964,0,true,164908246976,164908247040⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921594486588,0,false,-194081480256,-194081480192⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277542719816,0,true,165006322624,165006322688⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921480535736,0,false,-194217438144,-194217438080⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277362050035,0,true,164850819008,164850819072⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921661205517,0,false,-194001883840,-194001883776⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277498212044,0,true,164968016576,164968016640⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921525043508,0,false,-194164332672,-194164332608⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534297064,0,true,22668992,22669056⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488958488,0,false,-22669568,-22669504⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545655060,0,true,34026752,34026816⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477600492,0,false,-34027840,-34027776⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626722,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627309,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277395404956,0,true,164879529408,164879529472⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921627850596,0,false,-194041675904,-194041675840⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277520474451,0,true,164987177088,164987177152⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921502781101,0,false,-194190895232,-194190895168⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070692333196,0,false,-29203718080,-29203718016⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070732815998,0,false,-29162146432,-29162146368⟩
    { al := (662793/4096000), au := (265287/1638400), zl := (7997/8000), zu := (3999/4000),
      A := ⟨177917141188,178031092040⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164908246976,164908247040⟩ : DyadicInterval 40),(⟨-194081480256,-194081480192⟩ : DyadicInterval 40),(⟨747665093174,747665112504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165006322624,165006322688⟩ : DyadicInterval 40),(⟨-194217438144,-194217438080⟩ : DyadicInterval 40),(⟨747646484700,747646504030⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164850819008,164850819072⟩ : DyadicInterval 40),(⟨-194001883840,-194001883776⟩ : DyadicInterval 40),(⟨747675982913,747676002243⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164968016576,164968016640⟩ : DyadicInterval 40),(⟨-194164332672,-194164332608⟩ : DyadicInterval 40),(⟨747653754353,747653773682⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22669288,34027284⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22668992,22669056⟩ : DyadicInterval 40),(⟨-22669568,-22669504⟩ : DyadicInterval 40),(⟨762123383372,762123402701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34026752,34026816⟩ : DyadicInterval 40),(⟨-34027840,-34027776⟩ : DyadicInterval 40),(⟨762123383042,762123402371⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177883777180,178008846675⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164879529408,164879529472⟩ : DyadicInterval 40),(⟨-194041675904,-194041675840⟩ : DyadicInterval 40),(⟨747670539332,747670558661⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164987177088,164987177152⟩ : DyadicInterval 40),(⟨-194190895232,-194190895168⟩ : DyadicInterval 40),(⟨747650118364,747650137693⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29203718080,-29162146368⟩ : DyadicInterval 40),(⟨776704456800,776725261920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164908246976,165006322688⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194217438144,-194081480192⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2462_ok : ecellOkT e2462 = true := by decide +kernel
theorem e2462_pos {a z : ℝ} (ha1 : ((662793/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((265287/1638400 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2462 e2462_ok ha1 ha2 hz1 hz2 hz

-- box ['265287/1638400', '331821/2048000', '7997/8000', '3999/4000']  interval_lower 119141471/549755813888
noncomputable def e2463 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277542719815,0,true,165006322624,165006322688⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921480535737,0,false,-194217438144,-194217438080⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277656670667,0,true,165104389568,165104389632⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921366584885,0,false,-194353412800,-194353412736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277475958155,0,true,164948863040,164948863104⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921547297397,0,false,-194137780928,-194137780864⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277612134407,0,true,165066062400,165066062464⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921411121145,0,false,-194300266816,-194300266752⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534312148,0,true,22684096,22684160⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488943404,0,false,-22684608,-22684544⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545677688,0,true,34049344,34049408⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477577864,0,false,-34050496,-34050432⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626721,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627308,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277509334436,0,true,164977589312,164977589376⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921513921116,0,false,-194177603392,-194177603328⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277634411059,0,true,165085233472,165085233536⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921388844493,0,false,-194326849664,-194326849600⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070655429148,0,false,-29241616128,-29241616064⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070695940179,0,false,-29200014016,-29200013952⟩
    { al := (265287/1638400), au := (331821/2048000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨178031092039,178145042891⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165006322624,165006322688⟩ : DyadicInterval 40),(⟨-194217438144,-194217438080⟩ : DyadicInterval 40),(⟨747646484700,747646504030⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165104389568,165104389632⟩ : DyadicInterval 40),(⟨-194353412800,-194353412736⟩ : DyadicInterval 40),(⟨747627864054,747627883383⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164948863040,164948863104⟩ : DyadicInterval 40),(⟨-194137780928,-194137780864⟩ : DyadicInterval 40),(⟨747657388505,747657407835⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165066062400,165066062464⟩ : DyadicInterval 40),(⟨-194300266816,-194300266752⟩ : DyadicInterval 40),(⟨747635143132,747635162461⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22684372,34049912⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22684096,22684160⟩ : DyadicInterval 40),(⟨-22684608,-22684544⟩ : DyadicInterval 40),(⟨762123383339,762123402668⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34049344,34049408⟩ : DyadicInterval 40),(⟨-34050496,-34050432⟩ : DyadicInterval 40),(⟨762123383073,762123402402⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177997706660,178122783283⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164977589312,164977589376⟩ : DyadicInterval 40),(⟨-194177603392,-194177603328⟩ : DyadicInterval 40),(⟨747651937857,747651957186⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165085233472,165085233536⟩ : DyadicInterval 40),(⟨-194326849664,-194326849600⟩ : DyadicInterval 40),(⟨747631502442,747631521772⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29241616128,-29200013952⟩ : DyadicInterval 40),(⟨776723390592,776744210944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165006322624,165104389632⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194353412800,-194217438080⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2463_ok : ecellOkT e2463 = true := by decide +kernel
theorem e2463_pos {a z : ℝ} (ha1 : ((265287/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((331821/2048000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2463 e2463_ok ha1 ha2 hz1 hz2 hz

-- box ['82743/512000', '1324737/8192000', '3999/4000', '7999/8000']  interval_lower 29298357/137438953472
noncomputable def e2464 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277200867262,0,true,164712069376,164712069440⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921822388290,0,false,-193809614912,-193809614848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277314818114,0,true,164810162560,164810162624⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921708437438,0,false,-193945539200,-193945539136⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277156444952,0,true,164673826560,164673826624⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921866810600,0,false,-193756631104,-193756631040⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277292592716,0,true,164791030784,164791030848⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921730662836,0,false,-193919026688,-193919026624⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522947237,0,true,11319360,11319424⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500308315,0,false,-11319552,-11319488⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534282607,0,true,22654592,22654656⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488972945,0,false,-22655104,-22655040⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627309,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627660,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277178651499,0,true,164692944192,164692944256⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921844604053,0,false,-193783117184,-193783117120⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277303713898,0,true,164800603968,164800604032⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921719541654,0,false,-193932292992,-193932292928⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070762476708,0,false,-29131688960,-29131688896⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070802907904,0,false,-29090172992,-29090172928⟩
    { al := (82743/512000), au := (1324737/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨177689239486,177803190338⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164712069376,164712069440⟩ : DyadicInterval 40),(⟨-193809614912,-193809614848⟩ : DyadicInterval 40),(⟨747702273777,747702293107⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164810162560,164810162624⟩ : DyadicInterval 40),(⟨-193945539200,-193945539136⟩ : DyadicInterval 40),(⟨747683689542,747683708871⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164673826560,164673826624⟩ : DyadicInterval 40),(⟨-193756631104,-193756631040⟩ : DyadicInterval 40),(⟨747709515359,747709534688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164791030784,164791030848⟩ : DyadicInterval 40),(⟨-193919026688,-193919026624⟩ : DyadicInterval 40),(⟨747687315228,747687334558⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11319461,22654831⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11319360,11319424⟩ : DyadicInterval 40),(⟨-11319552,-11319488⟩ : DyadicInterval 40),(⟨762123383531,762123402860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22654592,22654656⟩ : DyadicInterval 40),(⟨-22655104,-22655040⟩ : DyadicInterval 40),(⟨762123383341,762123402670⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177667023723,177792086122⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164692944192,164692944256⟩ : DyadicInterval 40),(⟨-193783117184,-193783117120⟩ : DyadicInterval 40),(⟨747705895532,747705914861⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164800603968,164800604032⟩ : DyadicInterval 40),(⟨-193932292992,-193932292928⟩ : DyadicInterval 40),(⟨747685501090,747685520420⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29131688960,-29090172928⟩ : DyadicInterval 40),(⟨776668470080,776689247360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164712069376,164810162624⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193945539200,-193809614848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2464_ok : ecellOkT e2464 = true := by decide +kernel
theorem e2464_pos {a z : ℝ} (ha1 : ((82743/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1324737/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2464 e2464_ok ha1 ha2 hz1 hz2 hz

-- box ['1324737/8192000', '662793/4096000', '3999/4000', '7999/8000']  interval_lower 58905827/274877906944
noncomputable def e2465 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277314818113,0,true,164810162560,164810162624⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921708437439,0,false,-193945539200,-193945539136⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277428768965,0,true,164908246976,164908247040⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921594486587,0,false,-194081480256,-194081480192⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277270367315,0,true,164771898624,164771898688⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921752888237,0,false,-193892514816,-193892514752⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277406529323,0,true,164889104640,164889104704⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921616726229,0,false,-194054947456,-194054947392⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522954778,0,true,11326912,11326976⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500300774,0,false,-11327104,-11327040⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534297690,0,true,22669632,22669696⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488957862,0,false,-22670208,-22670144⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627308,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627660,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277292588103,0,true,164791026816,164791026880⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921730667449,0,false,-193919021184,-193919021120⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277417657627,0,true,164898683136,164898683200⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921605597925,0,false,-194068223872,-194068223808⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070725615279,0,false,-29169540736,-29169540672⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070766074700,0,false,-29127994368,-29127994304⟩
    { al := (1324737/8192000), au := (662793/4096000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨177803190337,177917141189⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164810162560,164810162624⟩ : DyadicInterval 40),(⟨-193945539200,-193945539136⟩ : DyadicInterval 40),(⟨747683689542,747683708872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164908246976,164908247040⟩ : DyadicInterval 40),(⟨-194081480256,-194081480192⟩ : DyadicInterval 40),(⟨747665093174,747665112504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164771898624,164771898688⟩ : DyadicInterval 40),(⟨-193892514816,-193892514752⟩ : DyadicInterval 40),(⟨747690940484,747690959813⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164889104640,164889104704⟩ : DyadicInterval 40),(⟨-194054947456,-194054947392⟩ : DyadicInterval 40),(⟨747668723548,747668742878⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11327002,22669914⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11326912,11326976⟩ : DyadicInterval 40),(⟨-11327104,-11327040⟩ : DyadicInterval 40),(⟨762123383531,762123402860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22669632,22669696⟩ : DyadicInterval 40),(⟨-22670208,-22670144⟩ : DyadicInterval 40),(⟨762123383372,762123402701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177780960327,177906029851⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164791026816,164791026880⟩ : DyadicInterval 40),(⟨-193919021184,-193919021120⟩ : DyadicInterval 40),(⟨747687315979,747687335308⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164898683136,164898683200⟩ : DyadicInterval 40),(⟨-194068223872,-194068223808⟩ : DyadicInterval 40),(⟨747666907033,747666926362⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29169540736,-29127994304⟩ : DyadicInterval 40),(⟨776687380768,776708173248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164810162560,164908247040⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194081480256,-193945539136⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2465_ok : ecellOkT e2465 = true := by decide +kernel
theorem e2465_pos {a z : ℝ} (ha1 : ((1324737/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((662793/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2465 e2465_ok ha1 ha2 hz1 hz2 hz

-- box ['82743/512000', '1324737/8192000', '7999/8000', '1']  interval_lower 29276245/137438953472
noncomputable def e2466 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277200867262,0,true,164712069376,164712069440⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921822388290,0,false,-193809614912,-193809614848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277314818114,0,true,164810162560,164810162624⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921708437438,0,false,-193945539200,-193945539136⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277178656106,0,true,164692948160,164692948224⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921844599446,0,false,-193783122688,-193783122624⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522955347,0,true,11327488,11327552⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500300205,0,false,-11327680,-11327616⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627659,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1277189757040,0,true,164702504768,164702504832⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨921833498512,0,false,-193796363200,-193796363136⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1277314826583,0,true,164810169856,164810169920⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨921708428969,0,false,-193945549248,-193945549184⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1070758882732,0,false,-29135379392,-29135379328⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1070799318765,0,false,-29093858368,-29093858304⟩
    { al := (82743/512000), au := (1324737/8192000), zl := (7999/8000), zu := 1,
      A := ⟨177689239486,177803190338⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164712069376,164712069440⟩ : DyadicInterval 40),(⟨-193809614912,-193809614848⟩ : DyadicInterval 40),(⟨747702273777,747702293107⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164810162560,164810162624⟩ : DyadicInterval 40),(⟨-193945539200,-193945539136⟩ : DyadicInterval 40),(⟨747683689542,747683708871⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164692948160,164692948224⟩ : DyadicInterval 40),(⟨-193783122688,-193783122624⟩ : DyadicInterval 40),(⟨747705894783,747705914113⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164810162560,164810162624⟩ : DyadicInterval 40),(⟨-193945539200,-193945539136⟩ : DyadicInterval 40),(⟨747683689542,747683708871⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11327571⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11327488,11327552⟩ : DyadicInterval 40),(⟨-11327680,-11327616⟩ : DyadicInterval 40),(⟨762123383531,762123402860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨177678129264,177803198807⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164702504768,164702504832⟩ : DyadicInterval 40),(⟨-193796363200,-193796363136⟩ : DyadicInterval 40),(⟨747704085128,747704104458⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164810169856,164810169920⟩ : DyadicInterval 40),(⟨-193945549248,-193945549184⟩ : DyadicInterval 40),(⟨747683688134,747683707464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29135379392,-29093858304⟩ : DyadicInterval 40),(⟨776670312768,776691092576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨164712069376,164810162624⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193945539200,-193809614848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2466_ok : ecellOkT e2466 = true := by decide +kernel
theorem e2466_pos {a z : ℝ} (ha1 : ((82743/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1324737/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2466 e2466_ok ha1 ha2 hz1 hz2 hz

-- box ['1324737/8192000', '662793/4096000', '7999/8000', '1']  interval_lower 14715375/68719476736
noncomputable def e2467 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277314818113,0,true,164810162560,164810162624⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921708437439,0,false,-193945539200,-193945539136⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277428768965,0,true,164908246976,164908247040⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921594486587,0,false,-194081480256,-194081480192⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277292592714,0,true,164791030784,164791030848⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921730662838,0,false,-193919026688,-193919026624⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522962889,0,true,11335040,11335104⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500292663,0,false,-11335232,-11335168⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627659,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1277303700765,0,true,164800592704,164800592768⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨921719554787,0,false,-193932277312,-193932277248⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1277428777434,0,true,164908254272,164908254336⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨921594478118,0,false,-194081490368,-194081490304⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1070722016695,0,false,-29173236032,-29173235968⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1070762480956,0,false,-29131684608,-29131684544⟩
    { al := (1324737/8192000), au := (662793/4096000), zl := (7999/8000), zu := 1,
      A := ⟨177803190337,177917141189⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164810162560,164810162624⟩ : DyadicInterval 40),(⟨-193945539200,-193945539136⟩ : DyadicInterval 40),(⟨747683689542,747683708872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164908246976,164908247040⟩ : DyadicInterval 40),(⟨-194081480256,-194081480192⟩ : DyadicInterval 40),(⟨747665093174,747665112504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164791030784,164791030848⟩ : DyadicInterval 40),(⟨-193919026688,-193919026624⟩ : DyadicInterval 40),(⟨747687315229,747687334558⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164908246976,164908247040⟩ : DyadicInterval 40),(⟨-194081480256,-194081480192⟩ : DyadicInterval 40),(⟨747665093174,747665112504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11335113⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11335040,11335104⟩ : DyadicInterval 40),(⟨-11335232,-11335168⟩ : DyadicInterval 40),(⟨762123383531,762123402860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨177792072989,177917149658⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164800592704,164800592768⟩ : DyadicInterval 40),(⟨-193932277312,-193932277248⟩ : DyadicInterval 40),(⟨747685503203,747685522533⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164908254272,164908254336⟩ : DyadicInterval 40),(⟨-194081490368,-194081490304⟩ : DyadicInterval 40),(⟨747665091791,747665111121⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29173236032,-29131684544⟩ : DyadicInterval 40),(⟨776689225888,776710020896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨164810162560,164908247040⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194081480256,-193945539136⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2467_ok : ecellOkT e2467 = true := by decide +kernel
theorem e2467_pos {a z : ℝ} (ha1 : ((1324737/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((662793/4096000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2467 e2467_ok ha1 ha2 hz1 hz2 hz

-- box ['662793/4096000', '265287/1638400', '3999/4000', '7999/8000']  interval_lower 236862427/1099511627776
noncomputable def e2468 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277428768964,0,true,164908246976,164908247040⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921594486588,0,false,-194081480256,-194081480192⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277542719816,0,true,165006322624,165006322688⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921480535736,0,false,-194217438144,-194217438080⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277384289678,0,true,164869961984,164869962048⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921638965874,0,false,-194028415360,-194028415296⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277520465930,0,true,164987169792,164987169856⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921502789622,0,false,-194190885056,-194190884992⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522962319,0,true,11334464,11334528⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500293233,0,false,-11334656,-11334592⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534312773,0,true,22684736,22684800⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488942779,0,false,-22685248,-22685184⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627307,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627660,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277406524709,0,true,164889100672,164889100736⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921616730843,0,false,-194054941952,-194054941888⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277531601355,0,true,164996753536,164996753600⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921491654197,0,false,-194204171648,-194204171584⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070688730234,0,false,-29207418048,-29207417984⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070729217882,0,false,-29165841280,-29165841216⟩
    { al := (662793/4096000), au := (265287/1638400), zl := (3999/4000), zu := (7999/8000),
      A := ⟨177917141188,178031092040⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164908246976,164908247040⟩ : DyadicInterval 40),(⟨-194081480256,-194081480192⟩ : DyadicInterval 40),(⟨747665093174,747665112504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165006322624,165006322688⟩ : DyadicInterval 40),(⟨-194217438144,-194217438080⟩ : DyadicInterval 40),(⟨747646484700,747646504030⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164869961984,164869962048⟩ : DyadicInterval 40),(⟨-194028415360,-194028415296⟩ : DyadicInterval 40),(⟨747672353479,747672372809⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164987169792,164987169856⟩ : DyadicInterval 40),(⟨-194190885056,-194190884992⟩ : DyadicInterval 40),(⟨747650119730,747650139060⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11334543,22684997⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11334464,11334528⟩ : DyadicInterval 40),(⟨-11334656,-11334592⟩ : DyadicInterval 40),(⟨762123383531,762123402860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22684736,22684800⟩ : DyadicInterval 40),(⟨-22685248,-22685184⟩ : DyadicInterval 40),(⟨762123383339,762123402668⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177894896933,178019973579⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164889100672,164889100736⟩ : DyadicInterval 40),(⟨-194054941952,-194054941888⟩ : DyadicInterval 40),(⟨747668724299,747668743629⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164996753536,164996753600⟩ : DyadicInterval 40),(⟨-194204171648,-194204171584⟩ : DyadicInterval 40),(⟨747648300899,747648320228⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29207418048,-29165841216⟩ : DyadicInterval 40),(⟨776706304224,776727111904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164908246976,165006322688⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194217438144,-194081480192⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2468_ok : ecellOkT e2468 = true := by decide +kernel
theorem e2468_pos {a z : ℝ} (ha1 : ((662793/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((265287/1638400 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2468 e2468_ok ha1 ha2 hz1 hz2 hz

-- box ['265287/1638400', '331821/2048000', '3999/4000', '7999/8000']  interval_lower 119052305/549755813888
noncomputable def e2469 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277542719815,0,true,165006322624,165006322688⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921480535737,0,false,-194217438144,-194217438080⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277656670667,0,true,165104389568,165104389632⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921366584885,0,false,-194353412800,-194353412736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277498212041,0,true,164968016576,164968016640⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921525043511,0,false,-194164332672,-194164332608⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277634402537,0,true,165085226176,165085226240⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921388853015,0,false,-194326839488,-194326839424⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522969861,0,true,11342016,11342080⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500285691,0,false,-11342144,-11342080⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534327858,0,true,22699840,22699904⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488927694,0,false,-22700352,-22700288⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627307,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627659,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277520461312,0,true,164987165824,164987165888⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921502794240,0,false,-194190879552,-194190879488⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277645545085,0,true,165094815232,165094815296⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921377710467,0,false,-194340136192,-194340136128⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070651821572,0,false,-29245320960,-29245320896⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070692337451,0,false,-29203713728,-29203713664⟩
    { al := (265287/1638400), au := (331821/2048000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨178031092039,178145042891⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165006322624,165006322688⟩ : DyadicInterval 40),(⟨-194217438144,-194217438080⟩ : DyadicInterval 40),(⟨747646484700,747646504030⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165104389568,165104389632⟩ : DyadicInterval 40),(⟨-194353412800,-194353412736⟩ : DyadicInterval 40),(⟨747627864054,747627883383⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164968016576,164968016640⟩ : DyadicInterval 40),(⟨-194164332672,-194164332608⟩ : DyadicInterval 40),(⟨747653754353,747653773683⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165085226176,165085226240⟩ : DyadicInterval 40),(⟨-194326839488,-194326839424⟩ : DyadicInterval 40),(⟨747631503810,747631523140⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11342085,22700082⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11342016,11342080⟩ : DyadicInterval 40),(⟨-11342144,-11342080⟩ : DyadicInterval 40),(⟨762123383499,762123402828⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22699840,22699904⟩ : DyadicInterval 40),(⟨-22700352,-22700288⟩ : DyadicInterval 40),(⟨762123383339,762123402668⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178008833536,178133917309⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164987165824,164987165888⟩ : DyadicInterval 40),(⟨-194190879552,-194190879488⟩ : DyadicInterval 40),(⟨747650120483,747650139812⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165094815232,165094815296⟩ : DyadicInterval 40),(⟨-194340136192,-194340136128⟩ : DyadicInterval 40),(⟨747629682595,747629701925⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29245320960,-29203713664⟩ : DyadicInterval 40),(⟨776725240448,776746063360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165006322624,165104389632⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194353412800,-194217438080⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2469_ok : ecellOkT e2469 = true := by decide +kernel
theorem e2469_pos {a z : ℝ} (ha1 : ((265287/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((331821/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2469 e2469_ok ha1 ha2 hz1 hz2 hz

-- box ['662793/4096000', '265287/1638400', '7999/8000', '1']  interval_lower 59171179/274877906944
noncomputable def e2470 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277428768964,0,true,164908246976,164908247040⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921594486588,0,false,-194081480256,-194081480192⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277542719816,0,true,165006322624,165006322688⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921480535736,0,false,-194217438144,-194217438080⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277406529321,0,true,164889104640,164889104704⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921616726231,0,false,-194054947456,-194054947392⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522970431,0,true,11342592,11342656⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500285121,0,false,-11342720,-11342656⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627658,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1277417644492,0,true,164898671872,164898671936⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨921605611060,0,false,-194068208256,-194068208192⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1277542728279,0,true,165006329920,165006329984⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨921480527273,0,false,-194217448192,-194217448128⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1070685127040,0,false,-29211118272,-29211118208⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1070725619530,0,false,-29169536384,-29169536320⟩
    { al := (662793/4096000), au := (265287/1638400), zl := (7999/8000), zu := 1,
      A := ⟨177917141188,178031092040⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164908246976,164908247040⟩ : DyadicInterval 40),(⟨-194081480256,-194081480192⟩ : DyadicInterval 40),(⟨747665093174,747665112504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165006322624,165006322688⟩ : DyadicInterval 40),(⟨-194217438144,-194217438080⟩ : DyadicInterval 40),(⟨747646484700,747646504030⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164889104640,164889104704⟩ : DyadicInterval 40),(⟨-194054947456,-194054947392⟩ : DyadicInterval 40),(⟨747668723548,747668742878⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165006322624,165006322688⟩ : DyadicInterval 40),(⟨-194217438144,-194217438080⟩ : DyadicInterval 40),(⟨747646484700,747646504030⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11342655⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11342592,11342656⟩ : DyadicInterval 40),(⟨-11342720,-11342656⟩ : DyadicInterval 40),(⟨762123383498,762123402827⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨177906016716,178031100503⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164898671872,164898671936⟩ : DyadicInterval 40),(⟨-194068208256,-194068208192⟩ : DyadicInterval 40),(⟨747666909176,747666928505⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165006329920,165006329984⟩ : DyadicInterval 40),(⟨-194217448192,-194217448128⟩ : DyadicInterval 40),(⟨747646483289,747646502619⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29211118272,-29169536320⟩ : DyadicInterval 40),(⟨776708151776,776728962016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨164908246976,165006322688⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194217438144,-194081480192⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2470_ok : ecellOkT e2470 = true := by decide +kernel
theorem e2470_pos {a z : ℝ} (ha1 : ((662793/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((265287/1638400 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2470 e2470_ok ha1 ha2 hz1 hz2 hz

-- box ['265287/1638400', '331821/2048000', '7999/8000', '1']  interval_lower 237926569/1099511627776
noncomputable def e2471 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277542719815,0,true,165006322624,165006322688⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921480535737,0,false,-194217438144,-194217438080⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277656670667,0,true,165104389568,165104389632⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921366584885,0,false,-194353412800,-194353412736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277520465928,0,true,164987169792,164987169856⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921502789624,0,false,-194190885056,-194190884992⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522977974,0,true,11350080,11350144⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500277578,0,false,-11350272,-11350208⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627658,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1277531588216,0,true,164996742272,164996742336⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨921491667336,0,false,-194204155968,-194204155904⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1277656679135,0,true,165104396864,165104396928⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨921366576417,0,false,-194353422912,-194353422848⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1070648213763,0,false,-29249026048,-29249025984⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1070688734490,0,false,-29207413696,-29207413632⟩
    { al := (265287/1638400), au := (331821/2048000), zl := (7999/8000), zu := 1,
      A := ⟨178031092039,178145042891⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165006322624,165006322688⟩ : DyadicInterval 40),(⟨-194217438144,-194217438080⟩ : DyadicInterval 40),(⟨747646484700,747646504030⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165104389568,165104389632⟩ : DyadicInterval 40),(⟨-194353412800,-194353412736⟩ : DyadicInterval 40),(⟨747627864054,747627883383⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164987169792,164987169856⟩ : DyadicInterval 40),(⟨-194190885056,-194190884992⟩ : DyadicInterval 40),(⟨747650119730,747650139060⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165104389568,165104389632⟩ : DyadicInterval 40),(⟨-194353412800,-194353412736⟩ : DyadicInterval 40),(⟨747627864054,747627883383⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11350198⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11350080,11350144⟩ : DyadicInterval 40),(⟨-11350272,-11350208⟩ : DyadicInterval 40),(⟨762123383530,762123402859⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨178019960440,178145051359⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164996742272,164996742336⟩ : DyadicInterval 40),(⟨-194204155968,-194204155904⟩ : DyadicInterval 40),(⟨747648303018,747648322347⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165104396864,165104396928⟩ : DyadicInterval 40),(⟨-194353422912,-194353422848⟩ : DyadicInterval 40),(⟨747627862667,747627881997⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29249026048,-29207413632⟩ : DyadicInterval 40),(⟨776727090432,776747915904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨165006322624,165104389632⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194353412800,-194217438080⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2471_ok : ecellOkT e2471 = true := by decide +kernel
theorem e2471_pos {a z : ℝ} (ha1 : ((265287/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((331821/2048000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2471 e2471_ok ha1 ha2 hz1 hz2 hz

-- box ['331821/2048000', '1328133/8192000', '1999/2000', '7997/8000']  interval_lower 119853551/549755813888
noncomputable def e2472 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277656670666,0,true,165104389568,165104389632⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921366584886,0,false,-194353412800,-194353412736⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277770621518,0,true,165202447744,165202447808⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921252634034,0,false,-194489404352,-194489404288⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277567598144,0,true,165027733888,165027733952⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921455657408,0,false,-194247123392,-194247123328⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277703774396,0,true,165144924864,165144924928⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921319481156,0,false,-194409625408,-194409625344⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545677006,0,true,34048640,34048704⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477578546,0,false,-34049792,-34049728⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557057633,0,true,45428864,45428928⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466197919,0,false,-45430848,-45430784⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625898,0,false,-1920,-1856⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626722,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277612129949,0,true,165066058560,165066058624⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921411125603,0,false,-194300261504,-194300261440⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277737206545,0,true,165173694080,165173694144⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921286049007,0,false,-194449524416,-194449524352⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070622113445,0,false,-29275830272,-29275830208⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070662647854,0,false,-29234202880,-29234202816⟩
    { al := (331821/2048000), au := (1328133/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨178145042890,178258993742⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165104389568,165104389632⟩ : DyadicInterval 40),(⟨-194353412800,-194353412736⟩ : DyadicInterval 40),(⟨747627864054,747627883384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165202447744,165202447808⟩ : DyadicInterval 40),(⟨-194489404352,-194489404288⟩ : DyadicInterval 40),(⟨747609231325,747609250655⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165027733888,165027733952⟩ : DyadicInterval 40),(⟨-194247123392,-194247123328⟩ : DyadicInterval 40),(⟨747642420357,747642439687⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165144924864,165144924928⟩ : DyadicInterval 40),(⟨-194409625408,-194409625344⟩ : DyadicInterval 40),(⟨747620163302,747620182631⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34049230,45429857⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34048640,34048704⟩ : DyadicInterval 40),(⟨-34049792,-34049728⟩ : DyadicInterval 40),(⟨762123383073,762123402402⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45428864,45428928⟩ : DyadicInterval 40),(⟨-45430848,-45430784⟩ : DyadicInterval 40),(⟨762123382666,762123401995⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1920,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178100502173,178225578769⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165066058560,165066058624⟩ : DyadicInterval 40),(⟨-194300261504,-194300261440⟩ : DyadicInterval 40),(⟨747635143865,747635163195⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165173694080,165173694144⟩ : DyadicInterval 40),(⟨-194449524416,-194449524352⟩ : DyadicInterval 40),(⟨747614696429,747614715759⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29275830272,-29234202816⟩ : DyadicInterval 40),(⟨776740485024,776761318016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165104389568,165202447808⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194489404352,-194353412736⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2472_ok : ecellOkT e2472 = true := by decide +kernel
theorem e2472_pos {a z : ℝ} (ha1 : ((331821/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1328133/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2472 e2472_ok ha1 ha2 hz1 hz2 hz

-- box ['1328133/8192000', '664491/4096000', '1999/2000', '7997/8000']  interval_lower 120477903/549755813888
noncomputable def e2473 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277770621517,0,true,165202447744,165202447808⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921252634035,0,false,-194489404352,-194489404288⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277884572369,0,true,165300497216,165300497280⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921138683183,0,false,-194625412672,-194625412608⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277681492020,0,true,165125749888,165125749952⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921341763532,0,false,-194383033728,-194383033664⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277817682515,0,true,165242942656,165242942720⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921205573037,0,false,-194545572864,-194545572800⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545699635,0,true,34071296,34071360⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477555917,0,false,-34072448,-34072384⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557087808,0,true,45459072,45459136⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466167744,0,false,-45460992,-45460928⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625896,0,false,-1920,-1856⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626721,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277726052309,0,true,165164095616,165164095680⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921297203243,0,false,-194436212416,-194436212352⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277851136032,0,true,165271727680,165271727744⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921172119520,0,false,-194585502272,-194585502208⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070585166789,0,false,-29313774592,-29313774528⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070625729429,0,false,-29272116736,-29272116672⟩
    { al := (1328133/8192000), au := (664491/4096000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨178258993741,178372944593⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165202447744,165202447808⟩ : DyadicInterval 40),(⟨-194489404352,-194489404288⟩ : DyadicInterval 40),(⟨747609231326,747609250655⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165300497216,165300497280⟩ : DyadicInterval 40),(⟨-194625412672,-194625412608⟩ : DyadicInterval 40),(⟨747590586422,747590605752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165125749888,165125749952⟩ : DyadicInterval 40),(⟨-194383033728,-194383033664⟩ : DyadicInterval 40),(⟨747623806381,747623825711⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165242942656,165242942720⟩ : DyadicInterval 40),(⟨-194545572864,-194545572800⟩ : DyadicInterval 40),(⟨747601532532,747601551862⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34071859,45460032⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34071296,34071360⟩ : DyadicInterval 40),(⟨-34072448,-34072384⟩ : DyadicInterval 40),(⟨762123383072,762123402401⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45459072,45459136⟩ : DyadicInterval 40),(⟨-45460992,-45460928⟩ : DyadicInterval 40),(⟨762123382632,762123401961⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1920,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178214424533,178339508256⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165164095616,165164095680⟩ : DyadicInterval 40),(⟨-194436212416,-194436212352⟩ : DyadicInterval 40),(⟨747616520522,747616539851⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165271727680,165271727744⟩ : DyadicInterval 40),(⟨-194585502272,-194585502208⟩ : DyadicInterval 40),(⟨747596058598,747596077927⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29313774592,-29272116672⟩ : DyadicInterval 40),(⟨776759441952,776780290176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165202447744,165300497280⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194625412672,-194489404288⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2473_ok : ecellOkT e2473 = true := by decide +kernel
theorem e2473_pos {a z : ℝ} (ha1 : ((1328133/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((664491/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2473 e2473_ok ha1 ha2 hz1 hz2 hz

-- box ['331821/2048000', '1328133/8192000', '7997/8000', '3999/4000']  interval_lower 239528371/1099511627776
noncomputable def e2474 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277656670666,0,true,165104389568,165104389632⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921366584886,0,false,-194353412800,-194353412736⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277770621518,0,true,165202447744,165202447808⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921252634034,0,false,-194489404352,-194489404288⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277589866274,0,true,165046898304,165046898368⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921433389278,0,false,-194273694784,-194273694720⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277726056770,0,true,165164099456,165164099520⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921297198782,0,false,-194436217728,-194436217664⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534327232,0,true,22699200,22699264⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488928320,0,false,-22699712,-22699648⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545700317,0,true,34072000,34072064⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477555235,0,false,-34073088,-34073024⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626720,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627308,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277623263920,0,true,165075640384,165075640448⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921399991632,0,false,-194313547648,-194313547584⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277748347662,0,true,165183281152,165183281216⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921274907890,0,false,-194462820864,-194462820800⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070618501488,0,false,-29279539712,-29279539648⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070659040747,0,false,-29237907200,-29237907136⟩
    { al := (331821/2048000), au := (1328133/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨178145042890,178258993742⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165104389568,165104389632⟩ : DyadicInterval 40),(⟨-194353412800,-194353412736⟩ : DyadicInterval 40),(⟨747627864054,747627883384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165202447744,165202447808⟩ : DyadicInterval 40),(⟨-194489404352,-194489404288⟩ : DyadicInterval 40),(⟨747609231325,747609250655⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165046898304,165046898368⟩ : DyadicInterval 40),(⟨-194273694784,-194273694720⟩ : DyadicInterval 40),(⟨747638781981,747638801310⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165164099456,165164099520⟩ : DyadicInterval 40),(⟨-194436217728,-194436217664⟩ : DyadicInterval 40),(⟨747616519787,747616539116⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22699456,34072541⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22699200,22699264⟩ : DyadicInterval 40),(⟨-22699712,-22699648⟩ : DyadicInterval 40),(⟨762123383339,762123402668⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34072000,34072064⟩ : DyadicInterval 40),(⟨-34073088,-34073024⟩ : DyadicInterval 40),(⟨762123383040,762123402369⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178111636144,178236719886⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165075640384,165075640448⟩ : DyadicInterval 40),(⟨-194313547648,-194313547584⟩ : DyadicInterval 40),(⟨747633324293,747633343622⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165183281152,165183281216⟩ : DyadicInterval 40),(⟨-194462820864,-194462820800⟩ : DyadicInterval 40),(⟨747612874354,747612893684⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29279539712,-29237907136⟩ : DyadicInterval 40),(⟨776742337184,776763172736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165104389568,165202447808⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194489404352,-194353412736⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2474_ok : ecellOkT e2474 = true := by decide +kernel
theorem e2474_pos {a z : ℝ} (ha1 : ((331821/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1328133/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2474 e2474_ok ha1 ha2 hz1 hz2 hz

-- box ['1328133/8192000', '664491/4096000', '7997/8000', '3999/4000']  interval_lower 60194241/274877906944
noncomputable def e2475 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277770621517,0,true,165202447744,165202447808⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921252634035,0,false,-194489404352,-194489404288⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277884572369,0,true,165300497216,165300497280⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921138683183,0,false,-194625412672,-194625412608⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277703774394,0,true,165144924864,165144924928⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921319481158,0,false,-194409625408,-194409625344⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277839979134,0,true,165262127808,165262127872⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921183276418,0,false,-194572185472,-194572185408⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534342319,0,true,22714304,22714368⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488913233,0,false,-22714816,-22714752⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545722948,0,true,34094592,34094656⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477532604,0,false,-34095744,-34095680⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626718,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627307,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277737193402,0,true,165173682752,165173682816⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921286062150,0,false,-194449508736,-194449508672⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277862284273,0,true,165281320000,165281320064⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921160971279,0,false,-194598808960,-194598808896⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070581550213,0,false,-29317488896,-29317488832⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070622117707,0,false,-29275825920,-29275825856⟩
    { al := (1328133/8192000), au := (664491/4096000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨178258993741,178372944593⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165202447744,165202447808⟩ : DyadicInterval 40),(⟨-194489404352,-194489404288⟩ : DyadicInterval 40),(⟨747609231326,747609250655⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165300497216,165300497280⟩ : DyadicInterval 40),(⟨-194625412672,-194625412608⟩ : DyadicInterval 40),(⟨747590586422,747590605752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165144924864,165144924928⟩ : DyadicInterval 40),(⟨-194409625408,-194409625344⟩ : DyadicInterval 40),(⟨747620163302,747620182632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165262127808,165262127872⟩ : DyadicInterval 40),(⟨-194572185472,-194572185408⟩ : DyadicInterval 40),(⟨747597884307,747597903636⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22714543,34095172⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22714304,22714368⟩ : DyadicInterval 40),(⟨-22714816,-22714752⟩ : DyadicInterval 40),(⟨762123383338,762123402667⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34094592,34094656⟩ : DyadicInterval 40),(⟨-34095744,-34095680⟩ : DyadicInterval 40),(⟨762123383070,762123402399⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178225565626,178350656497⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165173682752,165173682816⟩ : DyadicInterval 40),(⟨-194449508736,-194449508672⟩ : DyadicInterval 40),(⟨747614698592,747614717921⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165281320000,165281320064⟩ : DyadicInterval 40),(⟨-194598808960,-194598808896⟩ : DyadicInterval 40),(⟨747594234225,747594253555⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29317488896,-29275825856⟩ : DyadicInterval 40),(⟨776761296544,776782147328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165202447744,165300497280⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194625412672,-194489404288⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2475_ok : ecellOkT e2475 = true := by decide +kernel
theorem e2475_pos {a z : ℝ} (ha1 : ((1328133/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((664491/4096000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2475 e2475_ok ha1 ha2 hz1 hz2 hz

-- box ['664491/4096000', '1329831/8192000', '1999/2000', '7997/8000']  interval_lower 60551963/274877906944
noncomputable def e2476 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277884572368,0,true,165300497216,165300497280⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921138683184,0,false,-194625412672,-194625412608⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277998523220,0,true,165398537920,165398537984⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921024732332,0,false,-194761437824,-194761437760⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277795385895,0,true,165223757120,165223757184⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921227869657,0,false,-194518960896,-194518960832⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277931590635,0,true,165340951744,165340951808⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921091664917,0,false,-194681537152,-194681537088⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545722265,0,true,34093952,34094016⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477533287,0,false,-34095040,-34094976⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557117983,0,true,45489216,45489280⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466137569,0,false,-45491200,-45491136⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625893,0,false,-1920,-1856⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626719,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277839974671,0,true,165262123968,165262124032⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921183280881,0,false,-194572180160,-194572180096⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277965065520,0,true,165369752576,165369752640⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921058190032,0,false,-194721497024,-194721496960⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070548196523,0,false,-29351744384,-29351744320⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070588787396,0,false,-29310056128,-29310056064⟩
    { al := (664491/4096000), au := (1329831/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨178372944592,178486895444⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165300497216,165300497280⟩ : DyadicInterval 40),(⟨-194625412672,-194625412608⟩ : DyadicInterval 40),(⟨747590586422,747590605752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165398537920,165398537984⟩ : DyadicInterval 40),(⟨-194761437824,-194761437760⟩ : DyadicInterval 40),(⟨747571929408,747571948737⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165223757120,165223757184⟩ : DyadicInterval 40),(⟨-194518960896,-194518960832⟩ : DyadicInterval 40),(⟨747605180320,747605199650⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165340951744,165340951808⟩ : DyadicInterval 40),(⟨-194681537152,-194681537088⟩ : DyadicInterval 40),(⟨747582889632,747582908962⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34094489,45490207⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34093952,34094016⟩ : DyadicInterval 40),(⟨-34095040,-34094976⟩ : DyadicInterval 40),(⟨762123383038,762123402367⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45489216,45489280⟩ : DyadicInterval 40),(⟨-45491200,-45491136⟩ : DyadicInterval 40),(⟨762123382661,762123401990⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1920,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178328346895,178453437744⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165262123968,165262124032⟩ : DyadicInterval 40),(⟨-194572180160,-194572180096⟩ : DyadicInterval 40),(⟨747597885043,747597904373⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165369752576,165369752640⟩ : DyadicInterval 40),(⟨-194721497024,-194721496960⟩ : DyadicInterval 40),(⟨747577408653,747577427982⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29351744384,-29310056064⟩ : DyadicInterval 40),(⟨776778411648,776799275072⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165300497216,165398537984⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194761437824,-194625412608⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2476_ok : ecellOkT e2476 = true := by decide +kernel
theorem e2476_pos {a z : ℝ} (ha1 : ((664491/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1329831/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2476 e2476_ok ha1 ha2 hz1 hz2 hz

-- box ['1329831/8192000', '33267/204800', '1999/2000', '7997/8000']  interval_lower 121731379/549755813888
noncomputable def e2477 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277998523219,0,true,165398537920,165398537984⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921024732333,0,false,-194761437824,-194761437760⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278112474072,0,true,165496569856,165496569920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920910781480,0,false,-194897479808,-194897479744⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277909279771,0,true,165321755648,165321755712⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921113975781,0,false,-194654904896,-194654904832⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278045498755,0,true,165438952064,165438952128⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920977756797,0,false,-194817518272,-194817518208⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545744897,0,true,34116544,34116608⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477510655,0,false,-34117696,-34117632⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557148162,0,true,45519424,45519488⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466107390,0,false,-45521344,-45521280⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625891,0,false,-1920,-1856⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626718,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277953897032,0,true,165360143616,165360143680⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921069358520,0,false,-194708164736,-194708164672⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278078995002,0,true,165467768704,165467768768⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920944260550,0,false,-194857508544,-194857508480⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070511202648,0,false,-29389739776,-29389739712⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070551821756,0,false,-29348021120,-29348021056⟩
    { al := (1329831/8192000), au := (33267/204800), zl := (1999/2000), zu := (7997/8000),
      A := ⟨178486895443,178600846296⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165398537920,165398537984⟩ : DyadicInterval 40),(⟨-194761437824,-194761437760⟩ : DyadicInterval 40),(⟨747571929408,747571948737⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165496569856,165496569920⟩ : DyadicInterval 40),(⟨-194897479808,-194897479744⟩ : DyadicInterval 40),(⟨747553260280,747553279609⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165321755648,165321755712⟩ : DyadicInterval 40),(⟨-194654904896,-194654904832⟩ : DyadicInterval 40),(⟨747586542135,747586561464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165438952064,165438952128⟩ : DyadicInterval 40),(⟨-194817518272,-194817518208⟩ : DyadicInterval 40),(⟨747564234638,747564253968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34117121,45520386⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34116544,34116608⟩ : DyadicInterval 40),(⟨-34117696,-34117632⟩ : DyadicInterval 40),(⟨762123383069,762123402398⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45519424,45519488⟩ : DyadicInterval 40),(⟨-45521344,-45521280⟩ : DyadicInterval 40),(⟨762123382627,762123401956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1920,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178442269256,178567367226⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165360143616,165360143680⟩ : DyadicInterval 40),(⟨-194708164736,-194708164672⟩ : DyadicInterval 40),(⟨747579237429,747579256758⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165467768704,165467768768⟩ : DyadicInterval 40),(⟨-194857508544,-194857508480⟩ : DyadicInterval 40),(⟨747558746579,747558765908⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29389739776,-29348021056⟩ : DyadicInterval 40),(⟨776797394144,776818272768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165398537920,165496569920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194897479808,-194761437760⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2477_ok : ecellOkT e2477 = true := by decide +kernel
theorem e2477_pos {a z : ℝ} (ha1 : ((1329831/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((33267/204800 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2477 e2477_ok ha1 ha2 hz1 hz2 hz

-- box ['664491/4096000', '1329831/8192000', '7997/8000', '3999/4000']  interval_lower 60507117/274877906944
noncomputable def e2478 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277884572368,0,true,165300497216,165300497280⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921138683184,0,false,-194625412672,-194625412608⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277998523220,0,true,165398537920,165398537984⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921024732332,0,false,-194761437824,-194761437760⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277817682513,0,true,165242942656,165242942720⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921205573039,0,false,-194545572864,-194545572800⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277953901497,0,true,165360147456,165360147520⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921069354055,0,false,-194708170048,-194708169984⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534357404,0,true,22729344,22729408⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488898148,0,false,-22729920,-22729856⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545745579,0,true,34117248,34117312⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477509973,0,false,-34118336,-34118272⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626717,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627307,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277851122886,0,true,165271716416,165271716480⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921172132666,0,false,-194585486592,-194585486528⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277976220883,0,true,165379350208,165379350272⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921047034669,0,false,-194734813824,-194734813760⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070544575324,0,false,-29355463552,-29355463488⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070585171055,0,false,-29313770176,-29313770112⟩
    { al := (664491/4096000), au := (1329831/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨178372944592,178486895444⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165300497216,165300497280⟩ : DyadicInterval 40),(⟨-194625412672,-194625412608⟩ : DyadicInterval 40),(⟨747590586422,747590605752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165398537920,165398537984⟩ : DyadicInterval 40),(⟨-194761437824,-194761437760⟩ : DyadicInterval 40),(⟨747571929408,747571948737⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165242942656,165242942720⟩ : DyadicInterval 40),(⟨-194545572864,-194545572800⟩ : DyadicInterval 40),(⟨747601532533,747601551862⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165360147456,165360147520⟩ : DyadicInterval 40),(⟨-194708170048,-194708169984⟩ : DyadicInterval 40),(⟨747579236691,747579256021⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22729628,34117803⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22729344,22729408⟩ : DyadicInterval 40),(⟨-22729920,-22729856⟩ : DyadicInterval 40),(⟨762123383370,762123402699⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34117248,34117312⟩ : DyadicInterval 40),(⟨-34118336,-34118272⟩ : DyadicInterval 40),(⟨762123383037,762123402366⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178339495110,178464593107⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165271716416,165271716480⟩ : DyadicInterval 40),(⟨-194585486592,-194585486528⟩ : DyadicInterval 40),(⟨747596060726,747596080055⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165379350208,165379350272⟩ : DyadicInterval 40),(⟨-194734813824,-194734813760⟩ : DyadicInterval 40),(⟨747575581890,747575601219⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29355463552,-29313770112⟩ : DyadicInterval 40),(⟨776780268672,776801134656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165300497216,165398537984⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194761437824,-194625412608⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2478_ok : ecellOkT e2478 = true := by decide +kernel
theorem e2478_pos {a z : ℝ} (ha1 : ((664491/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1329831/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2478 e2478_ok ha1 ha2 hz1 hz2 hz

-- box ['1329831/8192000', '33267/204800', '7997/8000', '3999/4000']  interval_lower 121641359/549755813888
noncomputable def e2479 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277998523219,0,true,165398537920,165398537984⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921024732333,0,false,-194761437824,-194761437760⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278112474072,0,true,165496569856,165496569920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920910781480,0,false,-194897479808,-194897479744⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277931590633,0,true,165340951680,165340951744⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921091664919,0,false,-194681537152,-194681537088⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278067823861,0,true,165458158336,165458158400⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920955431691,0,false,-194844171456,-194844171392⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534372493,0,true,22744448,22744512⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488883059,0,false,-22744960,-22744896⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545768213,0,true,34139904,34139968⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477487339,0,false,-34140992,-34140928⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626715,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627306,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277965052367,0,true,165369741248,165369741312⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921058203185,0,false,-194721481344,-194721481280⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278090157489,0,true,165477371584,165477371648⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920933098063,0,false,-194870835456,-194870835392⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070507576823,0,false,-29393463872,-29393463808⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070548200793,0,false,-29351740032,-29351739968⟩
    { al := (1329831/8192000), au := (33267/204800), zl := (7997/8000), zu := (3999/4000),
      A := ⟨178486895443,178600846296⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165398537920,165398537984⟩ : DyadicInterval 40),(⟨-194761437824,-194761437760⟩ : DyadicInterval 40),(⟨747571929408,747571948737⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165496569856,165496569920⟩ : DyadicInterval 40),(⟨-194897479808,-194897479744⟩ : DyadicInterval 40),(⟨747553260280,747553279609⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165340951680,165340951744⟩ : DyadicInterval 40),(⟨-194681537152,-194681537088⟩ : DyadicInterval 40),(⟨747582889669,747582908999⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165458158336,165458158400⟩ : DyadicInterval 40),(⟨-194844171456,-194844171392⟩ : DyadicInterval 40),(⟨747560576974,747560596304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22744717,34140437⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22744448,22744512⟩ : DyadicInterval 40),(⟨-22744960,-22744896⟩ : DyadicInterval 40),(⟨762123383337,762123402666⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34139904,34139968⟩ : DyadicInterval 40),(⟨-34140992,-34140928⟩ : DyadicInterval 40),(⟨762123383035,762123402364⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178453424591,178578529713⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165369741248,165369741312⟩ : DyadicInterval 40),(⟨-194721481344,-194721481280⟩ : DyadicInterval 40),(⟨747577410822,747577430152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165477371584,165477371648⟩ : DyadicInterval 40),(⟨-194870835456,-194870835392⟩ : DyadicInterval 40),(⟨747556917458,747556936788⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29393463872,-29351739968⟩ : DyadicInterval 40),(⟨776799253600,776820134816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165398537920,165496569920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194897479808,-194761437760⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2479_ok : ecellOkT e2479 = true := by decide +kernel
theorem e2479_pos {a z : ℝ} (ha1 : ((1329831/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((33267/204800 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2479 e2479_ok ha1 ha2 hz1 hz2 hz

-- box ['331821/2048000', '1328133/8192000', '3999/4000', '7999/8000']  interval_lower 239349929/1099511627776
noncomputable def e2480 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277656670666,0,true,165104389568,165104389632⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921366584886,0,false,-194353412800,-194353412736⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277770621518,0,true,165202447744,165202447808⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921252634034,0,false,-194489404352,-194489404288⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277612134405,0,true,165066062400,165066062464⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921411121147,0,false,-194300266816,-194300266752⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277748339144,0,true,165183273792,165183273856⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921274916408,0,false,-194462810688,-194462810624⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522977403,0,true,11349568,11349632⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500278149,0,false,-11349696,-11349632⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534342945,0,true,22714880,22714944⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488912607,0,false,-22715456,-22715392⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627306,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627659,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277634397918,0,true,165085222208,165085222272⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921388857634,0,false,-194326833984,-194326833920⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277759488812,0,true,165192868096,165192868160⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921263766740,0,false,-194476117568,-194476117504⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070614889295,0,false,-29283249408,-29283249344⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070655433407,0,false,-29241611776,-29241611712⟩
    { al := (331821/2048000), au := (1328133/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨178145042890,178258993742⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165104389568,165104389632⟩ : DyadicInterval 40),(⟨-194353412800,-194353412736⟩ : DyadicInterval 40),(⟨747627864054,747627883384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165202447744,165202447808⟩ : DyadicInterval 40),(⟨-194489404352,-194489404288⟩ : DyadicInterval 40),(⟨747609231325,747609250655⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165066062400,165066062464⟩ : DyadicInterval 40),(⟨-194300266816,-194300266752⟩ : DyadicInterval 40),(⟨747635143132,747635162461⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165183273792,165183273856⟩ : DyadicInterval 40),(⟨-194462810688,-194462810624⟩ : DyadicInterval 40),(⟨747612875761,747612895090⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11349627,22715169⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11349568,11349632⟩ : DyadicInterval 40),(⟨-11349696,-11349632⟩ : DyadicInterval 40),(⟨762123383498,762123402827⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22714880,22714944⟩ : DyadicInterval 40),(⟨-22715456,-22715392⟩ : DyadicInterval 40),(⟨762123383370,762123402699⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178122770142,178247861036⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165085222208,165085222272⟩ : DyadicInterval 40),(⟨-194326833984,-194326833920⟩ : DyadicInterval 40),(⟨747631504564,747631523894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165192868096,165192868160⟩ : DyadicInterval 40),(⟨-194476117568,-194476117504⟩ : DyadicInterval 40),(⟨747611052224,747611071553⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29283249408,-29241611712⟩ : DyadicInterval 40),(⟨776744189472,776765027584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165104389568,165202447808⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194489404352,-194353412736⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2480_ok : ecellOkT e2480 = true := by decide +kernel
theorem e2480_pos {a z : ℝ} (ha1 : ((331821/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1328133/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2480 e2480_ok ha1 ha2 hz1 hz2 hz

-- box ['1328133/8192000', '664491/4096000', '3999/4000', '7999/8000']  interval_lower 240597811/1099511627776
noncomputable def e2481 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277770621517,0,true,165202447744,165202447808⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921252634035,0,false,-194489404352,-194489404288⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277884572369,0,true,165300497216,165300497280⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921138683183,0,false,-194625412672,-194625412608⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277726056768,0,true,165164099456,165164099520⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921297198784,0,false,-194436217728,-194436217664⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277862275752,0,true,165281312704,165281312768⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921160979800,0,false,-194598798784,-194598798720⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522984947,0,true,11357056,11357120⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500270605,0,false,-11357248,-11357184⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534358032,0,true,22729984,22730048⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488897520,0,false,-22730496,-22730432⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627306,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627659,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277748334519,0,true,165183269824,165183269888⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921274921033,0,false,-194462805184,-194462805120⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277873432542,0,true,165290912320,165290912384⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921149823010,0,false,-194612115776,-194612115712⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070577933401,0,false,-29321203456,-29321203392⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070618505750,0,false,-29279535360,-29279535296⟩
    { al := (1328133/8192000), au := (664491/4096000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨178258993741,178372944593⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165202447744,165202447808⟩ : DyadicInterval 40),(⟨-194489404352,-194489404288⟩ : DyadicInterval 40),(⟨747609231326,747609250655⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165300497216,165300497280⟩ : DyadicInterval 40),(⟨-194625412672,-194625412608⟩ : DyadicInterval 40),(⟨747590586422,747590605752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165164099456,165164099520⟩ : DyadicInterval 40),(⟨-194436217728,-194436217664⟩ : DyadicInterval 40),(⟨747616519787,747616539117⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165281312704,165281312768⟩ : DyadicInterval 40),(⟨-194598798784,-194598798720⟩ : DyadicInterval 40),(⟨747594235597,747594254926⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11357171,22730256⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11357056,11357120⟩ : DyadicInterval 40),(⟨-11357248,-11357184⟩ : DyadicInterval 40),(⟨762123383530,762123402859⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22729984,22730048⟩ : DyadicInterval 40),(⟨-22730496,-22730432⟩ : DyadicInterval 40),(⟨762123383338,762123402667⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178236706743,178361804766⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165183269824,165183269888⟩ : DyadicInterval 40),(⟨-194462805184,-194462805120⟩ : DyadicInterval 40),(⟨747612876517,747612895846⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165290912320,165290912384⟩ : DyadicInterval 40),(⟨-194612115776,-194612115712⟩ : DyadicInterval 40),(⟨747592409669,747592428999⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29321203456,-29279535296⟩ : DyadicInterval 40),(⟨776763151264,776784004608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165202447744,165300497280⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194625412672,-194489404288⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2481_ok : ecellOkT e2481 = true := by decide +kernel
theorem e2481_pos {a z : ℝ} (ha1 : ((1328133/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((664491/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2481 e2481_ok ha1 ha2 hz1 hz2 hz

-- box ['331821/2048000', '1328133/8192000', '7999/8000', '1']  interval_lower 239171341/1099511627776
noncomputable def e2482 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277656670666,0,true,165104389568,165104389632⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921366584886,0,false,-194353412800,-194353412736⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277770621518,0,true,165202447744,165202447808⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921252634034,0,false,-194489404352,-194489404288⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277634402535,0,true,165085226176,165085226240⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921388853017,0,false,-194326839488,-194326839424⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522985517,0,true,11357632,11357696⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500270035,0,false,-11357824,-11357760⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627658,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1277645531945,0,true,165094803904,165094803968⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨921377723607,0,false,-194340120512,-194340120448⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1277770629981,0,true,165202455040,165202455104⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨921252625571,0,false,-194489414400,-194489414336⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1070611276870,0,false,-29286959360,-29286959296⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1070651825831,0,false,-29245316608,-29245316544⟩
    { al := (331821/2048000), au := (1328133/8192000), zl := (7999/8000), zu := 1,
      A := ⟨178145042890,178258993742⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165104389568,165104389632⟩ : DyadicInterval 40),(⟨-194353412800,-194353412736⟩ : DyadicInterval 40),(⟨747627864054,747627883384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165202447744,165202447808⟩ : DyadicInterval 40),(⟨-194489404352,-194489404288⟩ : DyadicInterval 40),(⟨747609231325,747609250655⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165085226176,165085226240⟩ : DyadicInterval 40),(⟨-194326839488,-194326839424⟩ : DyadicInterval 40),(⟨747631503810,747631523140⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165202447744,165202447808⟩ : DyadicInterval 40),(⟨-194489404352,-194489404288⟩ : DyadicInterval 40),(⟨747609231325,747609250655⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11357741⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11357632,11357696⟩ : DyadicInterval 40),(⟨-11357824,-11357760⟩ : DyadicInterval 40),(⟨762123383530,762123402859⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨178133904169,178259002205⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165094803904,165094803968⟩ : DyadicInterval 40),(⟨-194340120512,-194340120448⟩ : DyadicInterval 40),(⟨747629684755,747629704084⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165202455040,165202455104⟩ : DyadicInterval 40),(⟨-194489414400,-194489414336⟩ : DyadicInterval 40),(⟨747609229911,747609249241⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29286959360,-29245316544⟩ : DyadicInterval 40),(⟨776746041888,776766882560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨165104389568,165202447808⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194489404352,-194353412736⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2482_ok : ecellOkT e2482 = true := by decide +kernel
theorem e2482_pos {a z : ℝ} (ha1 : ((331821/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1328133/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2482 e2482_ok ha1 ha2 hz1 hz2 hz

-- box ['1328133/8192000', '664491/4096000', '7999/8000', '1']  interval_lower 120209499/549755813888
noncomputable def e2483 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277770621517,0,true,165202447744,165202447808⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921252634035,0,false,-194489404352,-194489404288⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277884572369,0,true,165300497216,165300497280⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921138683183,0,false,-194625412672,-194625412608⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277748339142,0,true,165183273792,165183273856⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921274916410,0,false,-194462810688,-194462810624⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522993061,0,true,11365184,11365248⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500262491,0,false,-11365376,-11365312⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627658,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1277759475668,0,true,165192856832,165192856896⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨921263779884,0,false,-194476101888,-194476101824⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1277884580837,0,true,165300504512,165300504576⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨921138674715,0,false,-194625422784,-194625422720⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1070574316355,0,false,-29324918208,-29324918144⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1070614893558,0,false,-29283245056,-29283244992⟩
    { al := (1328133/8192000), au := (664491/4096000), zl := (7999/8000), zu := 1,
      A := ⟨178258993741,178372944593⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165202447744,165202447808⟩ : DyadicInterval 40),(⟨-194489404352,-194489404288⟩ : DyadicInterval 40),(⟨747609231326,747609250655⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165300497216,165300497280⟩ : DyadicInterval 40),(⟨-194625412672,-194625412608⟩ : DyadicInterval 40),(⟨747590586422,747590605752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165183273792,165183273856⟩ : DyadicInterval 40),(⟨-194462810688,-194462810624⟩ : DyadicInterval 40),(⟨747612875761,747612895091⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165300497216,165300497280⟩ : DyadicInterval 40),(⟨-194625412672,-194625412608⟩ : DyadicInterval 40),(⟨747590586422,747590605752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11365285⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11365184,11365248⟩ : DyadicInterval 40),(⟨-11365376,-11365312⟩ : DyadicInterval 40),(⟨762123383530,762123402859⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨178247847892,178372953061⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165192856832,165192856896⟩ : DyadicInterval 40),(⟨-194476101888,-194476101824⟩ : DyadicInterval 40),(⟨747611054350,747611073679⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165300504512,165300504576⟩ : DyadicInterval 40),(⟨-194625422784,-194625422720⟩ : DyadicInterval 40),(⟨747590585032,747590604362⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29324918208,-29283244992⟩ : DyadicInterval 40),(⟨776765006112,776785861984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨165202447744,165300497280⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194625412672,-194489404288⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2483_ok : ecellOkT e2483 = true := by decide +kernel
theorem e2483_pos {a z : ℝ} (ha1 : ((1328133/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((664491/4096000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2483 e2483_ok ha1 ha2 hz1 hz2 hz

-- box ['664491/4096000', '1329831/8192000', '3999/4000', '7999/8000']  interval_lower 241848887/1099511627776
noncomputable def e2484 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277884572368,0,true,165300497216,165300497280⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921138683184,0,false,-194625412672,-194625412608⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277998523220,0,true,165398537920,165398537984⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921024732332,0,false,-194761437824,-194761437760⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277839979131,0,true,165262127808,165262127872⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921183276421,0,false,-194572185472,-194572185408⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277976212359,0,true,165379342848,165379342912⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921047043193,0,false,-194734803648,-194734803584⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522992489,0,true,11364608,11364672⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500263063,0,false,-11364800,-11364736⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534373119,0,true,22745088,22745152⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488882433,0,false,-22745600,-22745536⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627305,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627659,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277862271126,0,true,165281308736,165281308800⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921160984426,0,false,-194598793216,-194598793152⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277987376271,0,true,165388947712,165388947776⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921035879281,0,false,-194748130752,-194748130688⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070540953891,0,false,-29359183040,-29359182976⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070581554479,0,false,-29317484480,-29317484416⟩
    { al := (664491/4096000), au := (1329831/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨178372944592,178486895444⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165300497216,165300497280⟩ : DyadicInterval 40),(⟨-194625412672,-194625412608⟩ : DyadicInterval 40),(⟨747590586422,747590605752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165398537920,165398537984⟩ : DyadicInterval 40),(⟨-194761437824,-194761437760⟩ : DyadicInterval 40),(⟨747571929408,747571948737⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165262127808,165262127872⟩ : DyadicInterval 40),(⟨-194572185472,-194572185408⟩ : DyadicInterval 40),(⟨747597884307,747597903637⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165379342848,165379342912⟩ : DyadicInterval 40),(⟨-194734803648,-194734803584⟩ : DyadicInterval 40),(⟨747575583301,747575602630⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11364713,22745343⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11364608,11364672⟩ : DyadicInterval 40),(⟨-11364800,-11364736⟩ : DyadicInterval 40),(⟨762123383530,762123402859⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22745088,22745152⟩ : DyadicInterval 40),(⟨-22745600,-22745536⟩ : DyadicInterval 40),(⟨762123383337,762123402666⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178350643350,178475748495⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165281308736,165281308800⟩ : DyadicInterval 40),(⟨-194598793216,-194598793152⟩ : DyadicInterval 40),(⟨747594236327,747594255657⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165388947712,165388947776⟩ : DyadicInterval 40),(⟨-194748130752,-194748130688⟩ : DyadicInterval 40),(⟨747573755017,747573774347⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29359183040,-29317484416⟩ : DyadicInterval 40),(⟨776782125824,776802994400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165300497216,165398537984⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194761437824,-194625412608⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2484_ok : ecellOkT e2484 = true := by decide +kernel
theorem e2484_pos {a z : ℝ} (ha1 : ((664491/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1329831/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2484 e2484_ok ha1 ha2 hz1 hz2 hz

-- box ['1329831/8192000', '33267/204800', '3999/4000', '7999/8000']  interval_lower 243102923/1099511627776
noncomputable def e2485 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277998523219,0,true,165398537920,165398537984⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921024732333,0,false,-194761437824,-194761437760⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278112474072,0,true,165496569856,165496569920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920910781480,0,false,-194897479808,-194897479744⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277953901495,0,true,165360147456,165360147520⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921069354057,0,false,-194708170048,-194708169984⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278090148967,0,true,165477364288,165477364352⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920933106585,0,false,-194870825280,-194870825216⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523000033,0,true,11372160,11372224⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500255519,0,false,-11372352,-11372288⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534388208,0,true,22760192,22760256⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488867344,0,false,-22760704,-22760640⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627304,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627659,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277976207734,0,true,165379338880,165379338944⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921047047818,0,false,-194734798080,-194734798016⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278101320004,0,true,165486974400,165486974464⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920921935548,0,false,-194884162624,-194884162560⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070503950763,0,false,-29397188160,-29397188096⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070544579593,0,false,-29355459200,-29355459136⟩
    { al := (1329831/8192000), au := (33267/204800), zl := (3999/4000), zu := (7999/8000),
      A := ⟨178486895443,178600846296⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165398537920,165398537984⟩ : DyadicInterval 40),(⟨-194761437824,-194761437760⟩ : DyadicInterval 40),(⟨747571929408,747571948737⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165496569856,165496569920⟩ : DyadicInterval 40),(⟨-194897479808,-194897479744⟩ : DyadicInterval 40),(⟨747553260280,747553279609⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165360147456,165360147520⟩ : DyadicInterval 40),(⟨-194708170048,-194708169984⟩ : DyadicInterval 40),(⟨747579236691,747579256021⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165477364288,165477364352⟩ : DyadicInterval 40),(⟨-194870825280,-194870825216⟩ : DyadicInterval 40),(⟨747556918833,747556938163⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11372257,22760432⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11372160,11372224⟩ : DyadicInterval 40),(⟨-11372352,-11372288⟩ : DyadicInterval 40),(⟨762123383530,762123402859⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22760192,22760256⟩ : DyadicInterval 40),(⟨-22760704,-22760640⟩ : DyadicInterval 40),(⟨762123383336,762123402665⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178464579958,178589692228⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165379338880,165379338944⟩ : DyadicInterval 40),(⟨-194734798080,-194734798016⟩ : DyadicInterval 40),(⟨747575584032,747575603361⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165486974400,165486974464⟩ : DyadicInterval 40),(⟨-194884162624,-194884162560⟩ : DyadicInterval 40),(⟨747555088245,747555107574⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29397188160,-29355459136⟩ : DyadicInterval 40),(⟨776801113184,776821996960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165398537920,165496569920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194897479808,-194761437760⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2485_ok : ecellOkT e2485 = true := by decide +kernel
theorem e2485_pos {a z : ℝ} (ha1 : ((1329831/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((33267/204800 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2485 e2485_ok ha1 ha2 hz1 hz2 hz

-- box ['664491/4096000', '1329831/8192000', '7999/8000', '1']  interval_lower 120834789/549755813888
noncomputable def e2486 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277884572368,0,true,165300497216,165300497280⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921138683184,0,false,-194625412672,-194625412608⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277998523220,0,true,165398537920,165398537984⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921024732332,0,false,-194761437824,-194761437760⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277862275749,0,true,165281312704,165281312768⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921160979803,0,false,-194598798784,-194598798720⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523000605,0,true,11372736,11372800⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500254947,0,false,-11372928,-11372864⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627658,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1277873419395,0,true,165290900992,165290901056⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨921149836157,0,false,-194612100032,-194612099968⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1277998531689,0,true,165398545216,165398545280⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨921024723863,0,false,-194761447936,-194761447872⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1070537332221,0,false,-29362902720,-29362902656⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1070577937667,0,false,-29321199040,-29321198976⟩
    { al := (664491/4096000), au := (1329831/8192000), zl := (7999/8000), zu := 1,
      A := ⟨178372944592,178486895444⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165300497216,165300497280⟩ : DyadicInterval 40),(⟨-194625412672,-194625412608⟩ : DyadicInterval 40),(⟨747590586422,747590605752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165398537920,165398537984⟩ : DyadicInterval 40),(⟨-194761437824,-194761437760⟩ : DyadicInterval 40),(⟨747571929408,747571948737⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165281312704,165281312768⟩ : DyadicInterval 40),(⟨-194598798784,-194598798720⟩ : DyadicInterval 40),(⟨747594235597,747594254926⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165398537920,165398537984⟩ : DyadicInterval 40),(⟨-194761437824,-194761437760⟩ : DyadicInterval 40),(⟨747571929408,747571948737⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11372829⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11372736,11372800⟩ : DyadicInterval 40),(⟨-11372928,-11372864⟩ : DyadicInterval 40),(⟨762123383530,762123402859⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨178361791619,178486903913⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165290900992,165290901056⟩ : DyadicInterval 40),(⟨-194612100032,-194612099968⟩ : DyadicInterval 40),(⟨747592411809,747592431139⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165398545216,165398545280⟩ : DyadicInterval 40),(⟨-194761447936,-194761447872⟩ : DyadicInterval 40),(⟨747571928016,747571947345⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29362902720,-29321198976⟩ : DyadicInterval 40),(⟨776783983104,776804854240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨165300497216,165398537984⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194761437824,-194625412608⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2486_ok : ecellOkT e2486 = true := by decide +kernel
theorem e2486_pos {a z : ℝ} (ha1 : ((664491/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1329831/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2486 e2486_ok ha1 ha2 hz1 hz2 hz

-- box ['1329831/8192000', '33267/204800', '7999/8000', '1']  interval_lower 242923097/1099511627776
noncomputable def e2487 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277998523219,0,true,165398537920,165398537984⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921024732333,0,false,-194761437824,-194761437760⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278112474072,0,true,165496569856,165496569920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920910781480,0,false,-194897479808,-194897479744⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277976212356,0,true,165379342848,165379342912⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921047043196,0,false,-194734803648,-194734803584⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523008149,0,true,11380288,11380352⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500247403,0,false,-11380480,-11380416⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627658,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1277987363121,0,true,165388936384,165388936448⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨921035892431,0,false,-194748115072,-194748115008⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1278112482538,0,true,165496577152,165496577216⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨920910773014,0,false,-194897489920,-194897489856⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1070500324470,0,false,-29400912704,-29400912640⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1070540958161,0,false,-29359178624,-29359178560⟩
    { al := (1329831/8192000), au := (33267/204800), zl := (7999/8000), zu := 1,
      A := ⟨178486895443,178600846296⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165398537920,165398537984⟩ : DyadicInterval 40),(⟨-194761437824,-194761437760⟩ : DyadicInterval 40),(⟨747571929408,747571948737⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165496569856,165496569920⟩ : DyadicInterval 40),(⟨-194897479808,-194897479744⟩ : DyadicInterval 40),(⟨747553260280,747553279609⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165379342848,165379342912⟩ : DyadicInterval 40),(⟨-194734803648,-194734803584⟩ : DyadicInterval 40),(⟨747575583301,747575602630⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165496569856,165496569920⟩ : DyadicInterval 40),(⟨-194897479808,-194897479744⟩ : DyadicInterval 40),(⟨747553260280,747553279609⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11380373⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11380288,11380352⟩ : DyadicInterval 40),(⟨-11380480,-11380416⟩ : DyadicInterval 40),(⟨762123383530,762123402859⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨178475735345,178600854762⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165388936384,165388936448⟩ : DyadicInterval 40),(⟨-194748115072,-194748115008⟩ : DyadicInterval 40),(⟨747573757187,747573776517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165496577152,165496577216⟩ : DyadicInterval 40),(⟨-194897489920,-194897489856⟩ : DyadicInterval 40),(⟨747553258886,747553278216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29400912704,-29359178560⟩ : DyadicInterval 40),(⟨776802972896,776823859232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨165398537920,165496569920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194897479808,-194761437760⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2487_ok : ecellOkT e2487 = true := by decide +kernel
theorem e2487_pos {a z : ℝ} (ha1 : ((1329831/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((33267/204800 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2487 e2487_ok ha1 ha2 hz1 hz2 hz

-- box ['33267/204800', '1331529/8192000', '999/1000', '7993/8000']  interval_lower 122720425/549755813888
noncomputable def e2488 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278112474071,0,true,165496569856,165496569920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920910781481,0,false,-194897479808,-194897479744⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278226424923,0,true,165594593088,165594593152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920796830629,0,false,-195033538624,-195033538560⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277933873224,0,true,165342915584,165342915648⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921089382328,0,false,-194684261888,-194684261824⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278070049476,0,true,165460073024,165460073088⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920953206076,0,false,-194846828608,-194846828544⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591286768,0,true,79656064,79656128⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431968784,0,false,-79661888,-79661824⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099602727759,0,true,91096192,91096256⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099420527793,0,false,-91103808,-91103744⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620227,0,false,-7552,-7488⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622005,0,false,-5824,-5760⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278023169821,0,true,165419742144,165419742208⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921000085731,0,false,-194790861120,-194790861056⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278148246326,0,true,165527342976,165527343040⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920875009226,0,false,-194940190528,-194940190464⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070488704615,0,false,-29412847552,-29412847488⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070529332512,0,false,-29371118976,-29371118912⟩
    { al := (33267/204800), au := (1331529/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨178600846295,178714797147⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165496569856,165496569920⟩ : DyadicInterval 40),(⟨-194897479808,-194897479744⟩ : DyadicInterval 40),(⟨747553260280,747553279609⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165594593088,165594593152⟩ : DyadicInterval 40),(⟨-195033538624,-195033538560⟩ : DyadicInterval 40),(⟨747534579000,747534598330⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165342915584,165342915648⟩ : DyadicInterval 40),(⟨-194684261888,-194684261824⟩ : DyadicInterval 40),(⟨747582515959,747582535289⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165460073024,165460073088⟩ : DyadicInterval 40),(⟨-194846828608,-194846828544⟩ : DyadicInterval 40),(⟨747560212318,747560231648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨79658992,91099983⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79656064,79656128⟩ : DyadicInterval 40),(⟨-79661888,-79661824⟩ : DyadicInterval 40),(⟨762123380692,762123400021⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨91096192,91096256⟩ : DyadicInterval 40),(⟨-91103808,-91103744⟩ : DyadicInterval 40),(⟨762123379811,762123399141⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7552,-5760⟩ : DyadicInterval 40),(⟨762123386496,762123406656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178511542045,178636618550⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165419742144,165419742208⟩ : DyadicInterval 40),(⟨-194790861120,-194790861056⟩ : DyadicInterval 40),(⟨747567892456,747567911785⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165527342976,165527343040⟩ : DyadicInterval 40),(⟨-194940190528,-194940190464⟩ : DyadicInterval 40),(⟨747547397003,747547416332⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29412847552,-29371118912⟩ : DyadicInterval 40),(⟨776808943072,776829826656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165496569856,165594593152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195033538624,-194897479744⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2488_ok : ecellOkT e2488 = true := by decide +kernel
theorem e2488_pos {a z : ℝ} (ha1 : ((33267/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1331529/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2488 e2488_ok ha1 ha2 hz1 hz2 hz

-- box ['1331529/8192000', '666189/4096000', '999/1000', '7993/8000']  interval_lower 123351613/549755813888
noncomputable def e2489 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278226424922,0,true,165594593088,165594593152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920796830630,0,false,-195033538624,-195033538560⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278340375774,0,true,165692607552,165692607616⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920682879778,0,false,-195169614272,-195169614208⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278047710124,0,true,165440854528,165440854592⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920975545428,0,false,-194820158272,-194820158208⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278183900620,0,true,165558013696,165558013760⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920839354932,0,false,-194982762112,-194982762048⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591339582,0,true,79708864,79708928⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431915970,0,false,-79714752,-79714688⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099602788124,0,true,91156544,91156608⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099420467428,0,false,-91164160,-91164096⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620217,0,false,-7616,-7552⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621998,0,false,-5824,-5760⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278137063703,0,true,165517723200,165517723264⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920886191849,0,false,-194926838720,-194926838656⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278262147321,0,true,165625320576,165625320640⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920761108231,0,false,-195076195136,-195076195072⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070451682041,0,false,-29450874560,-29450874496⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070492338163,0,false,-29409115520,-29409115456⟩
    { al := (1331529/8192000), au := (666189/4096000), zl := (999/1000), zu := (7993/8000),
      A := ⟨178714797146,178828747998⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165594593088,165594593152⟩ : DyadicInterval 40),(⟨-195033538624,-195033538560⟩ : DyadicInterval 40),(⟨747534579001,747534598330⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165692607552,165692607616⟩ : DyadicInterval 40),(⟨-195169614272,-195169614208⟩ : DyadicInterval 40),(⟨747515885606,747515904935⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165440854528,165440854592⟩ : DyadicInterval 40),(⟨-194820158272,-194820158208⟩ : DyadicInterval 40),(⟨747563872330,747563891659⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165558013696,165558013760⟩ : DyadicInterval 40),(⟨-194982762112,-194982762048⟩ : DyadicInterval 40),(⟨747541551932,747541571262⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨79711806,91160348⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79708864,79708928⟩ : DyadicInterval 40),(⟨-79714752,-79714688⟩ : DyadicInterval 40),(⟨762123380716,762123400046⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨91156544,91156608⟩ : DyadicInterval 40),(⟨-91164160,-91164096⟩ : DyadicInterval 40),(⟨762123379801,762123399131⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7616,-5760⟩ : DyadicInterval 40),(⟨762123386496,762123406688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178625435927,178750519545⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165517723200,165517723264⟩ : DyadicInterval 40),(⟨-194926838720,-194926838656⟩ : DyadicInterval 40),(⟨747549230030,747549249359⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165625320576,165625320640⟩ : DyadicInterval 40),(⟨-195076195136,-195076195072⟩ : DyadicInterval 40),(⟨747528720113,747528739443⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29450874560,-29409115456⟩ : DyadicInterval 40),(⟨776827941344,776848840160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165594593088,165692607616⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195169614272,-195033538560⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2489_ok : ecellOkT e2489 = true := by decide +kernel
theorem e2489_pos {a z : ℝ} (ha1 : ((1331529/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((666189/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2489 e2489_ok ha1 ha2 hz1 hz2 hz

-- box ['33267/204800', '1331529/8192000', '7993/8000', '3997/4000']  interval_lower 245260971/1099511627776
noncomputable def e2490 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278112474071,0,true,165496569856,165496569920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920910781481,0,false,-194897479808,-194897479744⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278226424923,0,true,165594593088,165594593152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920796830629,0,false,-195033538624,-195033538560⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277956198330,0,true,165362123584,165362123648⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921067057222,0,false,-194710911872,-194710911808⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278092388826,0,true,165479291136,165479291200⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920930866726,0,false,-194873499520,-194873499456⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579907042,0,true,68277120,68277184⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443348510,0,false,-68281408,-68281344⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591340488,0,true,79709760,79709824⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431915064,0,false,-79715648,-79715584⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621996,0,false,-5824,-5760⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623536,0,false,-4288,-4224⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278034332176,0,true,165429345344,165429345408⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920988923376,0,false,-194804187072,-194804187008⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278159415824,0,true,165536951360,165536951424⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920863839728,0,false,-194953526848,-194953526784⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070485075106,0,false,-29416575488,-29416575424⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070525707863,0,false,-29374841728,-29374841664⟩
    { al := (33267/204800), au := (1331529/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨178600846295,178714797147⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165496569856,165496569920⟩ : DyadicInterval 40),(⟨-194897479808,-194897479744⟩ : DyadicInterval 40),(⟨747553260280,747553279609⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165594593088,165594593152⟩ : DyadicInterval 40),(⟨-195033538624,-195033538560⟩ : DyadicInterval 40),(⟨747534579000,747534598330⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165362123584,165362123648⟩ : DyadicInterval 40),(⟨-194710911872,-194710911808⟩ : DyadicInterval 40),(⟨747578860606,747578879936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165479291136,165479291200⟩ : DyadicInterval 40),(⟨-194873499520,-194873499456⟩ : DyadicInterval 40),(⟨747556551839,747556571169⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨68279266,79712712⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68277120,68277184⟩ : DyadicInterval 40),(⟨-68281408,-68281344⟩ : DyadicInterval 40),(⟨762123381455,762123400785⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79709760,79709824⟩ : DyadicInterval 40),(⟨-79715648,-79715584⟩ : DyadicInterval 40),(⟨762123380716,762123400046⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5824,-4224⟩ : DyadicInterval 40),(⟨762123385728,762123405792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178522704400,178647788048⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165429345344,165429345408⟩ : DyadicInterval 40),(⟨-194804187072,-194804187008⟩ : DyadicInterval 40),(⟨747566063933,747566083263⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165536951360,165536951424⟩ : DyadicInterval 40),(⟨-194953526848,-194953526784⟩ : DyadicInterval 40),(⟨747545566029,747545585359⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29416575488,-29374841664⟩ : DyadicInterval 40),(⟨776810804448,776831690624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165496569856,165594593152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195033538624,-194897479744⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2490_ok : ecellOkT e2490 = true := by decide +kernel
theorem e2490_pos {a z : ℝ} (ha1 : ((33267/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1331529/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2490 e2490_ok ha1 ha2 hz1 hz2 hz

-- box ['1331529/8192000', '666189/4096000', '7993/8000', '3997/4000']  interval_lower 123261357/549755813888
noncomputable def e2491 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278226424922,0,true,165594593088,165594593152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920796830630,0,false,-195033538624,-195033538560⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278340375774,0,true,165692607552,165692607616⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920682879778,0,false,-195169614272,-195169614208⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278070049474,0,true,165460073024,165460073088⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920953206078,0,false,-194846828608,-194846828544⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278206254214,0,true,165577242432,165577242496⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920817001338,0,false,-195009453312,-195009453248⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579952311,0,true,68322368,68322432⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443303241,0,false,-68326720,-68326656⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591393307,0,true,79762624,79762688⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431862245,0,false,-79768448,-79768384⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621989,0,false,-5824,-5760⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623531,0,false,-4288,-4224⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278148233173,0,true,165527331648,165527331712⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920875022379,0,false,-194940174848,-194940174784⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278273323947,0,true,165634934208,165634934272⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920749931605,0,false,-195089541568,-195089541504⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070448047900,0,false,-29454607360,-29454607296⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070488708890,0,false,-29412843136,-29412843072⟩
    { al := (1331529/8192000), au := (666189/4096000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨178714797146,178828747998⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165594593088,165594593152⟩ : DyadicInterval 40),(⟨-195033538624,-195033538560⟩ : DyadicInterval 40),(⟨747534579001,747534598330⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165692607552,165692607616⟩ : DyadicInterval 40),(⟨-195169614272,-195169614208⟩ : DyadicInterval 40),(⟨747515885606,747515904935⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165460073024,165460073088⟩ : DyadicInterval 40),(⟨-194846828608,-194846828544⟩ : DyadicInterval 40),(⟨747560212318,747560231648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165577242432,165577242496⟩ : DyadicInterval 40),(⟨-195009453312,-195009453248⟩ : DyadicInterval 40),(⟨747537886686,747537906015⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨68324535,79765531⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68322368,68322432⟩ : DyadicInterval 40),(⟨-68326720,-68326656⟩ : DyadicInterval 40),(⟨762123381482,762123400811⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79762624,79762688⟩ : DyadicInterval 40),(⟨-79768448,-79768384⟩ : DyadicInterval 40),(⟨762123380677,762123400006⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5824,-4224⟩ : DyadicInterval 40),(⟨762123385728,762123405792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178636605397,178761696171⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165527331648,165527331712⟩ : DyadicInterval 40),(⟨-194940174848,-194940174784⟩ : DyadicInterval 40),(⟨747547399177,747547418506⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165634934208,165634934272⟩ : DyadicInterval 40),(⟨-195089541568,-195089541504⟩ : DyadicInterval 40),(⟨747526886777,747526906107⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29454607360,-29412843072⟩ : DyadicInterval 40),(⟨776829805152,776850706560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165594593088,165692607616⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195169614272,-195033538560⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2491_ok : ecellOkT e2491 = true := by decide +kernel
theorem e2491_pos {a z : ℝ} (ha1 : ((1331529/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((666189/4096000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2491 e2491_ok ha1 ha2 hz1 hz2 hz

-- box ['666189/4096000', '1333227/8192000', '999/1000', '7993/8000']  interval_lower 61992127/274877906944
noncomputable def e2492 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278340375773,0,true,165692607552,165692607616⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920682879779,0,false,-195169614272,-195169614208⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278454326625,0,true,165790613312,165790613376⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920568928927,0,false,-195305706816,-195305706752⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278161547024,0,true,165538784640,165538784704⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920861708528,0,false,-194956071488,-194956071424⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278297751764,0,true,165655945664,165655945728⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920725503788,0,false,-195118712384,-195118712320⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591392400,0,true,79761728,79761792⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431863152,0,false,-79767552,-79767488⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099602848491,0,true,91216896,91216960⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099420407061,0,false,-91224512,-91224448⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620207,0,false,-7616,-7552⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621990,0,false,-5824,-5760⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278250957571,0,true,165615695488,165615695552⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920772297981,0,false,-195062833152,-195062833088⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278376048321,0,true,165723289408,165723289472⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920647207231,0,false,-195212216512,-195212216448⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070414635867,0,false,-29488927040,-29488926976⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070455320223,0,false,-29447137600,-29447137536⟩
    { al := (666189/4096000), au := (1333227/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨178828747997,178942698849⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165692607552,165692607616⟩ : DyadicInterval 40),(⟨-195169614272,-195169614208⟩ : DyadicInterval 40),(⟨747515885606,747515904936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165790613312,165790613376⟩ : DyadicInterval 40),(⟨-195305706816,-195305706752⟩ : DyadicInterval 40),(⟨747497180084,747497199413⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165538784640,165538784704⟩ : DyadicInterval 40),(⟨-194956071488,-194956071424⟩ : DyadicInterval 40),(⟨747545216673,747545236002⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165655945664,165655945728⟩ : DyadicInterval 40),(⟨-195118712384,-195118712320⟩ : DyadicInterval 40),(⟨747522879410,747522898739⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨79764624,91220715⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79761728,79761792⟩ : DyadicInterval 40),(⟨-79767552,-79767488⟩ : DyadicInterval 40),(⟨762123380677,762123400006⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨91216896,91216960⟩ : DyadicInterval 40),(⟨-91224512,-91224448⟩ : DyadicInterval 40),(⟨762123379791,762123399121⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7616,-5760⟩ : DyadicInterval 40),(⟨762123386496,762123406688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178739329795,178864420545⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165615695488,165615695552⟩ : DyadicInterval 40),(⟨-195062833152,-195062833088⟩ : DyadicInterval 40),(⟨747530555516,747530574845⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165723289408,165723289472⟩ : DyadicInterval 40),(⟨-195212216512,-195212216448⟩ : DyadicInterval 40),(⟨747510031101,747510050431⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29488927040,-29447137536⟩ : DyadicInterval 40),(⟨776846952384,776867866400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165692607552,165790613376⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195305706816,-195169614208⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2492_ok : ecellOkT e2492 = true := by decide +kernel
theorem e2492_pos {a z : ℝ} (ha1 : ((666189/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1333227/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2492 e2492_ok ha1 ha2 hz1 hz2 hz

-- box ['1333227/8192000', '333519/2048000', '999/1000', '7993/8000']  interval_lower 249237027/1099511627776
noncomputable def e2493 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278454326624,0,true,165790613312,165790613376⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920568928928,0,false,-195305706816,-195305706752⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278568277476,0,true,165888610368,165888610432⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920454978076,0,false,-195441816128,-195441816064⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278275383925,0,true,165636706112,165636706176⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920747871627,0,false,-195092001472,-195092001408⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278411602908,0,true,165753868928,165753868992⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920611652644,0,false,-195254679488,-195254679424⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591445221,0,true,79814528,79814592⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431810331,0,false,-79820352,-79820288⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099602908864,0,true,91277248,91277312⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099420346688,0,false,-91284928,-91284864⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620197,0,false,-7616,-7552⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621982,0,false,-5824,-5760⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278364851449,0,true,165713659136,165713659200⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920658404103,0,false,-195198844416,-195198844352⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278489949325,0,true,165821249536,165821249600⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920533306227,0,false,-195348254784,-195348254720⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070377566093,0,false,-29527005184,-29527005120⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070418278684,0,false,-29485185216,-29485185152⟩
    { al := (1333227/8192000), au := (333519/2048000), zl := (999/1000), zu := (7993/8000),
      A := ⟨178942698848,179056649700⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165790613312,165790613376⟩ : DyadicInterval 40),(⟨-195305706816,-195305706752⟩ : DyadicInterval 40),(⟨747497180084,747497199413⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165888610368,165888610432⟩ : DyadicInterval 40),(⟨-195441816128,-195441816064⟩ : DyadicInterval 40),(⟨747478462380,747478481709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165636706112,165636706176⟩ : DyadicInterval 40),(⟨-195092001472,-195092001408⟩ : DyadicInterval 40),(⟨747526548848,747526568177⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165753868928,165753868992⟩ : DyadicInterval 40),(⟨-195254679488,-195254679424⟩ : DyadicInterval 40),(⟨747504194776,747504214105⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨79817445,91281088⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79814528,79814592⟩ : DyadicInterval 40),(⟨-79820352,-79820288⟩ : DyadicInterval 40),(⟨762123380669,762123399998⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨91277248,91277312⟩ : DyadicInterval 40),(⟨-91284928,-91284864⟩ : DyadicInterval 40),(⟨762123379813,762123399143⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7616,-5760⟩ : DyadicInterval 40),(⟨762123386496,762123406688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178853223673,178978321549⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165713659136,165713659200⟩ : DyadicInterval 40),(⟨-195198844416,-195198844352⟩ : DyadicInterval 40),(⟨747511868834,747511888163⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165821249536,165821249600⟩ : DyadicInterval 40),(⟨-195348254784,-195348254720⟩ : DyadicInterval 40),(⟨747491329982,747491349312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29527005184,-29485185152⟩ : DyadicInterval 40),(⟨776865976192,776886905472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165790613312,165888610432⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195441816128,-195305706752⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2493_ok : ecellOkT e2493 = true := by decide +kernel
theorem e2493_pos {a z : ℝ} (ha1 : ((1333227/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((333519/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2493 e2493_ok ha1 ha2 hz1 hz2 hz

-- box ['666189/4096000', '1333227/8192000', '7993/8000', '3997/4000']  interval_lower 247787991/1099511627776
noncomputable def e2494 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278340375773,0,true,165692607552,165692607616⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920682879779,0,false,-195169614272,-195169614208⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278454326625,0,true,165790613312,165790613376⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920568928927,0,false,-195305706816,-195305706752⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278183900618,0,true,165558013696,165558013760⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920839354934,0,false,-194982762112,-194982762048⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278320119601,0,true,165675184960,165675185024⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920703135951,0,false,-195145423936,-195145423872⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579997585,0,true,68367680,68367744⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443257967,0,false,-68371968,-68371904⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591446130,0,true,79815424,79815488⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431809422,0,false,-79821312,-79821248⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621981,0,false,-5824,-5760⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623525,0,false,-4288,-4224⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278262134166,0,true,165625309248,165625309312⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920761121386,0,false,-195076179392,-195076179328⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278387232067,0,true,165732908352,165732908416⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920636023485,0,false,-195225573120,-195225573056⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070410997094,0,false,-29492664768,-29492664704⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070451686319,0,false,-29450870144,-29450870080⟩
    { al := (666189/4096000), au := (1333227/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨178828747997,178942698849⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165692607552,165692607616⟩ : DyadicInterval 40),(⟨-195169614272,-195169614208⟩ : DyadicInterval 40),(⟨747515885606,747515904936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165790613312,165790613376⟩ : DyadicInterval 40),(⟨-195305706816,-195305706752⟩ : DyadicInterval 40),(⟨747497180084,747497199413⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165558013696,165558013760⟩ : DyadicInterval 40),(⟨-194982762112,-194982762048⟩ : DyadicInterval 40),(⟨747541551932,747541571262⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165675184960,165675185024⟩ : DyadicInterval 40),(⟨-195145423936,-195145423872⟩ : DyadicInterval 40),(⟨747519209454,747519228783⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨68369809,79818354⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68367680,68367744⟩ : DyadicInterval 40),(⟨-68371968,-68371904⟩ : DyadicInterval 40),(⟨762123381444,762123400773⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79815424,79815488⟩ : DyadicInterval 40),(⟨-79821312,-79821248⟩ : DyadicInterval 40),(⟨762123380701,762123400030⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5824,-4224⟩ : DyadicInterval 40),(⟨762123385728,762123405792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178750506390,178875604291⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165625309248,165625309312⟩ : DyadicInterval 40),(⟨-195076179392,-195076179328⟩ : DyadicInterval 40),(⟨747528722263,747528741593⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165732908352,165732908416⟩ : DyadicInterval 40),(⟨-195225573120,-195225573056⟩ : DyadicInterval 40),(⟨747508195390,747508214720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29492664768,-29450870080⟩ : DyadicInterval 40),(⟨776848818656,776869735264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165692607552,165790613376⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195305706816,-195169614208⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2494_ok : ecellOkT e2494 = true := by decide +kernel
theorem e2494_pos {a z : ℝ} (ha1 : ((666189/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1333227/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2494 e2494_ok ha1 ha2 hz1 hz2 hz

-- box ['1333227/8192000', '333519/2048000', '7993/8000', '3997/4000']  interval_lower 249055829/1099511627776
noncomputable def e2495 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278454326624,0,true,165790613312,165790613376⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920568928928,0,false,-195305706816,-195305706752⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278568277476,0,true,165888610368,165888610432⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920454978076,0,false,-195441816128,-195441816064⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278297751762,0,true,165655945664,165655945728⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920725503790,0,false,-195118712384,-195118712320⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278433984989,0,true,165773118720,165773118784⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920589270563,0,false,-195281411392,-195281411328⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580042861,0,true,68412928,68412992⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443212691,0,false,-68417216,-68417152⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591498957,0,true,79868224,79868288⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431756595,0,false,-79874112,-79874048⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621973,0,false,-5824,-5760⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623519,0,false,-4288,-4224⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278376035163,0,true,165723278080,165723278144⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920647220389,0,false,-195212200832,-195212200768⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278501140190,0,true,165830873728,165830873792⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920522115362,0,false,-195361621504,-195361621440⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070373922685,0,false,-29530747776,-29530747712⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070414640149,0,false,-29488922688,-29488922624⟩
    { al := (1333227/8192000), au := (333519/2048000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨178942698848,179056649700⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165790613312,165790613376⟩ : DyadicInterval 40),(⟨-195305706816,-195305706752⟩ : DyadicInterval 40),(⟨747497180084,747497199413⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165888610368,165888610432⟩ : DyadicInterval 40),(⟨-195441816128,-195441816064⟩ : DyadicInterval 40),(⟨747478462380,747478481709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165655945664,165655945728⟩ : DyadicInterval 40),(⟨-195118712384,-195118712320⟩ : DyadicInterval 40),(⟨747522879410,747522898739⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165773118720,165773118784⟩ : DyadicInterval 40),(⟨-195281411392,-195281411328⟩ : DyadicInterval 40),(⟨747500520141,747500539471⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨68415085,79871181⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68412928,68412992⟩ : DyadicInterval 40),(⟨-68417216,-68417152⟩ : DyadicInterval 40),(⟨762123381438,762123400768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79868224,79868288⟩ : DyadicInterval 40),(⟨-79874112,-79874048⟩ : DyadicInterval 40),(⟨762123380693,762123400023⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5824,-4224⟩ : DyadicInterval 40),(⟨762123385728,762123405792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178864407387,178989512414⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165723278080,165723278144⟩ : DyadicInterval 40),(⟨-195212200832,-195212200768⟩ : DyadicInterval 40),(⟨747510033282,747510052611⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165830873728,165830873792⟩ : DyadicInterval 40),(⟨-195361621504,-195361621440⟩ : DyadicInterval 40),(⟨747489491904,747489511233⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29530747776,-29488922624⟩ : DyadicInterval 40),(⟨776867844928,776888776768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165790613312,165888610432⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195441816128,-195305706752⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2495_ok : ecellOkT e2495 = true := by decide +kernel
theorem e2495_pos {a z : ℝ} (ha1 : ((1333227/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((333519/2048000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2495 e2495_ok ha1 ha2 hz1 hz2 hz

-- box ['33267/204800', '1331529/8192000', '3997/4000', '1599/1600']  interval_lower 245080985/1099511627776
noncomputable def e2496 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278112474071,0,true,165496569856,165496569920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920910781481,0,false,-194897479808,-194897479744⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278226424923,0,true,165594593088,165594593152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920796830629,0,false,-195033538624,-195033538560⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277978523436,0,true,165381331200,165381331264⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921044732116,0,false,-194737562496,-194737562432⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278114728175,0,true,165498508992,165498509056⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920908527377,0,false,-194900171072,-194900171008⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568527260,0,true,56897984,56898048⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454728292,0,false,-56900992,-56900928⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579953162,0,true,68323200,68323264⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443302390,0,false,-68327552,-68327488⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623530,0,false,-4288,-4224⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624832,0,false,-3008,-2944⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278045494555,0,true,165438948416,165438948480⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920977760997,0,false,-194817513216,-194817513152⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278170585353,0,true,165546559680,165546559744⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920852670199,0,false,-194966863360,-194966863296⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070481445360,0,false,-29420303616,-29420303552⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070522082981,0,false,-29378564800,-29378564736⟩
    { al := (33267/204800), au := (1331529/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨178600846295,178714797147⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165496569856,165496569920⟩ : DyadicInterval 40),(⟨-194897479808,-194897479744⟩ : DyadicInterval 40),(⟨747553260280,747553279609⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165594593088,165594593152⟩ : DyadicInterval 40),(⟨-195033538624,-195033538560⟩ : DyadicInterval 40),(⟨747534579000,747534598330⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165381331200,165381331264⟩ : DyadicInterval 40),(⟨-194737562496,-194737562432⟩ : DyadicInterval 40),(⟨747575204814,747575224143⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165498508992,165498509056⟩ : DyadicInterval 40),(⟨-194900171072,-194900171008⟩ : DyadicInterval 40),(⟨747552890845,747552910174⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨56899484,68325386⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56897984,56898048⟩ : DyadicInterval 40),(⟨-56900992,-56900928⟩ : DyadicInterval 40),(⟨762123382111,762123401440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68323200,68323264⟩ : DyadicInterval 40),(⟨-68327552,-68327488⟩ : DyadicInterval 40),(⟨762123381482,762123400811⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4288,-2944⟩ : DyadicInterval 40),(⟨762123385088,762123405024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178533866779,178658957577⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165438948416,165438948480⟩ : DyadicInterval 40),(⟨-194817513216,-194817513152⟩ : DyadicInterval 40),(⟨747564235329,747564254658⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165546559680,165546559744⟩ : DyadicInterval 40),(⟨-194966863360,-194966863296⟩ : DyadicInterval 40),(⟨747543734935,747543754265⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29420303616,-29378564736⟩ : DyadicInterval 40),(⟨776812665984,776833554688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165496569856,165594593152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195033538624,-194897479744⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2496_ok : ecellOkT e2496 = true := by decide +kernel
theorem e2496_pos {a z : ℝ} (ha1 : ((33267/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1331529/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2496 e2496_ok ha1 ha2 hz1 hz2 hz

-- box ['1331529/8192000', '666189/4096000', '3997/4000', '1599/1600']  interval_lower 123171155/549755813888
noncomputable def e2497 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278226424922,0,true,165594593088,165594593152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920796830630,0,false,-195033538624,-195033538560⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278340375774,0,true,165692607552,165692607616⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920682879778,0,false,-195169614272,-195169614208⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278092388824,0,true,165479291136,165479291200⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920930866728,0,false,-194873499520,-194873499456⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278228607807,0,true,165596470784,165596470848⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920794647745,0,false,-195036145216,-195036145152⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568564986,0,true,56935680,56935744⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454690566,0,false,-56938688,-56938624⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579998436,0,true,68368512,68368576⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443257116,0,false,-68372800,-68372736⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623524,0,false,-4288,-4224⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624828,0,false,-3008,-2944⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278159402671,0,true,165536940032,165536940096⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920863852881,0,false,-194953511168,-194953511104⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278284500595,0,true,165644547776,165644547840⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920738754957,0,false,-195102888256,-195102888192⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070444413525,0,false,-29458340416,-29458340352⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070485079381,0,false,-29416571072,-29416571008⟩
    { al := (1331529/8192000), au := (666189/4096000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨178714797146,178828747998⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165594593088,165594593152⟩ : DyadicInterval 40),(⟨-195033538624,-195033538560⟩ : DyadicInterval 40),(⟨747534579001,747534598330⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165692607552,165692607616⟩ : DyadicInterval 40),(⟨-195169614272,-195169614208⟩ : DyadicInterval 40),(⟨747515885606,747515904935⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165479291136,165479291200⟩ : DyadicInterval 40),(⟨-194873499520,-194873499456⟩ : DyadicInterval 40),(⟨747556551840,747556571169⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165596470784,165596470848⟩ : DyadicInterval 40),(⟨-195036145216,-195036145152⟩ : DyadicInterval 40),(⟨747534221024,747534240354⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨56937210,68370660⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56935680,56935744⟩ : DyadicInterval 40),(⟨-56938688,-56938624⟩ : DyadicInterval 40),(⟨762123382107,762123401436⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68368512,68368576⟩ : DyadicInterval 40),(⟨-68372800,-68372736⟩ : DyadicInterval 40),(⟨762123381444,762123400773⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4288,-2944⟩ : DyadicInterval 40),(⟨762123385088,762123405024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178647774895,178772872819⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165536940032,165536940096⟩ : DyadicInterval 40),(⟨-194953511168,-194953511104⟩ : DyadicInterval 40),(⟨747545568204,747545587533⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165644547776,165644547840⟩ : DyadicInterval 40),(⟨-195102888256,-195102888192⟩ : DyadicInterval 40),(⟨747525053348,747525072678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29458340416,-29416571008⟩ : DyadicInterval 40),(⟨776831669120,776852573088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165594593088,165692607616⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195169614272,-195033538560⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2497_ok : ecellOkT e2497 = true := by decide +kernel
theorem e2497_pos {a z : ℝ} (ha1 : ((1331529/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((666189/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2497 e2497_ok ha1 ha2 hz1 hz2 hz

-- box ['33267/204800', '1331529/8192000', '1599/1600', '1999/2000']  interval_lower 244900723/1099511627776
noncomputable def e2498 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278112474071,0,true,165496569856,165496569920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920910781481,0,false,-194897479808,-194897479744⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278226424923,0,true,165594593088,165594593152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920796830629,0,false,-195033538624,-195033538560⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278000848541,0,true,165400538496,165400538560⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921022407011,0,false,-194764213760,-194764213696⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278137067525,0,true,165517726464,165517726528⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920886188027,0,false,-194926843264,-194926843200⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557147424,0,true,45518656,45518720⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466108128,0,false,-45520640,-45520576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568565781,0,true,56936512,56936576⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454689771,0,false,-56939520,-56939456⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624827,0,false,-3008,-2944⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625892,0,false,-1920,-1856⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278056656962,0,true,165448551488,165448551552⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920966598590,0,false,-194830839552,-194830839488⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278181754908,0,true,165556167936,165556168000⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920841500644,0,false,-194980200064,-194980200000⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070477815378,0,false,-29424032064,-29424032000⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070518457862,0,false,-29382288064,-29382288000⟩
    { al := (33267/204800), au := (1331529/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨178600846295,178714797147⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165496569856,165496569920⟩ : DyadicInterval 40),(⟨-194897479808,-194897479744⟩ : DyadicInterval 40),(⟨747553260280,747553279609⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165594593088,165594593152⟩ : DyadicInterval 40),(⟨-195033538624,-195033538560⟩ : DyadicInterval 40),(⟨747534579000,747534598330⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165400538496,165400538560⟩ : DyadicInterval 40),(⟨-194764213760,-194764213696⟩ : DyadicInterval 40),(⟨747571548545,747571567874⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165517726464,165517726528⟩ : DyadicInterval 40),(⟨-194926843264,-194926843200⟩ : DyadicInterval 40),(⟨747549229409,747549248738⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨45519648,56938005⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45518656,45518720⟩ : DyadicInterval 40),(⟨-45520640,-45520576⟩ : DyadicInterval 40),(⟨762123382659,762123401988⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56936512,56936576⟩ : DyadicInterval 40),(⟨-56939520,-56939456⟩ : DyadicInterval 40),(⟨762123382107,762123401436⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3008,-1856⟩ : DyadicInterval 40),(⟨762123384544,762123404384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178545029186,178670127132⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165448551488,165448551552⟩ : DyadicInterval 40),(⟨-194830839552,-194830839488⟩ : DyadicInterval 40),(⟨747562406567,747562425897⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165556167936,165556168000⟩ : DyadicInterval 40),(⟨-194980200064,-194980200000⟩ : DyadicInterval 40),(⟨747541903722,747541923051⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29424032064,-29382288000⟩ : DyadicInterval 40),(⟨776814527616,776835418912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165496569856,165594593152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195033538624,-194897479744⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2498_ok : ecellOkT e2498 = true := by decide +kernel
theorem e2498_pos {a z : ℝ} (ha1 : ((33267/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1331529/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2498 e2498_ok ha1 ha2 hz1 hz2 hz

-- box ['1331529/8192000', '666189/4096000', '1599/1600', '1999/2000']  interval_lower 246161917/1099511627776
noncomputable def e2499 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278226424922,0,true,165594593088,165594593152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920796830630,0,false,-195033538624,-195033538560⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278340375774,0,true,165692607552,165692607616⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920682879778,0,false,-195169614272,-195169614208⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278114728173,0,true,165498508992,165498509056⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920908527379,0,false,-194900171072,-194900171008⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278250961401,0,true,165615698816,165615698880⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920772294151,0,false,-195062837696,-195062837632⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557177604,0,true,45548864,45548928⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466077948,0,false,-45550784,-45550720⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568603509,0,true,56974208,56974272⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454652043,0,false,-56977216,-56977152⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624823,0,false,-3008,-2944⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625889,0,false,-1920,-1856⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278170572200,0,true,165546548352,165546548416⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920852683352,0,false,-194966847616,-194966847552⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278295677272,0,true,165654161344,165654161408⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920727578280,0,false,-195116235072,-195116235008⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070440778912,0,false,-29462073728,-29462073664⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070481449635,0,false,-29420299264,-29420299200⟩
    { al := (1331529/8192000), au := (666189/4096000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨178714797146,178828747998⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165594593088,165594593152⟩ : DyadicInterval 40),(⟨-195033538624,-195033538560⟩ : DyadicInterval 40),(⟨747534579001,747534598330⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165692607552,165692607616⟩ : DyadicInterval 40),(⟨-195169614272,-195169614208⟩ : DyadicInterval 40),(⟨747515885606,747515904935⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165498508992,165498509056⟩ : DyadicInterval 40),(⟨-194900171072,-194900171008⟩ : DyadicInterval 40),(⟨747552890845,747552910175⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165615698816,165615698880⟩ : DyadicInterval 40),(⟨-195062837696,-195062837632⟩ : DyadicInterval 40),(⟨747530554856,747530574185⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨45549828,56975733⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45548864,45548928⟩ : DyadicInterval 40),(⟨-45550784,-45550720⟩ : DyadicInterval 40),(⟨762123382624,762123401954⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56974208,56974272⟩ : DyadicInterval 40),(⟨-56977216,-56977152⟩ : DyadicInterval 40),(⟨762123382103,762123401432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3008,-1856⟩ : DyadicInterval 40),(⟨762123384544,762123404384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178658944424,178784049496⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165546548352,165546548416⟩ : DyadicInterval 40),(⟨-194966847616,-194966847552⟩ : DyadicInterval 40),(⟨747543737083,747543756413⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165654161344,165654161408⟩ : DyadicInterval 40),(⟨-195116235072,-195116235008⟩ : DyadicInterval 40),(⟨747523219735,747523239064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29462073728,-29420299200⟩ : DyadicInterval 40),(⟨776833533216,776854439744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165594593088,165692607616⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195169614272,-195033538560⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2499_ok : ecellOkT e2499 = true := by decide +kernel
theorem e2499_pos {a z : ℝ} (ha1 : ((1331529/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((666189/4096000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2499 e2499_ok ha1 ha2 hz1 hz2 hz

-- box ['666189/4096000', '1333227/8192000', '3997/4000', '1599/1600']  interval_lower 247607081/1099511627776
noncomputable def e2500 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278340375773,0,true,165692607552,165692607616⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920682879779,0,false,-195169614272,-195169614208⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278454326625,0,true,165790613312,165790613376⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920568928927,0,false,-195305706816,-195305706752⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278206254211,0,true,165577242432,165577242496⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920817001341,0,false,-195009453312,-195009453248⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278342487439,0,true,165694423872,165694423936⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920680768113,0,false,-195172136128,-195172136064⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568602713,0,true,56973440,56973504⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454652839,0,false,-56976448,-56976384⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580043714,0,true,68413760,68413824⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443211838,0,false,-68418112,-68418048⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623518,0,false,-4288,-4224⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624824,0,false,-3008,-2944⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278273310792,0,true,165634922880,165634922944⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920749944760,0,false,-195089525888,-195089525824⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278398415838,0,true,165742527232,165742527296⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920624839714,0,false,-195238929920,-195238929856⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070407358085,0,false,-29496402688,-29496402624⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070448052179,0,false,-29454602944,-29454602880⟩
    { al := (666189/4096000), au := (1333227/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨178828747997,178942698849⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165692607552,165692607616⟩ : DyadicInterval 40),(⟨-195169614272,-195169614208⟩ : DyadicInterval 40),(⟨747515885606,747515904936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165790613312,165790613376⟩ : DyadicInterval 40),(⟨-195305706816,-195305706752⟩ : DyadicInterval 40),(⟨747497180084,747497199413⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165577242432,165577242496⟩ : DyadicInterval 40),(⟨-195009453312,-195009453248⟩ : DyadicInterval 40),(⟨747537886686,747537906016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165694423872,165694423936⟩ : DyadicInterval 40),(⟨-195172136128,-195172136064⟩ : DyadicInterval 40),(⟨747515539054,747515558384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨56974937,68415938⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56973440,56973504⟩ : DyadicInterval 40),(⟨-56976448,-56976384⟩ : DyadicInterval 40),(⟨762123382103,762123401432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68413760,68413824⟩ : DyadicInterval 40),(⟨-68418112,-68418048⟩ : DyadicInterval 40),(⟨762123381470,762123400800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4288,-2944⟩ : DyadicInterval 40),(⟨762123385088,762123405024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178761683016,178886788062⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165634922880,165634922944⟩ : DyadicInterval 40),(⟨-195089525888,-195089525824⟩ : DyadicInterval 40),(⟨747526888954,747526908284⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165742527232,165742527296⟩ : DyadicInterval 40),(⟨-195238929920,-195238929856⟩ : DyadicInterval 40),(⟨747506359559,747506378888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29496402688,-29454602880⟩ : DyadicInterval 40),(⟨776850685056,776871604224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165692607552,165790613376⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195305706816,-195169614208⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2500_ok : ecellOkT e2500 = true := by decide +kernel
theorem e2500_pos {a z : ℝ} (ha1 : ((666189/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1333227/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2500 e2500_ok ha1 ha2 hz1 hz2 hz

-- box ['1333227/8192000', '333519/2048000', '3997/4000', '1599/1600']  interval_lower 248874489/1099511627776
noncomputable def e2501 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278454326624,0,true,165790613312,165790613376⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920568928928,0,false,-195305706816,-195305706752⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278568277476,0,true,165888610368,165888610432⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920454978076,0,false,-195441816128,-195441816064⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278320119599,0,true,165675184960,165675185024⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920703135953,0,false,-195145423936,-195145423872⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278456367070,0,true,165792368192,165792368256⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920566888482,0,false,-195308143872,-195308143808⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568640444,0,true,57011136,57011200⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454615108,0,false,-57014208,-57014144⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580088993,0,true,68459072,68459136⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443166559,0,false,-68463360,-68463296⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623513,0,false,-4288,-4224⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624820,0,false,-3008,-2944⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278387218908,0,true,165732897024,165732897088⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920636036644,0,false,-195225557440,-195225557376⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278512331084,0,true,165840497856,165840497920⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920510924468,0,false,-195374988480,-195374988416⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070370279039,0,false,-29534490560,-29534490496⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070411001376,0,false,-29492660352,-29492660288⟩
    { al := (1333227/8192000), au := (333519/2048000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨178942698848,179056649700⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165790613312,165790613376⟩ : DyadicInterval 40),(⟨-195305706816,-195305706752⟩ : DyadicInterval 40),(⟨747497180084,747497199413⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165888610368,165888610432⟩ : DyadicInterval 40),(⟨-195441816128,-195441816064⟩ : DyadicInterval 40),(⟨747478462380,747478481709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165675184960,165675185024⟩ : DyadicInterval 40),(⟨-195145423936,-195145423872⟩ : DyadicInterval 40),(⟨747519209454,747519228784⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165792368192,165792368256⟩ : DyadicInterval 40),(⟨-195308143872,-195308143808⟩ : DyadicInterval 40),(⟨747496844998,747496864327⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57012668,68461217⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57011136,57011200⟩ : DyadicInterval 40),(⟨-57014208,-57014144⟩ : DyadicInterval 40),(⟨762123382131,762123401460⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68459072,68459136⟩ : DyadicInterval 40),(⟨-68463360,-68463296⟩ : DyadicInterval 40),(⟨762123381433,762123400762⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4288,-2944⟩ : DyadicInterval 40),(⟨762123385088,762123405024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178875591132,179000703308⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165732897024,165732897088⟩ : DyadicInterval 40),(⟨-195225557440,-195225557376⟩ : DyadicInterval 40),(⟨747508197571,747508216901⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165840497856,165840497920⟩ : DyadicInterval 40),(⟨-195374988480,-195374988416⟩ : DyadicInterval 40),(⟨747487653730,747487673060⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29534490560,-29492660288⟩ : DyadicInterval 40),(⟨776869713760,776890648160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165790613312,165888610432⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195441816128,-195305706752⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2501_ok : ecellOkT e2501 = true := by decide +kernel
theorem e2501_pos {a z : ℝ} (ha1 : ((1333227/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((333519/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2501 e2501_ok ha1 ha2 hz1 hz2 hz

-- box ['666189/4096000', '1333227/8192000', '1599/1600', '1999/2000']  interval_lower 247426117/1099511627776
noncomputable def e2502 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278340375773,0,true,165692607552,165692607616⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920682879779,0,false,-195169614272,-195169614208⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278454326625,0,true,165790613312,165790613376⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920568928927,0,false,-195305706816,-195305706752⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278228607805,0,true,165596470784,165596470848⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920794647747,0,false,-195036145216,-195036145152⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278364855276,0,true,165713662400,165713662464⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920658400276,0,false,-195198848960,-195198848896⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557207786,0,true,45579008,45579072⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466047766,0,false,-45580992,-45580928⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568641240,0,true,57011968,57012032⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454614312,0,false,-57014976,-57014912⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624819,0,false,-3008,-2944⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625887,0,false,-1920,-1856⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278284487438,0,true,165644536512,165644536576⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920738768114,0,false,-195102872512,-195102872448⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278409599634,0,true,165752145984,165752146048⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920613655918,0,false,-195252286976,-195252286912⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070403718840,0,false,-29500140928,-29500140864⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070444417804,0,false,-29458336000,-29458335936⟩
    { al := (666189/4096000), au := (1333227/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨178828747997,178942698849⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165692607552,165692607616⟩ : DyadicInterval 40),(⟨-195169614272,-195169614208⟩ : DyadicInterval 40),(⟨747515885606,747515904936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165790613312,165790613376⟩ : DyadicInterval 40),(⟨-195305706816,-195305706752⟩ : DyadicInterval 40),(⟨747497180084,747497199413⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165596470784,165596470848⟩ : DyadicInterval 40),(⟨-195036145216,-195036145152⟩ : DyadicInterval 40),(⟨747534221025,747534240354⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165713662400,165713662464⟩ : DyadicInterval 40),(⟨-195198848960,-195198848896⟩ : DyadicInterval 40),(⟨747511868211,747511887541⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨45580010,57013464⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45579008,45579072⟩ : DyadicInterval 40),(⟨-45580992,-45580928⟩ : DyadicInterval 40),(⟨762123382654,762123401983⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57011968,57012032⟩ : DyadicInterval 40),(⟨-57014976,-57014912⟩ : DyadicInterval 40),(⟨762123382099,762123401428⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3008,-1856⟩ : DyadicInterval 40),(⟨762123384544,762123404384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178772859662,178897971858⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165644536512,165644536576⟩ : DyadicInterval 40),(⟨-195102872512,-195102872448⟩ : DyadicInterval 40),(⟨747525055462,747525074792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165752145984,165752146048⟩ : DyadicInterval 40),(⟨-195252286976,-195252286912⟩ : DyadicInterval 40),(⟨747504523671,747504543000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29500140928,-29458335936⟩ : DyadicInterval 40),(⟨776852551584,776873473344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165692607552,165790613376⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195305706816,-195169614208⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2502_ok : ecellOkT e2502 = true := by decide +kernel
theorem e2502_pos {a z : ℝ} (ha1 : ((666189/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1333227/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2502 e2502_ok ha1 ha2 hz1 hz2 hz

-- box ['1333227/8192000', '333519/2048000', '1599/1600', '1999/2000']  interval_lower 124346703/549755813888
noncomputable def e2503 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278454326624,0,true,165790613312,165790613376⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920568928928,0,false,-195305706816,-195305706752⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278568277476,0,true,165888610368,165888610432⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920454978076,0,false,-195441816128,-195441816064⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278342487437,0,true,165694423808,165694423872⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920680768115,0,false,-195172136128,-195172136064⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278478749152,0,true,165811617280,165811617344⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920544506400,0,false,-195334877056,-195334876992⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557237970,0,true,45609216,45609280⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466017582,0,false,-45611200,-45611136⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568678974,0,true,57049664,57049728⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454576578,0,false,-57052736,-57052672⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624815,0,false,-3008,-2944⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625884,0,false,-1920,-1856⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278398402675,0,true,165742515904,165742515968⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920624852877,0,false,-195238914240,-195238914176⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278523522002,0,true,165850121984,165850122048⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920499733550,0,false,-195388355648,-195388355584⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070366635158,0,false,-29538233664,-29538233600⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070407362369,0,false,-29496398336,-29496398272⟩
    { al := (1333227/8192000), au := (333519/2048000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨178942698848,179056649700⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165790613312,165790613376⟩ : DyadicInterval 40),(⟨-195305706816,-195305706752⟩ : DyadicInterval 40),(⟨747497180084,747497199413⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165888610368,165888610432⟩ : DyadicInterval 40),(⟨-195441816128,-195441816064⟩ : DyadicInterval 40),(⟨747478462380,747478481709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165694423808,165694423872⟩ : DyadicInterval 40),(⟨-195172136128,-195172136064⟩ : DyadicInterval 40),(⟨747515539091,747515558421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165811617280,165811617344⟩ : DyadicInterval 40),(⟨-195334877056,-195334876992⟩ : DyadicInterval 40),(⟨747493169436,747493188766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨45610194,57051198⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45609216,45609280⟩ : DyadicInterval 40),(⟨-45611200,-45611136⟩ : DyadicInterval 40),(⟨762123382651,762123401981⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57049664,57049728⟩ : DyadicInterval 40),(⟨-57052736,-57052672⟩ : DyadicInterval 40),(⟨762123382127,762123401456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3008,-1856⟩ : DyadicInterval 40),(⟨762123384544,762123404384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178886774899,179011894226⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165742515904,165742515968⟩ : DyadicInterval 40),(⟨-195238914240,-195238914176⟩ : DyadicInterval 40),(⟨747506361740,747506381070⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165850121984,165850122048⟩ : DyadicInterval 40),(⟨-195388355648,-195388355584⟩ : DyadicInterval 40),(⟨747485815400,747485834729⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29538233664,-29496398272⟩ : DyadicInterval 40),(⟨776871582752,776892519712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165790613312,165888610432⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195441816128,-195305706752⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2503_ok : ecellOkT e2503 = true := by decide +kernel
theorem e2503_pos {a z : ℝ} (ha1 : ((1333227/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((333519/2048000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2503 e2503_ok ha1 ha2 hz1 hz2 hz

-- box ['333519/2048000', '53397/327680', '999/1000', '7993/8000']  interval_lower 62627129/274877906944
noncomputable def e2504 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278568277475,0,true,165888610368,165888610432⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920454978077,0,false,-195441816128,-195441816064⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278682228327,0,true,165986598592,165986598656⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920341027225,0,false,-195577942336,-195577942272⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278389220825,0,true,165734618816,165734618880⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920634034727,0,false,-195227948288,-195227948224⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278525454052,0,true,165851783488,165851783552⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920497801500,0,false,-195390663424,-195390663360⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591498047,0,true,79867328,79867392⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431757505,0,false,-79873216,-79873152⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099602969242,0,true,91337664,91337728⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099420286310,0,false,-91345280,-91345216⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620187,0,false,-7616,-7552⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621975,0,false,-5824,-5760⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278478745327,0,true,165811614016,165811614080⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920544510225,0,false,-195334872448,-195334872384⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278603850322,0,true,165919200960,165919201024⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920419405230,0,false,-195484309824,-195484309760⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070340472722,0,false,-29565108800,-29565108736⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070381213550,0,false,-29523258432,-29523258368⟩
    { al := (333519/2048000), au := (53397/327680), zl := (999/1000), zu := (7993/8000),
      A := ⟨179056649699,179170600551⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165888610368,165888610432⟩ : DyadicInterval 40),(⟨-195441816128,-195441816064⟩ : DyadicInterval 40),(⟨747478462380,747478481709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165986598592,165986598656⟩ : DyadicInterval 40),(⟨-195577942336,-195577942272⟩ : DyadicInterval 40),(⟨747459732621,747459751950⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165734618816,165734618880⟩ : DyadicInterval 40),(⟨-195227948288,-195227948224⟩ : DyadicInterval 40),(⟨747507868955,747507888285⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165851783488,165851783552⟩ : DyadicInterval 40),(⟨-195390663424,-195390663360⟩ : DyadicInterval 40),(⟨747485498030,747485517359⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨79870271,91341466⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79867328,79867392⟩ : DyadicInterval 40),(⟨-79873216,-79873152⟩ : DyadicInterval 40),(⟨762123380693,762123400023⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨91337664,91337728⟩ : DyadicInterval 40),(⟨-91345280,-91345216⟩ : DyadicInterval 40),(⟨762123379771,762123399101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7616,-5760⟩ : DyadicInterval 40),(⟨762123386496,762123406688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178967117551,179092222546⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165811614016,165811614080⟩ : DyadicInterval 40),(⟨-195334872448,-195334872384⟩ : DyadicInterval 40),(⟨747493170033,747493189362⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165919200960,165919201024⟩ : DyadicInterval 40),(⟨-195484309824,-195484309760⟩ : DyadicInterval 40),(⟨747472616704,747472636033⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29565108800,-29523258368⟩ : DyadicInterval 40),(⟨776885012800,776905957280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165888610368,165986598656⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195577942336,-195441816064⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2504_ok : ecellOkT e2504 = true := by decide +kernel
theorem e2504_pos {a z : ℝ} (ha1 : ((333519/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((53397/327680 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2504 e2504_ok ha1 ha2 hz1 hz2 hz

-- box ['53397/327680', '667887/4096000', '999/1000', '7993/8000']  interval_lower 251782879/1099511627776
noncomputable def e2505 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278682228326,0,true,165986598592,165986598656⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920341027226,0,false,-195577942336,-195577942272⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278796179178,0,true,166084578176,166084578240⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920227076374,0,false,-195714085440,-195714085376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278503057725,0,true,165832522816,165832522880⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920520197827,0,false,-195363911936,-195363911872⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278639305196,0,true,165949689280,165949689344⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920383950356,0,false,-195526664192,-195526664128⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591550877,0,true,79920192,79920256⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431704675,0,false,-79926016,-79925952⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099603029624,0,true,91398016,91398080⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099420225928,0,false,-91405696,-91405632⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620177,0,false,-7616,-7552⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621967,0,false,-5824,-5760⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278592639196,0,true,165909560128,165909560192⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920430616356,0,false,-195470917376,-195470917312⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278717751319,0,true,166017143680,166017143744⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920305504233,0,false,-195620381760,-195620381696⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070303355754,0,false,-29603238016,-29603237952⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070344124822,0,false,-29561357184,-29561357120⟩
    { al := (53397/327680), au := (667887/4096000), zl := (999/1000), zu := (7993/8000),
      A := ⟨179170600550,179284551402⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165986598592,165986598656⟩ : DyadicInterval 40),(⟨-195577942336,-195577942272⟩ : DyadicInterval 40),(⟨747459732621,747459751950⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166084578176,166084578240⟩ : DyadicInterval 40),(⟨-195714085440,-195714085376⟩ : DyadicInterval 40),(⟨747440990693,747441010022⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165832522816,165832522880⟩ : DyadicInterval 40),(⟨-195363911936,-195363911872⟩ : DyadicInterval 40),(⟨747489176957,747489196287⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165949689280,165949689344⟩ : DyadicInterval 40),(⟨-195526664192,-195526664128⟩ : DyadicInterval 40),(⟨747466789207,747466808537⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨79923101,91401848⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79920192,79920256⟩ : DyadicInterval 40),(⟨-79926016,-79925952⟩ : DyadicInterval 40),(⟨762123380654,762123399983⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨91398016,91398080⟩ : DyadicInterval 40),(⟨-91405696,-91405632⟩ : DyadicInterval 40),(⟨762123379793,762123399123⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7616,-5760⟩ : DyadicInterval 40),(⟨762123386496,762123406688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179081011420,179206123543⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165909560128,165909560192⟩ : DyadicInterval 40),(⟨-195470917376,-195470917312⟩ : DyadicInterval 40),(⟨747474459166,747474478495⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166017143680,166017143744⟩ : DyadicInterval 40),(⟨-195620381760,-195620381696⟩ : DyadicInterval 40),(⟨747453891316,747453910645⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29603238016,-29561357120⟩ : DyadicInterval 40),(⟨776904062176,776925021888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165986598592,166084578240⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195714085440,-195577942272⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2505_ok : ecellOkT e2505 = true := by decide +kernel
theorem e2505_pos {a z : ℝ} (ha1 : ((53397/327680 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((667887/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2505 e2505_ok ha1 ha2 hz1 hz2 hz

-- box ['333519/2048000', '53397/327680', '7993/8000', '3997/4000']  interval_lower 125163533/549755813888
noncomputable def e2506 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278568277475,0,true,165888610368,165888610432⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920454978077,0,false,-195441816128,-195441816064⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278682228327,0,true,165986598592,165986598656⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920341027225,0,false,-195577942336,-195577942272⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278411602906,0,true,165753868928,165753868992⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920611652646,0,false,-195254679488,-195254679424⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278547850377,0,true,165871043776,165871043840⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920475405175,0,false,-195417415616,-195417415552⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580088140,0,true,68458176,68458240⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443167412,0,false,-68462528,-68462464⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591551787,0,true,79921088,79921152⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431703765,0,false,-79926976,-79926912⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621966,0,false,-5824,-5760⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623514,0,false,-4288,-4224⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278489936165,0,true,165821238272,165821238336⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920533319387,0,false,-195348239040,-195348238976⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278615048306,0,true,165928830400,165928830464⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920408207246,0,false,-195497686784,-195497686720⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070336824676,0,false,-29568856320,-29568856256⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070377570378,0,false,-29527000768,-29527000704⟩
    { al := (333519/2048000), au := (53397/327680), zl := (7993/8000), zu := (3997/4000),
      A := ⟨179056649699,179170600551⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165888610368,165888610432⟩ : DyadicInterval 40),(⟨-195441816128,-195441816064⟩ : DyadicInterval 40),(⟨747478462380,747478481709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165986598592,165986598656⟩ : DyadicInterval 40),(⟨-195577942336,-195577942272⟩ : DyadicInterval 40),(⟨747459732621,747459751950⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165753868928,165753868992⟩ : DyadicInterval 40),(⟨-195254679488,-195254679424⟩ : DyadicInterval 40),(⟨747504194776,747504214106⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165871043776,165871043840⟩ : DyadicInterval 40),(⟨-195417415616,-195417415552⟩ : DyadicInterval 40),(⟨747481818684,747481838013⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨68460364,79924011⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68458176,68458240⟩ : DyadicInterval 40),(⟨-68462528,-68462464⟩ : DyadicInterval 40),(⟨762123381465,762123400794⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79921088,79921152⟩ : DyadicInterval 40),(⟨-79926976,-79926912⟩ : DyadicInterval 40),(⟨762123380686,762123400015⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5824,-4224⟩ : DyadicInterval 40),(⟨762123385728,762123405792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178978308389,179103420530⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165821238272,165821238336⟩ : DyadicInterval 40),(⟨-195348239040,-195348238976⟩ : DyadicInterval 40),(⟨747491332102,747491351432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165928830400,165928830464⟩ : DyadicInterval 40),(⟨-195497686784,-195497686720⟩ : DyadicInterval 40),(⟨747470776307,747470795637⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29568856320,-29527000704⟩ : DyadicInterval 40),(⟨776886883968,776907831040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165888610368,165986598656⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195577942336,-195441816064⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2506_ok : ecellOkT e2506 = true := by decide +kernel
theorem e2506_pos {a z : ℝ} (ha1 : ((333519/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((53397/327680 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2506 e2506_ok ha1 ha2 hz1 hz2 hz

-- box ['53397/327680', '667887/4096000', '7993/8000', '3997/4000']  interval_lower 251601037/1099511627776
noncomputable def e2507 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278682228326,0,true,165986598592,165986598656⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920341027226,0,false,-195577942336,-195577942272⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278796179178,0,true,166084578176,166084578240⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920227076374,0,false,-195714085440,-195714085376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278525454050,0,true,165851783488,165851783552⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920497801502,0,false,-195390663424,-195390663360⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278661715765,0,true,165968960128,165968960192⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920361539787,0,false,-195553436736,-195553436672⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580133423,0,true,68503488,68503552⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443122129,0,false,-68507840,-68507776⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591604622,0,true,79973888,79973952⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431650930,0,false,-79979776,-79979712⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621958,0,false,-5824,-5760⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623508,0,false,-4288,-4224⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278603837159,0,true,165919189632,165919189696⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920419418393,0,false,-195484294080,-195484294016⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278728956426,0,true,166026778368,166026778432⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920294299126,0,false,-195633768832,-195633768768⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070299703065,0,false,-29606990400,-29606990336⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070340477012,0,false,-29565104448,-29565104384⟩
    { al := (53397/327680), au := (667887/4096000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨179170600550,179284551402⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165986598592,165986598656⟩ : DyadicInterval 40),(⟨-195577942336,-195577942272⟩ : DyadicInterval 40),(⟨747459732621,747459751950⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166084578176,166084578240⟩ : DyadicInterval 40),(⟨-195714085440,-195714085376⟩ : DyadicInterval 40),(⟨747440990693,747441010022⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165851783488,165851783552⟩ : DyadicInterval 40),(⟨-195390663424,-195390663360⟩ : DyadicInterval 40),(⟨747485498030,747485517359⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165968960128,165968960192⟩ : DyadicInterval 40),(⟨-195553436736,-195553436672⟩ : DyadicInterval 40),(⟨747463105133,747463124462⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨68505647,79976846⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68503488,68503552⟩ : DyadicInterval 40),(⟨-68507840,-68507776⟩ : DyadicInterval 40),(⟨762123381459,762123400788⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79973888,79973952⟩ : DyadicInterval 40),(⟨-79979776,-79979712⟩ : DyadicInterval 40),(⟨762123380678,762123400007⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5824,-4224⟩ : DyadicInterval 40),(⟨762123385728,762123405792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179092209383,179217328650⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165919189632,165919189696⟩ : DyadicInterval 40),(⟨-195484294080,-195484294016⟩ : DyadicInterval 40),(⟨747472618863,747472638193⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166026778368,166026778432⟩ : DyadicInterval 40),(⟨-195633768832,-195633768768⟩ : DyadicInterval 40),(⟨747452048545,747452067874⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29606990400,-29565104384⟩ : DyadicInterval 40),(⟨776905935808,776926898080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165986598592,166084578240⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195714085440,-195577942272⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2507_ok : ecellOkT e2507 = true := by decide +kernel
theorem e2507_pos {a z : ℝ} (ha1 : ((53397/327680 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((667887/4096000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2507 e2507_ok ha1 ha2 hz1 hz2 hz

-- box ['667887/4096000', '1336623/8192000', '999/1000', '7993/8000']  interval_lower 126530187/549755813888
noncomputable def e2508 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278796179177,0,true,166084578176,166084578240⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920227076375,0,false,-195714085440,-195714085376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278910130029,0,true,166182548992,166182549056⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920113125523,0,false,-195850245312,-195850245248⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278616894625,0,true,165930418112,165930418176⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920406360927,0,false,-195499892352,-195499892288⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278753156340,0,true,166047586432,166047586496⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920270099212,0,false,-195662681792,-195662681728⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591603711,0,true,79972992,79973056⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431651841,0,false,-79978880,-79978816⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099603090011,0,true,91458368,91458432⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099420165541,0,false,-91466048,-91465984⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620167,0,false,-7616,-7552⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621959,0,false,-5824,-5760⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278706533073,0,true,166007497536,166007497600⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920316722479,0,false,-195606979072,-195606979008⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278831652323,0,true,166115077632,166115077696⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920191603229,0,false,-195756470464,-195756470400⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070266215184,0,false,-29641392832,-29641392768⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070307012497,0,false,-29599481536,-29599481472⟩
    { al := (667887/4096000), au := (1336623/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨179284551401,179398502253⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166084578176,166084578240⟩ : DyadicInterval 40),(⟨-195714085440,-195714085376⟩ : DyadicInterval 40),(⟨747440990693,747441010023⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166182548992,166182549056⟩ : DyadicInterval 40),(⟨-195850245312,-195850245248⟩ : DyadicInterval 40),(⟨747422236617,747422255947⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165930418112,165930418176⟩ : DyadicInterval 40),(⟨-195499892352,-195499892288⟩ : DyadicInterval 40),(⟨747470472825,747470492154⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166047586432,166047586496⟩ : DyadicInterval 40),(⟨-195662681792,-195662681728⟩ : DyadicInterval 40),(⟨747448068233,747448087562⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨79975935,91462235⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79972992,79973056⟩ : DyadicInterval 40),(⟨-79978880,-79978816⟩ : DyadicInterval 40),(⟨762123380678,762123400007⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨91458368,91458432⟩ : DyadicInterval 40),(⟨-91466048,-91465984⟩ : DyadicInterval 40),(⟨762123379783,762123399113⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7616,-5760⟩ : DyadicInterval 40),(⟨762123386496,762123406688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179194905297,179320024547⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166007497536,166007497600⟩ : DyadicInterval 40),(⟨-195606979072,-195606979008⟩ : DyadicInterval 40),(⟨747455736138,747455755468⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166115077632,166115077696⟩ : DyadicInterval 40),(⟨-195756470464,-195756470400⟩ : DyadicInterval 40),(⟨747435153801,747435173130⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29641392832,-29599481472⟩ : DyadicInterval 40),(⟨776923124352,776944099296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166084578176,166182549056⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195850245312,-195714085376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2508_ok : ecellOkT e2508 = true := by decide +kernel
theorem e2508_pos {a z : ℝ} (ha1 : ((667887/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1336623/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2508 e2508_ok ha1 ha2 hz1 hz2 hz

-- box ['1336623/8192000', '10449/64000', '999/1000', '7993/8000']  interval_lower 254340773/1099511627776
noncomputable def e2509 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278910130028,0,true,166182548992,166182549056⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920113125524,0,false,-195850245312,-195850245248⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279024080880,0,true,166280511040,166280511104⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919999174672,0,false,-195986422144,-195986422080⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278730731525,0,true,166028304704,166028304768⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920292524027,0,false,-195635889600,-195635889536⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278867007484,0,true,166145474816,166145474880⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920156248068,0,false,-195798716224,-195798716160⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591656549,0,true,80025856,80025920⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431599003,0,false,-80031744,-80031680⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099603150401,0,true,91518784,91518848⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099420105151,0,false,-91526464,-91526400⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620157,0,false,-7680,-7616⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621952,0,false,-5888,-5824⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278820426951,0,true,166105426240,166105426304⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920202828601,0,false,-195743057664,-195743057600⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278945553316,0,true,166213002880,166213002944⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920077702236,0,false,-195892576064,-195892576000⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070229051019,0,false,-29679573184,-29679573120⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070269876576,0,false,-29637631424,-29637631360⟩
    { al := (1336623/8192000), au := (10449/64000), zl := (999/1000), zu := (7993/8000),
      A := ⟨179398502252,179512453104⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166182548992,166182549056⟩ : DyadicInterval 40),(⟨-195850245312,-195850245248⟩ : DyadicInterval 40),(⟨747422236617,747422255947⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166280511040,166280511104⟩ : DyadicInterval 40),(⟨-195986422144,-195986422080⟩ : DyadicInterval 40),(⟨747403470472,747403489801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166028304704,166028304768⟩ : DyadicInterval 40),(⟨-195635889600,-195635889536⟩ : DyadicInterval 40),(⟨747451756584,747451775914⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166145474816,166145474880⟩ : DyadicInterval 40),(⟨-195798716224,-195798716160⟩ : DyadicInterval 40),(⟨747429335179,747429354509⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨80028773,91522625⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80025856,80025920⟩ : DyadicInterval 40),(⟨-80031744,-80031680⟩ : DyadicInterval 40),(⟨762123380670,762123400000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨91518784,91518848⟩ : DyadicInterval 40),(⟨-91526464,-91526400⟩ : DyadicInterval 40),(⟨762123379773,762123399103⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7680,-5824⟩ : DyadicInterval 40),(⟨762123386528,762123406720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179308799175,179433925540⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166105426240,166105426304⟩ : DyadicInterval 40),(⟨-195743057664,-195743057600⟩ : DyadicInterval 40),(⟨747437001004,747437020333⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166213002880,166213002944⟩ : DyadicInterval 40),(⟨-195892576064,-195892576000⟩ : DyadicInterval 40),(⟨747416404175,747416423505⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29679573184,-29637631360⟩ : DyadicInterval 40),(⟨776942199296,776963189472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166182548992,166280511104⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195986422144,-195850245248⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2509_ok : ecellOkT e2509 = true := by decide +kernel
theorem e2509_pos {a z : ℝ} (ha1 : ((1336623/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((10449/64000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2509 e2509_ok ha1 ha2 hz1 hz2 hz

-- box ['667887/4096000', '1336623/8192000', '7993/8000', '3997/4000']  interval_lower 126438935/549755813888
noncomputable def e2510 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278796179177,0,true,166084578176,166084578240⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920227076375,0,false,-195714085440,-195714085376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278910130029,0,true,166182548992,166182549056⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920113125523,0,false,-195850245312,-195850245248⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278639305194,0,true,165949689280,165949689344⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920383950358,0,false,-195526664192,-195526664128⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278775581153,0,true,166066867776,166066867840⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920247674399,0,false,-195689474624,-195689474560⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580178709,0,true,68548736,68548800⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443076843,0,false,-68553088,-68553024⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591657460,0,true,80026752,80026816⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431598092,0,false,-80032640,-80032576⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621950,0,false,-5888,-5824⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623503,0,false,-4288,-4224⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278717738153,0,true,166017132352,166017132416⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920305517399,0,false,-195620366016,-195620365952⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278842864551,0,true,166124717632,166124717696⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920180391001,0,false,-195769867776,-195769867712⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070262557851,0,false,-29645150080,-29645150016⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070303360046,0,false,-29603233664,-29603233600⟩
    { al := (667887/4096000), au := (1336623/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨179284551401,179398502253⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166084578176,166084578240⟩ : DyadicInterval 40),(⟨-195714085440,-195714085376⟩ : DyadicInterval 40),(⟨747440990693,747441010023⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166182548992,166182549056⟩ : DyadicInterval 40),(⟨-195850245312,-195850245248⟩ : DyadicInterval 40),(⟨747422236617,747422255947⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165949689280,165949689344⟩ : DyadicInterval 40),(⟨-195526664192,-195526664128⟩ : DyadicInterval 40),(⟨747466789208,747466808537⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166066867776,166066867840⟩ : DyadicInterval 40),(⟨-195689474624,-195689474560⟩ : DyadicInterval 40),(⟨747444379433,747444398763⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨68550933,80029684⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68548736,68548800⟩ : DyadicInterval 40),(⟨-68553088,-68553024⟩ : DyadicInterval 40),(⟨762123381453,762123400783⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80026752,80026816⟩ : DyadicInterval 40),(⟨-80032640,-80032576⟩ : DyadicInterval 40),(⟨762123380670,762123400000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5888,-4224⟩ : DyadicInterval 40),(⟨762123385728,762123405824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179206110377,179331236775⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166017132352,166017132416⟩ : DyadicInterval 40),(⟨-195620366016,-195620365952⟩ : DyadicInterval 40),(⟨747453893479,747453912809⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166124717632,166124717696⟩ : DyadicInterval 40),(⟨-195769867776,-195769867712⟩ : DyadicInterval 40),(⟨747433308669,747433327998⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29645150080,-29603233600⟩ : DyadicInterval 40),(⟨776925000416,776945977920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166084578176,166182549056⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195850245312,-195714085376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2510_ok : ecellOkT e2510 = true := by decide +kernel
theorem e2510_pos {a z : ℝ} (ha1 : ((667887/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1336623/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2510 e2510_ok ha1 ha2 hz1 hz2 hz

-- box ['1336623/8192000', '10449/64000', '7993/8000', '3997/4000']  interval_lower 127079013/549755813888
noncomputable def e2511 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278910130028,0,true,166182548992,166182549056⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920113125524,0,false,-195850245312,-195850245248⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279024080880,0,true,166280511040,166280511104⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919999174672,0,false,-195986422144,-195986422080⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278753156338,0,true,166047586432,166047586496⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920270099214,0,false,-195662681792,-195662681728⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278889446541,0,true,166164766720,166164766784⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920133809011,0,false,-195825529344,-195825529280⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580224000,0,true,68594048,68594112⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443031552,0,false,-68598400,-68598336⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591710303,0,true,80079552,80079616⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431545249,0,false,-80085504,-80085440⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621943,0,false,-5888,-5824⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623497,0,false,-4288,-4224⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278831639154,0,true,166115066304,166115066368⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920191616398,0,false,-195756454720,-195756454656⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278956772670,0,true,166222648128,166222648192⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920066482882,0,false,-195905983488,-195905983424⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070225389038,0,false,-29683335360,-29683335296⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070266219480,0,false,-29641388416,-29641388352⟩
    { al := (1336623/8192000), au := (10449/64000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨179398502252,179512453104⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166182548992,166182549056⟩ : DyadicInterval 40),(⟨-195850245312,-195850245248⟩ : DyadicInterval 40),(⟨747422236617,747422255947⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166280511040,166280511104⟩ : DyadicInterval 40),(⟨-195986422144,-195986422080⟩ : DyadicInterval 40),(⟨747403470472,747403489801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166047586432,166047586496⟩ : DyadicInterval 40),(⟨-195662681792,-195662681728⟩ : DyadicInterval 40),(⟨747448068233,747448087563⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166164766720,166164766784⟩ : DyadicInterval 40),(⟨-195825529344,-195825529280⟩ : DyadicInterval 40),(⟨747425641612,747425660942⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨68596224,80082527⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68594048,68594112⟩ : DyadicInterval 40),(⟨-68598400,-68598336⟩ : DyadicInterval 40),(⟨762123381448,762123400777⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80079552,80079616⟩ : DyadicInterval 40),(⟨-80085504,-80085440⟩ : DyadicInterval 40),(⟨762123380695,762123400024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5888,-4224⟩ : DyadicInterval 40),(⟨762123385728,762123405824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179320011378,179445144894⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166115066304,166115066368⟩ : DyadicInterval 40),(⟨-195756454720,-195756454656⟩ : DyadicInterval 40),(⟨747435155967,747435175296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166222648128,166222648192⟩ : DyadicInterval 40),(⟨-195905983488,-195905983424⟩ : DyadicInterval 40),(⟨747414556662,747414575992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29683335360,-29641388352⟩ : DyadicInterval 40),(⟨776944077792,776965070560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166182548992,166280511104⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195986422144,-195850245248⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2511_ok : ecellOkT e2511 = true := by decide +kernel
theorem e2511_pos {a z : ℝ} (ha1 : ((1336623/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((10449/64000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2511 e2511_ok ha1 ha2 hz1 hz2 hz

-- box ['333519/2048000', '53397/327680', '3997/4000', '1599/1600']  interval_lower 250145399/1099511627776
noncomputable def e2512 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278568277475,0,true,165888610368,165888610432⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920454978077,0,false,-195441816128,-195441816064⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278682228327,0,true,165986598592,165986598656⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920341027225,0,false,-195577942336,-195577942272⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278433984987,0,true,165773118720,165773118784⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920589270565,0,false,-195281411392,-195281411328⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278570246702,0,true,165890303808,165890303872⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920453008850,0,false,-195444168448,-195444168384⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568678177,0,true,57048896,57048960⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454577375,0,false,-57051904,-57051840⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580134277,0,true,68504320,68504384⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443121275,0,false,-68508672,-68508608⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623507,0,false,-4288,-4224⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624816,0,false,-3008,-2944⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278501127029,0,true,165830862464,165830862528⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920522128523,0,false,-195361605824,-195361605760⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278626246324,0,true,165938459840,165938459904⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920397009228,0,false,-195511063872,-195511063808⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070333176391,0,false,-29572604032,-29572603968⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070373926971,0,false,-29530743360,-29530743296⟩
    { al := (333519/2048000), au := (53397/327680), zl := (3997/4000), zu := (1599/1600),
      A := ⟨179056649699,179170600551⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165888610368,165888610432⟩ : DyadicInterval 40),(⟨-195441816128,-195441816064⟩ : DyadicInterval 40),(⟨747478462380,747478481709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165986598592,165986598656⟩ : DyadicInterval 40),(⟨-195577942336,-195577942272⟩ : DyadicInterval 40),(⟨747459732621,747459751950⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165773118720,165773118784⟩ : DyadicInterval 40),(⟨-195281411392,-195281411328⟩ : DyadicInterval 40),(⟨747500520142,747500539471⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165890303808,165890303872⟩ : DyadicInterval 40),(⟨-195444168448,-195444168384⟩ : DyadicInterval 40),(⟨747478138817,747478158146⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57050401,68506501⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57048896,57048960⟩ : DyadicInterval 40),(⟨-57051904,-57051840⟩ : DyadicInterval 40),(⟨762123382095,762123401424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68504320,68504384⟩ : DyadicInterval 40),(⟨-68508672,-68508608⟩ : DyadicInterval 40),(⟨762123381459,762123400788⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4288,-2944⟩ : DyadicInterval 40),(⟨762123385088,762123405024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178989499253,179114618548⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165830862464,165830862528⟩ : DyadicInterval 40),(⟨-195361605824,-195361605760⟩ : DyadicInterval 40),(⟨747489494050,747489513380⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165938459840,165938459904⟩ : DyadicInterval 40),(⟨-195511063872,-195511063808⟩ : DyadicInterval 40),(⟨747468935725,747468955054⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29572604032,-29530743296⟩ : DyadicInterval 40),(⟨776888755264,776909704896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165888610368,165986598656⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195577942336,-195441816064⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2512_ok : ecellOkT e2512 = true := by decide +kernel
theorem e2512_pos {a z : ℝ} (ha1 : ((333519/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((53397/327680 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2512 e2512_ok ha1 ha2 hz1 hz2 hz

-- box ['53397/327680', '667887/4096000', '3997/4000', '1599/1600']  interval_lower 62854735/274877906944
noncomputable def e2513 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278682228326,0,true,165986598592,165986598656⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920341027226,0,false,-195577942336,-195577942272⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278796179178,0,true,166084578176,166084578240⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920227076374,0,false,-195714085440,-195714085376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278547850375,0,true,165871043776,165871043840⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920475405177,0,false,-195417415616,-195417415552⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278684126334,0,true,165988230656,165988230720⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920339129218,0,false,-195580209856,-195580209792⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568715913,0,true,57086592,57086656⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454539639,0,false,-57089664,-57089600⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580179564,0,true,68549632,68549696⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443075988,0,false,-68553984,-68553920⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623501,0,false,-4288,-4224⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624812,0,false,-3008,-2944⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278615035143,0,true,165928819136,165928819200⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920408220409,0,false,-195497671040,-195497670976⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278740161565,0,true,166036413056,166036413120⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920283093987,0,false,-195647156096,-195647156032⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070296050138,0,false,-29610743040,-29610742976⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070336828966,0,false,-29568851904,-29568851840⟩
    { al := (53397/327680), au := (667887/4096000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨179170600550,179284551402⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165986598592,165986598656⟩ : DyadicInterval 40),(⟨-195577942336,-195577942272⟩ : DyadicInterval 40),(⟨747459732621,747459751950⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166084578176,166084578240⟩ : DyadicInterval 40),(⟨-195714085440,-195714085376⟩ : DyadicInterval 40),(⟨747440990693,747441010022⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165871043776,165871043840⟩ : DyadicInterval 40),(⟨-195417415616,-195417415552⟩ : DyadicInterval 40),(⟨747481818684,747481838013⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165988230656,165988230720⟩ : DyadicInterval 40),(⟨-195580209856,-195580209792⟩ : DyadicInterval 40),(⟨747459420546,747459439875⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57088137,68551788⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57086592,57086656⟩ : DyadicInterval 40),(⟨-57089664,-57089600⟩ : DyadicInterval 40),(⟨762123382123,762123401452⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68549632,68549696⟩ : DyadicInterval 40),(⟨-68553984,-68553920⟩ : DyadicInterval 40),(⟨762123381453,762123400783⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4288,-2944⟩ : DyadicInterval 40),(⟨762123385088,762123405024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179103407367,179228533789⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165928819136,165928819200⟩ : DyadicInterval 40),(⟨-195497671040,-195497670976⟩ : DyadicInterval 40),(⟨747470778431,747470797760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166036413056,166036413120⟩ : DyadicInterval 40),(⟨-195647156096,-195647156032⟩ : DyadicInterval 40),(⟨747450205615,747450224945⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29610743040,-29568851840⟩ : DyadicInterval 40),(⟨776907809536,776928774400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165986598592,166084578240⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195714085440,-195577942272⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2513_ok : ecellOkT e2513 = true := by decide +kernel
theorem e2513_pos {a z : ℝ} (ha1 : ((53397/327680 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((667887/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2513 e2513_ok ha1 ha2 hz1 hz2 hz

-- box ['333519/2048000', '53397/327680', '1599/1600', '1999/2000']  interval_lower 249963549/1099511627776
noncomputable def e2514 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278568277475,0,true,165888610368,165888610432⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920454978077,0,false,-195441816128,-195441816064⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278682228327,0,true,165986598592,165986598656⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920341027225,0,false,-195577942336,-195577942272⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278456367068,0,true,165792368192,165792368256⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920566888484,0,false,-195308143872,-195308143808⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278592643027,0,true,165909563392,165909563456⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920430612525,0,false,-195470921920,-195470921856⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557268157,0,true,45639424,45639488⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465987395,0,false,-45641344,-45641280⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568716710,0,true,57087424,57087488⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454538842,0,false,-57090432,-57090368⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624811,0,false,-3008,-2944⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625882,0,false,-1920,-1856⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278512317923,0,true,165840486592,165840486656⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920510937629,0,false,-195374972800,-195374972736⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278637444361,0,true,165948089152,165948089216⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920385811191,0,false,-195524441216,-195524441152⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070329527872,0,false,-29576352000,-29576351936⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070370283325,0,false,-29534486208,-29534486144⟩
    { al := (333519/2048000), au := (53397/327680), zl := (1599/1600), zu := (1999/2000),
      A := ⟨179056649699,179170600551⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165888610368,165888610432⟩ : DyadicInterval 40),(⟨-195441816128,-195441816064⟩ : DyadicInterval 40),(⟨747478462380,747478481709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165986598592,165986598656⟩ : DyadicInterval 40),(⟨-195577942336,-195577942272⟩ : DyadicInterval 40),(⟨747459732621,747459751950⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165792368192,165792368256⟩ : DyadicInterval 40),(⟨-195308143872,-195308143808⟩ : DyadicInterval 40),(⟨747496844998,747496864328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165909563392,165909563456⟩ : DyadicInterval 40),(⟨-195470921920,-195470921856⟩ : DyadicInterval 40),(⟨747474458541,747474477870⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨45640381,57088934⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45639424,45639488⟩ : DyadicInterval 40),(⟨-45641344,-45641280⟩ : DyadicInterval 40),(⟨762123382617,762123401946⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57087424,57087488⟩ : DyadicInterval 40),(⟨-57090432,-57090368⟩ : DyadicInterval 40),(⟨762123382091,762123401420⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3008,-1856⟩ : DyadicInterval 40),(⟨762123384544,762123404384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179000690147,179125816585⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165840486592,165840486656⟩ : DyadicInterval 40),(⟨-195374972800,-195374972736⟩ : DyadicInterval 40),(⟨747487655877,747487675207⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165948089152,165948089216⟩ : DyadicInterval 40),(⟨-195524441216,-195524441152⟩ : DyadicInterval 40),(⟨747467095087,747467114416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29576352000,-29534486144⟩ : DyadicInterval 40),(⟨776890626688,776911578880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165888610368,165986598656⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195577942336,-195441816064⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2514_ok : ecellOkT e2514 = true := by decide +kernel
theorem e2514_pos {a z : ℝ} (ha1 : ((333519/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((53397/327680 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2514 e2514_ok ha1 ha2 hz1 hz2 hz

-- box ['53397/327680', '667887/4096000', '1599/1600', '1999/2000']  interval_lower 31404559/137438953472
noncomputable def e2515 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278682228326,0,true,165986598592,165986598656⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920341027226,0,false,-195577942336,-195577942272⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278796179178,0,true,166084578176,166084578240⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920227076374,0,false,-195714085440,-195714085376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278570246700,0,true,165890303808,165890303872⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920453008852,0,false,-195444168448,-195444168384⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278706536903,0,true,166007500864,166007500928⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920316718649,0,false,-195606983680,-195606983616⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557298347,0,true,45669568,45669632⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465957205,0,false,-45671552,-45671488⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568754450,0,true,57125184,57125248⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454501102,0,false,-57128192,-57128128⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624807,0,false,-3008,-2944⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625879,0,false,-1920,-1856⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278626233161,0,true,165938448512,165938448576⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920397022391,0,false,-195511048192,-195511048128⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278751366729,0,true,166046047616,166046047680⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920271888823,0,false,-195660543616,-195660543552⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070292396975,0,false,-29614495936,-29614495872⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070333180681,0,false,-29572599616,-29572599552⟩
    { al := (53397/327680), au := (667887/4096000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨179170600550,179284551402⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165986598592,165986598656⟩ : DyadicInterval 40),(⟨-195577942336,-195577942272⟩ : DyadicInterval 40),(⟨747459732621,747459751950⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166084578176,166084578240⟩ : DyadicInterval 40),(⟨-195714085440,-195714085376⟩ : DyadicInterval 40),(⟨747440990693,747441010022⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165890303808,165890303872⟩ : DyadicInterval 40),(⟨-195444168448,-195444168384⟩ : DyadicInterval 40),(⟨747478138817,747478158146⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166007500864,166007500928⟩ : DyadicInterval 40),(⟨-195606983680,-195606983616⟩ : DyadicInterval 40),(⟨747455735502,747455754831⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨45670571,57126674⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45669568,45669632⟩ : DyadicInterval 40),(⟨-45671552,-45671488⟩ : DyadicInterval 40),(⟨762123382646,762123401976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57125184,57125248⟩ : DyadicInterval 40),(⟨-57128192,-57128128⟩ : DyadicInterval 40),(⟨762123382087,762123401416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3008,-1856⟩ : DyadicInterval 40),(⟨762123384544,762123404384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179114605385,179239738953⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165938448512,165938448576⟩ : DyadicInterval 40),(⟨-195511048192,-195511048128⟩ : DyadicInterval 40),(⟨747468937913,747468957242⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166046047616,166046047680⟩ : DyadicInterval 40),(⟨-195660543616,-195660543552⟩ : DyadicInterval 40),(⟨747448362627,747448381957⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29614495936,-29572599552⟩ : DyadicInterval 40),(⟨776909683392,776930650848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165986598592,166084578240⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195714085440,-195577942272⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2515_ok : ecellOkT e2515 = true := by decide +kernel
theorem e2515_pos {a z : ℝ} (ha1 : ((53397/327680 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((667887/4096000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2515 e2515_ok ha1 ha2 hz1 hz2 hz

-- box ['667887/4096000', '1336623/8192000', '3997/4000', '1599/1600']  interval_lower 252695289/1099511627776
noncomputable def e2516 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278796179177,0,true,166084578176,166084578240⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920227076375,0,false,-195714085440,-195714085376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278910130029,0,true,166182548992,166182549056⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920113125523,0,false,-195850245312,-195850245248⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278661715763,0,true,165968960128,165968960192⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920361539789,0,false,-195553436736,-195553436672⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278798005966,0,true,166086148864,166086148928⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920225249586,0,false,-195716268096,-195716268032⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568753653,0,true,57124352,57124416⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454501899,0,false,-57127424,-57127360⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580224855,0,true,68594880,68594944⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443030697,0,false,-68599232,-68599168⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623496,0,false,-4288,-4224⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624808,0,false,-3008,-2944⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278728943259,0,true,166026767040,166026767104⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920294312293,0,false,-195633753088,-195633753024⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278854076812,0,true,166134357568,166134357632⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920169178740,0,false,-195783265216,-195783265152⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070258900279,0,false,-29648907648,-29648907584⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070299707359,0,false,-29606985984,-29606985920⟩
    { al := (667887/4096000), au := (1336623/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨179284551401,179398502253⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166084578176,166084578240⟩ : DyadicInterval 40),(⟨-195714085440,-195714085376⟩ : DyadicInterval 40),(⟨747440990693,747441010023⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166182548992,166182549056⟩ : DyadicInterval 40),(⟨-195850245312,-195850245248⟩ : DyadicInterval 40),(⟨747422236617,747422255947⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165968960128,165968960192⟩ : DyadicInterval 40),(⟨-195553436736,-195553436672⟩ : DyadicInterval 40),(⟨747463105133,747463124462⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166086148864,166086148928⟩ : DyadicInterval 40),(⟨-195716268096,-195716268032⟩ : DyadicInterval 40),(⟨747440690111,747440709440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57125877,68597079⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57124352,57124416⟩ : DyadicInterval 40),(⟨-57127424,-57127360⟩ : DyadicInterval 40),(⟨762123382119,762123401449⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68594880,68594944⟩ : DyadicInterval 40),(⟨-68599232,-68599168⟩ : DyadicInterval 40),(⟨762123381448,762123400777⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4288,-2944⟩ : DyadicInterval 40),(⟨762123385088,762123405024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179217315483,179342449036⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166026767040,166026767104⟩ : DyadicInterval 40),(⟨-195633753088,-195633753024⟩ : DyadicInterval 40),(⟨747452050709,747452070038⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166134357568,166134357632⟩ : DyadicInterval 40),(⟨-195783265216,-195783265152⟩ : DyadicInterval 40),(⟨747431463387,747431482717⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29648907648,-29606985920⟩ : DyadicInterval 40),(⟨776926876576,776947856704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166084578176,166182549056⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195850245312,-195714085376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2516_ok : ecellOkT e2516 = true := by decide +kernel
theorem e2516_pos {a z : ℝ} (ha1 : ((667887/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1336623/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2516 e2516_ok ha1 ha2 hz1 hz2 hz

-- box ['1336623/8192000', '10449/64000', '3997/4000', '1599/1600']  interval_lower 253974967/1099511627776
noncomputable def e2517 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278910130028,0,true,166182548992,166182549056⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920113125524,0,false,-195850245312,-195850245248⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279024080880,0,true,166280511040,166280511104⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919999174672,0,false,-195986422144,-195986422080⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278775581151,0,true,166066867776,166066867840⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920247674401,0,false,-195689474624,-195689474560⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278911885597,0,true,166184058304,166184058368⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920111369955,0,false,-195852343168,-195852343104⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568791394,0,true,57162112,57162176⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454464158,0,false,-57165120,-57165056⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580270148,0,true,68640192,68640256⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442985404,0,false,-68644544,-68644480⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623490,0,false,-4288,-4224⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624805,0,false,-3008,-2944⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278842851382,0,true,166124706304,166124706368⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920180404170,0,false,-195769852032,-195769851968⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278967992050,0,true,166232293312,166232293376⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920055263502,0,false,-195919391168,-195919391104⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070221726819,0,false,-29687097792,-29687097728⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070262562148,0,false,-29645145664,-29645145600⟩
    { al := (1336623/8192000), au := (10449/64000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨179398502252,179512453104⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166182548992,166182549056⟩ : DyadicInterval 40),(⟨-195850245312,-195850245248⟩ : DyadicInterval 40),(⟨747422236617,747422255947⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166280511040,166280511104⟩ : DyadicInterval 40),(⟨-195986422144,-195986422080⟩ : DyadicInterval 40),(⟨747403470472,747403489801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166066867776,166066867840⟩ : DyadicInterval 40),(⟨-195689474624,-195689474560⟩ : DyadicInterval 40),(⟨747444379434,747444398763⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166184058304,166184058368⟩ : DyadicInterval 40),(⟨-195852343168,-195852343104⟩ : DyadicInterval 40),(⟨747421947585,747421966914⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57163618,68642372⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57162112,57162176⟩ : DyadicInterval 40),(⟨-57165120,-57165056⟩ : DyadicInterval 40),(⟨762123382083,762123401413⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68640192,68640256⟩ : DyadicInterval 40),(⟨-68644544,-68644480⟩ : DyadicInterval 40),(⟨762123381442,762123400771⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4288,-2944⟩ : DyadicInterval 40),(⟨762123385088,762123405024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179331223606,179456364274⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166124706304,166124706368⟩ : DyadicInterval 40),(⟨-195769852032,-195769851968⟩ : DyadicInterval 40),(⟨747433310836,747433330165⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166232293312,166232293376⟩ : DyadicInterval 40),(⟨-195919391168,-195919391104⟩ : DyadicInterval 40),(⟨747412709054,747412728383⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29687097792,-29645145600⟩ : DyadicInterval 40),(⟨776945956416,776966951776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166182548992,166280511104⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195986422144,-195850245248⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2517_ok : ecellOkT e2517 = true := by decide +kernel
theorem e2517_pos {a z : ℝ} (ha1 : ((1336623/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((10449/64000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2517 e2517_ok ha1 ha2 hz1 hz2 hz

-- box ['667887/4096000', '1336623/8192000', '1599/1600', '1999/2000']  interval_lower 252512749/1099511627776
noncomputable def e2518 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278796179177,0,true,166084578176,166084578240⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920227076375,0,false,-195714085440,-195714085376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278910130029,0,true,166182548992,166182549056⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920113125523,0,false,-195850245312,-195850245248⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278684126332,0,true,165988230656,165988230720⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920339129220,0,false,-195580209856,-195580209792⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278820430779,0,true,166105429568,166105429632⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920202824773,0,false,-195743062272,-195743062208⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557328537,0,true,45699776,45699840⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465927015,0,false,-45701760,-45701696⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568792193,0,true,57162880,57162944⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454463359,0,false,-57165952,-57165888⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624803,0,false,-3008,-2944⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625877,0,false,-1920,-1856⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278740148397,0,true,166036401728,166036401792⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920283107155,0,false,-195647140416,-195647140352⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278865289094,0,true,166143997376,166143997440⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920157966458,0,false,-195796662848,-195796662784⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070255242472,0,false,-29652665408,-29652665344⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070296054432,0,false,-29610738624,-29610738560⟩
    { al := (667887/4096000), au := (1336623/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨179284551401,179398502253⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166084578176,166084578240⟩ : DyadicInterval 40),(⟨-195714085440,-195714085376⟩ : DyadicInterval 40),(⟨747440990693,747441010023⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166182548992,166182549056⟩ : DyadicInterval 40),(⟨-195850245312,-195850245248⟩ : DyadicInterval 40),(⟨747422236617,747422255947⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165988230656,165988230720⟩ : DyadicInterval 40),(⟨-195580209856,-195580209792⟩ : DyadicInterval 40),(⟨747459420546,747459439876⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166105429568,166105429632⟩ : DyadicInterval 40),(⟨-195743062272,-195743062208⟩ : DyadicInterval 40),(⟨747437000367,747437019696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨45700761,57164417⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45699776,45699840⟩ : DyadicInterval 40),(⟨-45701760,-45701696⟩ : DyadicInterval 40),(⟨762123382644,762123401973⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57162880,57162944⟩ : DyadicInterval 40),(⟨-57165952,-57165888⟩ : DyadicInterval 40),(⟨762123382115,762123401445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3008,-1856⟩ : DyadicInterval 40),(⟨762123384544,762123404384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179228520621,179353661318⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166036401728,166036401792⟩ : DyadicInterval 40),(⟨-195647140416,-195647140352⟩ : DyadicInterval 40),(⟨747450207806,747450227136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166143997376,166143997440⟩ : DyadicInterval 40),(⟨-195796662848,-195796662784⟩ : DyadicInterval 40),(⟨747429618022,747429637352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29652665408,-29610738560⟩ : DyadicInterval 40),(⟨776928752896,776949735584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166084578176,166182549056⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195850245312,-195714085376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2518_ok : ecellOkT e2518 = true := by decide +kernel
theorem e2518_pos {a z : ℝ} (ha1 : ((667887/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1336623/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2518 e2518_ok ha1 ha2 hz1 hz2 hz

-- box ['1336623/8192000', '10449/64000', '1599/1600', '1999/2000']  interval_lower 31724019/137438953472
noncomputable def e2519 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278910130028,0,true,166182548992,166182549056⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920113125524,0,false,-195850245312,-195850245248⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279024080880,0,true,166280511040,166280511104⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919999174672,0,false,-195986422144,-195986422080⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278798005963,0,true,166086148864,166086148928⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920225249589,0,false,-195716268096,-195716268032⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278934324654,0,true,166203349504,166203349568⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920088930898,0,false,-195879157696,-195879157632⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557358732,0,true,45729984,45730048⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465896820,0,false,-45731968,-45731904⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568829938,0,true,57200640,57200704⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454425614,0,false,-57203712,-57203648⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624800,0,false,-3008,-2944⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625874,0,false,-1920,-1856⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278854063642,0,true,166134346240,166134346304⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920169191910,0,false,-195783249472,-195783249408⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278979211450,0,true,166241938432,166241938496⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920044044102,0,false,-195932798976,-195932798912⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070218064364,0,false,-29690860480,-29690860416⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070258904577,0,false,-29648903232,-29648903168⟩
    { al := (1336623/8192000), au := (10449/64000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨179398502252,179512453104⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166182548992,166182549056⟩ : DyadicInterval 40),(⟨-195850245312,-195850245248⟩ : DyadicInterval 40),(⟨747422236617,747422255947⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166280511040,166280511104⟩ : DyadicInterval 40),(⟨-195986422144,-195986422080⟩ : DyadicInterval 40),(⟨747403470472,747403489801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166086148864,166086148928⟩ : DyadicInterval 40),(⟨-195716268096,-195716268032⟩ : DyadicInterval 40),(⟨747440690111,747440709441⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166203349504,166203349568⟩ : DyadicInterval 40),(⟨-195879157696,-195879157632⟩ : DyadicInterval 40),(⟨747418253134,747418272463⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨45730956,57202162⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45729984,45730048⟩ : DyadicInterval 40),(⟨-45731968,-45731904⟩ : DyadicInterval 40),(⟨762123382641,762123401970⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57200640,57200704⟩ : DyadicInterval 40),(⟨-57203712,-57203648⟩ : DyadicInterval 40),(⟨762123382111,762123401441⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3008,-1856⟩ : DyadicInterval 40),(⟨762123384544,762123404384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179342435866,179467583674⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166134346240,166134346304⟩ : DyadicInterval 40),(⟨-195783249472,-195783249408⟩ : DyadicInterval 40),(⟨747431465555,747431484884⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166241938432,166241938496⟩ : DyadicInterval 40),(⟨-195932798976,-195932798912⟩ : DyadicInterval 40),(⟨747410861297,747410880627⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29690860480,-29648903168⟩ : DyadicInterval 40),(⟨776947835200,776968833120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166182548992,166280511104⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195986422144,-195850245248⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2519_ok : ecellOkT e2519 = true := by decide +kernel
theorem e2519_pos {a z : ℝ} (ha1 : ((1336623/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((10449/64000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2519 e2519_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B041

end


