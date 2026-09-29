-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B034
-- name    : CK_CKLaneC2R_EpCells_B034
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T18:45:44.544927+00:00
-- url     : https://prove2.me/theorems/227592f8-3083-43d4-ad0c-6eaed6fe6135
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B034` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B034` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B034` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B034 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B034.lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheckT

-- ===== source module CKLaneC2R.EpCells.B034 =====
section

namespace CKLaneC2R.EpCells.B034

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['20049/128000', '256797/1638400', '999/1000', '7993/8000']  interval_lower 179377113/1099511627776
noncomputable def e2040 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271731226411,0,true,159993275200,159993275264⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927292029141,0,false,-187304932224,-187304932160⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271845177263,0,true,160091790272,160091790336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927178078289,0,false,-187440054720,-187440054656⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271559006812,0,true,159844367744,159844367808⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927464248740,0,false,-187100746432,-187100746368⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271694385408,0,true,159961422784,159961422848⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927328870144,0,false,-187261249856,-187261249792⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588335360,0,true,76704896,76704960⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434920192,0,false,-76710272,-76710208⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099599354452,0,true,87723136,87723200⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099423901100,0,false,-87730176,-87730112⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620776,0,false,-7040,-6976⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622425,0,false,-5376,-5312⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271645112846,0,true,159918820736,159918820800⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927378142706,0,false,-187202830144,-187202830080⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271769786290,0,true,160026612736,160026612800⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927253469262,0,false,-187350654528,-187350654464⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072524306837,0,false,-27324041792,-27324041728⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072563357350,0,false,-27284009408,-27284009344⟩
    { al := (20049/128000), au := (256797/1638400), zl := (999/1000), zu := (7993/8000),
      A := ⟨172219598635,172333549487⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159993275200,159993275264⟩ : DyadicInterval 40),(⟨-187304932224,-187304932160⟩ : DyadicInterval 40),(⟨748580064561,748580083890⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160091790272,160091790336⟩ : DyadicInterval 40),(⟨-187440054720,-187440054656⟩ : DyadicInterval 40),(⟨748562061918,748562081248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159844367744,159844367808⟩ : DyadicInterval 40),(⟨-187100746432,-187100746368⟩ : DyadicInterval 40),(⟨748607249881,748607269211⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159961422784,159961422848⟩ : DyadicInterval 40),(⟨-187261249856,-187261249792⟩ : DyadicInterval 40),(⟨748585882340,748585901669⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨76707584,87726676⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76704896,76704960⟩ : DyadicInterval 40),(⟨-76710272,-76710208⟩ : DyadicInterval 40),(⟨762123380888,762123400217⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨87723136,87723200⟩ : DyadicInterval 40),(⟨-87730176,-87730112⟩ : DyadicInterval 40),(⟨762123380072,762123399401⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7040,-5312⟩ : DyadicInterval 40),(⟨762123386272,762123406400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172133485070,172258158514⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159918820736,159918820800⟩ : DyadicInterval 40),(⟨-187202830144,-187202830080⟩ : DyadicInterval 40),(⟨748593661281,748593680611⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160026612736,160026612800⟩ : DyadicInterval 40),(⟨-187350654528,-187350654464⟩ : DyadicInterval 40),(⟨748573974001,748573993331⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27324041792,-27284009344⟩ : DyadicInterval 40),(⟨775765388288,775785423776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159993275200,160091790336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187440054720,-187304932160⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2040_ok : ecellOkT e2040 = true := by decide +kernel
theorem e2040_pos {a z : ℝ} (ha1 : ((20049/128000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((256797/1638400 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2040 e2040_ok ha1 ha2 hz1 hz2 hz

-- box ['256797/1638400', '642417/4096000', '999/1000', '7993/8000']  interval_lower 180479475/1099511627776
noncomputable def e2041 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271845177262,0,true,160091790272,160091790336⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927178078290,0,false,-187440054720,-187440054656⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271959128114,0,true,160190296448,160190296512⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927064127438,0,false,-187575193792,-187575193728⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271672843712,0,true,159942797568,159942797632⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927350411840,0,false,-187235708672,-187235708608⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271808236552,0,true,160059854464,160059854528⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927215019000,0,false,-187396248704,-187396248640⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588387958,0,true,76757440,76757504⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434867594,0,false,-76762880,-76762816⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099599414570,0,true,87783232,87783296⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099423840982,0,false,-87790336,-87790272⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620766,0,false,-7040,-6976⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622418,0,false,-5376,-5312⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271759006718,0,true,160017293184,160017293248⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927264248834,0,false,-187337872512,-187337872448⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271883687283,0,true,160125081664,160125081728⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927139568269,0,false,-187485723456,-187485723392⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072488605783,0,false,-27360641728,-27360641664⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072527684358,0,false,-27320579264,-27320579200⟩
    { al := (256797/1638400), au := (642417/4096000), zl := (999/1000), zu := (7993/8000),
      A := ⟨172333549486,172447500338⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160091790272,160091790336⟩ : DyadicInterval 40),(⟨-187440054720,-187440054656⟩ : DyadicInterval 40),(⟨748562061918,748562081248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160190296448,160190296512⟩ : DyadicInterval 40),(⟨-187575193792,-187575193728⟩ : DyadicInterval 40),(⟨748544047196,748544066525⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159942797568,159942797632⟩ : DyadicInterval 40),(⟨-187235708672,-187235708608⟩ : DyadicInterval 40),(⟨748589283541,748589302870⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160059854464,160059854528⟩ : DyadicInterval 40),(⟨-187396248704,-187396248640⟩ : DyadicInterval 40),(⟨748567899374,748567918704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨76760182,87786794⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76757440,76757504⟩ : DyadicInterval 40),(⟨-76762880,-76762816⟩ : DyadicInterval 40),(⟨762123380912,762123400242⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨87783232,87783296⟩ : DyadicInterval 40),(⟨-87790336,-87790272⟩ : DyadicInterval 40),(⟨762123380094,762123399424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7040,-5312⟩ : DyadicInterval 40),(⟨762123386272,762123406400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172247378942,172372059507⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160017293184,160017293248⟩ : DyadicInterval 40),(⟨-187337872512,-187337872448⟩ : DyadicInterval 40),(⟨748575676801,748575696130⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160125081664,160125081728⟩ : DyadicInterval 40),(⟨-187485723456,-187485723392⟩ : DyadicInterval 40),(⟨748555975150,748555994480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27360641728,-27320579200⟩ : DyadicInterval 40),(⟨775783673216,775803723744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160091790272,160190296512⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187575193792,-187440054656⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2041_ok : ecellOkT e2041 = true := by decide +kernel
theorem e2041_pos {a z : ℝ} (ha1 : ((256797/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((642417/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2041 e2041_ok ha1 ha2 hz1 hz2 hz

-- box ['20049/128000', '256797/1638400', '7993/8000', '3997/4000']  interval_lower 89609627/549755813888
noncomputable def e2042 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271731226411,0,true,159993275200,159993275264⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927292029141,0,false,-187304932224,-187304932160⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271845177263,0,true,160091790272,160091790336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927178078289,0,false,-187440054720,-187440054656⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271580534262,0,true,159862982272,159862982336⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927442721290,0,false,-187126267584,-187126267520⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271715927102,0,true,159980047680,159980047744⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927307328450,0,false,-187286791616,-187286791552⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577377246,0,true,65747456,65747520⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445878306,0,false,-65751488,-65751424⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588388824,0,true,76758336,76758400⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434866728,0,false,-76763776,-76763712⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622417,0,false,-5376,-5312⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623845,0,false,-3968,-3904⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271655876390,0,true,159928127232,159928127296⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927367379162,0,false,-187215591616,-187215591552⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271780556983,0,true,160035924544,160035924608⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927242698569,0,false,-187363426176,-187363426112⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072520931888,0,false,-27327501632,-27327501568⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072559987082,0,false,-27287464320,-27287464256⟩
    { al := (20049/128000), au := (256797/1638400), zl := (7993/8000), zu := (3997/4000),
      A := ⟨172219598635,172333549487⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159993275200,159993275264⟩ : DyadicInterval 40),(⟨-187304932224,-187304932160⟩ : DyadicInterval 40),(⟨748580064561,748580083890⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160091790272,160091790336⟩ : DyadicInterval 40),(⟨-187440054720,-187440054656⟩ : DyadicInterval 40),(⟨748562061918,748562081248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159862982272,159862982336⟩ : DyadicInterval 40),(⟨-187126267584,-187126267520⟩ : DyadicInterval 40),(⟨748603853234,748603872563⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159980047680,159980047744⟩ : DyadicInterval 40),(⟨-187286791616,-187286791552⟩ : DyadicInterval 40),(⟨748582480702,748582500032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨65749470,76761048⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65747456,65747520⟩ : DyadicInterval 40),(⟨-65751488,-65751424⟩ : DyadicInterval 40),(⟨762123381636,762123400965⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76758336,76758400⟩ : DyadicInterval 40),(⟨-76763776,-76763712⟩ : DyadicInterval 40),(⟨762123380912,762123400242⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5376,-3904⟩ : DyadicInterval 40),(⟨762123385568,762123405568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172144248614,172268929207⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159928127232,159928127296⟩ : DyadicInterval 40),(⟨-187215591616,-187215591552⟩ : DyadicInterval 40),(⟨748591962188,748591981517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160035924544,160035924608⟩ : DyadicInterval 40),(⟨-187363426176,-187363426112⟩ : DyadicInterval 40),(⟨748572272494,748572291823⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27327501632,-27287464256⟩ : DyadicInterval 40),(⟨775767115744,775787153696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159993275200,160091790336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187440054720,-187304932160⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2042_ok : ecellOkT e2042 = true := by decide +kernel
theorem e2042_pos {a z : ℝ} (ha1 : ((20049/128000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((256797/1638400 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2042 e2042_ok ha1 ha2 hz1 hz2 hz

-- box ['256797/1638400', '642417/4096000', '7993/8000', '3997/4000']  interval_lower 180321393/1099511627776
noncomputable def e2043 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271845177262,0,true,160091790272,160091790336⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927178078290,0,false,-187440054720,-187440054656⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271959128114,0,true,160190296448,160190296512⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927064127438,0,false,-187575193792,-187575193728⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271694385406,0,true,159961422784,159961422848⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927328870146,0,false,-187261249856,-187261249792⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271829792489,0,true,160078489984,160078490048⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927193463063,0,false,-187421810496,-187421810432⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577422331,0,true,65792576,65792640⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445833221,0,false,-65796544,-65796480⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588441427,0,true,76810944,76811008⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434814125,0,false,-76816384,-76816320⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622409,0,false,-5376,-5312⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623839,0,false,-3968,-3904⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271769777386,0,true,160026605056,160026605120⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927253478166,0,false,-187350643968,-187350643904⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271894465097,0,true,160134398784,160134398848⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927128790455,0,false,-187498505152,-187498505088⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072485226370,0,false,-27364106304,-27364106240⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072524309628,0,false,-27324038912,-27324038848⟩
    { al := (256797/1638400), au := (642417/4096000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨172333549486,172447500338⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160091790272,160091790336⟩ : DyadicInterval 40),(⟨-187440054720,-187440054656⟩ : DyadicInterval 40),(⟨748562061918,748562081248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160190296448,160190296512⟩ : DyadicInterval 40),(⟨-187575193792,-187575193728⟩ : DyadicInterval 40),(⟨748544047196,748544066525⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159961422784,159961422848⟩ : DyadicInterval 40),(⟨-187261249856,-187261249792⟩ : DyadicInterval 40),(⟨748585882341,748585901670⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160078489984,160078490048⟩ : DyadicInterval 40),(⟨-187421810496,-187421810432⟩ : DyadicInterval 40),(⟨748564493214,748564512543⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨65794555,76813651⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65792576,65792640⟩ : DyadicInterval 40),(⟨-65796544,-65796480⟩ : DyadicInterval 40),(⟨762123381598,762123400927⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76810944,76811008⟩ : DyadicInterval 40),(⟨-76816384,-76816320⟩ : DyadicInterval 40),(⟨762123380905,762123400234⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5376,-3904⟩ : DyadicInterval 40),(⟨762123385568,762123405568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172258149610,172382837321⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160026605056,160026605120⟩ : DyadicInterval 40),(⟨-187350643968,-187350643904⟩ : DyadicInterval 40),(⟨748573975396,748573994726⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160134398784,160134398848⟩ : DyadicInterval 40),(⟨-187498505152,-187498505088⟩ : DyadicInterval 40),(⟨748554271394,748554290723⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27364106304,-27324038848⟩ : DyadicInterval 40),(⟨775785403040,775805456032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160091790272,160190296512⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187575193792,-187440054656⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2043_ok : ecellOkT e2043 = true := by decide +kernel
theorem e2043_pos {a z : ℝ} (ha1 : ((256797/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((642417/4096000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2043 e2043_ok ha1 ha2 hz1 hz2 hz

-- box ['642417/4096000', '1285683/8192000', '999/1000', '7993/8000']  interval_lower 181584477/1099511627776
noncomputable def e2044 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271959128113,0,true,160190296448,160190296512⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927064127439,0,false,-187575193792,-187575193728⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272073078965,0,true,160288793856,160288793920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926950176587,0,false,-187710349440,-187710349376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271786680612,0,true,160041218688,160041218752⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927236574940,0,false,-187370687552,-187370687488⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271922087696,0,true,160158277376,160158277440⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927101167856,0,false,-187531264192,-187531264128⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588440561,0,true,76810048,76810112⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434814991,0,false,-76815488,-76815424⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099599474691,0,true,87843392,87843456⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099423780861,0,false,-87850432,-87850368⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620757,0,false,-7040,-6976⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622410,0,false,-5376,-5312⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271872900590,0,true,160115756800,160115756864⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927150354962,0,false,-187472931392,-187472931328⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271997588283,0,true,160223541824,160223541888⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927025667269,0,false,-187620809024,-187620808960⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072452881128,0,false,-27397267136,-27397267072⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072491987769,0,false,-27357174592,-27357174528⟩
    { al := (642417/4096000), au := (1285683/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨172447500337,172561451189⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160190296448,160190296512⟩ : DyadicInterval 40),(⟨-187575193792,-187575193728⟩ : DyadicInterval 40),(⟨748544047196,748544066525⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160288793856,160288793920⟩ : DyadicInterval 40),(⟨-187710349440,-187710349376⟩ : DyadicInterval 40),(⟨748526020318,748526039648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160041218688,160041218752⟩ : DyadicInterval 40),(⟨-187370687552,-187370687488⟩ : DyadicInterval 40),(⟨748571305086,748571324415⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160158277376,160158277440⟩ : DyadicInterval 40),(⟨-187531264192,-187531264128⟩ : DyadicInterval 40),(⟨748549904324,748549923653⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨76812785,87846915⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76810048,76810112⟩ : DyadicInterval 40),(⟨-76815488,-76815424⟩ : DyadicInterval 40),(⟨762123380905,762123400234⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨87843392,87843456⟩ : DyadicInterval 40),(⟨-87850432,-87850368⟩ : DyadicInterval 40),(⟨762123380053,762123399382⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7040,-5312⟩ : DyadicInterval 40),(⟨762123386272,762123406400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172361272814,172485960507⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160115756800,160115756864⟩ : DyadicInterval 40),(⟨-187472931392,-187472931328⟩ : DyadicInterval 40),(⟨748557680201,748557699530⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160223541824,160223541888⟩ : DyadicInterval 40),(⟨-187620809024,-187620808960⟩ : DyadicInterval 40),(⟨748537964192,748537983522⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27397267136,-27357174528⟩ : DyadicInterval 40),(⟨775801970880,775822036448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160190296448,160288793920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187710349440,-187575193728⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2044_ok : ecellOkT e2044 = true := by decide +kernel
theorem e2044_pos {a z : ℝ} (ha1 : ((642417/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1285683/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2044 e2044_ok ha1 ha2 hz1 hz2 hz

-- box ['1285683/8192000', '321633/2048000', '999/1000', '7993/8000']  interval_lower 182692279/1099511627776
noncomputable def e2045 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272073078964,0,true,160288793856,160288793920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926950176588,0,false,-187710349440,-187710349376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272187029816,0,true,160387282432,160387282496⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926836225736,0,false,-187845521728,-187845521664⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271900517512,0,true,160139630912,160139630976⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927122738040,0,false,-187505682944,-187505682880⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272035938840,0,true,160256691456,160256691520⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926987316712,0,false,-187666296192,-187666296128⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588493167,0,true,76862656,76862720⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434762385,0,false,-76868096,-76868032⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099599534818,0,true,87903488,87903552⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099423720734,0,false,-87910592,-87910528⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620747,0,false,-7040,-6976⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622403,0,false,-5376,-5312⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271986794466,0,true,160214211648,160214211712⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927036461086,0,false,-187608006976,-187608006912⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272111489282,0,true,160321993216,160321993280⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926911766270,0,false,-187755911168,-187755911104⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072417132875,0,false,-27433917952,-27433917888⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072456267585,0,false,-27393795264,-27393795200⟩
    { al := (1285683/8192000), au := (321633/2048000), zl := (999/1000), zu := (7993/8000),
      A := ⟨172561451188,172675402040⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160288793856,160288793920⟩ : DyadicInterval 40),(⟨-187710349440,-187710349376⟩ : DyadicInterval 40),(⟨748526020318,748526039648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160387282432,160387282496⟩ : DyadicInterval 40),(⟨-187845521728,-187845521664⟩ : DyadicInterval 40),(⟨748507981349,748508000678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160139630912,160139630976⟩ : DyadicInterval 40),(⟨-187505682944,-187505682880⟩ : DyadicInterval 40),(⟨748553314573,748553333903⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160256691456,160256691520⟩ : DyadicInterval 40),(⟨-187666296192,-187666296128⟩ : DyadicInterval 40),(⟨748531897171,748531916500⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨76865391,87907042⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76862656,76862720⟩ : DyadicInterval 40),(⟨-76868096,-76868032⟩ : DyadicInterval 40),(⟨762123380898,762123400227⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨87903488,87903552⟩ : DyadicInterval 40),(⟨-87910592,-87910528⟩ : DyadicInterval 40),(⟨762123380075,762123399405⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7040,-5312⟩ : DyadicInterval 40),(⟨762123386272,762123406400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172475166690,172599861506⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160214211648,160214211712⟩ : DyadicInterval 40),(⟨-187608006976,-187608006912⟩ : DyadicInterval 40),(⟨748539671524,748539690854⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160321993216,160321993280⟩ : DyadicInterval 40),(⟨-187755911168,-187755911104⟩ : DyadicInterval 40),(⟨748519941100,748519960429⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27433917952,-27393795200⟩ : DyadicInterval 40),(⟨775820281216,775840361856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160288793856,160387282496⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187845521728,-187710349376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2045_ok : ecellOkT e2045 = true := by decide +kernel
theorem e2045_pos {a z : ℝ} (ha1 : ((1285683/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((321633/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2045 e2045_ok ha1 ha2 hz1 hz2 hz

-- box ['642417/4096000', '1285683/8192000', '7993/8000', '3997/4000']  interval_lower 181425989/1099511627776
noncomputable def e2046 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271959128113,0,true,160190296448,160190296512⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927064127439,0,false,-187575193792,-187575193728⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272073078965,0,true,160288793856,160288793920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926950176587,0,false,-187710349440,-187710349376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271808236550,0,true,160059854464,160059854528⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927215019002,0,false,-187396248704,-187396248640⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271943657877,0,true,160176923520,160176923584⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927079597675,0,false,-187556846016,-187556845952⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577467419,0,true,65837632,65837696⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445788133,0,false,-65841664,-65841600⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588494034,0,true,76863552,76863616⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434761518,0,false,-76868992,-76868928⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622402,0,false,-5376,-5312⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623834,0,false,-3968,-3904⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271883678377,0,true,160125073984,160125074048⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927139577175,0,false,-187485712896,-187485712832⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272008373216,0,true,160232864256,160232864320⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927014882336,0,false,-187633600704,-187633600640⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072449497248,0,false,-27400736448,-27400736384⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072488608576,0,false,-27360638912,-27360638848⟩
    { al := (642417/4096000), au := (1285683/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨172447500337,172561451189⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160190296448,160190296512⟩ : DyadicInterval 40),(⟨-187575193792,-187575193728⟩ : DyadicInterval 40),(⟨748544047196,748544066525⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160288793856,160288793920⟩ : DyadicInterval 40),(⟨-187710349440,-187710349376⟩ : DyadicInterval 40),(⟨748526020318,748526039648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160059854464,160059854528⟩ : DyadicInterval 40),(⟨-187396248704,-187396248640⟩ : DyadicInterval 40),(⟨748567899374,748567918704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160176923520,160176923584⟩ : DyadicInterval 40),(⟨-187556846016,-187556845952⟩ : DyadicInterval 40),(⟨748546493635,748546512965⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨65839643,76866258⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65837632,65837696⟩ : DyadicInterval 40),(⟨-65841664,-65841600⟩ : DyadicInterval 40),(⟨762123381625,762123400954⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76863552,76863616⟩ : DyadicInterval 40),(⟨-76868992,-76868928⟩ : DyadicInterval 40),(⟨762123380898,762123400227⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5376,-3904⟩ : DyadicInterval 40),(⟨762123385568,762123405568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172372050601,172496745440⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160125073984,160125074048⟩ : DyadicInterval 40),(⟨-187485712896,-187485712832⟩ : DyadicInterval 40),(⟨748555976548,748555995877⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160232864256,160232864320⟩ : DyadicInterval 40),(⟨-187633600704,-187633600640⟩ : DyadicInterval 40),(⟨748536258156,748536277486⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27400736448,-27360638848⟩ : DyadicInterval 40),(⟨775803703040,775823771104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160190296448,160288793920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187710349440,-187575193728⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2046_ok : ecellOkT e2046 = true := by decide +kernel
theorem e2046_pos {a z : ℝ} (ha1 : ((642417/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1285683/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2046 e2046_ok ha1 ha2 hz1 hz2 hz

-- box ['1285683/8192000', '321633/2048000', '7993/8000', '3997/4000']  interval_lower 11408329/68719476736
noncomputable def e2047 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272073078964,0,true,160288793856,160288793920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926950176588,0,false,-187710349440,-187710349376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272187029816,0,true,160387282432,160387282496⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926836225736,0,false,-187845521728,-187845521664⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271922087694,0,true,160158277376,160158277440⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927101167858,0,false,-187531264192,-187531264128⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272057523265,0,true,160275348288,160275348352⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926965732287,0,false,-187691898048,-187691897984⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577512511,0,true,65882752,65882816⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445743041,0,false,-65886720,-65886656⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588546645,0,true,76916160,76916224⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434708907,0,false,-76921600,-76921536⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622394,0,false,-5440,-5376⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623829,0,false,-3968,-3904⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271997579374,0,true,160223534144,160223534208⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927025676178,0,false,-187620798464,-187620798400⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272122281340,0,true,160331320960,160331321024⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926900974212,0,false,-187768712896,-187768712832⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072413744523,0,false,-27437391936,-27437391872⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072452883924,0,false,-27397264320,-27397264256⟩
    { al := (1285683/8192000), au := (321633/2048000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨172561451188,172675402040⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160288793856,160288793920⟩ : DyadicInterval 40),(⟨-187710349440,-187710349376⟩ : DyadicInterval 40),(⟨748526020318,748526039648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160387282432,160387282496⟩ : DyadicInterval 40),(⟨-187845521728,-187845521664⟩ : DyadicInterval 40),(⟨748507981349,748508000678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160158277376,160158277440⟩ : DyadicInterval 40),(⟨-187531264192,-187531264128⟩ : DyadicInterval 40),(⟨748549904324,748549923654⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160275348288,160275348352⟩ : DyadicInterval 40),(⟨-187691898048,-187691897984⟩ : DyadicInterval 40),(⟨748528481910,748528501240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨65884735,76918869⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65882752,65882816⟩ : DyadicInterval 40),(⟨-65886720,-65886656⟩ : DyadicInterval 40),(⟨762123381587,762123400917⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76916160,76916224⟩ : DyadicInterval 40),(⟨-76921600,-76921536⟩ : DyadicInterval 40),(⟨762123380890,762123400220⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5440,-3904⟩ : DyadicInterval 40),(⟨762123385568,762123405600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172485951598,172610653564⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160223534144,160223534208⟩ : DyadicInterval 40),(⟨-187620798464,-187620798400⟩ : DyadicInterval 40),(⟨748537965592,748537984921⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160331320960,160331321024⟩ : DyadicInterval 40),(⟨-187768712896,-187768712832⟩ : DyadicInterval 40),(⟨748518232808,748518252138⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27437391936,-27397264256⟩ : DyadicInterval 40),(⟨775822015744,775842098848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160288793856,160387282496⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187845521728,-187710349376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2047_ok : ecellOkT e2047 = true := by decide +kernel
theorem e2047_pos {a z : ℝ} (ha1 : ((1285683/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((321633/2048000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2047 e2047_ok ha1 ha2 hz1 hz2 hz

-- box ['20049/128000', '256797/1638400', '3997/4000', '1599/1600']  interval_lower 1398917/8589934592
noncomputable def e2048 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271731226411,0,true,159993275200,159993275264⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927292029141,0,false,-187304932224,-187304932160⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271845177263,0,true,160091790272,160091790336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927178078289,0,false,-187440054720,-187440054656⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271602061711,0,true,159881596480,159881596544⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927421193841,0,false,-187151789312,-187151789248⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271737468795,0,true,159998672192,159998672256⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927285786757,0,false,-187312334016,-187312333952⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566419083,0,true,54789888,54789952⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456836469,0,false,-54792704,-54792640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577423147,0,true,65793344,65793408⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445832405,0,false,-65797376,-65797312⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623838,0,false,-3968,-3904⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625046,0,false,-2752,-2688⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271666639959,0,true,159937433728,159937433792⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927356615593,0,false,-187228353280,-187228353216⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271791327692,0,true,160045236224,160045236288⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927231927860,0,false,-187376198016,-187376197952⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072517556723,0,false,-27330961728,-27330961664⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072556616596,0,false,-27290919488,-27290919424⟩
    { al := (20049/128000), au := (256797/1638400), zl := (3997/4000), zu := (1599/1600),
      A := ⟨172219598635,172333549487⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159993275200,159993275264⟩ : DyadicInterval 40),(⟨-187304932224,-187304932160⟩ : DyadicInterval 40),(⟨748580064561,748580083890⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160091790272,160091790336⟩ : DyadicInterval 40),(⟨-187440054720,-187440054656⟩ : DyadicInterval 40),(⟨748562061918,748562081248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159881596480,159881596544⟩ : DyadicInterval 40),(⟨-187151789312,-187151789248⟩ : DyadicInterval 40),(⟨748600456149,748600475479⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159998672192,159998672256⟩ : DyadicInterval 40),(⟨-187312334016,-187312333952⟩ : DyadicInterval 40),(⟨748579078692,748579098021⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54791307,65795371⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54789888,54789952⟩ : DyadicInterval 40),(⟨-54792704,-54792640⟩ : DyadicInterval 40),(⟨762123382229,762123401558⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65793344,65793408⟩ : DyadicInterval 40),(⟨-65797376,-65797312⟩ : DyadicInterval 40),(⟨762123381630,762123400959⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3968,-2688⟩ : DyadicInterval 40),(⟨762123384960,762123404864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172155012183,172279699916⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159937433728,159937433792⟩ : DyadicInterval 40),(⟨-187228353280,-187228353216⟩ : DyadicInterval 40),(⟨748590262955,748590282284⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160045236224,160045236288⟩ : DyadicInterval 40),(⟨-187376198016,-187376197952⟩ : DyadicInterval 40),(⟨748570570923,748570590253⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27330961728,-27290919424⟩ : DyadicInterval 40),(⟨775768843328,775788883744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159993275200,160091790336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187440054720,-187304932160⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2048_ok : ecellOkT e2048 = true := by decide +kernel
theorem e2048_pos {a z : ℝ} (ha1 : ((20049/128000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((256797/1638400 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2048 e2048_ok ha1 ha2 hz1 hz2 hz

-- box ['256797/1638400', '642417/4096000', '3997/4000', '1599/1600']  interval_lower 90081395/549755813888
noncomputable def e2049 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271845177262,0,true,160091790272,160091790336⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927178078290,0,false,-187440054720,-187440054656⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271959128114,0,true,160190296448,160190296512⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927064127438,0,false,-187575193792,-187575193728⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271715927099,0,true,159980047680,159980047744⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927307328453,0,false,-187286791616,-187286791552⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271851348427,0,true,160097125184,160097125248⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927171907125,0,false,-187447372928,-187447372864⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566456654,0,true,54827456,54827520⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456798898,0,false,-54830272,-54830208⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577468235,0,true,65838464,65838528⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445787317,0,false,-65842432,-65842368⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623833,0,false,-3968,-3904⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625042,0,false,-2752,-2688⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271780548078,0,true,160035916800,160035916864⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927242707474,0,false,-187363415616,-187363415552⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271905242931,0,true,160143715840,160143715904⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927118012621,0,false,-187511287040,-187511286976⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072481846739,0,false,-27367571136,-27367571072⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072520934679,0,false,-27327498752,-27327498688⟩
    { al := (256797/1638400), au := (642417/4096000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨172333549486,172447500338⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160091790272,160091790336⟩ : DyadicInterval 40),(⟨-187440054720,-187440054656⟩ : DyadicInterval 40),(⟨748562061918,748562081248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160190296448,160190296512⟩ : DyadicInterval 40),(⟨-187575193792,-187575193728⟩ : DyadicInterval 40),(⟨748544047196,748544066525⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159980047680,159980047744⟩ : DyadicInterval 40),(⟨-187286791616,-187286791552⟩ : DyadicInterval 40),(⟨748582480703,748582500032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160097125184,160097125248⟩ : DyadicInterval 40),(⟨-187447372928,-187447372864⟩ : DyadicInterval 40),(⟨748561086642,748561105972⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54828878,65840459⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54827456,54827520⟩ : DyadicInterval 40),(⟨-54830272,-54830208⟩ : DyadicInterval 40),(⟨762123382225,762123401554⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65838464,65838528⟩ : DyadicInterval 40),(⟨-65842432,-65842368⟩ : DyadicInterval 40),(⟨762123381593,762123400922⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3968,-2688⟩ : DyadicInterval 40),(⟨762123384960,762123404864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172268920302,172393615155⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160035916800,160035916864⟩ : DyadicInterval 40),(⟨-187363415616,-187363415552⟩ : DyadicInterval 40),(⟨748572273927,748572293256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160143715840,160143715904⟩ : DyadicInterval 40),(⟨-187511287040,-187511286976⟩ : DyadicInterval 40),(⟨748552567536,748552586865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27367571136,-27327498688⟩ : DyadicInterval 40),(⟨775787132960,775807188448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160091790272,160190296512⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187575193792,-187440054656⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2049_ok : ecellOkT e2049 = true := by decide +kernel
theorem e2049_pos {a z : ℝ} (ha1 : ((256797/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((642417/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2049 e2049_ok ha1 ha2 hz1 hz2 hz

-- box ['20049/128000', '256797/1638400', '1599/1600', '1999/2000']  interval_lower 22362913/137438953472
noncomputable def e2050 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271731226411,0,true,159993275200,159993275264⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927292029141,0,false,-187304932224,-187304932160⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271845177263,0,true,160091790272,160091790336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927178078289,0,false,-187440054720,-187440054656⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271623589161,0,true,159900210368,159900210432⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927399666391,0,false,-187177311680,-187177311616⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271759010489,0,true,160017296448,160017296512⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927264245063,0,false,-187337876928,-187337876864⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555460869,0,true,43832192,43832256⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467794683,0,false,-43833984,-43833920⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566457420,0,true,54828224,54828288⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456798132,0,false,-54831040,-54830976⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625041,0,false,-2752,-2688⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626029,0,false,-1792,-1728⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271677403550,0,true,159946740096,159946740160⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927345852002,0,false,-187241115072,-187241115008⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271802098434,0,true,160054547904,160054547968⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927221157118,0,false,-187388970048,-187388969984⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072514181337,0,false,-27334422080,-27334422016⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072553245892,0,false,-27294374912,-27294374848⟩
    { al := (20049/128000), au := (256797/1638400), zl := (1599/1600), zu := (1999/2000),
      A := ⟨172219598635,172333549487⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159993275200,159993275264⟩ : DyadicInterval 40),(⟨-187304932224,-187304932160⟩ : DyadicInterval 40),(⟨748580064561,748580083890⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160091790272,160091790336⟩ : DyadicInterval 40),(⟨-187440054720,-187440054656⟩ : DyadicInterval 40),(⟨748562061918,748562081248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159900210368,159900210432⟩ : DyadicInterval 40),(⟨-187177311680,-187177311616⟩ : DyadicInterval 40),(⟨748597058656,748597077985⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160017296448,160017296512⟩ : DyadicInterval 40),(⟨-187337876928,-187337876864⟩ : DyadicInterval 40),(⟨748575676179,748575695509⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨43833093,54829644⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43832192,43832256⟩ : DyadicInterval 40),(⟨-43833984,-43833920⟩ : DyadicInterval 40),(⟨762123382700,762123402029⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54828224,54828288⟩ : DyadicInterval 40),(⟨-54831040,-54830976⟩ : DyadicInterval 40),(⟨762123382225,762123401554⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2752,-1728⟩ : DyadicInterval 40),(⟨762123384480,762123404256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172165775774,172290470658⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159946740096,159946740160⟩ : DyadicInterval 40),(⟨-187241115072,-187241115008⟩ : DyadicInterval 40),(⟨748588563631,748588582960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160054547904,160054547968⟩ : DyadicInterval 40),(⟨-187388970048,-187388969984⟩ : DyadicInterval 40),(⟨748568869212,748568888542⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27334422080,-27294374848⟩ : DyadicInterval 40),(⟨775770571040,775790613920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159993275200,160091790336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187440054720,-187304932160⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2050_ok : ecellOkT e2050 = true := by decide +kernel
theorem e2050_pos {a z : ℝ} (ha1 : ((20049/128000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((256797/1638400 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2050 e2050_ok ha1 ha2 hz1 hz2 hz

-- box ['256797/1638400', '642417/4096000', '1599/1600', '1999/2000']  interval_lower 180004663/1099511627776
noncomputable def e2051 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271845177262,0,true,160091790272,160091790336⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927178078290,0,false,-187440054720,-187440054656⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271959128114,0,true,160190296448,160190296512⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927064127438,0,false,-187575193792,-187575193728⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271737468793,0,true,159998672192,159998672256⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927285786759,0,false,-187312334016,-187312333952⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271872904364,0,true,160115760064,160115760128⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927150351188,0,false,-187472935872,-187472935808⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555490927,0,true,43862272,43862336⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467764625,0,false,-43864064,-43864000⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566494993,0,true,54865792,54865856⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456760559,0,false,-54868608,-54868544⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625038,0,false,-2752,-2688⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626027,0,false,-1792,-1728⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271791318788,0,true,160045228544,160045228608⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927231936764,0,false,-187376187456,-187376187392⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271916020793,0,true,160153032832,160153032896⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927107234759,0,false,-187524069056,-187524068992⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072478466888,0,false,-27371036160,-27371036096⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072517559514,0,false,-27330958912,-27330958848⟩
    { al := (256797/1638400), au := (642417/4096000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨172333549486,172447500338⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160091790272,160091790336⟩ : DyadicInterval 40),(⟨-187440054720,-187440054656⟩ : DyadicInterval 40),(⟨748562061918,748562081248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160190296448,160190296512⟩ : DyadicInterval 40),(⟨-187575193792,-187575193728⟩ : DyadicInterval 40),(⟨748544047196,748544066525⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159998672192,159998672256⟩ : DyadicInterval 40),(⟨-187312334016,-187312333952⟩ : DyadicInterval 40),(⟨748579078692,748579098021⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160115760064,160115760128⟩ : DyadicInterval 40),(⟨-187472935872,-187472935808⟩ : DyadicInterval 40),(⟨748557679605,748557698935⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨43863151,54867217⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43862272,43862336⟩ : DyadicInterval 40),(⟨-43864064,-43864000⟩ : DyadicInterval 40),(⟨762123382698,762123402027⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54865792,54865856⟩ : DyadicInterval 40),(⟨-54868608,-54868544⟩ : DyadicInterval 40),(⟨762123382221,762123401551⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2752,-1728⟩ : DyadicInterval 40),(⟨762123384480,762123404256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172279691012,172404393017⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160045228544,160045228608⟩ : DyadicInterval 40),(⟨-187376187456,-187376187392⟩ : DyadicInterval 40),(⟨748570572319,748570591649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160153032832,160153032896⟩ : DyadicInterval 40),(⟨-187524069056,-187524068992⟩ : DyadicInterval 40),(⟨748550863548,748550882877⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27371036160,-27330958848⟩ : DyadicInterval 40),(⟨775788863040,775808920960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160091790272,160190296512⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187575193792,-187440054656⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2051_ok : ecellOkT e2051 = true := by decide +kernel
theorem e2051_pos {a z : ℝ} (ha1 : ((256797/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((642417/4096000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2051 e2051_ok ha1 ha2 hz1 hz2 hz

-- box ['642417/4096000', '1285683/8192000', '3997/4000', '1599/1600']  interval_lower 2832301/17179869184
noncomputable def e2052 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271959128113,0,true,160190296448,160190296512⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927064127439,0,false,-187575193792,-187575193728⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272073078965,0,true,160288793856,160288793920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926950176587,0,false,-187710349440,-187710349376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271829792487,0,true,160078489984,160078490048⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927193463065,0,false,-187421810496,-187421810432⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271965228059,0,true,160195569408,160195569472⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927058027493,0,false,-187582428416,-187582428352⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566494227,0,true,54865024,54865088⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456761325,0,false,-54867840,-54867776⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577513328,0,true,65883520,65883584⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445742224,0,false,-65887552,-65887488⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623827,0,false,-3968,-3904⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625039,0,false,-2752,-2688⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271894456190,0,true,160134391104,160134391168⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927128799362,0,false,-187498494592,-187498494528⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272019158178,0,true,160242186688,160242186752⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927004097374,0,false,-187646392640,-187646392576⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072446113147,0,false,-27404205952,-27404205888⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072485229163,0,false,-27364103488,-27364103424⟩
    { al := (642417/4096000), au := (1285683/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨172447500337,172561451189⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160190296448,160190296512⟩ : DyadicInterval 40),(⟨-187575193792,-187575193728⟩ : DyadicInterval 40),(⟨748544047196,748544066525⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160288793856,160288793920⟩ : DyadicInterval 40),(⟨-187710349440,-187710349376⟩ : DyadicInterval 40),(⟨748526020318,748526039648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160078489984,160078490048⟩ : DyadicInterval 40),(⟨-187421810496,-187421810432⟩ : DyadicInterval 40),(⟨748564493214,748564512544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160195569408,160195569472⟩ : DyadicInterval 40),(⟨-187582428416,-187582428352⟩ : DyadicInterval 40),(⟨748543082469,748543101799⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54866451,65885552⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54865024,54865088⟩ : DyadicInterval 40),(⟨-54867840,-54867776⟩ : DyadicInterval 40),(⟨762123382222,762123401551⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65883520,65883584⟩ : DyadicInterval 40),(⟨-65887552,-65887488⟩ : DyadicInterval 40),(⟨762123381619,762123400949⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3968,-2688⟩ : DyadicInterval 40),(⟨762123384960,762123404864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172382828414,172507530402⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160134391104,160134391168⟩ : DyadicInterval 40),(⟨-187498494592,-187498494528⟩ : DyadicInterval 40),(⟨748554272792,748554292121⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160242186688,160242186752⟩ : DyadicInterval 40),(⟨-187646392640,-187646392576⟩ : DyadicInterval 40),(⟨748534552008,748534571337⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27404205952,-27364103424⟩ : DyadicInterval 40),(⟨775805435328,775825505856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160190296448,160288793920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187710349440,-187575193728⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2052_ok : ecellOkT e2052 = true := by decide +kernel
theorem e2052_pos {a z : ℝ} (ha1 : ((642417/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1285683/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2052 e2052_ok ha1 ha2 hz1 hz2 hz

-- box ['1285683/8192000', '321633/2048000', '3997/4000', '1599/1600']  interval_lower 182374345/1099511627776
noncomputable def e2053 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272073078964,0,true,160288793856,160288793920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926950176588,0,false,-187710349440,-187710349376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272187029816,0,true,160387282432,160387282496⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926836225736,0,false,-187845521728,-187845521664⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271943657875,0,true,160176923520,160176923584⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927079597677,0,false,-187556846016,-187556845952⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272079107690,0,true,160294004800,160294004864⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926944147862,0,false,-187717500544,-187717500480⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566531804,0,true,54902656,54902720⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456723748,0,false,-54905408,-54905344⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577558422,0,true,65928640,65928704⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445697130,0,false,-65932672,-65932608⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623822,0,false,-3968,-3904⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625035,0,false,-2752,-2688⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272008364306,0,true,160232856576,160232856640⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927014891246,0,false,-187633590144,-187633590080⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272133073419,0,true,160340648640,160340648704⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926890182133,0,false,-187781514816,-187781514752⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072410355953,0,false,-27440866112,-27440866048⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072449500045,0,false,-27400733568,-27400733504⟩
    { al := (1285683/8192000), au := (321633/2048000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨172561451188,172675402040⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160288793856,160288793920⟩ : DyadicInterval 40),(⟨-187710349440,-187710349376⟩ : DyadicInterval 40),(⟨748526020318,748526039648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160387282432,160387282496⟩ : DyadicInterval 40),(⟨-187845521728,-187845521664⟩ : DyadicInterval 40),(⟨748507981349,748508000678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160176923520,160176923584⟩ : DyadicInterval 40),(⟨-187556846016,-187556845952⟩ : DyadicInterval 40),(⟨748546493635,748546512965⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160294004800,160294004864⟩ : DyadicInterval 40),(⟨-187717500544,-187717500480⟩ : DyadicInterval 40),(⟨748525066236,748525085565⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54904028,65930646⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54902656,54902720⟩ : DyadicInterval 40),(⟨-54905408,-54905344⟩ : DyadicInterval 40),(⟨762123382186,762123401515⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65928640,65928704⟩ : DyadicInterval 40),(⟨-65932672,-65932608⟩ : DyadicInterval 40),(⟨762123381614,762123400943⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3968,-2688⟩ : DyadicInterval 40),(⟨762123384960,762123404864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172496736530,172621445643⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160232856576,160232856640⟩ : DyadicInterval 40),(⟨-187633590144,-187633590080⟩ : DyadicInterval 40),(⟨748536259557,748536278886⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160340648640,160340648704⟩ : DyadicInterval 40),(⟨-187781514816,-187781514752⟩ : DyadicInterval 40),(⟨748516524413,748516543743⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27440866112,-27400733504⟩ : DyadicInterval 40),(⟨775823750368,775843835936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160288793856,160387282496⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187845521728,-187710349376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2053_ok : ecellOkT e2053 = true := by decide +kernel
theorem e2053_pos {a z : ℝ} (ha1 : ((1285683/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((321633/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2053 e2053_ok ha1 ha2 hz1 hz2 hz

-- box ['642417/4096000', '1285683/8192000', '1599/1600', '1999/2000']  interval_lower 181108443/1099511627776
noncomputable def e2054 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271959128113,0,true,160190296448,160190296512⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927064127439,0,false,-187575193792,-187575193728⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272073078965,0,true,160288793856,160288793920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926950176587,0,false,-187710349440,-187710349376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271851348425,0,true,160097125184,160097125248⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927171907127,0,false,-187447372928,-187447372864⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271986798240,0,true,160214214912,160214214976⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927036457312,0,false,-187608011456,-187608011392⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555520986,0,true,43892288,43892352⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467734566,0,false,-43894144,-43894080⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566532570,0,true,54903360,54903424⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456722982,0,false,-54906176,-54906112⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625034,0,false,-2752,-2688⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626024,0,false,-1792,-1728⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271905234024,0,true,160143708160,160143708224⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927118021528,0,false,-187511276480,-187511276416⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272029943157,0,true,160251508992,160251509056⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926993312395,0,false,-187659184640,-187659184576⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072442728830,0,false,-27407675648,-27407675584⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072481849533,0,false,-27367568256,-27367568192⟩
    { al := (642417/4096000), au := (1285683/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨172447500337,172561451189⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160190296448,160190296512⟩ : DyadicInterval 40),(⟨-187575193792,-187575193728⟩ : DyadicInterval 40),(⟨748544047196,748544066525⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160288793856,160288793920⟩ : DyadicInterval 40),(⟨-187710349440,-187710349376⟩ : DyadicInterval 40),(⟨748526020318,748526039648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160097125184,160097125248⟩ : DyadicInterval 40),(⟨-187447372928,-187447372864⟩ : DyadicInterval 40),(⟨748561086643,748561105972⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160214214912,160214214976⟩ : DyadicInterval 40),(⟨-187608011456,-187608011392⟩ : DyadicInterval 40),(⟨748539670928,748539690258⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨43893210,54904794⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43892288,43892352⟩ : DyadicInterval 40),(⟨-43894144,-43894080⟩ : DyadicInterval 40),(⟨762123382727,762123402056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54903360,54903424⟩ : DyadicInterval 40),(⟨-54906176,-54906112⟩ : DyadicInterval 40),(⟨762123382218,762123401547⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2752,-1728⟩ : DyadicInterval 40),(⟨762123384480,762123404256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172393606248,172518315381⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160143708160,160143708224⟩ : DyadicInterval 40),(⟨-187511276480,-187511276416⟩ : DyadicInterval 40),(⟨748552568934,748552588263⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160251508992,160251509056⟩ : DyadicInterval 40),(⟨-187659184640,-187659184576⟩ : DyadicInterval 40),(⟨748532845740,748532865069⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27407675648,-27367568192⟩ : DyadicInterval 40),(⟨775807167712,775827240704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160190296448,160288793920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187710349440,-187575193728⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2054_ok : ecellOkT e2054 = true := by decide +kernel
theorem e2054_pos {a z : ℝ} (ha1 : ((642417/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1285683/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2054 e2054_ok ha1 ha2 hz1 hz2 hz

-- box ['1285683/8192000', '321633/2048000', '1599/1600', '1999/2000']  interval_lower 91107635/549755813888
noncomputable def e2055 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272073078964,0,true,160288793856,160288793920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926950176588,0,false,-187710349440,-187710349376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272187029816,0,true,160387282432,160387282496⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926836225736,0,false,-187845521728,-187845521664⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271965228056,0,true,160195569408,160195569472⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927058027496,0,false,-187582428416,-187582428352⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272100692116,0,true,160312660928,160312660992⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926922563436,0,false,-187743103552,-187743103488⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555551047,0,true,43922368,43922432⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467704505,0,false,-43924160,-43924096⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566570150,0,true,54940992,54941056⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456685402,0,false,-54943808,-54943744⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625030,0,false,-2752,-2688⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626022,0,false,-1792,-1728⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272019149268,0,true,160242178944,160242179008⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927004106284,0,false,-187646382016,-187646381952⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272143865523,0,true,160349976256,160349976320⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926879390029,0,false,-187794316864,-187794316800⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072406967164,0,false,-27444340544,-27444340480⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072446115944,0,false,-27404203072,-27404203008⟩
    { al := (1285683/8192000), au := (321633/2048000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨172561451188,172675402040⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160288793856,160288793920⟩ : DyadicInterval 40),(⟨-187710349440,-187710349376⟩ : DyadicInterval 40),(⟨748526020318,748526039648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160387282432,160387282496⟩ : DyadicInterval 40),(⟨-187845521728,-187845521664⟩ : DyadicInterval 40),(⟨748507981349,748508000678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160195569408,160195569472⟩ : DyadicInterval 40),(⟨-187582428416,-187582428352⟩ : DyadicInterval 40),(⟨748543082470,748543101799⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160312660928,160312660992⟩ : DyadicInterval 40),(⟨-187743103552,-187743103488⟩ : DyadicInterval 40),(⟨748521650130,748521669459⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨43923271,54942374⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43922368,43922432⟩ : DyadicInterval 40),(⟨-43924160,-43924096⟩ : DyadicInterval 40),(⟨762123382693,762123402022⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54940992,54941056⟩ : DyadicInterval 40),(⟨-54943808,-54943744⟩ : DyadicInterval 40),(⟨762123382214,762123401543⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2752,-1728⟩ : DyadicInterval 40),(⟨762123384480,762123404256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172507521492,172632237747⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160242178944,160242179008⟩ : DyadicInterval 40),(⟨-187646382016,-187646381952⟩ : DyadicInterval 40),(⟨748534553418,748534572747⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160349976256,160349976320⟩ : DyadicInterval 40),(⟨-187794316864,-187794316800⟩ : DyadicInterval 40),(⟨748514815889,748514835218⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27444340544,-27404203008⟩ : DyadicInterval 40),(⟨775825485120,775845573152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160288793856,160387282496⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187845521728,-187710349376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2055_ok : ecellOkT e2055 = true := by decide +kernel
theorem e2055_pos {a z : ℝ} (ha1 : ((1285683/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((321633/2048000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2055 e2055_ok ha1 ha2 hz1 hz2 hz

-- box ['321633/2048000', '1287381/8192000', '999/1000', '7993/8000']  interval_lower 22975363/137438953472
noncomputable def e2056 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272187029815,0,true,160387282432,160387282496⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926836225737,0,false,-187845521728,-187845521664⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272300980667,0,true,160485762240,160485762304⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926722274885,0,false,-187980710656,-187980710592⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272014354412,0,true,160238034368,160238034432⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927008901140,0,false,-187640694912,-187640694848⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272149789984,0,true,160355096768,160355096832⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926873465568,0,false,-187801344768,-187801344704⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588545778,0,true,76915264,76915328⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434709774,0,false,-76920704,-76920640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099599594948,0,true,87963648,87963712⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099423660604,0,false,-87970752,-87970688⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620738,0,false,-7040,-6976⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622396,0,false,-5440,-5376⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272100688341,0,true,160312657664,160312657728⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926922567211,0,false,-187743099072,-187743099008⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272225390288,0,true,160420435712,160420435776⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926797865264,0,false,-187891029952,-187891029888⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072381361021,0,false,-27470594240,-27470594176⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072420523804,0,false,-27430441408,-27430441344⟩
    { al := (321633/2048000), au := (1287381/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨172675402039,172789352891⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160387282432,160387282496⟩ : DyadicInterval 40),(⟨-187845521728,-187845521664⟩ : DyadicInterval 40),(⟨748507981349,748508000678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160485762240,160485762304⟩ : DyadicInterval 40),(⟨-187980710656,-187980710592⟩ : DyadicInterval 40),(⟨748489930248,748489949578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160238034368,160238034432⟩ : DyadicInterval 40),(⟨-187640694912,-187640694848⟩ : DyadicInterval 40),(⟨748535311955,748535331284⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160355096768,160355096832⟩ : DyadicInterval 40),(⟨-187801344768,-187801344704⟩ : DyadicInterval 40),(⟨748513877905,748513897234⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨76918002,87967172⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76915264,76915328⟩ : DyadicInterval 40),(⟨-76920704,-76920640⟩ : DyadicInterval 40),(⟨762123380890,762123400220⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨87963648,87963712⟩ : DyadicInterval 40),(⟨-87970752,-87970688⟩ : DyadicInterval 40),(⟨762123380065,762123399395⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7040,-5376⟩ : DyadicInterval 40),(⟨762123386304,762123406400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172589060565,172713762512⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160312657664,160312657728⟩ : DyadicInterval 40),(⟨-187743099072,-187743099008⟩ : DyadicInterval 40),(⟨748521650727,748521670057⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160420435712,160420435776⟩ : DyadicInterval 40),(⟨-187891029952,-187891029888⟩ : DyadicInterval 40),(⟨748501905972,748501925302⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27470594240,-27430441344⟩ : DyadicInterval 40),(⟨775838604288,775858700000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160387282432,160485762304⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187980710656,-187845521664⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2056_ok : ecellOkT e2056 = true := by decide +kernel
theorem e2056_pos {a z : ℝ} (ha1 : ((321633/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1287381/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2056 e2056_ok ha1 ha2 hz1 hz2 hz

-- box ['1287381/8192000', '128823/819200', '999/1000', '7993/8000']  interval_lower 184916147/1099511627776
noncomputable def e2057 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272300980666,0,true,160485762240,160485762304⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926722274886,0,false,-187980710656,-187980710592⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272414931518,0,true,160584233152,160584233216⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926608324034,0,false,-188115916224,-188115916160⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272128191313,0,true,160336428992,160336429056⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926895064239,0,false,-187775723456,-187775723392⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272263641128,0,true,160453493248,160453493312⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926759614424,0,false,-187936409984,-187936409920⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588598390,0,true,76967872,76967936⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434657162,0,false,-76973312,-76973248⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099599655082,0,true,88023744,88023808⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099423600470,0,false,-88030848,-88030784⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620728,0,false,-7104,-7040⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622388,0,false,-5440,-5376⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272214582218,0,true,160411094912,160411094976⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926808673334,0,false,-187878207808,-187878207744⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272339291283,0,true,160518869440,160518869504⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926683964269,0,false,-188026165312,-188026165248⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072345565572,0,false,-27507295872,-27507295808⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072384756428,0,false,-27467112896,-27467112832⟩
    { al := (1287381/8192000), au := (128823/819200), zl := (999/1000), zu := (7993/8000),
      A := ⟨172789352890,172903303742⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160485762240,160485762304⟩ : DyadicInterval 40),(⟨-187980710656,-187980710592⟩ : DyadicInterval 40),(⟨748489930248,748489949578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160584233152,160584233216⟩ : DyadicInterval 40),(⟨-188115916224,-188115916160⟩ : DyadicInterval 40),(⟨748471867090,748471886419⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160336428992,160336429056⟩ : DyadicInterval 40),(⟨-187775723456,-187775723392⟩ : DyadicInterval 40),(⟨748517297265,748517316595⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160453493248,160453493312⟩ : DyadicInterval 40),(⟨-187936409984,-187936409920⟩ : DyadicInterval 40),(⟨748495846588,748495865917⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨76970614,88027306⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76967872,76967936⟩ : DyadicInterval 40),(⟨-76973312,-76973248⟩ : DyadicInterval 40),(⟨762123380883,762123400212⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨88023744,88023808⟩ : DyadicInterval 40),(⟨-88030848,-88030784⟩ : DyadicInterval 40),(⟨762123380056,762123399385⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7104,-5376⟩ : DyadicInterval 40),(⟨762123386304,762123406432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172702954442,172827663507⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160411094912,160411094976⟩ : DyadicInterval 40),(⟨-187878207808,-187878207744⟩ : DyadicInterval 40),(⟨748503617824,748503637154⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160518869440,160518869504⟩ : DyadicInterval 40),(⟨-188026165312,-188026165248⟩ : DyadicInterval 40),(⟨748483858709,748483878038⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27507295872,-27467112832⟩ : DyadicInterval 40),(⟨775856940032,775877050816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160485762240,160584233216⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188115916224,-187980710592⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2057_ok : ecellOkT e2057 = true := by decide +kernel
theorem e2057_pos {a z : ℝ} (ha1 : ((1287381/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((128823/819200 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2057 e2057_ok ha1 ha2 hz1 hz2 hz

-- box ['321633/2048000', '1287381/8192000', '7993/8000', '3997/4000']  interval_lower 183643381/1099511627776
noncomputable def e2058 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272187029815,0,true,160387282432,160387282496⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926836225737,0,false,-187845521728,-187845521664⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272300980667,0,true,160485762240,160485762304⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926722274885,0,false,-187980710656,-187980710592⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272035938838,0,true,160256691456,160256691520⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926987316714,0,false,-187666296192,-187666296128⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272171388653,0,true,160373764224,160373764288⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926851866899,0,false,-187826966720,-187826966656⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577557605,0,true,65927808,65927872⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445697947,0,false,-65931840,-65931776⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588599259,0,true,76968768,76968832⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434656293,0,false,-76974208,-76974144⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622387,0,false,-5440,-5376⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623823,0,false,-3968,-3904⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272111480370,0,true,160321985472,160321985536⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926911775182,0,false,-187755900608,-187755900544⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272236189463,0,true,160429768768,160429768832⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926787066089,0,false,-187903841728,-187903841664⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072377968198,0,false,-27474072896,-27474072832⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072417135674,0,false,-27433915136,-27433915072⟩
    { al := (321633/2048000), au := (1287381/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨172675402039,172789352891⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160387282432,160387282496⟩ : DyadicInterval 40),(⟨-187845521728,-187845521664⟩ : DyadicInterval 40),(⟨748507981349,748508000678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160485762240,160485762304⟩ : DyadicInterval 40),(⟨-187980710656,-187980710592⟩ : DyadicInterval 40),(⟨748489930248,748489949578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160256691456,160256691520⟩ : DyadicInterval 40),(⟨-187666296192,-187666296128⟩ : DyadicInterval 40),(⟨748531897172,748531916501⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160373764224,160373764288⟩ : DyadicInterval 40),(⟨-187826966720,-187826966656⟩ : DyadicInterval 40),(⟨748510458130,748510477459⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨65929829,76971483⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65927808,65927872⟩ : DyadicInterval 40),(⟨-65931840,-65931776⟩ : DyadicInterval 40),(⟨762123381614,762123400943⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76968768,76968832⟩ : DyadicInterval 40),(⟨-76974208,-76974144⟩ : DyadicInterval 40),(⟨762123380883,762123400212⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5440,-3904⟩ : DyadicInterval 40),(⟨762123385568,762123405600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172599852594,172724561687⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160321985472,160321985536⟩ : DyadicInterval 40),(⟨-187755900608,-187755900544⟩ : DyadicInterval 40),(⟨748519942539,748519961869⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160429768768,160429768832⟩ : DyadicInterval 40),(⟨-187903841728,-187903841664⟩ : DyadicInterval 40),(⟨748500195421,748500214751⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27474072896,-27433915072⟩ : DyadicInterval 40),(⟨775840341152,775860439328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160387282432,160485762304⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187980710656,-187845521664⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2058_ok : ecellOkT e2058 = true := by decide +kernel
theorem e2058_pos {a z : ℝ} (ha1 : ((321633/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1287381/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2058 e2058_ok ha1 ha2 hz1 hz2 hz

-- box ['1287381/8192000', '128823/819200', '7993/8000', '3997/4000']  interval_lower 46189101/274877906944
noncomputable def e2059 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272300980666,0,true,160485762240,160485762304⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926722274886,0,false,-187980710656,-187980710592⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272414931518,0,true,160584233152,160584233216⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926608324034,0,false,-188115916224,-188115916160⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272149789982,0,true,160355096768,160355096832⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926873465570,0,false,-187801344768,-187801344704⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272285254041,0,true,160472171328,160472171392⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926738001511,0,false,-187962051968,-187962051904⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577602703,0,true,65972928,65972992⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445652849,0,false,-65976960,-65976896⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588651878,0,true,77021376,77021440⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434603674,0,false,-77026816,-77026752⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622380,0,false,-5440,-5376⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623818,0,false,-3968,-3904⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272225381373,0,true,160420428032,160420428096⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926797874179,0,false,-187891019392,-187891019328⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272350097580,0,true,160528207808,160528207872⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926673157972,0,false,-188038987072,-188038987008⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072342168272,0,false,-27510779264,-27510779200⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072381363823,0,false,-27470591360,-27470591296⟩
    { al := (1287381/8192000), au := (128823/819200), zl := (7993/8000), zu := (3997/4000),
      A := ⟨172789352890,172903303742⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160485762240,160485762304⟩ : DyadicInterval 40),(⟨-187980710656,-187980710592⟩ : DyadicInterval 40),(⟨748489930248,748489949578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160584233152,160584233216⟩ : DyadicInterval 40),(⟨-188115916224,-188115916160⟩ : DyadicInterval 40),(⟨748471867090,748471886419⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160355096768,160355096832⟩ : DyadicInterval 40),(⟨-187801344768,-187801344704⟩ : DyadicInterval 40),(⟨748513877905,748513897235⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160472171328,160472171392⟩ : DyadicInterval 40),(⟨-187962051968,-187962051904⟩ : DyadicInterval 40),(⟨748492422265,748492441594⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨65974927,77024102⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65972928,65972992⟩ : DyadicInterval 40),(⟨-65976960,-65976896⟩ : DyadicInterval 40),(⟨762123381609,762123400938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77021376,77021440⟩ : DyadicInterval 40),(⟨-77026816,-77026752⟩ : DyadicInterval 40),(⟨762123380876,762123400205⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5440,-3904⟩ : DyadicInterval 40),(⟨762123385568,762123405600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172713753597,172838469804⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160420428032,160420428096⟩ : DyadicInterval 40),(⟨-187891019392,-187891019328⟩ : DyadicInterval 40),(⟨748501907377,748501926706⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160528207808,160528207872⟩ : DyadicInterval 40),(⟨-188038987072,-188038987008⟩ : DyadicInterval 40),(⟨748482145869,748482165199⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27510779264,-27470591296⟩ : DyadicInterval 40),(⟨775858679264,775878792512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160485762240,160584233216⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188115916224,-187980710592⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2059_ok : ecellOkT e2059 = true := by decide +kernel
theorem e2059_pos {a z : ℝ} (ha1 : ((1287381/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((128823/819200 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2059 e2059_ok ha1 ha2 hz1 hz2 hz

-- box ['128823/819200', '1289079/8192000', '999/1000', '7993/8000']  interval_lower 11627001/68719476736
noncomputable def e2060 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272414931517,0,true,160584233152,160584233216⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926608324035,0,false,-188115916224,-188115916160⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272528882369,0,true,160682695296,160682695360⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926494373183,0,false,-188251138368,-188251138304⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272242028213,0,true,160434814848,160434814912⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926781227339,0,false,-187910768640,-187910768576⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272377492272,0,true,160551880896,160551880960⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926645763280,0,false,-188071491776,-188071491712⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588651008,0,true,77020480,77020544⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434604544,0,false,-77025984,-77025920⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099599715222,0,true,88083904,88083968⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099423540330,0,false,-88091008,-88090944⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620718,0,false,-7104,-7040⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622381,0,false,-5440,-5376⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272328476091,0,true,160509523264,160509523328⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926694779461,0,false,-188013333184,-188013333120⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272453192283,0,true,160617294336,160617294400⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926570063269,0,false,-188161317312,-188161317248⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072309746523,0,false,-27544022976,-27544022912⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072348965457,0,false,-27503809856,-27503809792⟩
    { al := (128823/819200), au := (1289079/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨172903303741,173017254593⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160584233152,160584233216⟩ : DyadicInterval 40),(⟨-188115916224,-188115916160⟩ : DyadicInterval 40),(⟨748471867090,748471886419⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160682695296,160682695360⟩ : DyadicInterval 40),(⟨-188251138368,-188251138304⟩ : DyadicInterval 40),(⟨748453791772,748453811101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160434814848,160434814912⟩ : DyadicInterval 40),(⟨-187910768640,-187910768576⟩ : DyadicInterval 40),(⟨748499270495,748499289824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160551880896,160551880960⟩ : DyadicInterval 40),(⟨-188071491776,-188071491712⟩ : DyadicInterval 40),(⟨748477803192,748477822521⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨77023232,88087446⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77020480,77020544⟩ : DyadicInterval 40),(⟨-77025984,-77025920⟩ : DyadicInterval 40),(⟨762123380908,762123400237⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨88083904,88083968⟩ : DyadicInterval 40),(⟨-88091008,-88090944⟩ : DyadicInterval 40),(⟨762123380046,762123399376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7104,-5376⟩ : DyadicInterval 40),(⟨762123386304,762123406432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172816848315,172941564507⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160509523264,160509523328⟩ : DyadicInterval 40),(⟨-188013333184,-188013333120⟩ : DyadicInterval 40),(⟨748485572889,748485592218⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160617294336,160617294400⟩ : DyadicInterval 40),(⟨-188161317312,-188161317248⟩ : DyadicInterval 40),(⟨748465799371,748465818700⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27544022976,-27503809792⟩ : DyadicInterval 40),(⟨775875288512,775895414368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160584233152,160682695360⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188251138368,-188115916160⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2060_ok : ecellOkT e2060 = true := by decide +kernel
theorem e2060_pos {a z : ℝ} (ha1 : ((128823/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1289079/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2060 e2060_ok ha1 ha2 hz1 hz2 hz

-- box ['1289079/8192000', '161241/1024000', '999/1000', '7993/8000']  interval_lower 93575511/549755813888
noncomputable def e2061 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272528882368,0,true,160682695296,160682695360⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926494373184,0,false,-188251138368,-188251138304⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272642833220,0,true,160781148608,160781148672⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926380422332,0,false,-188386377216,-188386377152⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272355865113,0,true,160533191872,160533191936⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926667390439,0,false,-188045830400,-188045830336⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272491343416,0,true,160650259776,160650259840⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926531912136,0,false,-188206590144,-188206590080⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588703629,0,true,77073088,77073152⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434551923,0,false,-77078592,-77078528⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099599775365,0,true,88144000,88144064⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099423480187,0,false,-88151168,-88151104⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620709,0,false,-7104,-7040⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622373,0,false,-5440,-5376⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272442369965,0,true,160607942848,160607942912⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926580885587,0,false,-188148475136,-188148475072⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272567093281,0,true,160715710400,160715710464⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926456162271,0,false,-188296485888,-188296485824⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072273903876,0,false,-27580775424,-27580775360⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072313150890,0,false,-27540532224,-27540532160⟩
    { al := (1289079/8192000), au := (161241/1024000), zl := (999/1000), zu := (7993/8000),
      A := ⟨173017254592,173131205444⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160682695296,160682695360⟩ : DyadicInterval 40),(⟨-188251138368,-188251138304⟩ : DyadicInterval 40),(⟨748453791772,748453811101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160781148608,160781148672⟩ : DyadicInterval 40),(⟨-188386377216,-188386377152⟩ : DyadicInterval 40),(⟨748435704383,748435723712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160533191872,160533191936⟩ : DyadicInterval 40),(⟨-188045830400,-188045830336⟩ : DyadicInterval 40),(⟨748481231651,748481250981⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160650259776,160650259840⟩ : DyadicInterval 40),(⟨-188206590144,-188206590080⟩ : DyadicInterval 40),(⟨748459747679,748459767008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨77075853,88147589⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77073088,77073152⟩ : DyadicInterval 40),(⟨-77078592,-77078528⟩ : DyadicInterval 40),(⟨762123380900,762123400230⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨88144000,88144064⟩ : DyadicInterval 40),(⟨-88151168,-88151104⟩ : DyadicInterval 40),(⟨762123380068,762123399398⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7104,-5376⟩ : DyadicInterval 40),(⟨762123386304,762123406432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172930742189,173055465505⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160607942848,160607942912⟩ : DyadicInterval 40),(⟨-188148475136,-188148475072⟩ : DyadicInterval 40),(⟨748467515818,748467535148⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160715710400,160715710464⟩ : DyadicInterval 40),(⟨-188296485888,-188296485824⟩ : DyadicInterval 40),(⟨748447727931,748447747260⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27580775424,-27540532160⟩ : DyadicInterval 40),(⟨775893649696,775913790592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160682695296,160781148672⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188386377216,-188251138304⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2061_ok : ecellOkT e2061 = true := by decide +kernel
theorem e2061_pos {a z : ℝ} (ha1 : ((1289079/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((161241/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2061 e2061_ok ha1 ha2 hz1 hz2 hz

-- box ['128823/819200', '1289079/8192000', '7993/8000', '3997/4000']  interval_lower 46468011/274877906944
noncomputable def e2062 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272414931517,0,true,160584233152,160584233216⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926608324035,0,false,-188115916224,-188115916160⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272528882369,0,true,160682695296,160682695360⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926494373183,0,false,-188251138368,-188251138304⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272263641126,0,true,160453493248,160453493312⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926759614426,0,false,-187936409984,-187936409920⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272399119429,0,true,160570569600,160570569664⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926624136123,0,false,-188097153792,-188097153728⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577647804,0,true,66017984,66018048⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445607748,0,false,-66022016,-66021952⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588704499,0,true,77073984,77074048⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434551053,0,false,-77079488,-77079424⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622372,0,false,-5440,-5376⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623812,0,false,-3968,-3904⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272339282365,0,true,160518861696,160518861760⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926683973187,0,false,-188026154752,-188026154688⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272464005701,0,true,160626638016,160626638080⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926559249851,0,false,-188174149120,-188174149056⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072306344744,0,false,-27547511040,-27547510976⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072345568377,0,false,-27507292992,-27507292928⟩
    { al := (128823/819200), au := (1289079/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨172903303741,173017254593⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160584233152,160584233216⟩ : DyadicInterval 40),(⟨-188115916224,-188115916160⟩ : DyadicInterval 40),(⟨748471867090,748471886419⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160682695296,160682695360⟩ : DyadicInterval 40),(⟨-188251138368,-188251138304⟩ : DyadicInterval 40),(⟨748453791772,748453811101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160453493248,160453493312⟩ : DyadicInterval 40),(⟨-187936409984,-187936409920⟩ : DyadicInterval 40),(⟨748495846588,748495865918⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160570569600,160570569664⟩ : DyadicInterval 40),(⟨-188097153792,-188097153728⟩ : DyadicInterval 40),(⟨748474374315,748474393645⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨66020028,77076723⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66017984,66018048⟩ : DyadicInterval 40),(⟨-66022016,-66021952⟩ : DyadicInterval 40),(⟨762123381603,762123400932⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77073984,77074048⟩ : DyadicInterval 40),(⟨-77079488,-77079424⟩ : DyadicInterval 40),(⟨762123380900,762123400230⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5440,-3904⟩ : DyadicInterval 40),(⟨762123385568,762123405600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172827654589,172952377925⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160518861696,160518861760⟩ : DyadicInterval 40),(⟨-188026154752,-188026154688⟩ : DyadicInterval 40),(⟨748483860153,748483879482⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160626638016,160626638080⟩ : DyadicInterval 40),(⟨-188174149120,-188174149056⟩ : DyadicInterval 40),(⟨748464084266,748464103596⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27547511040,-27507292928⟩ : DyadicInterval 40),(⟨775877030080,775897158400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160584233152,160682695360⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188251138368,-188115916160⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2062_ok : ecellOkT e2062 = true := by decide +kernel
theorem e2062_pos {a z : ℝ} (ha1 : ((128823/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1289079/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2062 e2062_ok ha1 ha2 hz1 hz2 hz

-- box ['1289079/8192000', '161241/1024000', '7993/8000', '3997/4000']  interval_lower 186990587/1099511627776
noncomputable def e2063 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272528882368,0,true,160682695296,160682695360⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926494373184,0,false,-188251138368,-188251138304⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272642833220,0,true,160781148608,160781148672⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926380422332,0,false,-188386377216,-188386377152⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272377492270,0,true,160551880896,160551880960⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926645763282,0,false,-188071491776,-188071491712⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272512984817,0,true,160668959104,160668959168⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926510270735,0,false,-188232272256,-188232272192⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577692908,0,true,66063104,66063168⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445562644,0,false,-66067136,-66067072⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588757125,0,true,77126592,77126656⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434498427,0,false,-77132096,-77132032⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622365,0,false,-5440,-5376⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623807,0,false,-4032,-3968⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272453183362,0,true,160617286592,160617286656⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926570072190,0,false,-188161306752,-188161306688⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272577913819,0,true,160725059456,160725059520⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926445341733,0,false,-188309327680,-188309327616⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072270497615,0,false,-27584268224,-27584268160⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072309749331,0,false,-27544020096,-27544020032⟩
    { al := (1289079/8192000), au := (161241/1024000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨173017254592,173131205444⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160682695296,160682695360⟩ : DyadicInterval 40),(⟨-188251138368,-188251138304⟩ : DyadicInterval 40),(⟨748453791772,748453811101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160781148608,160781148672⟩ : DyadicInterval 40),(⟨-188386377216,-188386377152⟩ : DyadicInterval 40),(⟨748435704383,748435723712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160551880896,160551880960⟩ : DyadicInterval 40),(⟨-188071491776,-188071491712⟩ : DyadicInterval 40),(⟨748477803192,748477822522⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160668959104,160668959168⟩ : DyadicInterval 40),(⟨-188232272256,-188232272192⟩ : DyadicInterval 40),(⟨748456314269,748456333598⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨66065132,77129349⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66063104,66063168⟩ : DyadicInterval 40),(⟨-66067136,-66067072⟩ : DyadicInterval 40),(⟨762123381598,762123400927⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77126592,77126656⟩ : DyadicInterval 40),(⟨-77132096,-77132032⟩ : DyadicInterval 40),(⟨762123380893,762123400222⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5440,-3968⟩ : DyadicInterval 40),(⟨762123385600,762123405600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172941555586,173066286043⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160617286592,160617286656⟩ : DyadicInterval 40),(⟨-188161306752,-188161306688⟩ : DyadicInterval 40),(⟨748465800818,748465820147⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160725059456,160725059520⟩ : DyadicInterval 40),(⟨-188309327680,-188309327616⟩ : DyadicInterval 40),(⟨748446010494,748446029824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27584268224,-27544020032⟩ : DyadicInterval 40),(⟨775895393632,775915536992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160682695296,160781148672⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188386377216,-188251138304⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2063_ok : ecellOkT e2063 = true := by decide +kernel
theorem e2063_pos {a z : ℝ} (ha1 : ((1289079/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((161241/1024000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2063 e2063_ok ha1 ha2 hz1 hz2 hz

-- box ['321633/2048000', '1287381/8192000', '3997/4000', '1599/1600']  interval_lower 45870949/274877906944
noncomputable def e2064 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272187029815,0,true,160387282432,160387282496⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926836225737,0,false,-187845521728,-187845521664⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272300980667,0,true,160485762240,160485762304⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926722274885,0,false,-187980710656,-187980710592⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272057523263,0,true,160275348288,160275348352⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926965732289,0,false,-187691898048,-187691897984⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272192987322,0,true,160392431360,160392431424⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926830268230,0,false,-187852589184,-187852589120⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566569383,0,true,54940224,54940288⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456686169,0,false,-54943040,-54942976⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577603521,0,true,65973760,65973824⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445652031,0,false,-65977728,-65977664⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623817,0,false,-3968,-3904⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625031,0,false,-2752,-2688⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272122272428,0,true,160331313216,160331313280⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926900983124,0,false,-187768702336,-187768702272⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272246988667,0,true,160439101824,160439101888⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926776266885,0,false,-187916653632,-187916653568⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072374575153,0,false,-27477551808,-27477551744⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072413747323,0,false,-27437389056,-27437388992⟩
    { al := (321633/2048000), au := (1287381/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨172675402039,172789352891⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160387282432,160387282496⟩ : DyadicInterval 40),(⟨-187845521728,-187845521664⟩ : DyadicInterval 40),(⟨748507981349,748508000678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160485762240,160485762304⟩ : DyadicInterval 40),(⟨-187980710656,-187980710592⟩ : DyadicInterval 40),(⟨748489930248,748489949578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160275348288,160275348352⟩ : DyadicInterval 40),(⟨-187691898048,-187691897984⟩ : DyadicInterval 40),(⟨748528481911,748528501240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160392431360,160392431424⟩ : DyadicInterval 40),(⟨-187852589184,-187852589120⟩ : DyadicInterval 40),(⟨748507037885,748507057215⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54941607,65975745⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54940224,54940288⟩ : DyadicInterval 40),(⟨-54943040,-54942976⟩ : DyadicInterval 40),(⟨762123382214,762123401543⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65973760,65973824⟩ : DyadicInterval 40),(⟨-65977728,-65977664⟩ : DyadicInterval 40),(⟨762123381577,762123400906⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3968,-2688⟩ : DyadicInterval 40),(⟨762123384960,762123404864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172610644652,172735360891⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160331313216,160331313280⟩ : DyadicInterval 40),(⟨-187768702336,-187768702272⟩ : DyadicInterval 40),(⟨748518234247,748518253577⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160439101824,160439101888⟩ : DyadicInterval 40),(⟨-187916653632,-187916653568⟩ : DyadicInterval 40),(⟨748498484703,748498504033⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27477551808,-27437388992⟩ : DyadicInterval 40),(⟨775842078112,775862178784⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160387282432,160485762304⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187980710656,-187845521664⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2064_ok : ecellOkT e2064 = true := by decide +kernel
theorem e2064_pos {a z : ℝ} (ha1 : ((321633/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1287381/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2064 e2064_ok ha1 ha2 hz1 hz2 hz

-- box ['1287381/8192000', '128823/819200', '3997/4000', '1599/1600']  interval_lower 184596733/1099511627776
noncomputable def e2065 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272300980666,0,true,160485762240,160485762304⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926722274886,0,false,-187980710656,-187980710592⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272414931518,0,true,160584233152,160584233216⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926608324034,0,false,-188115916224,-188115916160⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272171388651,0,true,160373764224,160373764288⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926851866901,0,false,-187826966720,-187826966656⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272306866954,0,true,160490849088,160490849152⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926716388598,0,false,-187987694528,-187987694464⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566606964,0,true,54977792,54977856⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456648588,0,false,-54980608,-54980544⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577648622,0,true,66018816,66018880⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445606930,0,false,-66022848,-66022784⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623811,0,false,-3968,-3904⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625027,0,false,-2752,-2688⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272236180548,0,true,160429761088,160429761152⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926787075004,0,false,-187903831104,-187903831040⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272360903901,0,true,160537546176,160537546240⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926662351651,0,false,-188051809024,-188051808960⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072338770752,0,false,-27514262848,-27514262784⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072377971000,0,false,-27474070016,-27474069952⟩
    { al := (1287381/8192000), au := (128823/819200), zl := (3997/4000), zu := (1599/1600),
      A := ⟨172789352890,172903303742⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160485762240,160485762304⟩ : DyadicInterval 40),(⟨-187980710656,-187980710592⟩ : DyadicInterval 40),(⟨748489930248,748489949578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160584233152,160584233216⟩ : DyadicInterval 40),(⟨-188115916224,-188115916160⟩ : DyadicInterval 40),(⟨748471867090,748471886419⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160373764224,160373764288⟩ : DyadicInterval 40),(⟨-187826966720,-187826966656⟩ : DyadicInterval 40),(⟨748510458130,748510477460⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160490849088,160490849152⟩ : DyadicInterval 40),(⟨-187987694528,-187987694464⟩ : DyadicInterval 40),(⟨748488997499,748489016828⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54979188,66020846⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54977792,54977856⟩ : DyadicInterval 40),(⟨-54980608,-54980544⟩ : DyadicInterval 40),(⟨762123382210,762123401539⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66018816,66018880⟩ : DyadicInterval 40),(⟨-66022848,-66022784⟩ : DyadicInterval 40),(⟨762123381603,762123400932⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3968,-2688⟩ : DyadicInterval 40),(⟨762123384960,762123404864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172724552772,172849276125⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160429761088,160429761152⟩ : DyadicInterval 40),(⟨-187903831104,-187903831040⟩ : DyadicInterval 40),(⟨748500196799,748500216129⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160537546176,160537546240⟩ : DyadicInterval 40),(⟨-188051809024,-188051808960⟩ : DyadicInterval 40),(⟨748480432889,748480452219⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27514262848,-27474069952⟩ : DyadicInterval 40),(⟨775860418592,775880534304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160485762240,160584233216⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188115916224,-187980710592⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2065_ok : ecellOkT e2065 = true := by decide +kernel
theorem e2065_pos {a z : ℝ} (ha1 : ((1287381/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((128823/819200 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2065 e2065_ok ha1 ha2 hz1 hz2 hz

-- box ['321633/2048000', '1287381/8192000', '1599/1600', '1999/2000']  interval_lower 183324635/1099511627776
noncomputable def e2066 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272187029815,0,true,160387282432,160387282496⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926836225737,0,false,-187845521728,-187845521664⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272300980667,0,true,160485762240,160485762304⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926722274885,0,false,-187980710656,-187980710592⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272079107688,0,true,160294004800,160294004864⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926944147864,0,false,-187717500544,-187717500480⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272214585991,0,true,160411098176,160411098240⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926808669561,0,false,-187878212288,-187878212224⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555581110,0,true,43952448,43952512⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467674442,0,false,-43954240,-43954176⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566607731,0,true,54978560,54978624⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456647821,0,false,-54981376,-54981312⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625026,0,false,-2752,-2688⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626019,0,false,-1792,-1728⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272133064507,0,true,160340640960,160340641024⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926890191045,0,false,-187781504256,-187781504192⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272257787892,0,true,160448434752,160448434816⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926765467660,0,false,-187929465728,-187929465664⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072371181889,0,false,-27481030912,-27481030848⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072410358753,0,false,-27440863296,-27440863232⟩
    { al := (321633/2048000), au := (1287381/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨172675402039,172789352891⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160387282432,160387282496⟩ : DyadicInterval 40),(⟨-187845521728,-187845521664⟩ : DyadicInterval 40),(⟨748507981349,748508000678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160485762240,160485762304⟩ : DyadicInterval 40),(⟨-187980710656,-187980710592⟩ : DyadicInterval 40),(⟨748489930248,748489949578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160294004800,160294004864⟩ : DyadicInterval 40),(⟨-187717500544,-187717500480⟩ : DyadicInterval 40),(⟨748525066236,748525085565⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160411098176,160411098240⟩ : DyadicInterval 40),(⟨-187878212288,-187878212224⟩ : DyadicInterval 40),(⟨748503617226,748503636556⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨43953334,54979955⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43952448,43952512⟩ : DyadicInterval 40),(⟨-43954240,-43954176⟩ : DyadicInterval 40),(⟨762123382690,762123402019⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54978560,54978624⟩ : DyadicInterval 40),(⟨-54981376,-54981312⟩ : DyadicInterval 40),(⟨762123382210,762123401539⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2752,-1728⟩ : DyadicInterval 40),(⟨762123384480,762123404256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172621436731,172746160116⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160340640960,160340641024⟩ : DyadicInterval 40),(⟨-187781504256,-187781504192⟩ : DyadicInterval 40),(⟨748516525816,748516545146⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160448434752,160448434816⟩ : DyadicInterval 40),(⟨-187929465728,-187929465664⟩ : DyadicInterval 40),(⟨748496773919,748496793248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27481030912,-27440863232⟩ : DyadicInterval 40),(⟨775843815232,775863918336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160387282432,160485762304⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187980710656,-187845521664⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2066_ok : ecellOkT e2066 = true := by decide +kernel
theorem e2066_pos {a z : ℝ} (ha1 : ((321633/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1287381/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2066 e2066_ok ha1 ha2 hz1 hz2 hz

-- box ['1287381/8192000', '128823/819200', '1599/1600', '1999/2000']  interval_lower 184436613/1099511627776
noncomputable def e2067 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272300980666,0,true,160485762240,160485762304⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926722274886,0,false,-187980710656,-187980710592⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272414931518,0,true,160584233152,160584233216⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926608324034,0,false,-188115916224,-188115916160⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272192987320,0,true,160392431360,160392431424⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926830268232,0,false,-187852589184,-187852589120⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272328479867,0,true,160509526528,160509526592⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926694775685,0,false,-188013337664,-188013337600⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555611176,0,true,43982464,43982528⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467644376,0,false,-43984320,-43984256⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566645317,0,true,55016128,55016192⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456610235,0,false,-55018944,-55018880⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625023,0,false,-2816,-2752⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626017,0,false,-1792,-1728⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272246979752,0,true,160439094080,160439094144⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926776275800,0,false,-187916643072,-187916643008⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272371710249,0,true,160546884416,160546884480⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926651545303,0,false,-188064631168,-188064631104⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072335373011,0,false,-27517746688,-27517746624⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072374577955,0,false,-27477548928,-27477548864⟩
    { al := (1287381/8192000), au := (128823/819200), zl := (1599/1600), zu := (1999/2000),
      A := ⟨172789352890,172903303742⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160485762240,160485762304⟩ : DyadicInterval 40),(⟨-187980710656,-187980710592⟩ : DyadicInterval 40),(⟨748489930248,748489949578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160584233152,160584233216⟩ : DyadicInterval 40),(⟨-188115916224,-188115916160⟩ : DyadicInterval 40),(⟨748471867090,748471886419⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160392431360,160392431424⟩ : DyadicInterval 40),(⟨-187852589184,-187852589120⟩ : DyadicInterval 40),(⟨748507037886,748507057215⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160509526528,160509526592⟩ : DyadicInterval 40),(⟨-188013337664,-188013337600⟩ : DyadicInterval 40),(⟨748485572289,748485591619⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨43983400,55017541⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43982464,43982528⟩ : DyadicInterval 40),(⟨-43984320,-43984256⟩ : DyadicInterval 40),(⟨762123382720,762123402049⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55016128,55016192⟩ : DyadicInterval 40),(⟨-55018944,-55018880⟩ : DyadicInterval 40),(⟨762123382206,762123401536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2816,-1728⟩ : DyadicInterval 40),(⟨762123384480,762123404288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172735351976,172860082473⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160439094080,160439094144⟩ : DyadicInterval 40),(⟨-187916643072,-187916643008⟩ : DyadicInterval 40),(⟨748498486145,748498505475⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160546884416,160546884480⟩ : DyadicInterval 40),(⟨-188064631168,-188064631104⟩ : DyadicInterval 40),(⟨748478719842,748478739172⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27517746688,-27477548864⟩ : DyadicInterval 40),(⟨775862158048,775882276224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160485762240,160584233216⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188115916224,-187980710592⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2067_ok : ecellOkT e2067 = true := by decide +kernel
theorem e2067_pos {a z : ℝ} (ha1 : ((1287381/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((128823/819200 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2067 e2067_ok ha1 ha2 hz1 hz2 hz

-- box ['128823/819200', '1289079/8192000', '3997/4000', '1599/1600']  interval_lower 185711869/1099511627776
noncomputable def e2068 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272414931517,0,true,160584233152,160584233216⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926608324035,0,false,-188115916224,-188115916160⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272528882369,0,true,160682695296,160682695360⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926494373183,0,false,-188251138368,-188251138304⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272285254039,0,true,160472171328,160472171392⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926738001513,0,false,-187962051968,-187962051904⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272420746585,0,true,160589258048,160589258112⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926602508967,0,false,-188122816384,-188122816320⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566644549,0,true,55015360,55015424⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456611003,0,false,-55018176,-55018112⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577693728,0,true,66063936,66064000⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445561824,0,false,-66067968,-66067904⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623806,0,false,-4032,-3968⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625024,0,false,-2816,-2752⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272350088662,0,true,160528200128,160528200192⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926673166890,0,false,-188038976512,-188038976448⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272474819149,0,true,160635981696,160635981760⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926548436403,0,false,-188186981056,-188186980992⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072302942743,0,false,-27550999360,-27550999296⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072342171077,0,false,-27510776384,-27510776320⟩
    { al := (128823/819200), au := (1289079/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨172903303741,173017254593⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160584233152,160584233216⟩ : DyadicInterval 40),(⟨-188115916224,-188115916160⟩ : DyadicInterval 40),(⟨748471867090,748471886419⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160682695296,160682695360⟩ : DyadicInterval 40),(⟨-188251138368,-188251138304⟩ : DyadicInterval 40),(⟨748453791772,748453811101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160472171328,160472171392⟩ : DyadicInterval 40),(⟨-187962051968,-187962051904⟩ : DyadicInterval 40),(⟨748492422265,748492441595⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160589258048,160589258112⟩ : DyadicInterval 40),(⟨-188122816384,-188122816320⟩ : DyadicInterval 40),(⟨748470944957,748470964286⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55016773,66065952⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55015360,55015424⟩ : DyadicInterval 40),(⟨-55018176,-55018112⟩ : DyadicInterval 40),(⟨762123382207,762123401536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66063936,66064000⟩ : DyadicInterval 40),(⟨-66067968,-66067904⟩ : DyadicInterval 40),(⟨762123381598,762123400927⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4032,-2752⟩ : DyadicInterval 40),(⟨762123384992,762123404896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172838460886,172963191373⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160528200128,160528200192⟩ : DyadicInterval 40),(⟨-188038976512,-188038976448⟩ : DyadicInterval 40),(⟨748482147276,748482166606⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160635981696,160635981760⟩ : DyadicInterval 40),(⟨-188186981056,-188186980992⟩ : DyadicInterval 40),(⟨748462368993,748462388322⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27550999360,-27510776320⟩ : DyadicInterval 40),(⟨775878771776,775898902560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160584233152,160682695360⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188251138368,-188115916160⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2068_ok : ecellOkT e2068 = true := by decide +kernel
theorem e2068_pos {a z : ℝ} (ha1 : ((128823/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1289079/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2068 e2068_ok ha1 ha2 hz1 hz2 hz

-- box ['1289079/8192000', '161241/1024000', '3997/4000', '1599/1600']  interval_lower 186829957/1099511627776
noncomputable def e2069 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272528882368,0,true,160682695296,160682695360⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926494373184,0,false,-188251138368,-188251138304⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272642833220,0,true,160781148608,160781148672⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926380422332,0,false,-188386377216,-188386377152⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272399119427,0,true,160570569600,160570569664⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926624136125,0,false,-188097153792,-188097153728⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272534626217,0,true,160687658176,160687658240⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926488629335,0,false,-188257954880,-188257954816⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566682136,0,true,55052928,55052992⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456573416,0,false,-55055744,-55055680⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577738836,0,true,66109056,66109120⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445516716,0,false,-66113088,-66113024⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623800,0,false,-4032,-3968⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625020,0,false,-2816,-2752⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272463996781,0,true,160626630336,160626630400⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926559258771,0,false,-188174138496,-188174138432⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272588734389,0,true,160734408384,160734408448⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926434521163,0,false,-188322169728,-188322169664⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072267091131,0,false,-27587761280,-27587761216⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072306347551,0,false,-27547508160,-27547508096⟩
    { al := (1289079/8192000), au := (161241/1024000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨173017254592,173131205444⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160682695296,160682695360⟩ : DyadicInterval 40),(⟨-188251138368,-188251138304⟩ : DyadicInterval 40),(⟨748453791772,748453811101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160781148608,160781148672⟩ : DyadicInterval 40),(⟨-188386377216,-188386377152⟩ : DyadicInterval 40),(⟨748435704383,748435723712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160570569600,160570569664⟩ : DyadicInterval 40),(⟨-188097153792,-188097153728⟩ : DyadicInterval 40),(⟨748474374315,748474393645⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160687658176,160687658240⟩ : DyadicInterval 40),(⟨-188257954880,-188257954816⟩ : DyadicInterval 40),(⟨748452880349,748452899679⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55054360,66111060⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55052928,55052992⟩ : DyadicInterval 40),(⟨-55055744,-55055680⟩ : DyadicInterval 40),(⟨762123382203,762123401532⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66109056,66109120⟩ : DyadicInterval 40),(⟨-66113088,-66113024⟩ : DyadicInterval 40),(⟨762123381592,762123400922⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4032,-2752⟩ : DyadicInterval 40),(⟨762123384992,762123404896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172952369005,173077106613⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160626630336,160626630400⟩ : DyadicInterval 40),(⟨-188174138496,-188174138432⟩ : DyadicInterval 40),(⟨748464085649,748464104978⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160734408384,160734408448⟩ : DyadicInterval 40),(⟨-188322169728,-188322169664⟩ : DyadicInterval 40),(⟨748444293016,748444312345⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27587761280,-27547508096⟩ : DyadicInterval 40),(⟨775897137664,775917283520⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160682695296,160781148672⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188386377216,-188251138304⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2069_ok : ecellOkT e2069 = true := by decide +kernel
theorem e2069_pos {a z : ℝ} (ha1 : ((1289079/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((161241/1024000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2069 e2069_ok ha1 ha2 hz1 hz2 hz

-- box ['128823/819200', '1289079/8192000', '1599/1600', '1999/2000']  interval_lower 92775757/549755813888
noncomputable def e2070 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272414931517,0,true,160584233152,160584233216⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926608324035,0,false,-188115916224,-188115916160⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272528882369,0,true,160682695296,160682695360⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926494373183,0,false,-188251138368,-188251138304⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272306866952,0,true,160490849088,160490849152⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926716388600,0,false,-187987694464,-187987694400⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272442373742,0,true,160607946112,160607946176⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926580881810,0,false,-188148479616,-188148479552⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555641243,0,true,44012544,44012608⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467614309,0,false,-44014400,-44014336⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566682905,0,true,55053696,55053760⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456572647,0,false,-55056512,-55056448⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625019,0,false,-2816,-2752⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626015,0,false,-1792,-1728⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272360894987,0,true,160537538432,160537538496⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926662360565,0,false,-188051798464,-188051798400⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272485632616,0,true,160645325248,160645325312⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926537622936,0,false,-188199813184,-188199813120⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072299540523,0,false,-27554487872,-27554487808⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072338773556,0,false,-27514259968,-27514259904⟩
    { al := (128823/819200), au := (1289079/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨172903303741,173017254593⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160584233152,160584233216⟩ : DyadicInterval 40),(⟨-188115916224,-188115916160⟩ : DyadicInterval 40),(⟨748471867090,748471886419⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160682695296,160682695360⟩ : DyadicInterval 40),(⟨-188251138368,-188251138304⟩ : DyadicInterval 40),(⟨748453791772,748453811101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160490849088,160490849152⟩ : DyadicInterval 40),(⟨-187987694464,-187987694400⟩ : DyadicInterval 40),(⟨748488997473,748489016802⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160607946112,160607946176⟩ : DyadicInterval 40),(⟨-188148479616,-188148479552⟩ : DyadicInterval 40),(⟨748467515218,748467534548⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨44013467,55055129⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44012544,44012608⟩ : DyadicInterval 40),(⟨-44014400,-44014336⟩ : DyadicInterval 40),(⟨762123382718,762123402047⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55053696,55053760⟩ : DyadicInterval 40),(⟨-55056512,-55056448⟩ : DyadicInterval 40),(⟨762123382203,762123401532⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2816,-1728⟩ : DyadicInterval 40),(⟨762123384480,762123404288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172849267211,172974004840⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160537538432,160537538496⟩ : DyadicInterval 40),(⟨-188051798464,-188051798400⟩ : DyadicInterval 40),(⟨748480434333,748480453663⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160645325248,160645325312⟩ : DyadicInterval 40),(⟨-188199813184,-188199813120⟩ : DyadicInterval 40),(⟨748460653653,748460672982⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27554487872,-27514259904⟩ : DyadicInterval 40),(⟨775880513568,775900646816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160584233152,160682695360⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188251138368,-188115916160⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2070_ok : ecellOkT e2070 = true := by decide +kernel
theorem e2070_pos {a z : ℝ} (ha1 : ((128823/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1289079/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2070 e2070_ok ha1 ha2 hz1 hz2 hz

-- box ['1289079/8192000', '161241/1024000', '1599/1600', '1999/2000']  interval_lower 46667303/274877906944
noncomputable def e2071 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272528882368,0,true,160682695296,160682695360⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926494373184,0,false,-188251138368,-188251138304⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272642833220,0,true,160781148608,160781148672⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926380422332,0,false,-188386377216,-188386377152⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272420746583,0,true,160589258048,160589258112⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926602508969,0,false,-188122816384,-188122816320⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272556267618,0,true,160706356864,160706356928⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926466987934,0,false,-188283638144,-188283638080⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555671313,0,true,44042624,44042688⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467584239,0,false,-44044480,-44044416⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566720495,0,true,55091328,55091392⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456535057,0,false,-55094144,-55094080⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625015,0,false,-2816,-2752⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626012,0,false,-1792,-1728⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272474810228,0,true,160635973952,160635974016⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926548445324,0,false,-188186970496,-188186970432⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272599554978,0,true,160743757312,160743757376⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926423700574,0,false,-188335011904,-188335011840⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072263684428,0,false,-27591254528,-27591254464⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072302945551,0,false,-27550996480,-27550996416⟩
    { al := (1289079/8192000), au := (161241/1024000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨173017254592,173131205444⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160682695296,160682695360⟩ : DyadicInterval 40),(⟨-188251138368,-188251138304⟩ : DyadicInterval 40),(⟨748453791772,748453811101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160781148608,160781148672⟩ : DyadicInterval 40),(⟨-188386377216,-188386377152⟩ : DyadicInterval 40),(⟨748435704383,748435723712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160589258048,160589258112⟩ : DyadicInterval 40),(⟨-188122816384,-188122816320⟩ : DyadicInterval 40),(⟨748470944958,748470964287⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160706356864,160706356928⟩ : DyadicInterval 40),(⟨-188283638144,-188283638080⟩ : DyadicInterval 40),(⟨748449446048,748449465378⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨44043537,55092719⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44042624,44042688⟩ : DyadicInterval 40),(⟨-44044480,-44044416⟩ : DyadicInterval 40),(⟨762123382715,762123402044⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55091328,55091392⟩ : DyadicInterval 40),(⟨-55094144,-55094080⟩ : DyadicInterval 40),(⟨762123382199,762123401528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2816,-1728⟩ : DyadicInterval 40),(⟨762123384480,762123404288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172963182452,173087927202⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160635973952,160635974016⟩ : DyadicInterval 40),(⟨-188186970496,-188186970432⟩ : DyadicInterval 40),(⟨748462370440,748462389769⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160743757312,160743757376⟩ : DyadicInterval 40),(⟨-188335011904,-188335011840⟩ : DyadicInterval 40),(⟨748442575370,748442594700⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27591254528,-27550996416⟩ : DyadicInterval 40),(⟨775898881824,775919030144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160682695296,160781148672⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188386377216,-188251138304⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2071_ok : ecellOkT e2071 = true := by decide +kernel
theorem e2071_pos {a z : ℝ} (ha1 : ((1289079/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((161241/1024000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2071 e2071_ok ha1 ha2 hz1 hz2 hz

-- box ['20049/128000', '256797/1638400', '1999/2000', '7997/8000']  interval_lower 89372611/549755813888
noncomputable def e2072 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271731226411,0,true,159993275200,159993275264⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927292029141,0,false,-187304932224,-187304932160⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271845177263,0,true,160091790272,160091790336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927178078289,0,false,-187440054720,-187440054656⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271645116611,0,true,159918824000,159918824064⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927378138941,0,false,-187202834560,-187202834496⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271780552183,0,true,160035920384,160035920448⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927242703369,0,false,-187363420480,-187363420416⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544502606,0,true,32874304,32874368⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478752946,0,false,-32875328,-32875264⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555491642,0,true,43862976,43863040⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467763910,0,false,-43864768,-43864704⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626026,0,false,-1792,-1728⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626794,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271688167171,0,true,159956046464,159956046528⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927335088381,0,false,-187253877056,-187253876992⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271812869198,0,true,160063859520,160063859584⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927210386354,0,false,-187401742208,-187401742144⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072510805733,0,false,-27337882688,-27337882624⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072549874968,0,false,-27297830592,-27297830528⟩
    { al := (20049/128000), au := (256797/1638400), zl := (1999/2000), zu := (7997/8000),
      A := ⟨172219598635,172333549487⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159993275200,159993275264⟩ : DyadicInterval 40),(⟨-187304932224,-187304932160⟩ : DyadicInterval 40),(⟨748580064561,748580083890⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160091790272,160091790336⟩ : DyadicInterval 40),(⟨-187440054720,-187440054656⟩ : DyadicInterval 40),(⟨748562061918,748562081248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159918824000,159918824064⟩ : DyadicInterval 40),(⟨-187202834560,-187202834496⟩ : DyadicInterval 40),(⟨748593660662,748593679991⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160035920384,160035920448⟩ : DyadicInterval 40),(⟨-187363420480,-187363420416⟩ : DyadicInterval 40),(⟨748572273257,748572292586⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32874830,43863866⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32874304,32874368⟩ : DyadicInterval 40),(⟨-32875328,-32875264⟩ : DyadicInterval 40),(⟨762123383081,762123402410⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43862976,43863040⟩ : DyadicInterval 40),(⟨-43864768,-43864704⟩ : DyadicInterval 40),(⟨762123382698,762123402027⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1792,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172176539395,172301241422⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159956046464,159956046528⟩ : DyadicInterval 40),(⟨-187253877056,-187253876992⟩ : DyadicInterval 40),(⟨748586864166,748586883496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160063859520,160063859584⟩ : DyadicInterval 40),(⟨-187401742208,-187401742144⟩ : DyadicInterval 40),(⟨748567167372,748567186702⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27337882688,-27297830528⟩ : DyadicInterval 40),(⟨775772298880,775792344224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159993275200,160091790336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187440054720,-187304932160⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2072_ok : ecellOkT e2072 = true := by decide +kernel
theorem e2072_pos {a z : ℝ} (ha1 : ((20049/128000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((256797/1638400 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2072 e2072_ok ha1 ha2 hz1 hz2 hz

-- box ['256797/1638400', '642417/4096000', '1999/2000', '7997/8000']  interval_lower 2810097/17179869184
noncomputable def e2073 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271845177262,0,true,160091790272,160091790336⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927178078290,0,false,-187440054720,-187440054656⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271959128114,0,true,160190296448,160190296512⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927064127438,0,false,-187575193792,-187575193728⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271759010487,0,true,160017296448,160017296512⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927264245065,0,false,-187337876928,-187337876864⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271894460302,0,true,160134394688,160134394752⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927128795250,0,false,-187498499456,-187498499392⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544525149,0,true,32896832,32896896⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478730403,0,false,-32897920,-32897856⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555521702,0,true,43892992,43893056⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467733850,0,false,-43894848,-43894784⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626023,0,false,-1792,-1728⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626792,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271802089530,0,true,160054540224,160054540288⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927221166022,0,false,-187388959488,-187388959424⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271926798680,0,true,160162349760,160162349824⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927096456872,0,false,-187536851264,-187536851200⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072475086818,0,false,-27374501440,-27374501376⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072514184128,0,false,-27334419264,-27334419200⟩
    { al := (256797/1638400), au := (642417/4096000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨172333549486,172447500338⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160091790272,160091790336⟩ : DyadicInterval 40),(⟨-187440054720,-187440054656⟩ : DyadicInterval 40),(⟨748562061918,748562081248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160190296448,160190296512⟩ : DyadicInterval 40),(⟨-187575193792,-187575193728⟩ : DyadicInterval 40),(⟨748544047196,748544066525⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160017296448,160017296512⟩ : DyadicInterval 40),(⟨-187337876928,-187337876864⟩ : DyadicInterval 40),(⟨748575676180,748575695509⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160134394688,160134394752⟩ : DyadicInterval 40),(⟨-187498499456,-187498499392⟩ : DyadicInterval 40),(⟨748554272120,748554291449⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32897373,43893926⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32896832,32896896⟩ : DyadicInterval 40),(⟨-32897920,-32897856⟩ : DyadicInterval 40),(⟨762123383111,762123402440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43892992,43893056⟩ : DyadicInterval 40),(⟨-43894848,-43894784⟩ : DyadicInterval 40),(⟨762123382727,762123402056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1792,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172290461754,172415170904⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160054540224,160054540288⟩ : DyadicInterval 40),(⟨-187388959488,-187388959424⟩ : DyadicInterval 40),(⟨748568870608,748568889938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160162349760,160162349824⟩ : DyadicInterval 40),(⟨-187536851264,-187536851200⟩ : DyadicInterval 40),(⟨748549159457,748549178787⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27374501440,-27334419200⟩ : DyadicInterval 40),(⟨775790593216,775810653600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160091790272,160190296512⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187575193792,-187440054656⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2073_ok : ecellOkT e2073 = true := by decide +kernel
theorem e2073_pos {a z : ℝ} (ha1 : ((256797/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((642417/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2073 e2073_ok ha1 ha2 hz1 hz2 hz

-- box ['20049/128000', '256797/1638400', '7997/8000', '3999/4000']  interval_lower 178587009/1099511627776
noncomputable def e2074 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271731226411,0,true,159993275200,159993275264⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927292029141,0,false,-187304932224,-187304932160⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271845177263,0,true,160091790272,160091790336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927178078289,0,false,-187440054720,-187440054656⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271666644061,0,true,159937437248,159937437312⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927356611491,0,false,-187228358144,-187228358080⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271802093876,0,true,160054544000,160054544064⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927221161676,0,false,-187388964608,-187388964544⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533544293,0,true,21916288,21916352⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489711259,0,false,-21916736,-21916672⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544525815,0,true,32897536,32897600⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478729737,0,false,-32898560,-32898496⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626791,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627340,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271698930808,0,true,159965352768,159965352832⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927324324744,0,false,-187266639232,-187266639168⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271823639986,0,true,160073171072,160073171136⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927199615566,0,false,-187414514624,-187414514560⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072507429910,0,false,-27341343488,-27341343424⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072546503828,0,false,-27301286464,-27301286400⟩
    { al := (20049/128000), au := (256797/1638400), zl := (7997/8000), zu := (3999/4000),
      A := ⟨172219598635,172333549487⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159993275200,159993275264⟩ : DyadicInterval 40),(⟨-187304932224,-187304932160⟩ : DyadicInterval 40),(⟨748580064561,748580083890⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160091790272,160091790336⟩ : DyadicInterval 40),(⟨-187440054720,-187440054656⟩ : DyadicInterval 40),(⟨748562061918,748562081248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159937437248,159937437312⟩ : DyadicInterval 40),(⟨-187228358144,-187228358080⟩ : DyadicInterval 40),(⟨748590262323,748590281652⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160054544000,160054544064⟩ : DyadicInterval 40),(⟨-187388964608,-187388964544⟩ : DyadicInterval 40),(⟨748568869896,748568889226⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21916517,32898039⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21916288,21916352⟩ : DyadicInterval 40),(⟨-21916736,-21916672⟩ : DyadicInterval 40),(⟨762123383339,762123402668⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32897536,32897600⟩ : DyadicInterval 40),(⟨-32898560,-32898496⟩ : DyadicInterval 40),(⟨762123383079,762123402408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172187303032,172312012210⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159965352768,159965352832⟩ : DyadicInterval 40),(⟨-187266639232,-187266639168⟩ : DyadicInterval 40),(⟨748585164602,748585183931⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160073171072,160073171136⟩ : DyadicInterval 40),(⟨-187414514624,-187414514560⟩ : DyadicInterval 40),(⟨748565465457,748565484787⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27341343488,-27301286400⟩ : DyadicInterval 40),(⟨775774026816,775794074624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159993275200,160091790336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187440054720,-187304932160⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2074_ok : ecellOkT e2074 = true := by decide +kernel
theorem e2074_pos {a z : ℝ} (ha1 : ((20049/128000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((256797/1638400 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2074 e2074_ok ha1 ha2 hz1 hz2 hz

-- box ['256797/1638400', '642417/4096000', '7997/8000', '3999/4000']  interval_lower 2807617/17179869184
noncomputable def e2075 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271845177262,0,true,160091790272,160091790336⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927178078290,0,false,-187440054720,-187440054656⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271959128114,0,true,160190296448,160190296512⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927064127438,0,false,-187575193792,-187575193728⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271780552180,0,true,160035920384,160035920448⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927242703372,0,false,-187363420480,-187363420416⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271916016240,0,true,160153028928,160153028992⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927107239312,0,false,-187524063616,-187524063552⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533559322,0,true,21931264,21931328⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489696230,0,false,-21931776,-21931712⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544548359,0,true,32920064,32920128⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478707193,0,false,-32921088,-32921024⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626790,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627339,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271812860293,0,true,160063851840,160063851904⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927210395259,0,false,-187401731648,-187401731584⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271937576589,0,true,160171666688,160171666752⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927085678963,0,false,-187549633664,-187549633600⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072471706530,0,false,-27377966976,-27377966912⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072510808525,0,false,-27337879808,-27337879744⟩
    { al := (256797/1638400), au := (642417/4096000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨172333549486,172447500338⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160091790272,160091790336⟩ : DyadicInterval 40),(⟨-187440054720,-187440054656⟩ : DyadicInterval 40),(⟨748562061918,748562081248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160190296448,160190296512⟩ : DyadicInterval 40),(⟨-187575193792,-187575193728⟩ : DyadicInterval 40),(⟨748544047196,748544066525⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160035920384,160035920448⟩ : DyadicInterval 40),(⟨-187363420480,-187363420416⟩ : DyadicInterval 40),(⟨748572273257,748572292586⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160153028928,160153028992⟩ : DyadicInterval 40),(⟨-187524063616,-187524063552⟩ : DyadicInterval 40),(⟨748550864232,748550883562⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21931546,32920583⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21931264,21931328⟩ : DyadicInterval 40),(⟨-21931776,-21931712⟩ : DyadicInterval 40),(⟨762123383370,762123402699⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32920064,32920128⟩ : DyadicInterval 40),(⟨-32921088,-32921024⟩ : DyadicInterval 40),(⟨762123383078,762123402407⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172301232517,172425948813⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160063851840,160063851904⟩ : DyadicInterval 40),(⟨-187401731648,-187401731584⟩ : DyadicInterval 40),(⟨748567168768,748567188098⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160171666688,160171666752⟩ : DyadicInterval 40),(⟨-187549633664,-187549633600⟩ : DyadicInterval 40),(⟨748547455227,748547474557⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27377966976,-27337879744⟩ : DyadicInterval 40),(⟨775792323488,775812386368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160091790272,160190296512⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187575193792,-187440054656⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2075_ok : ecellOkT e2075 = true := by decide +kernel
theorem e2075_pos {a z : ℝ} (ha1 : ((256797/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((642417/4096000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2075 e2075_ok ha1 ha2 hz1 hz2 hz

-- box ['642417/4096000', '1285683/8192000', '1999/2000', '7997/8000']  interval_lower 180949609/1099511627776
noncomputable def e2076 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271959128113,0,true,160190296448,160190296512⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927064127439,0,false,-187575193792,-187575193728⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272073078965,0,true,160288793856,160288793920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926950176587,0,false,-187710349440,-187710349376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271872904362,0,true,160115760064,160115760128⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927150351190,0,false,-187472935872,-187472935808⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272008368421,0,true,160232860160,160232860224⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927014887131,0,false,-187633595072,-187633595008⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544547694,0,true,32919424,32919488⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478707858,0,false,-32920448,-32920384⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555551763,0,true,43923072,43923136⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467703789,0,false,-43924928,-43924864⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626021,0,false,-1792,-1728⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626791,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271916011885,0,true,160153025152,160153025216⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927107243667,0,false,-187524058496,-187524058432⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272040728165,0,true,160260831232,160260831296⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926982527387,0,false,-187671976896,-187671976832⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072439344292,0,false,-27411145600,-27411145536⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072478469682,0,false,-27371033280,-27371033216⟩
    { al := (642417/4096000), au := (1285683/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨172447500337,172561451189⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160190296448,160190296512⟩ : DyadicInterval 40),(⟨-187575193792,-187575193728⟩ : DyadicInterval 40),(⟨748544047196,748544066525⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160288793856,160288793920⟩ : DyadicInterval 40),(⟨-187710349440,-187710349376⟩ : DyadicInterval 40),(⟨748526020318,748526039648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160115760064,160115760128⟩ : DyadicInterval 40),(⟨-187472935872,-187472935808⟩ : DyadicInterval 40),(⟨748557679605,748557698935⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160232860160,160232860224⟩ : DyadicInterval 40),(⟨-187633595072,-187633595008⟩ : DyadicInterval 40),(⟨748536258910,748536278240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32919918,43923987⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32919424,32919488⟩ : DyadicInterval 40),(⟨-32920448,-32920384⟩ : DyadicInterval 40),(⟨762123383078,762123402407⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43923072,43923136⟩ : DyadicInterval 40),(⟨-43924928,-43924864⟩ : DyadicInterval 40),(⟨762123382725,762123402054⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1792,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172404384109,172529100389⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160153025152,160153025216⟩ : DyadicInterval 40),(⟨-187524058496,-187524058432⟩ : DyadicInterval 40),(⟨748550864946,748550884275⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160260831232,160260831296⟩ : DyadicInterval 40),(⟨-187671976896,-187671976832⟩ : DyadicInterval 40),(⟨748531139396,748531158725⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27411145600,-27371033216⟩ : DyadicInterval 40),(⟨775808900224,775828975680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160190296448,160288793920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187710349440,-187575193728⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2076_ok : ecellOkT e2076 = true := by decide +kernel
theorem e2076_pos {a z : ℝ} (ha1 : ((642417/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1285683/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2076 e2076_ok ha1 ha2 hz1 hz2 hz

-- box ['1285683/8192000', '321633/2048000', '1999/2000', '7997/8000']  interval_lower 22756965/137438953472
noncomputable def e2077 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272073078964,0,true,160288793856,160288793920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926950176588,0,false,-187710349440,-187710349376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272187029816,0,true,160387282432,160387282496⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926836225736,0,false,-187845521728,-187845521664⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271986798238,0,true,160214214912,160214214976⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927036457314,0,false,-187608011456,-187608011392⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272122276541,0,true,160331316800,160331316864⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926900979011,0,false,-187768707200,-187768707136⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544570240,0,true,32941952,32942016⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478685312,0,false,-32942976,-32942912⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555581827,0,true,43953152,43953216⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467673725,0,false,-43954944,-43954880⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626018,0,false,-1792,-1728⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626790,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272029934248,0,true,160251501248,160251501312⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926993321304,0,false,-187659174080,-187659174016⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272154657653,0,true,160359303872,160359303936⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926868597899,0,false,-187807119104,-187807119040⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072403578154,0,false,-27447815232,-27447815168⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072442731627,0,false,-27407672768,-27407672704⟩
    { al := (1285683/8192000), au := (321633/2048000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨172561451188,172675402040⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160288793856,160288793920⟩ : DyadicInterval 40),(⟨-187710349440,-187710349376⟩ : DyadicInterval 40),(⟨748526020318,748526039648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160387282432,160387282496⟩ : DyadicInterval 40),(⟨-187845521728,-187845521664⟩ : DyadicInterval 40),(⟨748507981349,748508000678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160214214912,160214214976⟩ : DyadicInterval 40),(⟨-187608011456,-187608011392⟩ : DyadicInterval 40),(⟨748539670928,748539690258⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160331316800,160331316864⟩ : DyadicInterval 40),(⟨-187768707200,-187768707136⟩ : DyadicInterval 40),(⟨748518233573,748518252902⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32942464,43954051⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32941952,32942016⟩ : DyadicInterval 40),(⟨-32942976,-32942912⟩ : DyadicInterval 40),(⟨762123383076,762123402406⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43953152,43953216⟩ : DyadicInterval 40),(⟨-43954944,-43954880⟩ : DyadicInterval 40),(⟨762123382690,762123402019⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1792,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172518306472,172643029877⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160251501248,160251501312⟩ : DyadicInterval 40),(⟨-187659174080,-187659174016⟩ : DyadicInterval 40),(⟨748532847177,748532866507⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160359303872,160359303936⟩ : DyadicInterval 40),(⟨-187807119104,-187807119040⟩ : DyadicInterval 40),(⟨748513107223,748513126553⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27447815232,-27407672704⟩ : DyadicInterval 40),(⟨775827219968,775847310496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160288793856,160387282496⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187845521728,-187710349376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2077_ok : ecellOkT e2077 = true := by decide +kernel
theorem e2077_pos {a z : ℝ} (ha1 : ((1285683/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((321633/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2077 e2077_ok ha1 ha2 hz1 hz2 hz

-- box ['642417/4096000', '1285683/8192000', '7997/8000', '3999/4000']  interval_lower 11299419/68719476736
noncomputable def e2078 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271959128113,0,true,160190296448,160190296512⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927064127439,0,false,-187575193792,-187575193728⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272073078965,0,true,160288793856,160288793920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926950176587,0,false,-187710349440,-187710349376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271894460300,0,true,160134394688,160134394752⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927128795252,0,false,-187498499456,-187498499392⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272029938603,0,true,160251505024,160251505088⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926993316949,0,false,-187659179264,-187659179200⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533574352,0,true,21946304,21946368⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489681200,0,false,-21946816,-21946752⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544570906,0,true,32942592,32942656⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478684646,0,false,-32943680,-32943616⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626788,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627338,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271926789773,0,true,160162342080,160162342144⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927096465779,0,false,-187536840704,-187536840640⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272051513195,0,true,160270153408,160270153472⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926971742357,0,false,-187684769280,-187684769216⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072435959535,0,false,-27414615808,-27414615744⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072475089612,0,false,-27374498560,-27374498496⟩
    { al := (642417/4096000), au := (1285683/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨172447500337,172561451189⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160190296448,160190296512⟩ : DyadicInterval 40),(⟨-187575193792,-187575193728⟩ : DyadicInterval 40),(⟨748544047196,748544066525⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160288793856,160288793920⟩ : DyadicInterval 40),(⟨-187710349440,-187710349376⟩ : DyadicInterval 40),(⟨748526020318,748526039648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160134394688,160134394752⟩ : DyadicInterval 40),(⟨-187498499456,-187498499392⟩ : DyadicInterval 40),(⟨748554272120,748554291449⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160251505024,160251505088⟩ : DyadicInterval 40),(⟨-187659179264,-187659179200⟩ : DyadicInterval 40),(⟨748532846489,748532865819⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21946576,32943130⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21946304,21946368⟩ : DyadicInterval 40),(⟨-21946816,-21946752⟩ : DyadicInterval 40),(⟨762123383369,762123402698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32942592,32942656⟩ : DyadicInterval 40),(⟨-32943680,-32943616⟩ : DyadicInterval 40),(⟨762123383108,762123402437⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172415161997,172539885419⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160162342080,160162342144⟩ : DyadicInterval 40),(⟨-187536840704,-187536840640⟩ : DyadicInterval 40),(⟨748549160855,748549180185⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160270153408,160270153472⟩ : DyadicInterval 40),(⟨-187684769280,-187684769216⟩ : DyadicInterval 40),(⟨748529432922,748529452251⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27414615808,-27374498496⟩ : DyadicInterval 40),(⟨775810632864,775830710784⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160190296448,160288793920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187710349440,-187575193728⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2078_ok : ecellOkT e2078 = true := by decide +kernel
theorem e2078_pos {a z : ℝ} (ha1 : ((642417/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1285683/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2078 e2078_ok ha1 ha2 hz1 hz2 hz

-- box ['1285683/8192000', '321633/2048000', '7997/8000', '3999/4000']  interval_lower 90948363/549755813888
noncomputable def e2079 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272073078964,0,true,160288793856,160288793920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926950176588,0,false,-187710349440,-187710349376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272187029816,0,true,160387282432,160387282496⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926836225736,0,false,-187845521728,-187845521664⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272008368419,0,true,160232860160,160232860224⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927014887133,0,false,-187633595072,-187633595008⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272143860966,0,true,160349972352,160349972416⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926879394586,0,false,-187794311488,-187794311424⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533589383,0,true,21961344,21961408⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489666169,0,false,-21961856,-21961792⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544593453,0,true,32965120,32965184⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478662099,0,false,-32966208,-32966144⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626787,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627338,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272040719255,0,true,160260823552,160260823616⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926982536297,0,false,-187671966336,-187671966272⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272165449804,0,true,160368631360,160368631424⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926857805748,0,false,-187819921536,-187819921472⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072400188926,0,false,-27451290176,-27451290112⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072439347089,0,false,-27411142784,-27411142720⟩
    { al := (1285683/8192000), au := (321633/2048000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨172561451188,172675402040⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160288793856,160288793920⟩ : DyadicInterval 40),(⟨-187710349440,-187710349376⟩ : DyadicInterval 40),(⟨748526020318,748526039648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160387282432,160387282496⟩ : DyadicInterval 40),(⟨-187845521728,-187845521664⟩ : DyadicInterval 40),(⟨748507981349,748508000678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160232860160,160232860224⟩ : DyadicInterval 40),(⟨-187633595072,-187633595008⟩ : DyadicInterval 40),(⟨748536258910,748536278240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160349972352,160349972416⟩ : DyadicInterval 40),(⟨-187794311488,-187794311424⟩ : DyadicInterval 40),(⟨748514816602,748514835932⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21961607,32965677⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21961344,21961408⟩ : DyadicInterval 40),(⟨-21961856,-21961792⟩ : DyadicInterval 40),(⟨762123383369,762123402698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32965120,32965184⟩ : DyadicInterval 40),(⟨-32966208,-32966144⟩ : DyadicInterval 40),(⟨762123383107,762123402436⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172529091479,172653822028⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160260823552,160260823616⟩ : DyadicInterval 40),(⟨-187671966336,-187671966272⟩ : DyadicInterval 40),(⟨748531140796,748531160126⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160368631360,160368631424⟩ : DyadicInterval 40),(⟨-187819921536,-187819921472⟩ : DyadicInterval 40),(⟨748511398493,748511417822⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27451290176,-27411142720⟩ : DyadicInterval 40),(⟨775828954976,775849047968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160288793856,160387282496⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187845521728,-187710349376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2079_ok : ecellOkT e2079 = true := by decide +kernel
theorem e2079_pos {a z : ℝ} (ha1 : ((1285683/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((321633/2048000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2079 e2079_ok ha1 ha2 hz1 hz2 hz

-- box ['20049/128000', '256797/1638400', '3999/4000', '7999/8000']  interval_lower 178428955/1099511627776
noncomputable def e2080 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271731226411,0,true,159993275200,159993275264⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927292029141,0,false,-187304932224,-187304932160⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271845177263,0,true,160091790272,160091790336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927178078289,0,false,-187440054720,-187440054656⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271688171511,0,true,159956050240,159956050304⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927335084041,0,false,-187253882240,-187253882176⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271823635570,0,true,160073167296,160073167360⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927199619982,0,false,-187414509376,-187414509312⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522585930,0,true,10958080,10958144⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500669622,0,false,-10958272,-10958208⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533559937,0,true,21931904,21931968⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489695615,0,false,-21932416,-21932352⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627338,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627667,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271709694475,0,true,159974659008,159974659072⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927313561077,0,false,-187279401600,-187279401536⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271834410795,0,true,160082482560,160082482624⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927188844757,0,false,-187427287168,-187427287104⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072504053870,0,false,-27344804544,-27344804480⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072543132468,0,false,-27304742592,-27304742528⟩
    { al := (20049/128000), au := (256797/1638400), zl := (3999/4000), zu := (7999/8000),
      A := ⟨172219598635,172333549487⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159993275200,159993275264⟩ : DyadicInterval 40),(⟨-187304932224,-187304932160⟩ : DyadicInterval 40),(⟨748580064561,748580083890⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160091790272,160091790336⟩ : DyadicInterval 40),(⟨-187440054720,-187440054656⟩ : DyadicInterval 40),(⟨748562061918,748562081248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159956050240,159956050304⟩ : DyadicInterval 40),(⟨-187253882240,-187253882176⟩ : DyadicInterval 40),(⟨748586863484,748586882813⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160073167296,160073167360⟩ : DyadicInterval 40),(⟨-187414509376,-187414509312⟩ : DyadicInterval 40),(⟨748565466126,748565485455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10958154,21932161⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10958080,10958144⟩ : DyadicInterval 40),(⟨-10958272,-10958208⟩ : DyadicInterval 40),(⟨762123383538,762123402867⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21931904,21931968⟩ : DyadicInterval 40),(⟨-21932416,-21932352⟩ : DyadicInterval 40),(⟨762123383370,762123402699⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172198066699,172322783019⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159974659008,159974659072⟩ : DyadicInterval 40),(⟨-187279401600,-187279401536⟩ : DyadicInterval 40),(⟨748583464934,748583484264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160082482560,160082482624⟩ : DyadicInterval 40),(⟨-187427287168,-187427287104⟩ : DyadicInterval 40),(⟨748563763413,748563782742⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27344804544,-27304742528⟩ : DyadicInterval 40),(⟨775775754880,775795805152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159993275200,160091790336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187440054720,-187304932160⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2080_ok : ecellOkT e2080 = true := by decide +kernel
theorem e2080_pos {a z : ℝ} (ha1 : ((20049/128000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((256797/1638400 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2080 e2080_ok ha1 ha2 hz1 hz2 hz

-- box ['256797/1638400', '642417/4096000', '3999/4000', '7999/8000']  interval_lower 89764467/549755813888
noncomputable def e2081 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271845177262,0,true,160091790272,160091790336⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927178078290,0,false,-187440054720,-187440054656⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271959128114,0,true,160190296448,160190296512⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927064127438,0,false,-187575193792,-187575193728⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271802093874,0,true,160054544000,160054544064⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927221161678,0,false,-187388964608,-187388964544⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271937572177,0,true,160171662848,160171662912⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927085683375,0,false,-187549628416,-187549628352⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522593445,0,true,10965568,10965632⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500662107,0,false,-10965760,-10965696⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533574967,0,true,21946944,21947008⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489680585,0,false,-21947456,-21947392⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627337,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627667,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271823631081,0,true,160073163392,160073163456⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927199624471,0,false,-187414504064,-187414504000⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271948354519,0,true,160180983488,160180983552⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927074901033,0,false,-187562416192,-187562416128⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072468326023,0,false,-27381432704,-27381432640⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072507432702,0,false,-27341340608,-27341340544⟩
    { al := (256797/1638400), au := (642417/4096000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨172333549486,172447500338⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160091790272,160091790336⟩ : DyadicInterval 40),(⟨-187440054720,-187440054656⟩ : DyadicInterval 40),(⟨748562061918,748562081248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160190296448,160190296512⟩ : DyadicInterval 40),(⟨-187575193792,-187575193728⟩ : DyadicInterval 40),(⟨748544047196,748544066525⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160054544000,160054544064⟩ : DyadicInterval 40),(⟨-187388964608,-187388964544⟩ : DyadicInterval 40),(⟨748568869897,748568889226⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160171662848,160171662912⟩ : DyadicInterval 40),(⟨-187549628416,-187549628352⟩ : DyadicInterval 40),(⟨748547455933,748547475263⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10965669,21947191⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10965568,10965632⟩ : DyadicInterval 40),(⟨-10965760,-10965696⟩ : DyadicInterval 40),(⟨762123383538,762123402867⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21946944,21947008⟩ : DyadicInterval 40),(⟨-21947456,-21947392⟩ : DyadicInterval 40),(⟨762123383369,762123402698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172312003305,172436726743⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160073163392,160073163456⟩ : DyadicInterval 40),(⟨-187414504064,-187414504000⟩ : DyadicInterval 40),(⟨748565466854,748565486183⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160180983488,160180983552⟩ : DyadicInterval 40),(⟨-187562416192,-187562416128⟩ : DyadicInterval 40),(⟨748545750905,748545770234⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27381432704,-27341340544⟩ : DyadicInterval 40),(⟨775794053888,775814119232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160091790272,160190296512⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187575193792,-187440054656⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2081_ok : ecellOkT e2081 = true := by decide +kernel
theorem e2081_pos {a z : ℝ} (ha1 : ((256797/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((642417/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2081 e2081_ok ha1 ha2 hz1 hz2 hz

-- box ['20049/128000', '256797/1638400', '7999/8000', '1']  interval_lower 178270625/1099511627776
noncomputable def e2082 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271731226411,0,true,159993275200,159993275264⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927292029141,0,false,-187304932224,-187304932160⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271845177263,0,true,160091790272,160091790336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927178078289,0,false,-187440054720,-187440054656⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271709698961,0,true,159974662848,159974662912⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927313556591,0,false,-187279406912,-187279406848⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522594010,0,true,10966144,10966208⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500661542,0,false,-10966336,-10966272⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627666,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1271720458163,0,true,159983965120,159983965184⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨927302797389,0,false,-187292164160,-187292164096⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1271845181629,0,true,160091794048,160091794112⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨927178073923,0,false,-187440059904,-187440059840⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1072500677611,0,false,-27348265856,-27348265792⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1072539760891,0,false,-27308198976,-27308198912⟩
    { al := (20049/128000), au := (256797/1638400), zl := (7999/8000), zu := 1,
      A := ⟨172219598635,172333549487⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159993275200,159993275264⟩ : DyadicInterval 40),(⟨-187304932224,-187304932160⟩ : DyadicInterval 40),(⟨748580064561,748580083890⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160091790272,160091790336⟩ : DyadicInterval 40),(⟨-187440054720,-187440054656⟩ : DyadicInterval 40),(⟨748562061918,748562081248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159974662848,159974662912⟩ : DyadicInterval 40),(⟨-187279406912,-187279406848⟩ : DyadicInterval 40),(⟨748583464245,748583483575⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160091790272,160091790336⟩ : DyadicInterval 40),(⟨-187440054720,-187440054656⟩ : DyadicInterval 40),(⟨748562061918,748562081248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10966234⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10966144,10966208⟩ : DyadicInterval 40),(⟨-10966336,-10966272⟩ : DyadicInterval 40),(⟨762123383538,762123402867⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨172208830387,172333553853⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159983965120,159983965184⟩ : DyadicInterval 40),(⟨-187292164160,-187292164096⟩ : DyadicInterval 40),(⟨748581765203,748581784532⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160091794048,160091794112⟩ : DyadicInterval 40),(⟨-187440059904,-187440059840⟩ : DyadicInterval 40),(⟨748562061230,748562080559⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27348265856,-27308198912⟩ : DyadicInterval 40),(⟨775777483072,775797535808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨159993275200,160091790336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187440054720,-187304932160⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2082_ok : ecellOkT e2082 = true := by decide +kernel
theorem e2082_pos {a z : ℝ} (ha1 : ((20049/128000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((256797/1638400 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2082 e2082_ok ha1 ha2 hz1 hz2 hz

-- box ['256797/1638400', '642417/4096000', '7999/8000', '1']  interval_lower 179370413/1099511627776
noncomputable def e2083 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271845177262,0,true,160091790272,160091790336⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927178078290,0,false,-187440054720,-187440054656⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271959128114,0,true,160190296448,160190296512⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927064127438,0,false,-187575193792,-187575193728⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271823635568,0,true,160073167296,160073167360⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927199619984,0,false,-187414509376,-187414509312⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522601525,0,true,10973632,10973696⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500654027,0,false,-10973824,-10973760⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627666,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1271834401890,0,true,160082474880,160082474944⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨927188853662,0,false,-187427276608,-187427276544⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1271959132473,0,true,160190300224,160190300288⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨927064123079,0,false,-187575198912,-187575198848⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1072464945299,0,false,-27384898688,-27384898624⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1072504056662,0,false,-27344801664,-27344801600⟩
    { al := (256797/1638400), au := (642417/4096000), zl := (7999/8000), zu := 1,
      A := ⟨172333549486,172447500338⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160091790272,160091790336⟩ : DyadicInterval 40),(⟨-187440054720,-187440054656⟩ : DyadicInterval 40),(⟨748562061918,748562081248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160190296448,160190296512⟩ : DyadicInterval 40),(⟨-187575193792,-187575193728⟩ : DyadicInterval 40),(⟨748544047196,748544066525⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160073167296,160073167360⟩ : DyadicInterval 40),(⟨-187414509376,-187414509312⟩ : DyadicInterval 40),(⟨748565466127,748565485456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160190296448,160190296512⟩ : DyadicInterval 40),(⟨-187575193792,-187575193728⟩ : DyadicInterval 40),(⟨748544047196,748544066525⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10973749⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10973632,10973696⟩ : DyadicInterval 40),(⟨-10973824,-10973760⟩ : DyadicInterval 40),(⟨762123383538,762123402867⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨172322774114,172447504697⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160082474880,160082474944⟩ : DyadicInterval 40),(⟨-187427276608,-187427276544⟩ : DyadicInterval 40),(⟨748563764810,748563784139⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160190300224,160190300288⟩ : DyadicInterval 40),(⟨-187575198912,-187575198848⟩ : DyadicInterval 40),(⟨748544046481,748544065810⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27384898688,-27344801600⟩ : DyadicInterval 40),(⟨775795784416,775815852224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨160091790272,160190296512⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187575193792,-187440054656⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2083_ok : ecellOkT e2083 = true := by decide +kernel
theorem e2083_pos {a z : ℝ} (ha1 : ((256797/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((642417/4096000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2083 e2083_ok ha1 ha2 hz1 hz2 hz

-- box ['642417/4096000', '1285683/8192000', '3999/4000', '7999/8000']  interval_lower 45157919/274877906944
noncomputable def e2084 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271959128113,0,true,160190296448,160190296512⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927064127439,0,false,-187575193792,-187575193728⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272073078965,0,true,160288793856,160288793920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926950176587,0,false,-187710349440,-187710349376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271916016237,0,true,160153028928,160153028992⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927107239315,0,false,-187524063616,-187524063552⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272051508784,0,true,160270149632,160270149696⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926971746768,0,false,-187684764032,-187684763968⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522600960,0,true,10973120,10973184⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500654592,0,false,-10973248,-10973184⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533589998,0,true,21961984,21962048⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489665554,0,false,-21962496,-21962432⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627337,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627667,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271937567681,0,true,160171658944,160171659008⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927085687871,0,false,-187549623104,-187549623040⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272062298253,0,true,160279475584,160279475648⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926960957299,0,false,-187697561856,-187697561792⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072432574558,0,false,-27418086272,-27418086208⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072471709324,0,false,-27377964096,-27377964032⟩
    { al := (642417/4096000), au := (1285683/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨172447500337,172561451189⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160190296448,160190296512⟩ : DyadicInterval 40),(⟨-187575193792,-187575193728⟩ : DyadicInterval 40),(⟨748544047196,748544066525⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160288793856,160288793920⟩ : DyadicInterval 40),(⟨-187710349440,-187710349376⟩ : DyadicInterval 40),(⟨748526020318,748526039648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160153028928,160153028992⟩ : DyadicInterval 40),(⟨-187524063616,-187524063552⟩ : DyadicInterval 40),(⟨748550864232,748550883562⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160270149632,160270149696⟩ : DyadicInterval 40),(⟨-187684764032,-187684763968⟩ : DyadicInterval 40),(⟨748529433592,748529452921⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10973184,21962222⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10973120,10973184⟩ : DyadicInterval 40),(⟨-10973248,-10973184⟩ : DyadicInterval 40),(⟨762123383506,762123402835⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21961984,21962048⟩ : DyadicInterval 40),(⟨-21962496,-21962432⟩ : DyadicInterval 40),(⟨762123383369,762123402698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172425939905,172550670477⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160171658944,160171659008⟩ : DyadicInterval 40),(⟨-187549623104,-187549623040⟩ : DyadicInterval 40),(⟨748547456663,748547475992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160279475584,160279475648⟩ : DyadicInterval 40),(⟨-187697561856,-187697561792⟩ : DyadicInterval 40),(⟨748527726308,748527745637⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27418086272,-27377964032⟩ : DyadicInterval 40),(⟨775812365632,775832446016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160190296448,160288793920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187710349440,-187575193728⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2084_ok : ecellOkT e2084 = true := by decide +kernel
theorem e2084_pos {a z : ℝ} (ha1 : ((642417/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1285683/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2084 e2084_ok ha1 ha2 hz1 hz2 hz

-- box ['1285683/8192000', '321633/2048000', '3999/4000', '7999/8000']  interval_lower 90868665/549755813888
noncomputable def e2085 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272073078964,0,true,160288793856,160288793920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926950176588,0,false,-187710349440,-187710349376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272187029816,0,true,160387282432,160387282496⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926836225736,0,false,-187845521728,-187845521664⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272029938601,0,true,160251505024,160251505088⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926993316951,0,false,-187659179264,-187659179200⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272165445391,0,true,160368627584,160368627648⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926857810161,0,false,-187819916288,-187819916224⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522608476,0,true,10980608,10980672⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500647076,0,false,-10980800,-10980736⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533605030,0,true,21977024,21977088⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489650522,0,false,-21977536,-21977472⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627336,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627667,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272051504284,0,true,160270145728,160270145792⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926971751268,0,false,-187684758720,-187684758656⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272176241983,0,true,160377958848,160377958912⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926847013569,0,false,-187832724160,-187832724096⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072396799477,0,false,-27454765312,-27454765248⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072435962333,0,false,-27414612992,-27414612928⟩
    { al := (1285683/8192000), au := (321633/2048000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨172561451188,172675402040⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160288793856,160288793920⟩ : DyadicInterval 40),(⟨-187710349440,-187710349376⟩ : DyadicInterval 40),(⟨748526020318,748526039648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160387282432,160387282496⟩ : DyadicInterval 40),(⟨-187845521728,-187845521664⟩ : DyadicInterval 40),(⟨748507981349,748508000678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160251505024,160251505088⟩ : DyadicInterval 40),(⟨-187659179264,-187659179200⟩ : DyadicInterval 40),(⟨748532846489,748532865819⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160368627584,160368627648⟩ : DyadicInterval 40),(⟨-187819916288,-187819916224⟩ : DyadicInterval 40),(⟨748511399164,748511418493⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10980700,21977254⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10980608,10980672⟩ : DyadicInterval 40),(⟨-10980800,-10980736⟩ : DyadicInterval 40),(⟨762123383538,762123402867⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21977024,21977088⟩ : DyadicInterval 40),(⟨-21977536,-21977472⟩ : DyadicInterval 40),(⟨762123383368,762123402697⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172539876508,172664614207⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160270145728,160270145792⟩ : DyadicInterval 40),(⟨-187684758720,-187684758656⟩ : DyadicInterval 40),(⟨748529434323,748529453652⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160377958848,160377958912⟩ : DyadicInterval 40),(⟨-187832724160,-187832724096⟩ : DyadicInterval 40),(⟨748509689621,748509708951⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27454765312,-27414612928⟩ : DyadicInterval 40),(⟨775830690080,775850785536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160288793856,160387282496⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187845521728,-187710349376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2085_ok : ecellOkT e2085 = true := by decide +kernel
theorem e2085_pos {a z : ℝ} (ha1 : ((1285683/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((321633/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2085 e2085_ok ha1 ha2 hz1 hz2 hz

-- box ['642417/4096000', '1285683/8192000', '7999/8000', '1']  interval_lower 45118235/274877906944
noncomputable def e2086 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271959128113,0,true,160190296448,160190296512⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927064127439,0,false,-187575193792,-187575193728⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272073078965,0,true,160288793856,160288793920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926950176587,0,false,-187710349440,-187710349376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271937572175,0,true,160171662848,160171662912⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927085683377,0,false,-187549628416,-187549628352⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522609041,0,true,10981184,10981248⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500646511,0,false,-10981376,-10981312⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627666,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1271948345612,0,true,160180975808,160180975872⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨927074909940,0,false,-187562405632,-187562405568⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1272073083328,0,true,160288797632,160288797696⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨926950172224,0,false,-187710354624,-187710354560⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1072429189364,0,false,-27421556928,-27421556864⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1072468328818,0,false,-27381429824,-27381429760⟩
    { al := (642417/4096000), au := (1285683/8192000), zl := (7999/8000), zu := 1,
      A := ⟨172447500337,172561451189⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160190296448,160190296512⟩ : DyadicInterval 40),(⟨-187575193792,-187575193728⟩ : DyadicInterval 40),(⟨748544047196,748544066525⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160288793856,160288793920⟩ : DyadicInterval 40),(⟨-187710349440,-187710349376⟩ : DyadicInterval 40),(⟨748526020318,748526039648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160171662848,160171662912⟩ : DyadicInterval 40),(⟨-187549628416,-187549628352⟩ : DyadicInterval 40),(⟨748547455934,748547475263⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160288793856,160288793920⟩ : DyadicInterval 40),(⟨-187710349440,-187710349376⟩ : DyadicInterval 40),(⟨748526020318,748526039648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10981265⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10981184,10981248⟩ : DyadicInterval 40),(⟨-10981376,-10981312⟩ : DyadicInterval 40),(⟨762123383538,762123402867⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨172436717836,172561455552⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160180975808,160180975872⟩ : DyadicInterval 40),(⟨-187562405632,-187562405568⟩ : DyadicInterval 40),(⟨748545752304,748545771634⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160288797632,160288797696⟩ : DyadicInterval 40),(⟨-187710354624,-187710354560⟩ : DyadicInterval 40),(⟨748526019629,748526038958⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27421556928,-27381429760⟩ : DyadicInterval 40),(⟨775814098496,775834181344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨160190296448,160288793920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187710349440,-187575193728⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2086_ok : ecellOkT e2086 = true := by decide +kernel
theorem e2086_pos {a z : ℝ} (ha1 : ((642417/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1285683/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2086 e2086_ok ha1 ha2 hz1 hz2 hz

-- box ['1285683/8192000', '321633/2048000', '7999/8000', '1']  interval_lower 181578001/1099511627776
noncomputable def e2087 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272073078964,0,true,160288793856,160288793920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926950176588,0,false,-187710349440,-187710349376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272187029816,0,true,160387282432,160387282496⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926836225736,0,false,-187845521728,-187845521664⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272051508782,0,true,160270149632,160270149696⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926971746770,0,false,-187684764032,-187684763968⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522616557,0,true,10988672,10988736⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500638995,0,false,-10988864,-10988800⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627666,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1272062289343,0,true,160279467840,160279467904⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨926960966209,0,false,-187697551296,-187697551232⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1272187034179,0,true,160387286208,160387286272⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨926836221373,0,false,-187845526912,-187845526848⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1072393409811,0,false,-27458240640,-27458240576⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1072432577355,0,false,-27418083392,-27418083328⟩
    { al := (1285683/8192000), au := (321633/2048000), zl := (7999/8000), zu := 1,
      A := ⟨172561451188,172675402040⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160288793856,160288793920⟩ : DyadicInterval 40),(⟨-187710349440,-187710349376⟩ : DyadicInterval 40),(⟨748526020318,748526039648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160387282432,160387282496⟩ : DyadicInterval 40),(⟨-187845521728,-187845521664⟩ : DyadicInterval 40),(⟨748507981349,748508000678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160270149632,160270149696⟩ : DyadicInterval 40),(⟨-187684764032,-187684763968⟩ : DyadicInterval 40),(⟨748529433592,748529452921⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160387282432,160387282496⟩ : DyadicInterval 40),(⟨-187845521728,-187845521664⟩ : DyadicInterval 40),(⟨748507981349,748508000678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10988781⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10988672,10988736⟩ : DyadicInterval 40),(⟨-10988864,-10988800⟩ : DyadicInterval 40),(⟨762123383538,762123402867⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨172550661567,172675406403⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160279467840,160279467904⟩ : DyadicInterval 40),(⟨-187697551296,-187697551232⟩ : DyadicInterval 40),(⟨748527727746,748527747075⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160387286208,160387286272⟩ : DyadicInterval 40),(⟨-187845526912,-187845526848⟩ : DyadicInterval 40),(⟨748507980658,748507999987⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27458240640,-27418083328⟩ : DyadicInterval 40),(⟨775832425280,775852523200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨160288793856,160387282496⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187845521728,-187710349376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2087_ok : ecellOkT e2087 = true := by decide +kernel
theorem e2087_pos {a z : ℝ} (ha1 : ((1285683/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((321633/2048000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2087 e2087_ok ha1 ha2 hz1 hz2 hz

-- box ['321633/2048000', '1287381/8192000', '1999/2000', '7997/8000']  interval_lower 183164919/1099511627776
noncomputable def e2088 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272187029815,0,true,160387282432,160387282496⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926836225737,0,false,-187845521728,-187845521664⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272300980667,0,true,160485762240,160485762304⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926722274885,0,false,-187980710656,-187980710592⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272100692113,0,true,160312660928,160312660992⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926922563439,0,false,-187743103552,-187743103488⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272236184660,0,true,160429764672,160429764736⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926787070892,0,false,-187903836032,-187903835968⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544592787,0,true,32964480,32964544⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478662765,0,false,-32965568,-32965504⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555611893,0,true,43983232,43983296⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467643659,0,false,-43985024,-43984960⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626016,0,false,-1792,-1728⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626788,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272143856611,0,true,160349968576,160349968640⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926879398941,0,false,-187794306304,-187794306240⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272268587141,0,true,160457767680,160457767744⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926754668411,0,false,-187942277952,-187942277888⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072367788406,0,false,-27484510272,-27484510208⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072406969963,0,false,-27444337728,-27444337664⟩
    { al := (321633/2048000), au := (1287381/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨172675402039,172789352891⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160387282432,160387282496⟩ : DyadicInterval 40),(⟨-187845521728,-187845521664⟩ : DyadicInterval 40),(⟨748507981349,748508000678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160485762240,160485762304⟩ : DyadicInterval 40),(⟨-187980710656,-187980710592⟩ : DyadicInterval 40),(⟨748489930248,748489949578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160312660928,160312660992⟩ : DyadicInterval 40),(⟨-187743103552,-187743103488⟩ : DyadicInterval 40),(⟨748521650130,748521669460⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160429764672,160429764736⟩ : DyadicInterval 40),(⟨-187903836032,-187903835968⟩ : DyadicInterval 40),(⟨748500196151,748500215481⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32965011,43984117⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32964480,32964544⟩ : DyadicInterval 40),(⟨-32965568,-32965504⟩ : DyadicInterval 40),(⟨762123383107,762123402436⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43983232,43983296⟩ : DyadicInterval 40),(⟨-43985024,-43984960⟩ : DyadicInterval 40),(⟨762123382688,762123402017⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1792,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172632228835,172756959365⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160349968576,160349968640⟩ : DyadicInterval 40),(⟨-187794306304,-187794306240⟩ : DyadicInterval 40),(⟨748514817291,748514836621⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160457767680,160457767744⟩ : DyadicInterval 40),(⟨-187942277952,-187942277888⟩ : DyadicInterval 40),(⟨748495062967,748495082297⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27484510272,-27444337664⟩ : DyadicInterval 40),(⟨775845552448,775865658016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160387282432,160485762304⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187980710656,-187845521664⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2088_ok : ecellOkT e2088 = true := by decide +kernel
theorem e2088_pos {a z : ℝ} (ha1 : ((321633/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1287381/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2088 e2088_ok ha1 ha2 hz1 hz2 hz

-- box ['1287381/8192000', '128823/819200', '1999/2000', '7997/8000']  interval_lower 11517307/68719476736
noncomputable def e2089 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272300980666,0,true,160485762240,160485762304⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926722274886,0,false,-187980710656,-187980710592⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272414931518,0,true,160584233152,160584233216⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926608324034,0,false,-188115916224,-188115916160⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272214585989,0,true,160411098176,160411098240⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926808669563,0,false,-187878212288,-187878212224⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272350092780,0,true,160528203648,160528203712⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926673162772,0,false,-188038981376,-188038981312⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544615336,0,true,32987008,32987072⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478640216,0,false,-32988096,-32988032⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555641961,0,true,44013248,44013312⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467613591,0,false,-44015104,-44015040⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626014,0,false,-1792,-1728⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626787,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272257778977,0,true,160448427072,160448427136⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926765476575,0,false,-187929455104,-187929455040⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272382516622,0,true,160556222656,160556222720⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926640738930,0,false,-188077453440,-188077453376⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072331975050,0,false,-27521230784,-27521230720⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072371184692,0,false,-27481028032,-27481027968⟩
    { al := (1287381/8192000), au := (128823/819200), zl := (1999/2000), zu := (7997/8000),
      A := ⟨172789352890,172903303742⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160485762240,160485762304⟩ : DyadicInterval 40),(⟨-187980710656,-187980710592⟩ : DyadicInterval 40),(⟨748489930248,748489949578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160584233152,160584233216⟩ : DyadicInterval 40),(⟨-188115916224,-188115916160⟩ : DyadicInterval 40),(⟨748471867090,748471886419⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160411098176,160411098240⟩ : DyadicInterval 40),(⟨-187878212288,-187878212224⟩ : DyadicInterval 40),(⟨748503617227,748503636556⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160528203648,160528203712⟩ : DyadicInterval 40),(⟨-188038981376,-188038981312⟩ : DyadicInterval 40),(⟨748482146637,748482165967⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32987560,44014185⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32987008,32987072⟩ : DyadicInterval 40),(⟨-32988096,-32988032⟩ : DyadicInterval 40),(⟨762123383106,762123402435⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44013248,44013312⟩ : DyadicInterval 40),(⟨-44015104,-44015040⟩ : DyadicInterval 40),(⟨762123382718,762123402047⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1792,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172746151201,172870888846⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160448427072,160448427136⟩ : DyadicInterval 40),(⟨-187929455104,-187929455040⟩ : DyadicInterval 40),(⟨748496775297,748496794627⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160556222656,160556222720⟩ : DyadicInterval 40),(⟨-188077453440,-188077453376⟩ : DyadicInterval 40),(⟨748477006627,748477025956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27521230784,-27481027968⟩ : DyadicInterval 40),(⟨775863897600,775884018272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160485762240,160584233216⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188115916224,-187980710592⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2089_ok : ecellOkT e2089 = true := by decide +kernel
theorem e2089_pos {a z : ℝ} (ha1 : ((1287381/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((128823/819200 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2089 e2089_ok ha1 ha2 hz1 hz2 hz

-- box ['321633/2048000', '1287381/8192000', '7997/8000', '3999/4000']  interval_lower 183005085/1099511627776
noncomputable def e2090 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272187029815,0,true,160387282432,160387282496⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926836225737,0,false,-187845521728,-187845521664⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272300980667,0,true,160485762240,160485762304⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926722274885,0,false,-187980710656,-187980710592⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272122276539,0,true,160331316800,160331316864⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926900979013,0,false,-187768707200,-187768707136⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272257783329,0,true,160448430848,160448430912⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926765472223,0,false,-187929460288,-187929460224⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533604415,0,true,21976384,21976448⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489651137,0,false,-21976896,-21976832⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544616003,0,true,32987712,32987776⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478639549,0,false,-32988736,-32988672⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626786,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627337,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272154648740,0,true,160359296128,160359296192⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926868606812,0,false,-187807108544,-187807108480⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272279386415,0,true,160467100480,160467100544⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926743869137,0,false,-187955090432,-187955090368⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072364394703,0,false,-27487989888,-27487989824⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072403580954,0,false,-27447812352,-27447812288⟩
    { al := (321633/2048000), au := (1287381/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨172675402039,172789352891⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160387282432,160387282496⟩ : DyadicInterval 40),(⟨-187845521728,-187845521664⟩ : DyadicInterval 40),(⟨748507981349,748508000678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160485762240,160485762304⟩ : DyadicInterval 40),(⟨-187980710656,-187980710592⟩ : DyadicInterval 40),(⟨748489930248,748489949578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160331316800,160331316864⟩ : DyadicInterval 40),(⟨-187768707200,-187768707136⟩ : DyadicInterval 40),(⟨748518233574,748518252903⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160448430848,160448430912⟩ : DyadicInterval 40),(⟨-187929460288,-187929460224⟩ : DyadicInterval 40),(⟨748496774608,748496793937⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21976639,32988227⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21976384,21976448⟩ : DyadicInterval 40),(⟨-21976896,-21976832⟩ : DyadicInterval 40),(⟨762123383368,762123402697⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32987712,32987776⟩ : DyadicInterval 40),(⟨-32988736,-32988672⟩ : DyadicInterval 40),(⟨762123383074,762123402403⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172643020964,172767758639⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160359296128,160359296192⟩ : DyadicInterval 40),(⟨-187807108544,-187807108480⟩ : DyadicInterval 40),(⟨748513108664,748513127993⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160467100480,160467100544⟩ : DyadicInterval 40),(⟨-187955090432,-187955090368⟩ : DyadicInterval 40),(⟨748493351976,748493371306⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27487989888,-27447812288⟩ : DyadicInterval 40),(⟨775847289760,775867397824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160387282432,160485762304⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187980710656,-187845521664⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2090_ok : ecellOkT e2090 = true := by decide +kernel
theorem e2090_pos {a z : ℝ} (ha1 : ((321633/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1287381/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2090 e2090_ok ha1 ha2 hz1 hz2 hz

-- box ['1287381/8192000', '128823/819200', '7997/8000', '3999/4000']  interval_lower 23014583/137438953472
noncomputable def e2091 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272300980666,0,true,160485762240,160485762304⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926722274886,0,false,-187980710656,-187980710592⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272414931518,0,true,160584233152,160584233216⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926608324034,0,false,-188115916224,-188115916160⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272236184658,0,true,160429764608,160429764672⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926787070894,0,false,-187903836032,-187903835968⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272371705693,0,true,160546880512,160546880576⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926651549859,0,false,-188064625728,-188064625664⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533619448,0,true,21991424,21991488⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489636104,0,false,-21991936,-21991872⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544638555,0,true,33010240,33010304⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478616997,0,false,-33011328,-33011264⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626784,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627337,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272268578221,0,true,160457759936,160457760000⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926754677331,0,false,-187942267392,-187942267328⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272393323020,0,true,160565560768,160565560832⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926629932532,0,false,-188090275904,-188090275840⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072328576869,0,false,-27524715072,-27524715008⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072367791210,0,false,-27484507392,-27484507328⟩
    { al := (1287381/8192000), au := (128823/819200), zl := (7997/8000), zu := (3999/4000),
      A := ⟨172789352890,172903303742⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160485762240,160485762304⟩ : DyadicInterval 40),(⟨-187980710656,-187980710592⟩ : DyadicInterval 40),(⟨748489930248,748489949578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160584233152,160584233216⟩ : DyadicInterval 40),(⟨-188115916224,-188115916160⟩ : DyadicInterval 40),(⟨748471867090,748471886419⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160429764608,160429764672⟩ : DyadicInterval 40),(⟨-187903836032,-187903835968⟩ : DyadicInterval 40),(⟨748500196189,748500215518⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160546880512,160546880576⟩ : DyadicInterval 40),(⟨-188064625728,-188064625664⟩ : DyadicInterval 40),(⟨748478720531,748478739860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21991672,33010779⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21991424,21991488⟩ : DyadicInterval 40),(⟨-21991936,-21991872⟩ : DyadicInterval 40),(⟨762123383368,762123402697⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33010240,33010304⟩ : DyadicInterval 40),(⟨-33011328,-33011264⟩ : DyadicInterval 40),(⟨762123383104,762123402433⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172756950445,172881695244⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160457759936,160457760000⟩ : DyadicInterval 40),(⟨-187942267392,-187942267328⟩ : DyadicInterval 40),(⟨748495064411,748495083740⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160565560768,160565560832⟩ : DyadicInterval 40),(⟨-188090275904,-188090275840⟩ : DyadicInterval 40),(⟨748475293345,748475312675⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27524715072,-27484507328⟩ : DyadicInterval 40),(⟨775865637280,775885760416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160485762240,160584233216⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188115916224,-187980710592⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2091_ok : ecellOkT e2091 = true := by decide +kernel
theorem e2091_pos {a z : ℝ} (ha1 : ((1287381/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((128823/819200 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2091 e2091_ok ha1 ha2 hz1 hz2 hz

-- box ['128823/819200', '1289079/8192000', '1999/2000', '7997/8000']  interval_lower 185391421/1099511627776
noncomputable def e2092 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272414931517,0,true,160584233152,160584233216⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926608324035,0,false,-188115916224,-188115916160⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272528882369,0,true,160682695296,160682695360⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926494373183,0,false,-188251138368,-188251138304⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272328479865,0,true,160509526528,160509526592⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926694775687,0,false,-188013337664,-188013337600⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272464000899,0,true,160626633856,160626633920⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926559254653,0,false,-188174143424,-188174143360⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544637888,0,true,33009600,33009664⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478617664,0,false,-33010624,-33010560⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555672031,0,true,44043328,44043392⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467583521,0,false,-44045184,-44045120⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626011,0,false,-1792,-1728⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626785,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272371701331,0,true,160546876736,160546876800⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926651554221,0,false,-188064620544,-188064620480⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272496446107,0,true,160654668800,160654668864⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926526809445,0,false,-188212645504,-188212645440⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072296138083,0,false,-27557976704,-27557976640⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072335375816,0,false,-27517743808,-27517743744⟩
    { al := (128823/819200), au := (1289079/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨172903303741,173017254593⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160584233152,160584233216⟩ : DyadicInterval 40),(⟨-188115916224,-188115916160⟩ : DyadicInterval 40),(⟨748471867090,748471886419⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160682695296,160682695360⟩ : DyadicInterval 40),(⟨-188251138368,-188251138304⟩ : DyadicInterval 40),(⟨748453791772,748453811101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160509526528,160509526592⟩ : DyadicInterval 40),(⟨-188013337664,-188013337600⟩ : DyadicInterval 40),(⟨748485572290,748485591619⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160626633856,160626633920⟩ : DyadicInterval 40),(⟨-188174143424,-188174143360⟩ : DyadicInterval 40),(⟨748464085035,748464104365⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33010112,44044255⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33009600,33009664⟩ : DyadicInterval 40),(⟨-33010624,-33010560⟩ : DyadicInterval 40),(⟨762123383072,762123402401⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44043328,44043392⟩ : DyadicInterval 40),(⟨-44045184,-44045120⟩ : DyadicInterval 40),(⟨762123382715,762123402044⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1792,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172860073555,172984818331⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160546876736,160546876800⟩ : DyadicInterval 40),(⟨-188064620544,-188064620480⟩ : DyadicInterval 40),(⟨748478721222,748478740552⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160654668800,160654668864⟩ : DyadicInterval 40),(⟨-188212645504,-188212645440⟩ : DyadicInterval 40),(⟨748458938172,748458957502⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27557976704,-27517743744⟩ : DyadicInterval 40),(⟨775882255488,775902391232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160584233152,160682695360⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188251138368,-188115916160⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2092_ok : ecellOkT e2092 = true := by decide +kernel
theorem e2092_pos {a z : ℝ} (ha1 : ((128823/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1289079/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2092 e2092_ok ha1 ha2 hz1 hz2 hz

-- box ['1289079/8192000', '161241/1024000', '1999/2000', '7997/8000']  interval_lower 93254297/549755813888
noncomputable def e2093 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272528882368,0,true,160682695296,160682695360⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926494373184,0,false,-188251138368,-188251138304⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272642833220,0,true,160781148608,160781148672⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926380422332,0,false,-188386377216,-188386377152⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272442373740,0,true,160607946112,160607946176⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926580881812,0,false,-188148479616,-188148479552⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272577909019,0,true,160725055296,160725055360⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926445346533,0,false,-188309321984,-188309321920⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544660441,0,true,33032128,33032192⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478595111,0,false,-33033216,-33033152⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555702104,0,true,44073408,44073472⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467553448,0,false,-44075264,-44075200⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626009,0,false,-1792,-1728⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626784,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272485623694,0,true,160645317568,160645317632⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926537631858,0,false,-188199802624,-188199802560⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272610375597,0,true,160753106176,160753106240⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926412879955,0,false,-188347854272,-188347854208⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072260277503,0,false,-27594748032,-27594747968⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072299543331,0,false,-27554484992,-27554484928⟩
    { al := (1289079/8192000), au := (161241/1024000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨173017254592,173131205444⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160682695296,160682695360⟩ : DyadicInterval 40),(⟨-188251138368,-188251138304⟩ : DyadicInterval 40),(⟨748453791772,748453811101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160781148608,160781148672⟩ : DyadicInterval 40),(⟨-188386377216,-188386377152⟩ : DyadicInterval 40),(⟨748435704383,748435723712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160607946112,160607946176⟩ : DyadicInterval 40),(⟨-188148479616,-188148479552⟩ : DyadicInterval 40),(⟨748467515219,748467534548⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160725055296,160725055360⟩ : DyadicInterval 40),(⟨-188309321984,-188309321920⟩ : DyadicInterval 40),(⟨748446011264,748446030594⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33032665,44074328⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33032128,33032192⟩ : DyadicInterval 40),(⟨-33033216,-33033152⟩ : DyadicInterval 40),(⟨762123383103,762123402432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44073408,44073472⟩ : DyadicInterval 40),(⟨-44075264,-44075200⟩ : DyadicInterval 40),(⟨762123382713,762123402042⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1792,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172973995918,173098747821⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160645317568,160645317632⟩ : DyadicInterval 40),(⟨-188199802624,-188199802560⟩ : DyadicInterval 40),(⟨748460655063,748460674393⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160753106176,160753106240⟩ : DyadicInterval 40),(⟨-188347854272,-188347854208⟩ : DyadicInterval 40),(⟨748440857619,748440876949⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27594748032,-27554484928⟩ : DyadicInterval 40),(⟨775900626080,775920776896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160682695296,160781148672⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188386377216,-188251138304⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2093_ok : ecellOkT e2093 = true := by decide +kernel
theorem e2093_pos {a z : ℝ} (ha1 : ((1289079/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((161241/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2093 e2093_ok ha1 ha2 hz1 hz2 hz

-- box ['128823/819200', '1289079/8192000', '7997/8000', '3999/4000']  interval_lower 185230687/1099511627776
noncomputable def e2094 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272414931517,0,true,160584233152,160584233216⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926608324035,0,false,-188115916224,-188115916160⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272528882369,0,true,160682695296,160682695360⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926494373183,0,false,-188251138368,-188251138304⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272350092778,0,true,160528203648,160528203712⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926673162774,0,false,-188038981376,-188038981312⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272485628056,0,true,160645321344,160645321408⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926537627496,0,false,-188199807808,-188199807744⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533634482,0,true,22006464,22006528⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489621070,0,false,-22006976,-22006912⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544661108,0,true,33032832,33032896⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478594444,0,false,-33033856,-33033792⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626783,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627336,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272382507703,0,true,160556214912,160556214976⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926640747849,0,false,-188077442880,-188077442816⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272507259628,0,true,160664012288,160664012352⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926515995924,0,false,-188225478016,-188225477952⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072292735420,0,false,-27561465728,-27561465664⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072331977856,0,false,-27521227904,-27521227840⟩
    { al := (128823/819200), au := (1289079/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨172903303741,173017254593⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160584233152,160584233216⟩ : DyadicInterval 40),(⟨-188115916224,-188115916160⟩ : DyadicInterval 40),(⟨748471867090,748471886419⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160682695296,160682695360⟩ : DyadicInterval 40),(⟨-188251138368,-188251138304⟩ : DyadicInterval 40),(⟨748453791772,748453811101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160528203648,160528203712⟩ : DyadicInterval 40),(⟨-188038981376,-188038981312⟩ : DyadicInterval 40),(⟨748482146637,748482165967⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160645321344,160645321408⟩ : DyadicInterval 40),(⟨-188199807808,-188199807744⟩ : DyadicInterval 40),(⟨748460654370,748460673700⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22006706,33033332⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22006464,22006528⟩ : DyadicInterval 40),(⟨-22006976,-22006912⟩ : DyadicInterval 40),(⟨762123383367,762123402696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33032832,33032896⟩ : DyadicInterval 40),(⟨-33033856,-33033792⟩ : DyadicInterval 40),(⟨762123383071,762123402400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172870879927,172995631852⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160556214912,160556214976⟩ : DyadicInterval 40),(⟨-188077442880,-188077442816⟩ : DyadicInterval 40),(⟨748477008072,748477027401⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160664012288,160664012352⟩ : DyadicInterval 40),(⟨-188225478016,-188225477952⟩ : DyadicInterval 40),(⟨748457222587,748457241916⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27561465728,-27521227840⟩ : DyadicInterval 40),(⟨775883997536,775904135744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160584233152,160682695360⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188251138368,-188115916160⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2094_ok : ecellOkT e2094 = true := by decide +kernel
theorem e2094_pos {a z : ℝ} (ha1 : ((128823/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1289079/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2094 e2094_ok ha1 ha2 hz1 hz2 hz

-- box ['1289079/8192000', '161241/1024000', '7997/8000', '3999/4000']  interval_lower 186347781/1099511627776
noncomputable def e2095 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272528882368,0,true,160682695296,160682695360⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926494373184,0,false,-188251138368,-188251138304⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272642833220,0,true,160781148608,160781148672⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926380422332,0,false,-188386377216,-188386377152⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272464000897,0,true,160626633856,160626633920⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926559254655,0,false,-188174143360,-188174143296⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272599550419,0,true,160743753408,160743753472⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926423705133,0,false,-188335006464,-188335006400⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533649517,0,true,22021504,22021568⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489606035,0,false,-22022016,-22021952⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544683663,0,true,33055360,33055424⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478571889,0,false,-33056384,-33056320⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626782,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627335,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272496437188,0,true,160654661120,160654661184⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926526818364,0,false,-188212634944,-188212634880⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272621196237,0,true,160762454976,160762455040⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926402059315,0,false,-188360696768,-188360696704⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072256870358,0,false,-27598241792,-27598241728⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072296140890,0,false,-27557973824,-27557973760⟩
    { al := (1289079/8192000), au := (161241/1024000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨173017254592,173131205444⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160682695296,160682695360⟩ : DyadicInterval 40),(⟨-188251138368,-188251138304⟩ : DyadicInterval 40),(⟨748453791772,748453811101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160781148608,160781148672⟩ : DyadicInterval 40),(⟨-188386377216,-188386377152⟩ : DyadicInterval 40),(⟨748435704383,748435723712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160626633856,160626633920⟩ : DyadicInterval 40),(⟨-188174143360,-188174143296⟩ : DyadicInterval 40),(⟨748464085008,748464104338⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160743753408,160743753472⟩ : DyadicInterval 40),(⟨-188335006464,-188335006400⟩ : DyadicInterval 40),(⟨748442576061,748442595391⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22021741,33055887⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22021504,22021568⟩ : DyadicInterval 40),(⟨-22022016,-22021952⟩ : DyadicInterval 40),(⟨762123383366,762123402695⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33055360,33055424⟩ : DyadicInterval 40),(⟨-33056384,-33056320⟩ : DyadicInterval 40),(⟨762123383070,762123402399⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172984809412,173109568461⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160654661120,160654661184⟩ : DyadicInterval 40),(⟨-188212634944,-188212634880⟩ : DyadicInterval 40),(⟨748458939582,748458958912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160762454976,160762455040⟩ : DyadicInterval 40),(⟨-188360696768,-188360696704⟩ : DyadicInterval 40),(⟨748439139737,748439159067⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27598241792,-27557973760⟩ : DyadicInterval 40),(⟨775902370496,775922523776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160682695296,160781148672⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188386377216,-188251138304⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2095_ok : ecellOkT e2095 = true := by decide +kernel
theorem e2095_pos {a z : ℝ} (ha1 : ((1289079/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((161241/1024000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2095 e2095_ok ha1 ha2 hz1 hz2 hz

-- box ['321633/2048000', '1287381/8192000', '3999/4000', '7999/8000']  interval_lower 182845483/1099511627776
noncomputable def e2096 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272187029815,0,true,160387282432,160387282496⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926836225737,0,false,-187845521728,-187845521664⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272300980667,0,true,160485762240,160485762304⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926722274885,0,false,-187980710656,-187980710592⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272143860964,0,true,160349972352,160349972416⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926879394588,0,false,-187794311488,-187794311424⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272279381998,0,true,160467096704,160467096768⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926743873554,0,false,-187955085184,-187955085120⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522615991,0,true,10988160,10988224⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500639561,0,false,-10988288,-10988224⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533620064,0,true,21992064,21992128⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489635488,0,false,-21992512,-21992448⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627336,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627667,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272165440890,0,true,160368623680,160368623744⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926857814662,0,false,-187819910976,-187819910912⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272290185714,0,true,160476433280,160476433344⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926733069838,0,false,-187967903040,-187967902976⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072361000780,0,false,-27491469760,-27491469696⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072400191726,0,false,-27451287296,-27451287232⟩
    { al := (321633/2048000), au := (1287381/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨172675402039,172789352891⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160387282432,160387282496⟩ : DyadicInterval 40),(⟨-187845521728,-187845521664⟩ : DyadicInterval 40),(⟨748507981349,748508000678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160485762240,160485762304⟩ : DyadicInterval 40),(⟨-187980710656,-187980710592⟩ : DyadicInterval 40),(⟨748489930248,748489949578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160349972352,160349972416⟩ : DyadicInterval 40),(⟨-187794311488,-187794311424⟩ : DyadicInterval 40),(⟨748514816603,748514835933⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160467096704,160467096768⟩ : DyadicInterval 40),(⟨-187955085184,-187955085120⟩ : DyadicInterval 40),(⟨748493352649,748493371978⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10988215,21992288⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10988160,10988224⟩ : DyadicInterval 40),(⟨-10988288,-10988224⟩ : DyadicInterval 40),(⟨762123383506,762123402835⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21992064,21992128⟩ : DyadicInterval 40),(⟨-21992512,-21992448⟩ : DyadicInterval 40),(⟨762123383336,762123402665⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172653813114,172778557938⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160368623680,160368623744⟩ : DyadicInterval 40),(⟨-187819910976,-187819910912⟩ : DyadicInterval 40),(⟨748511399896,748511419226⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160476433280,160476433344⟩ : DyadicInterval 40),(⟨-187967903040,-187967902976⟩ : DyadicInterval 40),(⟨748491640817,748491660147⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27491469760,-27451287232⟩ : DyadicInterval 40),(⟨775849027232,775869137760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160387282432,160485762304⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187980710656,-187845521664⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2096_ok : ecellOkT e2096 = true := by decide +kernel
theorem e2096_pos {a z : ℝ} (ha1 : ((321633/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1287381/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2096 e2096_ok ha1 ha2 hz1 hz2 hz

-- box ['1287381/8192000', '128823/819200', '3999/4000', '7999/8000']  interval_lower 183956631/1099511627776
noncomputable def e2097 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272300980666,0,true,160485762240,160485762304⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926722274886,0,false,-187980710656,-187980710592⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272414931518,0,true,160584233152,160584233216⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926608324034,0,false,-188115916224,-188115916160⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272257783327,0,true,160448430848,160448430912⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926765472225,0,false,-187929460288,-187929460224⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272393318606,0,true,160565556992,160565557056⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926629936946,0,false,-188090270656,-188090270592⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522623508,0,true,10995648,10995712⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500632044,0,false,-10995840,-10995776⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533635097,0,true,22007040,22007104⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489620455,0,false,-22007552,-22007488⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627335,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627667,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272279377500,0,true,160467092800,160467092864⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926743878052,0,false,-187955079872,-187955079808⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272404129440,0,true,160574898880,160574898944⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926619126112,0,false,-188103098560,-188103098496⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072325178468,0,false,-27528199616,-27528199552⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072364397506,0,false,-27487987008,-27487986944⟩
    { al := (1287381/8192000), au := (128823/819200), zl := (3999/4000), zu := (7999/8000),
      A := ⟨172789352890,172903303742⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160485762240,160485762304⟩ : DyadicInterval 40),(⟨-187980710656,-187980710592⟩ : DyadicInterval 40),(⟨748489930248,748489949578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160584233152,160584233216⟩ : DyadicInterval 40),(⟨-188115916224,-188115916160⟩ : DyadicInterval 40),(⟨748471867090,748471886419⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160448430848,160448430912⟩ : DyadicInterval 40),(⟨-187929460288,-187929460224⟩ : DyadicInterval 40),(⟨748496774608,748496793938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160565556992,160565557056⟩ : DyadicInterval 40),(⟨-188090270656,-188090270592⟩ : DyadicInterval 40),(⟨748475294018,748475313348⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10995732,22007321⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10995648,10995712⟩ : DyadicInterval 40),(⟨-10995840,-10995776⟩ : DyadicInterval 40),(⟨762123383538,762123402867⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22007040,22007104⟩ : DyadicInterval 40),(⟨-22007552,-22007488⟩ : DyadicInterval 40),(⟨762123383367,762123402696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172767749724,172892501664⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160467092800,160467092864⟩ : DyadicInterval 40),(⟨-187955079872,-187955079808⟩ : DyadicInterval 40),(⟨748493353382,748493372711⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160574898880,160574898944⟩ : DyadicInterval 40),(⟨-188103098560,-188103098496⟩ : DyadicInterval 40),(⟨748473579923,748473599253⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27528199616,-27487986944⟩ : DyadicInterval 40),(⟨775867377088,775887502688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160485762240,160584233216⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188115916224,-187980710592⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2097_ok : ecellOkT e2097 = true := by decide +kernel
theorem e2097_pos {a z : ℝ} (ha1 : ((1287381/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((128823/819200 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2097 e2097_ok ha1 ha2 hz1 hz2 hz

-- box ['321633/2048000', '1287381/8192000', '7999/8000', '1']  interval_lower 182685859/1099511627776
noncomputable def e2098 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272187029815,0,true,160387282432,160387282496⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926836225737,0,false,-187845521728,-187845521664⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272300980667,0,true,160485762240,160485762304⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926722274885,0,false,-187980710656,-187980710592⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272165445389,0,true,160368627584,160368627648⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926857810163,0,false,-187819916288,-187819916224⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522624074,0,true,10996224,10996288⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500631478,0,false,-10996416,-10996352⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627666,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1272176233070,0,true,160377951104,160377951168⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨926847022482,0,false,-187832713600,-187832713536⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1272300985036,0,true,160485766016,160485766080⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨926722270516,0,false,-187980715840,-187980715776⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1072357606637,0,false,-27494949824,-27494949760⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1072396802277,0,false,-27454762432,-27454762368⟩
    { al := (321633/2048000), au := (1287381/8192000), zl := (7999/8000), zu := 1,
      A := ⟨172675402039,172789352891⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160387282432,160387282496⟩ : DyadicInterval 40),(⟨-187845521728,-187845521664⟩ : DyadicInterval 40),(⟨748507981349,748508000678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160485762240,160485762304⟩ : DyadicInterval 40),(⟨-187980710656,-187980710592⟩ : DyadicInterval 40),(⟨748489930248,748489949578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160368627584,160368627648⟩ : DyadicInterval 40),(⟨-187819916288,-187819916224⟩ : DyadicInterval 40),(⟨748511399164,748511418494⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160485762240,160485762304⟩ : DyadicInterval 40),(⟨-187980710656,-187980710592⟩ : DyadicInterval 40),(⟨748489930248,748489949578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10996298⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10996224,10996288⟩ : DyadicInterval 40),(⟨-10996416,-10996352⟩ : DyadicInterval 40),(⟨762123383538,762123402867⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨172664605294,172789357260⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160377951104,160377951168⟩ : DyadicInterval 40),(⟨-187832713600,-187832713536⟩ : DyadicInterval 40),(⟨748509691062,748509710392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160485766016,160485766080⟩ : DyadicInterval 40),(⟨-187980715840,-187980715776⟩ : DyadicInterval 40),(⟨748489929556,748489948885⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27494949824,-27454762368⟩ : DyadicInterval 40),(⟨775850764800,775870877792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨160387282432,160485762304⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187980710656,-187845521664⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2098_ok : ecellOkT e2098 = true := by decide +kernel
theorem e2098_pos {a z : ℝ} (ha1 : ((321633/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1287381/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2098 e2098_ok ha1 ha2 hz1 hz2 hz

-- box ['1287381/8192000', '128823/819200', '7999/8000', '1']  interval_lower 183796753/1099511627776
noncomputable def e2099 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272300980666,0,true,160485762240,160485762304⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926722274886,0,false,-187980710656,-187980710592⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272414931518,0,true,160584233152,160584233216⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926608324034,0,false,-188115916224,-188115916160⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272279381996,0,true,160467096704,160467096768⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926743873556,0,false,-187955085184,-187955085120⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522631591,0,true,11003712,11003776⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500623961,0,false,-11003904,-11003840⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627665,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1272290176797,0,true,160476425600,160476425664⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨926733078755,0,false,-187967892480,-187967892416⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1272414935881,0,true,160584236928,160584236992⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨926608319671,0,false,-188115921408,-188115921344⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1072321779848,0,false,-27531684416,-27531684352⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1072361003583,0,false,-27491466880,-27491466816⟩
    { al := (1287381/8192000), au := (128823/819200), zl := (7999/8000), zu := 1,
      A := ⟨172789352890,172903303742⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160485762240,160485762304⟩ : DyadicInterval 40),(⟨-187980710656,-187980710592⟩ : DyadicInterval 40),(⟨748489930248,748489949578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160584233152,160584233216⟩ : DyadicInterval 40),(⟨-188115916224,-188115916160⟩ : DyadicInterval 40),(⟨748471867090,748471886419⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160467096704,160467096768⟩ : DyadicInterval 40),(⟨-187955085184,-187955085120⟩ : DyadicInterval 40),(⟨748493352649,748493371979⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160584233152,160584233216⟩ : DyadicInterval 40),(⟨-188115916224,-188115916160⟩ : DyadicInterval 40),(⟨748471867090,748471886419⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11003815⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11003712,11003776⟩ : DyadicInterval 40),(⟨-11003904,-11003840⟩ : DyadicInterval 40),(⟨762123383537,762123402866⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨172778549021,172903308105⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160476425600,160476425664⟩ : DyadicInterval 40),(⟨-187967892480,-187967892416⟩ : DyadicInterval 40),(⟨748491642224,748491661553⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160584236928,160584236992⟩ : DyadicInterval 40),(⟨-188115921408,-188115921344⟩ : DyadicInterval 40),(⟨748471866398,748471885727⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27531684416,-27491466816⟩ : DyadicInterval 40),(⟨775869117024,775889245088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨160485762240,160584233216⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188115916224,-187980710592⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2099_ok : ecellOkT e2099 = true := by decide +kernel
theorem e2099_pos {a z : ℝ} (ha1 : ((1287381/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((128823/819200 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2099 e2099_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B034

end


