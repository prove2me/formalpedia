-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B043
-- name    : CK_CKLaneC2R_EpCells_B043
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:33:24.121764+00:00
-- url     : https://prove2.me/theorems/edb91ed6-7cf3-4d05-8a7b-6c08ca4cf942
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B043` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B043` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B043` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B043 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B043.lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheckT

-- ===== source module CKLaneC2R.EpCells.B043 =====
section

namespace CKLaneC2R.EpCells.B043

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['671283/4096000', '268683/1638400', '3997/4000', '1599/1600']  interval_lower 263016329/1099511627776
noncomputable def e2580 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279707785986,0,true,166868100352,166868100416⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919315469566,0,false,-196803837184,-196803837120⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279821736838,0,true,166966001408,166966001472⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919201518714,0,false,-196940132096,-196940132032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279572638867,0,true,166751977216,166751977280⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919450616685,0,false,-196642211584,-196642211520⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279709043020,0,true,166869180416,166869180480⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919314212532,0,false,-196805340608,-196805340544⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569055666,0,true,57426368,57426432⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454199886,0,false,-57429440,-57429376⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580587300,0,true,68957312,68957376⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442668252,0,false,-68961728,-68961664⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623450,0,false,-4352,-4288⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624777,0,false,-3008,-2944⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279640208205,0,true,166810036672,166810036736⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919383047347,0,false,-196723016384,-196723016320⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279765398749,0,true,166917599552,166917599616⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919257856803,0,false,-196872744832,-196872744768⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069960851659,0,false,-29955145280,-29955145216⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070001884844,0,false,-29912979648,-29912979584⟩
    { al := (671283/4096000), au := (268683/1638400), zl := (3997/4000), zu := (1599/1600),
      A := ⟨180196158210,180310109062⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166868100352,166868100416⟩ : DyadicInterval 40),(⟨-196803837184,-196803837120⟩ : DyadicInterval 40),(⟨747290618514,747290637844⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166966001408,166966001472⟩ : DyadicInterval 40),(⟨-196940132096,-196940132032⟩ : DyadicInterval 40),(⟨747271767356,747271786685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166751977216,166751977280⟩ : DyadicInterval 40),(⟨-196642211584,-196642211520⟩ : DyadicInterval 40),(⟨747312960454,747312979783⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166869180416,166869180480⟩ : DyadicInterval 40),(⟨-196805340608,-196805340544⟩ : DyadicInterval 40),(⟨747290410606,747290429935⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57427890,68959524⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57426368,57426432⟩ : DyadicInterval 40),(⟨-57429440,-57429376⟩ : DyadicInterval 40),(⟨762123382088,762123401417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68957312,68957376⟩ : DyadicInterval 40),(⟨-68961728,-68961664⟩ : DyadicInterval 40),(⟨762123381434,762123400764⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4352,-2944⟩ : DyadicInterval 40),(⟨762123385088,762123405056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180128580429,180253770973⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166810036672,166810036736⟩ : DyadicInterval 40),(⟨-196723016384,-196723016320⟩ : DyadicInterval 40),(⟨747301792334,747301811663⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166917599552,166917599616⟩ : DyadicInterval 40),(⟨-196872744832,-196872744768⟩ : DyadicInterval 40),(⟨747281089005,747281108335⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29955145280,-29912979584⟩ : DyadicInterval 40),(⟨777079873408,777100975520⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166868100352,166966001472⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196940132096,-196803837120⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2580_ok : ecellOkT e2580 = true := by decide +kernel
theorem e2580_pos {a z : ℝ} (ha1 : ((671283/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((268683/1638400 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2580 e2580_ok ha1 ha2 hz1 hz2 hz

-- box ['268683/1638400', '168033/1024000', '3997/4000', '1599/1600']  interval_lower 132160061/549755813888
noncomputable def e2581 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279821736837,0,true,166966001408,166966001472⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919201518715,0,false,-196940132096,-196940132032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279935687689,0,true,167063893696,167063893760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919087567863,0,false,-197076443968,-197076443904⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279686504255,0,true,166849815168,166849815232⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919336751297,0,false,-196778384256,-196778384192⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279822922652,0,true,166967020160,166967020224⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919200332900,0,false,-196941550528,-196941550464⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569093431,0,true,57464128,57464192⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454162121,0,false,-57467200,-57467136⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580632622,0,true,69002624,69002688⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442622930,0,false,-69007040,-69006976⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623445,0,false,-4352,-4288⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624773,0,false,-3008,-2944⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279754116329,0,true,166907906176,166907906240⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919269139223,0,false,-196859250176,-196859250112⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279879313990,0,true,167015465536,167015465600⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919143941562,0,false,-197009005760,-197009005696⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069923489362,0,false,-29993540160,-29993540096⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069964550821,0,false,-29951343936,-29951343872⟩
    { al := (268683/1638400), au := (168033/1024000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨180310109061,180424059913⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166966001408,166966001472⟩ : DyadicInterval 40),(⟨-196940132096,-196940132032⟩ : DyadicInterval 40),(⟨747271767356,747271786685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167063893696,167063893760⟩ : DyadicInterval 40),(⟨-197076443968,-197076443904⟩ : DyadicInterval 40),(⟨747252904117,747252923447⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166849815168,166849815232⟩ : DyadicInterval 40),(⟨-196778384256,-196778384192⟩ : DyadicInterval 40),(⟨747294137832,747294157161⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166967020160,166967020224⟩ : DyadicInterval 40),(⟨-196941550528,-196941550464⟩ : DyadicInterval 40),(⟨747271571121,747271590451⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57465655,69004846⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57464128,57464192⟩ : DyadicInterval 40),(⟨-57467200,-57467136⟩ : DyadicInterval 40),(⟨762123382084,762123401413⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69002624,69002688⟩ : DyadicInterval 40),(⟨-69007040,-69006976⟩ : DyadicInterval 40),(⟨762123381429,762123400758⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4352,-2944⟩ : DyadicInterval 40),(⟨762123385088,762123405056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180242488553,180367686214⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166907906176,166907906240⟩ : DyadicInterval 40),(⟨-196859250176,-196859250112⟩ : DyadicInterval 40),(⟨747282955449,747282974779⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167015465536,167015465600⟩ : DyadicInterval 40),(⟨-197009005760,-197009005696⟩ : DyadicInterval 40),(⟨747262237678,747262257008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29993540160,-29951343872⟩ : DyadicInterval 40),(⟨777099055552,777120172960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166966001408,167063893760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197076443968,-196940132032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2581_ok : ecellOkT e2581 = true := by decide +kernel
theorem e2581_pos {a z : ℝ} (ha1 : ((268683/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((168033/1024000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2581 e2581_ok ha1 ha2 hz1 hz2 hz

-- box ['671283/4096000', '268683/1638400', '1599/1600', '1999/2000']  interval_lower 262830493/1099511627776
noncomputable def e2582 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279707785986,0,true,166868100352,166868100416⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919315469566,0,false,-196803837184,-196803837120⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279821736838,0,true,166966001408,166966001472⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919201518714,0,false,-196940132096,-196940132032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279595163387,0,true,166771331904,166771331968⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919428092165,0,false,-196669147520,-196669147456⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279731581784,0,true,166888545280,166888545344⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919291673768,0,false,-196832297600,-196832297536⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557570151,0,true,45941376,45941440⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465685401,0,false,-45943360,-45943296⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569094233,0,true,57464896,57464960⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454161319,0,false,-57467968,-57467904⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624772,0,false,-3008,-2944⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625857,0,false,-1920,-1856⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279651470312,0,true,166819713472,166819713536⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919371785240,0,false,-196736485056,-196736484992⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279776668006,0,true,166927281472,166927281536⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919246587546,0,false,-196886223936,-196886223872⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069957156583,0,false,-29958942400,-29958942336⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069998194677,0,false,-29916771584,-29916771520⟩
    { al := (671283/4096000), au := (268683/1638400), zl := (1599/1600), zu := (1999/2000),
      A := ⟨180196158210,180310109062⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166868100352,166868100416⟩ : DyadicInterval 40),(⟨-196803837184,-196803837120⟩ : DyadicInterval 40),(⟨747290618514,747290637844⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166966001408,166966001472⟩ : DyadicInterval 40),(⟨-196940132096,-196940132032⟩ : DyadicInterval 40),(⟨747271767356,747271786685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166771331904,166771331968⟩ : DyadicInterval 40),(⟨-196669147520,-196669147456⟩ : DyadicInterval 40),(⟨747309237988,747309257318⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166888545280,166888545344⟩ : DyadicInterval 40),(⟨-196832297600,-196832297536⟩ : DyadicInterval 40),(⟨747286682921,747286702251⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨45942375,57466457⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45941376,45941440⟩ : DyadicInterval 40),(⟨-45943360,-45943296⟩ : DyadicInterval 40),(⟨762123382624,762123401953⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57464896,57464960⟩ : DyadicInterval 40),(⟨-57467968,-57467904⟩ : DyadicInterval 40),(⟨762123382084,762123401413⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3008,-1856⟩ : DyadicInterval 40),(⟨762123384544,762123404384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180139842536,180265040230⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166819713472,166819713536⟩ : DyadicInterval 40),(⟨-196736485056,-196736484992⟩ : DyadicInterval 40),(⟨747299930434,747299949763⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166927281472,166927281536⟩ : DyadicInterval 40),(⟨-196886223936,-196886223872⟩ : DyadicInterval 40),(⟨747279224668,747279243998⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29958942400,-29916771520⟩ : DyadicInterval 40),(⟨777081769376,777102874080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166868100352,166966001472⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196940132096,-196803837120⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2582_ok : ecellOkT e2582 = true := by decide +kernel
theorem e2582_pos {a z : ℝ} (ha1 : ((671283/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((268683/1638400 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2582 e2582_ok ha1 ha2 hz1 hz2 hz

-- box ['268683/1638400', '168033/1024000', '1599/1600', '1999/2000']  interval_lower 132066833/549755813888
noncomputable def e2583 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279821736837,0,true,166966001408,166966001472⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919201518715,0,false,-196940132096,-196940132032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279935687689,0,true,167063893696,167063893760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919087567863,0,false,-197076443968,-197076443904⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279709043018,0,true,166869180416,166869180480⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919314212534,0,false,-196805340608,-196805340544⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279845475660,0,true,166986395520,166986395584⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919177779892,0,false,-196968527936,-196968527872⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557600363,0,true,45971584,45971648⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465655189,0,false,-45973568,-45973504⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569132000,0,true,57502720,57502784⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454123552,0,false,-57505728,-57505664⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624768,0,false,-3072,-3008⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625854,0,false,-1984,-1920⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279765385558,0,true,166917588224,166917588288⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919257869994,0,false,-196872729088,-196872729024⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279890590366,0,true,167025152768,167025152832⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919132665186,0,false,-197022495040,-197022494976⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069919789615,0,false,-29997342208,-29997342144⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069960855985,0,false,-29955140864,-29955140800⟩
    { al := (268683/1638400), au := (168033/1024000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨180310109061,180424059913⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166966001408,166966001472⟩ : DyadicInterval 40),(⟨-196940132096,-196940132032⟩ : DyadicInterval 40),(⟨747271767356,747271786685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167063893696,167063893760⟩ : DyadicInterval 40),(⟨-197076443968,-197076443904⟩ : DyadicInterval 40),(⟨747252904117,747252923447⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166869180416,166869180480⟩ : DyadicInterval 40),(⟨-196805340608,-196805340544⟩ : DyadicInterval 40),(⟨747290410606,747290429935⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166986395520,166986395584⟩ : DyadicInterval 40),(⟨-196968527936,-196968527872⟩ : DyadicInterval 40),(⟨747267838707,747267858036⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨45972587,57504224⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45971584,45971648⟩ : DyadicInterval 40),(⟨-45973568,-45973504⟩ : DyadicInterval 40),(⟨762123382621,762123401950⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57502720,57502784⟩ : DyadicInterval 40),(⟨-57505728,-57505664⟩ : DyadicInterval 40),(⟨762123382048,762123401377⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3072,-1920⟩ : DyadicInterval 40),(⟨762123384576,762123404416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180253757782,180378962590⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166917588224,166917588288⟩ : DyadicInterval 40),(⟨-196872729088,-196872729024⟩ : DyadicInterval 40),(⟨747281091199,747281110529⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167025152768,167025152832⟩ : DyadicInterval 40),(⟨-197022495040,-197022494976⟩ : DyadicInterval 40),(⟨747260370924,747260390254⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29997342208,-29955140800⟩ : DyadicInterval 40),(⟨777100954016,777122073984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166966001408,167063893760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197076443968,-196940132032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2583_ok : ecellOkT e2583 = true := by decide +kernel
theorem e2583_pos {a z : ℝ} (ha1 : ((268683/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((168033/1024000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2583 e2583_ok ha1 ha2 hz1 hz2 hz

-- box ['10449/64000', '1338321/8192000', '1999/2000', '7997/8000']  interval_lower 127445233/549755813888
noncomputable def e2584 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279024080879,0,true,166280511040,166280511104⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919999174673,0,false,-195986422144,-195986422080⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279138031731,0,true,166378464448,166378464512⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919885223821,0,false,-196122615744,-196122615680⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278934324652,0,true,166203349504,166203349568⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920088930900,0,false,-195879157696,-195879157632⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279070671830,0,true,166320562176,166320562240⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919952583722,0,false,-196042105408,-196042105344⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545948660,0,true,34320320,34320384⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477306892,0,false,-34321472,-34321408⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557419868,0,true,45791104,45791168⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465835684,0,false,-45793088,-45793024⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625868,0,false,-1920,-1856⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626705,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278979198278,0,true,166241927104,166241927168⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920044057274,0,false,-195932783232,-195932783168⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279104360377,0,true,166349521088,166349521152⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919918895175,0,false,-196082370112,-196082370048⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070177195298,0,false,-29732849024,-29732848960⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070218068665,0,false,-29690856064,-29690856000⟩
    { al := (10449/64000), au := (1338321/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨179512453103,179626403955⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166280511040,166280511104⟩ : DyadicInterval 40),(⟨-195986422144,-195986422080⟩ : DyadicInterval 40),(⟨747403470472,747403489801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166378464448,166378464512⟩ : DyadicInterval 40),(⟨-196122615744,-196122615680⟩ : DyadicInterval 40),(⟨747384692101,747384711430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166203349504,166203349568⟩ : DyadicInterval 40),(⟨-195879157696,-195879157632⟩ : DyadicInterval 40),(⟨747418253134,747418272464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166320562176,166320562240⟩ : DyadicInterval 40),(⟨-196042105408,-196042105344⟩ : DyadicInterval 40),(⟨747395794049,747395813379⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34320884,45792092⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34320320,34320384⟩ : DyadicInterval 40),(⟨-34321472,-34321408⟩ : DyadicInterval 40),(⟨762123383056,762123402385⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45791104,45791168⟩ : DyadicInterval 40),(⟨-45793088,-45793024⟩ : DyadicInterval 40),(⟨762123382636,762123401965⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1920,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179467570502,179592732601⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166241927104,166241927168⟩ : DyadicInterval 40),(⟨-195932783232,-195932783168⟩ : DyadicInterval 40),(⟨747410863468,747410882798⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166349521088,166349521152⟩ : DyadicInterval 40),(⟨-196082370112,-196082370048⟩ : DyadicInterval 40),(⟨747390242184,747390261514⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29732849024,-29690856000⟩ : DyadicInterval 40),(⟨776968811616,776989827392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166280511040,166378464512⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196122615744,-195986422080⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2584_ok : ecellOkT e2584 = true := by decide +kernel
theorem e2584_pos {a z : ℝ} (ha1 : ((10449/64000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1338321/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2584 e2584_ok ha1 ha2 hz1 hz2 hz

-- box ['1338321/8192000', '133917/819200', '1999/2000', '7997/8000']  interval_lower 32021913/137438953472
noncomputable def e2585 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279138031730,0,true,166378464448,166378464512⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919885223822,0,false,-196122615744,-196122615680⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279251982582,0,true,166476409024,166476409088⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919771272970,0,false,-196258826304,-196258826240⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279048218528,0,true,166301260736,166301260800⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919975037024,0,false,-196015269952,-196015269888⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279184579950,0,true,166418475264,166418475328⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919838675602,0,false,-196178254912,-196178254848⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545971309,0,true,34342976,34343040⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477284243,0,false,-34344128,-34344064⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557450069,0,true,45821312,45821376⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465805483,0,false,-45823296,-45823232⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625866,0,false,-1920,-1856⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626704,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279093120644,0,true,166339859392,166339859456⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919930134908,0,false,-196068936192,-196068936128⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279218289857,0,true,166447449920,166447449984⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919804965695,0,false,-196218550144,-196218550080⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070139965321,0,false,-29771100160,-29771100096⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070180866950,0,false,-29729076736,-29729076672⟩
    { al := (1338321/8192000), au := (133917/819200), zl := (1999/2000), zu := (7997/8000),
      A := ⟨179626403954,179740354806⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166378464448,166378464512⟩ : DyadicInterval 40),(⟨-196122615744,-196122615680⟩ : DyadicInterval 40),(⟨747384692101,747384711430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166476409024,166476409088⟩ : DyadicInterval 40),(⟨-196258826304,-196258826240⟩ : DyadicInterval 40),(⟨747365901695,747365921024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166301260736,166301260800⟩ : DyadicInterval 40),(⟨-196015269952,-196015269888⟩ : DyadicInterval 40),(⟨747399493765,747399513095⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166418475264,166418475328⟩ : DyadicInterval 40),(⟨-196178254912,-196178254848⟩ : DyadicInterval 40),(⟨747377017811,747377037141⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34343533,45822293⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34342976,34343040⟩ : DyadicInterval 40),(⟨-34344128,-34344064⟩ : DyadicInterval 40),(⟨762123383055,762123402384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45821312,45821376⟩ : DyadicInterval 40),(⟨-45823296,-45823232⟩ : DyadicInterval 40),(⟨762123382634,762123401963⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1920,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179581492868,179706662081⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166339859392,166339859456⟩ : DyadicInterval 40),(⟨-196068936192,-196068936128⟩ : DyadicInterval 40),(⟨747392094633,747392113963⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166447449920,166447449984⟩ : DyadicInterval 40),(⟨-196218550144,-196218550080⟩ : DyadicInterval 40),(⟨747371458863,747371478193⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29771100160,-29729076672⟩ : DyadicInterval 40),(⟨776987921952,777008952960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166378464448,166476409088⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196258826304,-196122615680⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2585_ok : ecellOkT e2585 = true := by decide +kernel
theorem e2585_pos {a z : ℝ} (ha1 : ((1338321/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((133917/819200 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2585 e2585_ok ha1 ha2 hz1 hz2 hz

-- box ['10449/64000', '1338321/8192000', '7997/8000', '3999/4000']  interval_lower 127353347/549755813888
noncomputable def e2586 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279024080879,0,true,166280511040,166280511104⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919999174673,0,false,-195986422144,-195986422080⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279138031731,0,true,166378464448,166378464512⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919885223821,0,false,-196122615744,-196122615680⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278956763708,0,true,166222640384,166222640448⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920066491844,0,false,-195905972800,-195905972736⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279093125131,0,true,166339863296,166339863360⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919930130421,0,false,-196068941568,-196068941504⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534508336,0,true,22880320,22880384⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488747216,0,false,-22880832,-22880768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545971995,0,true,34343680,34343744⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477283557,0,false,-34344768,-34344704⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626703,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627300,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278990417711,0,true,166251572160,166251572224⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920032837841,0,false,-195946191232,-195946191168⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279115586960,0,true,166359171328,166359171392⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919907668592,0,false,-196095788544,-196095788480⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070173527714,0,false,-29736617152,-29736617088⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070214405971,0,false,-29694619008,-29694618944⟩
    { al := (10449/64000), au := (1338321/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨179512453103,179626403955⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166280511040,166280511104⟩ : DyadicInterval 40),(⟨-195986422144,-195986422080⟩ : DyadicInterval 40),(⟨747403470472,747403489801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166378464448,166378464512⟩ : DyadicInterval 40),(⟨-196122615744,-196122615680⟩ : DyadicInterval 40),(⟨747384692101,747384711430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166222640384,166222640448⟩ : DyadicInterval 40),(⟨-195905972800,-195905972736⟩ : DyadicInterval 40),(⟨747414558170,747414577500⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166339863296,166339863360⟩ : DyadicInterval 40),(⟨-196068941568,-196068941504⟩ : DyadicInterval 40),(⟨747392093872,747392113201⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22880560,34344219⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22880320,22880384⟩ : DyadicInterval 40),(⟨-22880832,-22880768⟩ : DyadicInterval 40),(⟨762123383331,762123402660⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34343680,34343744⟩ : DyadicInterval 40),(⟨-34344768,-34344704⟩ : DyadicInterval 40),(⟨762123383023,762123402352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179478789935,179603959184⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166251572160,166251572224⟩ : DyadicInterval 40),(⟨-195946191232,-195946191168⟩ : DyadicInterval 40),(⟨747409015589,747409034919⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166359171328,166359171392⟩ : DyadicInterval 40),(⟨-196095788544,-196095788480⟩ : DyadicInterval 40),(⟨747388391851,747388411180⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29736617152,-29694618944⟩ : DyadicInterval 40),(⟨776970693088,776991711456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166280511040,166378464512⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196122615744,-195986422080⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2586_ok : ecellOkT e2586 = true := by decide +kernel
theorem e2586_pos {a z : ℝ} (ha1 : ((10449/64000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1338321/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2586 e2586_ok ha1 ha2 hz1 hz2 hz

-- box ['1338321/8192000', '133917/819200', '7997/8000', '3999/4000']  interval_lower 255991405/1099511627776
noncomputable def e2587 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279138031730,0,true,166378464448,166378464512⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919885223822,0,false,-196122615744,-196122615680⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279251982582,0,true,166476409024,166476409088⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919771272970,0,false,-196258826304,-196258826240⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279070671828,0,true,166320562176,166320562240⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919952583724,0,false,-196042105408,-196042105344⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279207047494,0,true,166437786880,166437786944⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919816208058,0,false,-196205111360,-196205111296⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534523436,0,true,22895360,22895424⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488732116,0,false,-22895936,-22895872⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545994645,0,true,34366272,34366336⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477260907,0,false,-34367424,-34367360⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626701,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627300,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279104347201,0,true,166349509760,166349509824⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919918908351,0,false,-196082354368,-196082354304⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279229523562,0,true,166457105472,166457105536⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919793731990,0,false,-196231978688,-196231978624⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070136293082,0,false,-29774873216,-29774873152⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070177199603,0,false,-29732844608,-29732844544⟩
    { al := (1338321/8192000), au := (133917/819200), zl := (7997/8000), zu := (3999/4000),
      A := ⟨179626403954,179740354806⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166378464448,166378464512⟩ : DyadicInterval 40),(⟨-196122615744,-196122615680⟩ : DyadicInterval 40),(⟨747384692101,747384711430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166476409024,166476409088⟩ : DyadicInterval 40),(⟨-196258826304,-196258826240⟩ : DyadicInterval 40),(⟨747365901695,747365921024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166320562176,166320562240⟩ : DyadicInterval 40),(⟨-196042105408,-196042105344⟩ : DyadicInterval 40),(⟨747395794050,747395813379⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166437786880,166437786944⟩ : DyadicInterval 40),(⟨-196205111360,-196205111296⟩ : DyadicInterval 40),(⟨747373312886,747373332216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22895660,34366869⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22895360,22895424⟩ : DyadicInterval 40),(⟨-22895936,-22895872⟩ : DyadicInterval 40),(⟨762123383363,762123402692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34366272,34366336⟩ : DyadicInterval 40),(⟨-34367424,-34367360⟩ : DyadicInterval 40),(⟨762123383053,762123402382⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179592719425,179717895786⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166349509760,166349509824⟩ : DyadicInterval 40),(⟨-196082354368,-196082354304⟩ : DyadicInterval 40),(⟨747390244359,747390263688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166457105472,166457105536⟩ : DyadicInterval 40),(⟨-196231978688,-196231978624⟩ : DyadicInterval 40),(⟨747369606104,747369625434⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29774873216,-29732844544⟩ : DyadicInterval 40),(⟨776989805888,777010839488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166378464448,166476409088⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196258826304,-196122615680⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2587_ok : ecellOkT e2587 = true := by decide +kernel
theorem e2587_pos {a z : ℝ} (ha1 : ((1338321/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((133917/819200 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2587 e2587_ok ha1 ha2 hz1 hz2 hz

-- box ['133917/819200', '1340019/8192000', '1999/2000', '7997/8000']  interval_lower 257463023/1099511627776
noncomputable def e2588 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279251982581,0,true,166476409024,166476409088⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919771272971,0,false,-196258826304,-196258826240⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279365933433,0,true,166574344960,166574345024⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919657322119,0,false,-196395053696,-196395053632⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279162112403,0,true,166399163328,166399163392⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919861143149,0,false,-196151399040,-196151398976⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279298488069,0,true,166516379584,166516379648⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919724767483,0,false,-196314421184,-196314421120⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545993960,0,true,34365632,34365696⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477261592,0,false,-34366784,-34366720⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557480272,0,true,45851520,45851584⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465775280,0,false,-45853504,-45853440⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625863,0,false,-1920,-1856⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626702,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279207043005,0,true,166437782976,166437783040⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919816212547,0,false,-196205105984,-196205105920⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279332219345,0,true,166545370048,166545370112⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919691036207,0,false,-196354747008,-196354746944⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070102711730,0,false,-29809376896,-29809376832⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070143641628,0,false,-29767322944,-29767322880⟩
    { al := (133917/819200), au := (1340019/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨179740354805,179854305657⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166476409024,166476409088⟩ : DyadicInterval 40),(⟨-196258826304,-196258826240⟩ : DyadicInterval 40),(⟨747365901695,747365921024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166574344960,166574345024⟩ : DyadicInterval 40),(⟨-196395053696,-196395053632⟩ : DyadicInterval 40),(⟨747347099088,747347118417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166399163328,166399163392⟩ : DyadicInterval 40),(⟨-196151399040,-196151398976⟩ : DyadicInterval 40),(⟨747380722221,747380741551⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166516379584,166516379648⟩ : DyadicInterval 40),(⟨-196314421184,-196314421120⟩ : DyadicInterval 40),(⟨747358229440,747358248769⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34366184,45852496⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34365632,34365696⟩ : DyadicInterval 40),(⟨-34366784,-34366720⟩ : DyadicInterval 40),(⟨762123383053,762123402382⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45851520,45851584⟩ : DyadicInterval 40),(⟨-45853504,-45853440⟩ : DyadicInterval 40),(⟨762123382631,762123401960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1920,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179695415229,179820591569⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166437782976,166437783040⟩ : DyadicInterval 40),(⟨-196205105984,-196205105920⟩ : DyadicInterval 40),(⟨747373313649,747373332978⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166545370048,166545370112⟩ : DyadicInterval 40),(⟨-196354747008,-196354746944⟩ : DyadicInterval 40),(⟨747352663386,747352682715⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29809376896,-29767322880⟩ : DyadicInterval 40),(⟨777007045056,777028091328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166476409024,166574345024⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196395053696,-196258826240⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2588_ok : ecellOkT e2588 = true := by decide +kernel
theorem e2588_pos {a z : ℝ} (ha1 : ((133917/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1340019/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2588 e2588_ok ha1 ha2 hz1 hz2 hz

-- box ['1340019/8192000', '335217/2048000', '1999/2000', '7997/8000']  interval_lower 64688463/274877906944
noncomputable def e2589 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279365933432,0,true,166574344960,166574345024⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919657322120,0,false,-196395053696,-196395053632⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279479884284,0,true,166672272128,166672272192⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919543371268,0,false,-196531297984,-196531297920⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279276006279,0,true,166497057152,166497057216⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919747249273,0,false,-196287545024,-196287544960⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279412396188,0,true,166614275200,166614275264⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919610859364,0,false,-196450604416,-196450604352⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546016612,0,true,34388288,34388352⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477238940,0,false,-34389376,-34389312⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557510478,0,true,45881728,45881792⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465745074,0,false,-45883712,-45883648⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625861,0,false,-1920,-1856⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626701,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279320965368,0,true,166535697856,166535697920⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919702290184,0,false,-196341292672,-196341292608⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279446148827,0,true,166643281472,166643281536⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919577106725,0,false,-196490960704,-196490960640⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070065434531,0,false,-29847679232,-29847679168⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070106392699,0,false,-29805594752,-29805594688⟩
    { al := (1340019/8192000), au := (335217/2048000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨179854305656,179968256508⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166574344960,166574345024⟩ : DyadicInterval 40),(⟨-196395053696,-196395053632⟩ : DyadicInterval 40),(⟨747347099088,747347118417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166672272128,166672272192⟩ : DyadicInterval 40),(⟨-196531297984,-196531297920⟩ : DyadicInterval 40),(⟨747328284379,747328303709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166497057152,166497057216⟩ : DyadicInterval 40),(⟨-196287545024,-196287544960⟩ : DyadicInterval 40),(⟨747361938602,747361957932⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166614275200,166614275264⟩ : DyadicInterval 40),(⟨-196450604416,-196450604352⟩ : DyadicInterval 40),(⟨747339428975,747339448304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34388836,45882702⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34388288,34388352⟩ : DyadicInterval 40),(⟨-34389376,-34389312⟩ : DyadicInterval 40),(⟨762123383020,762123402349⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45881728,45881792⟩ : DyadicInterval 40),(⟨-45883712,-45883648⟩ : DyadicInterval 40),(⟨762123382629,762123401958⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1920,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179809337592,179934521051⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166535697856,166535697920⟩ : DyadicInterval 40),(⟨-196341292672,-196341292608⟩ : DyadicInterval 40),(⟨747354520539,747354539869⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166643281472,166643281536⟩ : DyadicInterval 40),(⟨-196490960704,-196490960640⟩ : DyadicInterval 40),(⟨747333855754,747333875083⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29847679232,-29805594688⟩ : DyadicInterval 40),(⟨777026180960,777047242496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166574344960,166672272192⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196531297984,-196395053632⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2589_ok : ecellOkT e2589 = true := by decide +kernel
theorem e2589_pos {a z : ℝ} (ha1 : ((1340019/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((335217/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2589 e2589_ok ha1 ha2 hz1 hz2 hz

-- box ['133917/819200', '1340019/8192000', '7997/8000', '3999/4000']  interval_lower 257278691/1099511627776
noncomputable def e2590 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279251982581,0,true,166476409024,166476409088⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919771272971,0,false,-196258826304,-196258826240⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279365933433,0,true,166574344960,166574345024⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919657322119,0,false,-196395053696,-196395053632⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279184579947,0,true,166418475264,166418475328⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919838675605,0,false,-196178254912,-196178254848⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279320969857,0,true,166535701696,166535701760⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919702285695,0,false,-196341298048,-196341297984⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534538536,0,true,22910464,22910528⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488717016,0,false,-22911040,-22910976⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546017298,0,true,34388928,34388992⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477238254,0,false,-34390080,-34390016⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626700,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627299,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279218276678,0,true,166447438592,166447438656⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919804978874,0,false,-196218534336,-196218534272⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279343460168,0,true,166555030848,166555030912⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919679795384,0,false,-196368185728,-196368185664⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070099034835,0,false,-29813154880,-29813154816⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070139969630,0,false,-29771095744,-29771095680⟩
    { al := (133917/819200), au := (1340019/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨179740354805,179854305657⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166476409024,166476409088⟩ : DyadicInterval 40),(⟨-196258826304,-196258826240⟩ : DyadicInterval 40),(⟨747365901695,747365921024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166574344960,166574345024⟩ : DyadicInterval 40),(⟨-196395053696,-196395053632⟩ : DyadicInterval 40),(⟨747347099088,747347118417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166418475264,166418475328⟩ : DyadicInterval 40),(⟨-196178254912,-196178254848⟩ : DyadicInterval 40),(⟨747377017812,747377037141⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166535701696,166535701760⟩ : DyadicInterval 40),(⟨-196341298048,-196341297984⟩ : DyadicInterval 40),(⟨747354519813,747354539143⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22910760,34389522⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22910464,22910528⟩ : DyadicInterval 40),(⟨-22911040,-22910976⟩ : DyadicInterval 40),(⟨762123383362,762123402691⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34388928,34388992⟩ : DyadicInterval 40),(⟨-34390080,-34390016⟩ : DyadicInterval 40),(⟨762123383052,762123402381⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179706648902,179831832392⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166447438592,166447438656⟩ : DyadicInterval 40),(⟨-196218534336,-196218534272⟩ : DyadicInterval 40),(⟨747371461014,747371480343⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166555030848,166555030912⟩ : DyadicInterval 40),(⟨-196368185728,-196368185664⟩ : DyadicInterval 40),(⟨747350808263,747350827592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29813154880,-29771095680⟩ : DyadicInterval 40),(⟨777008931456,777029980320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166476409024,166574345024⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196395053696,-196258826240⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2590_ok : ecellOkT e2590 = true := by decide +kernel
theorem e2590_pos {a z : ℝ} (ha1 : ((133917/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1340019/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2590 e2590_ok ha1 ha2 hz1 hz2 hz

-- box ['1340019/8192000', '335217/2048000', '7997/8000', '3999/4000']  interval_lower 258569109/1099511627776
noncomputable def e2591 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279365933432,0,true,166574344960,166574345024⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919657322120,0,false,-196395053696,-196395053632⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279479884284,0,true,166672272128,166672272192⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919543371268,0,false,-196531297984,-196531297920⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279298488067,0,true,166516379584,166516379648⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919724767485,0,false,-196314421184,-196314421120⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279434892221,0,true,166633607872,166633607936⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919588363331,0,false,-196477501632,-196477501568⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534553638,0,true,22925568,22925632⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488701914,0,false,-22926144,-22926080⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546039953,0,true,34411584,34411648⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477215599,0,false,-34412736,-34412672⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626698,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627298,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279332206164,0,true,166545358720,166545358784⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919691049388,0,false,-196354731200,-196354731136⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279457396776,0,true,166652947520,166652947584⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919565858776,0,false,-196504409664,-196504409600⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070061752974,0,false,-29851462080,-29851462016⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070102716042,0,false,-29809372480,-29809372416⟩
    { al := (1340019/8192000), au := (335217/2048000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨179854305656,179968256508⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166574344960,166574345024⟩ : DyadicInterval 40),(⟨-196395053696,-196395053632⟩ : DyadicInterval 40),(⟨747347099088,747347118417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166672272128,166672272192⟩ : DyadicInterval 40),(⟨-196531297984,-196531297920⟩ : DyadicInterval 40),(⟨747328284379,747328303709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166516379584,166516379648⟩ : DyadicInterval 40),(⟨-196314421184,-196314421120⟩ : DyadicInterval 40),(⟨747358229440,747358248770⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166633607872,166633607936⟩ : DyadicInterval 40),(⟨-196477501632,-196477501568⟩ : DyadicInterval 40),(⟨747335714577,747335733906⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22925862,34412177⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22925568,22925632⟩ : DyadicInterval 40),(⟨-22926144,-22926080⟩ : DyadicInterval 40),(⟨762123383361,762123402690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34411584,34411648⟩ : DyadicInterval 40),(⟨-34412736,-34412672⟩ : DyadicInterval 40),(⟨762123383050,762123402379⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179820578388,179945769000⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166545358720,166545358784⟩ : DyadicInterval 40),(⟨-196354731200,-196354731136⟩ : DyadicInterval 40),(⟨747352665540,747352684870⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166652947520,166652947584⟩ : DyadicInterval 40),(⟨-196504409664,-196504409600⟩ : DyadicInterval 40),(⟨747331998289,747332017619⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29851462080,-29809372416⟩ : DyadicInterval 40),(⟨777028069824,777049133920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166574344960,166672272192⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196531297984,-196395053632⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2591_ok : ecellOkT e2591 = true := by decide +kernel
theorem e2591_pos {a z : ℝ} (ha1 : ((1340019/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((335217/2048000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2591 e2591_ok ha1 ha2 hz1 hz2 hz

-- box ['10449/64000', '1338321/8192000', '3999/4000', '7999/8000']  interval_lower 254523087/1099511627776
noncomputable def e2592 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279024080879,0,true,166280511040,166280511104⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919999174673,0,false,-195986422144,-195986422080⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279138031731,0,true,166378464448,166378464512⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919885223821,0,false,-196122615744,-196122615680⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278979202765,0,true,166241930944,166241931008⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920044052787,0,false,-195932788608,-195932788544⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279115578431,0,true,166359164032,166359164096⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919907677121,0,false,-196095778304,-196095778240⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523067956,0,true,11440064,11440128⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500187596,0,false,-11440256,-11440192⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534524064,0,true,22896000,22896064⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488731488,0,false,-22896576,-22896512⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627299,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627657,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279001637170,0,true,166261217152,166261217216⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920021618382,0,false,-195959599488,-195959599424⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279126813571,0,true,166368821568,166368821632⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919896441981,0,false,-196109207104,-196109207040⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070169859891,0,false,-29740385536,-29740385472⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070210743040,0,false,-29698382272,-29698382208⟩
    { al := (10449/64000), au := (1338321/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨179512453103,179626403955⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166280511040,166280511104⟩ : DyadicInterval 40),(⟨-195986422144,-195986422080⟩ : DyadicInterval 40),(⟨747403470472,747403489801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166378464448,166378464512⟩ : DyadicInterval 40),(⟨-196122615744,-196122615680⟩ : DyadicInterval 40),(⟨747384692101,747384711430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166241930944,166241931008⟩ : DyadicInterval 40),(⟨-195932788608,-195932788544⟩ : DyadicInterval 40),(⟨747410862745,747410882075⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166359164032,166359164096⟩ : DyadicInterval 40),(⟨-196095778304,-196095778240⟩ : DyadicInterval 40),(⟨747388393217,747388412547⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11440180,22896288⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11440064,11440128⟩ : DyadicInterval 40),(⟨-11440256,-11440192⟩ : DyadicInterval 40),(⟨762123383528,762123402857⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22896000,22896064⟩ : DyadicInterval 40),(⟨-22896576,-22896512⟩ : DyadicInterval 40),(⟨762123383363,762123402692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179490009394,179615185795⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166261217152,166261217216⟩ : DyadicInterval 40),(⟨-195959599488,-195959599424⟩ : DyadicInterval 40),(⟨747407167615,747407186945⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166368821568,166368821632⟩ : DyadicInterval 40),(⟨-196109207104,-196109207040⟩ : DyadicInterval 40),(⟨747386541331,747386560661⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29740385536,-29698382208⟩ : DyadicInterval 40),(⟨776972574720,776993595648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166280511040,166378464512⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196122615744,-195986422080⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2592_ok : ecellOkT e2592 = true := by decide +kernel
theorem e2592_pos {a z : ℝ} (ha1 : ((10449/64000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1338321/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2592 e2592_ok ha1 ha2 hz1 hz2 hz

-- box ['1338321/8192000', '133917/819200', '3999/4000', '7999/8000']  interval_lower 127903567/549755813888
noncomputable def e2593 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279138031730,0,true,166378464448,166378464512⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919885223822,0,false,-196122615744,-196122615680⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279251982582,0,true,166476409024,166476409088⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919771272970,0,false,-196258826304,-196258826240⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279093125129,0,true,166339863296,166339863360⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919930130423,0,false,-196068941568,-196068941504⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279229515038,0,true,166457098112,166457098176⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919793740514,0,false,-196231968512,-196231968448⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523075506,0,true,11447616,11447680⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500180046,0,false,-11447808,-11447744⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534539165,0,true,22911104,22911168⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488716387,0,false,-22911680,-22911616⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627298,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627657,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279115573784,0,true,166359160000,166359160064⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919907681768,0,false,-196095772800,-196095772736⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279240757291,0,true,166466760896,166466760960⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919782498261,0,false,-196245407424,-196245407360⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070132620605,0,false,-29778646528,-29778646464⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070173532019,0,false,-29736612736,-29736612672⟩
    { al := (1338321/8192000), au := (133917/819200), zl := (3999/4000), zu := (7999/8000),
      A := ⟨179626403954,179740354806⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166378464448,166378464512⟩ : DyadicInterval 40),(⟨-196122615744,-196122615680⟩ : DyadicInterval 40),(⟨747384692101,747384711430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166476409024,166476409088⟩ : DyadicInterval 40),(⟨-196258826304,-196258826240⟩ : DyadicInterval 40),(⟨747365901695,747365921024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166339863296,166339863360⟩ : DyadicInterval 40),(⟨-196068941568,-196068941504⟩ : DyadicInterval 40),(⟨747392093872,747392113202⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166457098112,166457098176⟩ : DyadicInterval 40),(⟨-196231968512,-196231968448⟩ : DyadicInterval 40),(⟨747369607535,747369626865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11447730,22911389⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11447616,11447680⟩ : DyadicInterval 40),(⟨-11447808,-11447744⟩ : DyadicInterval 40),(⟨762123383528,762123402857⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22911104,22911168⟩ : DyadicInterval 40),(⟨-22911680,-22911616⟩ : DyadicInterval 40),(⟨762123383362,762123402691⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179603946008,179729129515⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166359160000,166359160064⟩ : DyadicInterval 40),(⟨-196095772800,-196095772736⟩ : DyadicInterval 40),(⟨747388394026,747388413355⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166466760896,166466760960⟩ : DyadicInterval 40),(⟨-196245407424,-196245407360⟩ : DyadicInterval 40),(⟨747367753261,747367772590⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29778646528,-29736612672⟩ : DyadicInterval 40),(⟨776991689952,777012726144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166378464448,166476409088⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196258826304,-196122615680⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2593_ok : ecellOkT e2593 = true := by decide +kernel
theorem e2593_pos {a z : ℝ} (ha1 : ((1338321/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((133917/819200 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2593 e2593_ok ha1 ha2 hz1 hz2 hz

-- box ['10449/64000', '1338321/8192000', '7999/8000', '1']  interval_lower 254339627/1099511627776
noncomputable def e2594 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279024080879,0,true,166280511040,166280511104⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919999174673,0,false,-195986422144,-195986422080⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279138031731,0,true,166378464448,166378464512⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919885223821,0,false,-196122615744,-196122615680⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279001641822,0,true,166261221184,166261221248⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920021613730,0,false,-195959604992,-195959604928⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523076078,0,true,11448192,11448256⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500179474,0,false,-11448384,-11448320⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627656,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1279012856662,0,true,166270862144,166270862208⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨920010398890,0,false,-195973007872,-195973007808⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1279138040208,0,true,166378471680,166378471744⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨919885215344,0,false,-196122625920,-196122625856⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1070166191831,0,false,-29744154176,-29744154112⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1070207079868,0,false,-29702145728,-29702145664⟩
    { al := (10449/64000), au := (1338321/8192000), zl := (7999/8000), zu := 1,
      A := ⟨179512453103,179626403955⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166280511040,166280511104⟩ : DyadicInterval 40),(⟨-195986422144,-195986422080⟩ : DyadicInterval 40),(⟨747403470472,747403489801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166378464448,166378464512⟩ : DyadicInterval 40),(⟨-196122615744,-196122615680⟩ : DyadicInterval 40),(⟨747384692101,747384711430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166261221184,166261221248⟩ : DyadicInterval 40),(⟨-195959604992,-195959604928⟩ : DyadicInterval 40),(⟨747407166807,747407186136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166378464448,166378464512⟩ : DyadicInterval 40),(⟨-196122615744,-196122615680⟩ : DyadicInterval 40),(⟨747384692101,747384711430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11448302⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11448192,11448256⟩ : DyadicInterval 40),(⟨-11448384,-11448320⟩ : DyadicInterval 40),(⟨762123383528,762123402857⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨179501228886,179626412432⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166270862144,166270862208⟩ : DyadicInterval 40),(⟨-195973007872,-195973007808⟩ : DyadicInterval 40),(⟨747405319454,747405338783⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166378471680,166378471744⟩ : DyadicInterval 40),(⟨-196122625920,-196122625856⟩ : DyadicInterval 40),(⟨747384690753,747384710083⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29744154176,-29702145664⟩ : DyadicInterval 40),(⟨776974456448,776995479968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨166280511040,166378464512⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196122615744,-195986422080⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2594_ok : ecellOkT e2594 = true := by decide +kernel
theorem e2594_pos {a z : ℝ} (ha1 : ((10449/64000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1338321/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2594 e2594_ok ha1 ha2 hz1 hz2 hz

-- box ['1338321/8192000', '133917/819200', '7999/8000', '1']  interval_lower 127811637/549755813888
noncomputable def e2595 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279138031730,0,true,166378464448,166378464512⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919885223822,0,false,-196122615744,-196122615680⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279251982582,0,true,166476409024,166476409088⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919771272970,0,false,-196258826304,-196258826240⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279115578429,0,true,166359164032,166359164096⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919907677123,0,false,-196095778304,-196095778240⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523083628,0,true,11455744,11455808⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500171924,0,false,-11455936,-11455872⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627656,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1279126800395,0,true,166368810240,166368810304⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨919896455157,0,false,-196109191360,-196109191296⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1279251991047,0,true,166476416320,166476416384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨919771264505,0,false,-196258836416,-196258836352⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1070128947890,0,false,-29782420032,-29782419968⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1070169864197,0,false,-29740381120,-29740381056⟩
    { al := (1338321/8192000), au := (133917/819200), zl := (7999/8000), zu := 1,
      A := ⟨179626403954,179740354806⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166378464448,166378464512⟩ : DyadicInterval 40),(⟨-196122615744,-196122615680⟩ : DyadicInterval 40),(⟨747384692101,747384711430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166476409024,166476409088⟩ : DyadicInterval 40),(⟨-196258826304,-196258826240⟩ : DyadicInterval 40),(⟨747365901695,747365921024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166359164032,166359164096⟩ : DyadicInterval 40),(⟨-196095778304,-196095778240⟩ : DyadicInterval 40),(⟨747388393217,747388412547⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166476409024,166476409088⟩ : DyadicInterval 40),(⟨-196258826304,-196258826240⟩ : DyadicInterval 40),(⟨747365901695,747365921024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11455852⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11455744,11455808⟩ : DyadicInterval 40),(⟨-11455936,-11455872⟩ : DyadicInterval 40),(⟨762123383528,762123402857⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨179615172619,179740363271⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166368810240,166368810304⟩ : DyadicInterval 40),(⟨-196109191360,-196109191296⟩ : DyadicInterval 40),(⟨747386543506,747386562836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166476416320,166476416384⟩ : DyadicInterval 40),(⟨-196258836416,-196258836352⟩ : DyadicInterval 40),(⟨747365900284,747365919613⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29782420032,-29740381056⟩ : DyadicInterval 40),(⟨776993574144,777014612896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨166378464448,166476409088⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196258826304,-196122615680⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2595_ok : ecellOkT e2595 = true := by decide +kernel
theorem e2595_pos {a z : ℝ} (ha1 : ((1338321/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((133917/819200 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2595 e2595_ok ha1 ha2 hz1 hz2 hz

-- box ['133917/819200', '1340019/8192000', '3999/4000', '7999/8000']  interval_lower 128547081/549755813888
noncomputable def e2596 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279251982581,0,true,166476409024,166476409088⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919771272971,0,false,-196258826304,-196258826240⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279365933433,0,true,166574344960,166574345024⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919657322119,0,false,-196395053696,-196395053632⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279207047492,0,true,166437786880,166437786944⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919816208060,0,false,-196205111360,-196205111296⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279343451645,0,true,166555023488,166555023552⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919679803907,0,false,-196368175552,-196368175488⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523083056,0,true,11455168,11455232⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500172496,0,false,-11455360,-11455296⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534554267,0,true,22926208,22926272⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488701285,0,false,-22926784,-22926720⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627297,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627657,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279229510384,0,true,166457094144,166457094208⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919793745168,0,false,-196231962944,-196231962880⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279354701021,0,true,166564691584,166564691648⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919668554531,0,false,-196381624640,-196381624576⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070095357700,0,false,-29816933056,-29816932992⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070136297391,0,false,-29774868800,-29774868736⟩
    { al := (133917/819200), au := (1340019/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨179740354805,179854305657⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166476409024,166476409088⟩ : DyadicInterval 40),(⟨-196258826304,-196258826240⟩ : DyadicInterval 40),(⟨747365901695,747365921024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166574344960,166574345024⟩ : DyadicInterval 40),(⟨-196395053696,-196395053632⟩ : DyadicInterval 40),(⟨747347099088,747347118417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166437786880,166437786944⟩ : DyadicInterval 40),(⟨-196205111360,-196205111296⟩ : DyadicInterval 40),(⟨747373312886,747373332216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166555023488,166555023552⟩ : DyadicInterval 40),(⟨-196368175552,-196368175488⟩ : DyadicInterval 40),(⟨747350809696,747350829025⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11455280,22926491⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11455168,11455232⟩ : DyadicInterval 40),(⟨-11455360,-11455296⟩ : DyadicInterval 40),(⟨762123383528,762123402857⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22926208,22926272⟩ : DyadicInterval 40),(⟨-22926784,-22926720⟩ : DyadicInterval 40),(⟨762123383361,762123402690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179717882608,179843073245⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166457094144,166457094208⟩ : DyadicInterval 40),(⟨-196231962944,-196231962880⟩ : DyadicInterval 40),(⟨747369608282,747369627612⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166564691584,166564691648⟩ : DyadicInterval 40),(⟨-196381624640,-196381624576⟩ : DyadicInterval 40),(⟨747348953017,747348972346⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29816933056,-29774868736⟩ : DyadicInterval 40),(⟨777010817984,777031869408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166476409024,166574345024⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196395053696,-196258826240⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2596_ok : ecellOkT e2596 = true := by decide +kernel
theorem e2596_pos {a z : ℝ} (ha1 : ((133917/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1340019/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2596 e2596_ok ha1 ha2 hz1 hz2 hz

-- box ['1340019/8192000', '335217/2048000', '3999/4000', '7999/8000']  interval_lower 129191959/549755813888
noncomputable def e2597 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279365933432,0,true,166574344960,166574345024⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919657322120,0,false,-196395053696,-196395053632⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279479884284,0,true,166672272128,166672272192⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919543371268,0,false,-196531297984,-196531297920⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279320969855,0,true,166535701696,166535701760⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919702285697,0,false,-196341298048,-196341297984⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279457388253,0,true,166652940160,166652940224⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919565867299,0,false,-196504399424,-196504399360⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523090607,0,true,11462720,11462784⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500164945,0,false,-11462912,-11462848⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534569370,0,true,22941312,22941376⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488686182,0,false,-22941888,-22941824⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627297,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627657,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279343446987,0,true,166555019520,166555019584⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919679808565,0,false,-196368169984,-196368169920⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279468644752,0,true,166662613504,166662613568⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919554610800,0,false,-196517858752,-196517858688⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070058071177,0,false,-29855245248,-29855245184⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070099039147,0,false,-29813150400,-29813150336⟩
    { al := (1340019/8192000), au := (335217/2048000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨179854305656,179968256508⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166574344960,166574345024⟩ : DyadicInterval 40),(⟨-196395053696,-196395053632⟩ : DyadicInterval 40),(⟨747347099088,747347118417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166672272128,166672272192⟩ : DyadicInterval 40),(⟨-196531297984,-196531297920⟩ : DyadicInterval 40),(⟨747328284379,747328303709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166535701696,166535701760⟩ : DyadicInterval 40),(⟨-196341298048,-196341297984⟩ : DyadicInterval 40),(⟨747354519813,747354539143⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166652940160,166652940224⟩ : DyadicInterval 40),(⟨-196504399424,-196504399360⟩ : DyadicInterval 40),(⟨747331999697,747332019026⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11462831,22941594⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11462720,11462784⟩ : DyadicInterval 40),(⟨-11462912,-11462848⟩ : DyadicInterval 40),(⟨762123383528,762123402857⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22941312,22941376⟩ : DyadicInterval 40),(⟨-22941888,-22941824⟩ : DyadicInterval 40),(⟨762123383361,762123402690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179831819211,179957016976⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166555019520,166555019584⟩ : DyadicInterval 40),(⟨-196368169984,-196368169920⟩ : DyadicInterval 40),(⟨747350810444,747350829774⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166662613504,166662613568⟩ : DyadicInterval 40),(⟨-196517858752,-196517858688⟩ : DyadicInterval 40),(⟨747330140675,747330160004⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29855245248,-29813150336⟩ : DyadicInterval 40),(⟨777029958784,777051025504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166574344960,166672272192⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196531297984,-196395053632⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2597_ok : ecellOkT e2597 = true := by decide +kernel
theorem e2597_pos {a z : ℝ} (ha1 : ((1340019/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((335217/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2597 e2597_ok ha1 ha2 hz1 hz2 hz

-- box ['133917/819200', '1340019/8192000', '7999/8000', '1']  interval_lower 256909461/1099511627776
noncomputable def e2598 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279251982581,0,true,166476409024,166476409088⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919771272971,0,false,-196258826304,-196258826240⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279365933433,0,true,166574344960,166574345024⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919657322119,0,false,-196395053696,-196395053632⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279229515036,0,true,166457098112,166457098176⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919793740516,0,false,-196231968512,-196231968448⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523091179,0,true,11463296,11463360⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500164373,0,false,-11463488,-11463424⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627656,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1279240744112,0,true,166466749568,166466749632⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨919782511440,0,false,-196245391680,-196245391616⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1279365941903,0,true,166574352256,166574352320⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨919657313649,0,false,-196395063808,-196395063744⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1070091680325,0,false,-29820711552,-29820711488⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1070132624915,0,false,-29778642048,-29778641984⟩
    { al := (133917/819200), au := (1340019/8192000), zl := (7999/8000), zu := 1,
      A := ⟨179740354805,179854305657⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166476409024,166476409088⟩ : DyadicInterval 40),(⟨-196258826304,-196258826240⟩ : DyadicInterval 40),(⟨747365901695,747365921024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166574344960,166574345024⟩ : DyadicInterval 40),(⟨-196395053696,-196395053632⟩ : DyadicInterval 40),(⟨747347099088,747347118417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166457098112,166457098176⟩ : DyadicInterval 40),(⟨-196231968512,-196231968448⟩ : DyadicInterval 40),(⟨747369607535,747369626865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166574344960,166574345024⟩ : DyadicInterval 40),(⟨-196395053696,-196395053632⟩ : DyadicInterval 40),(⟨747347099088,747347118417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11463403⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11463296,11463360⟩ : DyadicInterval 40),(⟨-11463488,-11463424⟩ : DyadicInterval 40),(⟨762123383528,762123402857⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨179729116336,179854314127⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166466749568,166466749632⟩ : DyadicInterval 40),(⟨-196245391680,-196245391616⟩ : DyadicInterval 40),(⟨747367755439,747367774768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166574352256,166574352320⟩ : DyadicInterval 40),(⟨-196395063808,-196395063744⟩ : DyadicInterval 40),(⟨747347097674,747347117003⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29820711552,-29778641984⟩ : DyadicInterval 40),(⟨777012704608,777033758656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨166476409024,166574345024⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196395053696,-196258826240⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2598_ok : ecellOkT e2598 = true := by decide +kernel
theorem e2598_pos {a z : ℝ} (ha1 : ((133917/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1340019/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2598 e2598_ok ha1 ha2 hz1 hz2 hz

-- box ['1340019/8192000', '335217/2048000', '7999/8000', '1']  interval_lower 64549797/274877906944
noncomputable def e2599 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279365933432,0,true,166574344960,166574345024⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919657322120,0,false,-196395053696,-196395053632⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279479884284,0,true,166672272128,166672272192⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919543371268,0,false,-196531297984,-196531297920⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279343451643,0,true,166555023488,166555023552⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919679803909,0,false,-196368175552,-196368175488⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523098730,0,true,11470848,11470912⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500156822,0,false,-11471040,-11470976⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627656,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1279354687839,0,true,166564680256,166564680320⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨919668567713,0,false,-196381608896,-196381608832⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1279479892750,0,true,166672279424,166672279488⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨919543362802,0,false,-196531308096,-196531308032⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1070054389144,0,false,-29859028608,-29859028544⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1070095362013,0,false,-29816928640,-29816928576⟩
    { al := (1340019/8192000), au := (335217/2048000), zl := (7999/8000), zu := 1,
      A := ⟨179854305656,179968256508⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166574344960,166574345024⟩ : DyadicInterval 40),(⟨-196395053696,-196395053632⟩ : DyadicInterval 40),(⟨747347099088,747347118417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166672272128,166672272192⟩ : DyadicInterval 40),(⟨-196531297984,-196531297920⟩ : DyadicInterval 40),(⟨747328284379,747328303709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166555023488,166555023552⟩ : DyadicInterval 40),(⟨-196368175552,-196368175488⟩ : DyadicInterval 40),(⟨747350809696,747350829026⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166672272128,166672272192⟩ : DyadicInterval 40),(⟨-196531297984,-196531297920⟩ : DyadicInterval 40),(⟨747328284379,747328303709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11470954⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11470848,11470912⟩ : DyadicInterval 40),(⟨-11471040,-11470976⟩ : DyadicInterval 40),(⟨762123383528,762123402857⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨179843060063,179968264974⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166564680256,166564680320⟩ : DyadicInterval 40),(⟨-196381608896,-196381608832⟩ : DyadicInterval 40),(⟨747348955198,747348974528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166672279424,166672279488⟩ : DyadicInterval 40),(⟨-196531308096,-196531308032⟩ : DyadicInterval 40),(⟨747328282964,747328302294⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29859028608,-29816928576⟩ : DyadicInterval 40),(⟨777031847904,777052917184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨166574344960,166672272192⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196531297984,-196395053632⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2599_ok : ecellOkT e2599 = true := by decide +kernel
theorem e2599_pos {a z : ℝ} (ha1 : ((1340019/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((335217/2048000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2599 e2599_ok ha1 ha2 hz1 hz2 hz

-- box ['335217/2048000', '1341717/8192000', '1999/2000', '7997/8000']  interval_lower 16252977/68719476736
noncomputable def e2600 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279479884283,0,true,166672272128,166672272192⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919543371269,0,false,-196531297984,-196531297920⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279593835135,0,true,166770190592,166770190656⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919429420417,0,false,-196667559104,-196667559040⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279389900154,0,true,166594942208,166594942272⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919633355398,0,false,-196423707840,-196423707776⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279526304308,0,true,166712162112,166712162176⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919496951244,0,false,-196586804480,-196586804416⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546039266,0,true,34410944,34411008⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477216286,0,false,-34412032,-34411968⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557540685,0,true,45911936,45912000⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465714867,0,false,-45913920,-45913856⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625858,0,false,-1920,-1856⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626700,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279434887725,0,true,166633604032,166633604096⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919588367827,0,false,-196477496256,-196477496192⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279560078315,0,true,166741184128,166741184192⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919463177237,0,false,-196627191360,-196627191296⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070028133720,0,false,-29886007168,-29886007104⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070069120164,0,false,-29843892160,-29843892096⟩
    { al := (335217/2048000), au := (1341717/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨179968256507,180082207359⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166672272128,166672272192⟩ : DyadicInterval 40),(⟨-196531297984,-196531297920⟩ : DyadicInterval 40),(⟨747328284379,747328303709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166770190592,166770190656⟩ : DyadicInterval 40),(⟨-196667559104,-196667559040⟩ : DyadicInterval 40),(⟨747309457504,747309476833⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166594942208,166594942272⟩ : DyadicInterval 40),(⟨-196423707840,-196423707776⟩ : DyadicInterval 40),(⟨747343142881,747343162210⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166712162112,166712162176⟩ : DyadicInterval 40),(⟨-196586804480,-196586804416⟩ : DyadicInterval 40),(⟨747320616362,747320635691⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34411490,45912909⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34410944,34411008⟩ : DyadicInterval 40),(⟨-34412032,-34411968⟩ : DyadicInterval 40),(⟨762123383019,762123402348⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45911936,45912000⟩ : DyadicInterval 40),(⟨-45913920,-45913856⟩ : DyadicInterval 40),(⟨762123382626,762123401955⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1920,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179923259949,180048450539⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166633604032,166633604096⟩ : DyadicInterval 40),(⟨-196477496256,-196477496192⟩ : DyadicInterval 40),(⟨747335715305,747335734634⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166741184128,166741184192⟩ : DyadicInterval 40),(⟨-196627191360,-196627191296⟩ : DyadicInterval 40),(⟨747315036054,747315055384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29886007168,-29843892096⟩ : DyadicInterval 40),(⟨777045329664,777066406464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166672272128,166770190656⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196667559104,-196531297920⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2600_ok : ecellOkT e2600 = true := by decide +kernel
theorem e2600_pos {a z : ℝ} (ha1 : ((335217/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1341717/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2600 e2600_ok ha1 ha2 hz1 hz2 hz

-- box ['1341717/8192000', '671283/4096000', '1999/2000', '7997/8000']  interval_lower 130672155/549755813888
noncomputable def e2601 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279593835134,0,true,166770190592,166770190656⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919429420418,0,false,-196667559104,-196667559040⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279707785987,0,true,166868100352,166868100416⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919315469565,0,false,-196803837184,-196803837120⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279503794030,0,true,166692818624,166692818688⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919519461522,0,false,-196559887552,-196559887488⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279640212428,0,true,166810040320,166810040384⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919383043124,0,false,-196723021440,-196723021376⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546061921,0,true,34433600,34433664⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477193631,0,false,-34434688,-34434624⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557570895,0,true,45942144,45942208⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465684657,0,false,-45944128,-45944064⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625856,0,false,-1984,-1920⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626698,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279548810090,0,true,166731501440,166731501504⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919474445462,0,false,-196613716672,-196613716608⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279674007801,0,true,166839078080,166839078144⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919349247751,0,false,-196763438848,-196763438784⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069990809299,0,false,-29924360704,-29924360640⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070031824019,0,false,-29882215168,-29882215104⟩
    { al := (1341717/8192000), au := (671283/4096000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨180082207358,180196158211⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166770190592,166770190656⟩ : DyadicInterval 40),(⟨-196667559104,-196667559040⟩ : DyadicInterval 40),(⟨747309457504,747309476833⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166868100352,166868100416⟩ : DyadicInterval 40),(⟨-196803837184,-196803837120⟩ : DyadicInterval 40),(⟨747290618514,747290637844⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166692818624,166692818688⟩ : DyadicInterval 40),(⟨-196559887552,-196559887488⟩ : DyadicInterval 40),(⟨747324335007,747324354337⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166810040320,166810040384⟩ : DyadicInterval 40),(⟨-196723021440,-196723021376⟩ : DyadicInterval 40),(⟨747301791627,747301810957⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34434145,45943119⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34433600,34433664⟩ : DyadicInterval 40),(⟨-34434688,-34434624⟩ : DyadicInterval 40),(⟨762123383017,762123402346⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45942144,45942208⟩ : DyadicInterval 40),(⟨-45944128,-45944064⟩ : DyadicInterval 40),(⟨762123382624,762123401953⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1984,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180037182314,180162380025⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166731501440,166731501504⟩ : DyadicInterval 40),(⟨-196613716672,-196613716608⟩ : DyadicInterval 40),(⟨747316897952,747316917282⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166839078080,166839078144⟩ : DyadicInterval 40),(⟨-196763438848,-196763438784⟩ : DyadicInterval 40),(⟨747296204197,747296223526⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29924360704,-29882215104⟩ : DyadicInterval 40),(⟨777064491168,777085583232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166770190592,166868100416⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196803837184,-196667559040⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2601_ok : ecellOkT e2601 = true := by decide +kernel
theorem e2601_pos {a z : ℝ} (ha1 : ((1341717/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((671283/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2601 e2601_ok ha1 ha2 hz1 hz2 hz

-- box ['335217/2048000', '1341717/8192000', '7997/8000', '3999/4000']  interval_lower 259862453/1099511627776
noncomputable def e2602 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279479884283,0,true,166672272128,166672272192⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919543371269,0,false,-196531297984,-196531297920⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279593835135,0,true,166770190592,166770190656⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919429420417,0,false,-196667559104,-196667559040⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279412396186,0,true,166614275200,166614275264⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919610859366,0,false,-196450604416,-196450604352⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279548814584,0,true,166731505280,166731505344⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919474440968,0,false,-196613722048,-196613721984⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534568740,0,true,22940672,22940736⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488686812,0,false,-22941248,-22941184⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546062608,0,true,34434240,34434304⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477192944,0,false,-34435392,-34435328⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626697,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627298,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279446135642,0,true,166643270144,166643270208⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919577119910,0,false,-196490944960,-196490944896⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279571333384,0,true,166750855424,166750855488⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919451922168,0,false,-196640650432,-196640650368⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070024447500,0,false,-29889794944,-29889794880⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070065438848,0,false,-29847674816,-29847674752⟩
    { al := (335217/2048000), au := (1341717/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨179968256507,180082207359⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166672272128,166672272192⟩ : DyadicInterval 40),(⟨-196531297984,-196531297920⟩ : DyadicInterval 40),(⟨747328284379,747328303709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166770190592,166770190656⟩ : DyadicInterval 40),(⟨-196667559104,-196667559040⟩ : DyadicInterval 40),(⟨747309457504,747309476833⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166614275200,166614275264⟩ : DyadicInterval 40),(⟨-196450604416,-196450604352⟩ : DyadicInterval 40),(⟨747339428975,747339448305⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166731505280,166731505344⟩ : DyadicInterval 40),(⟨-196613722048,-196613721984⟩ : DyadicInterval 40),(⟨747316897223,747316916553⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22940964,34434832⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22940672,22940736⟩ : DyadicInterval 40),(⟨-22941248,-22941184⟩ : DyadicInterval 40),(⟨762123383361,762123402690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34434240,34434304⟩ : DyadicInterval 40),(⟨-34435392,-34435328⟩ : DyadicInterval 40),(⟨762123383049,762123402378⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179934507866,180059705608⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166643270144,166643270208⟩ : DyadicInterval 40),(⟨-196490944960,-196490944896⟩ : DyadicInterval 40),(⟨747333857938,747333877268⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166750855424,166750855488⟩ : DyadicInterval 40),(⟨-196640650432,-196640650368⟩ : DyadicInterval 40),(⟨747313176193,747313195522⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29889794944,-29847674752⟩ : DyadicInterval 40),(⟨777047220992,777068300352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166672272128,166770190656⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196667559104,-196531297920⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2602_ok : ecellOkT e2602 = true := by decide +kernel
theorem e2602_pos {a z : ℝ} (ha1 : ((335217/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1341717/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2602 e2602_ok ha1 ha2 hz1 hz2 hz

-- box ['1341717/8192000', '671283/4096000', '7997/8000', '3999/4000']  interval_lower 130579423/549755813888
noncomputable def e2603 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279593835134,0,true,166770190592,166770190656⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919429420418,0,false,-196667559104,-196667559040⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279707785987,0,true,166868100352,166868100416⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919315469565,0,false,-196803837184,-196803837120⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279526304306,0,true,166712162112,166712162176⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919496951246,0,false,-196586804480,-196586804416⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279662736948,0,true,166829393984,166829394048⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919360518604,0,false,-196749959360,-196749959296⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534583844,0,true,22955776,22955840⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488671708,0,false,-22956352,-22956288⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546085265,0,true,34456896,34456960⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477170287,0,false,-34458048,-34457984⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626696,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627297,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279560065128,0,true,166741172800,166741172864⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919463190424,0,false,-196627175552,-196627175488⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279685269991,0,true,166848754688,166848754752⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919337985561,0,false,-196776908096,-196776908032⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069987118412,0,false,-29928153408,-29928153344⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070028138040,0,false,-29886002752,-29886002688⟩
    { al := (1341717/8192000), au := (671283/4096000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨180082207358,180196158211⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166770190592,166770190656⟩ : DyadicInterval 40),(⟨-196667559104,-196667559040⟩ : DyadicInterval 40),(⟨747309457504,747309476833⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166868100352,166868100416⟩ : DyadicInterval 40),(⟨-196803837184,-196803837120⟩ : DyadicInterval 40),(⟨747290618514,747290637844⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166712162112,166712162176⟩ : DyadicInterval 40),(⟨-196586804480,-196586804416⟩ : DyadicInterval 40),(⟨747320616362,747320635692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166829393984,166829394048⟩ : DyadicInterval 40),(⟨-196749959360,-196749959296⟩ : DyadicInterval 40),(⟨747298067741,747298087071⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22956068,34457489⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22955776,22955840⟩ : DyadicInterval 40),(⟨-22956352,-22956288⟩ : DyadicInterval 40),(⟨762123383360,762123402689⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34456896,34456960⟩ : DyadicInterval 40),(⟨-34458048,-34457984⟩ : DyadicInterval 40),(⟨762123383048,762123402377⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180048437352,180173642215⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166741172800,166741172864⟩ : DyadicInterval 40),(⟨-196627175552,-196627175488⟩ : DyadicInterval 40),(⟨747315038215,747315057545⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166848754688,166848754752⟩ : DyadicInterval 40),(⟨-196776908096,-196776908032⟩ : DyadicInterval 40),(⟨747294341924,747294361253⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29928153408,-29886002688⟩ : DyadicInterval 40),(⟨777066384960,777087479584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166770190592,166868100416⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196803837184,-196667559040⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2603_ok : ecellOkT e2603 = true := by decide +kernel
theorem e2603_pos {a z : ℝ} (ha1 : ((1341717/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((671283/4096000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2603 e2603_ok ha1 ha2 hz1 hz2 hz

-- box ['671283/4096000', '268683/1638400', '1999/2000', '7997/8000']  interval_lower 262644075/1099511627776
noncomputable def e2604 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279707785986,0,true,166868100352,166868100416⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919315469566,0,false,-196803837184,-196803837120⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279821736838,0,true,166966001408,166966001472⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919201518714,0,false,-196940132096,-196940132032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279617687906,0,true,166790686272,166790686336⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919405567646,0,false,-196696084160,-196696084096⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279754120548,0,true,166907909824,166907909888⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919269135004,0,false,-196859255232,-196859255168⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546084578,0,true,34456256,34456320⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477170974,0,false,-34457344,-34457280⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557601108,0,true,45972352,45972416⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465654444,0,false,-45974336,-45974272⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625853,0,false,-1984,-1920⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626697,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279662732447,0,true,166829390144,166829390208⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919360523105,0,false,-196749953984,-196749953920⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279787937292,0,true,166936963392,166936963456⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919235318260,0,false,-196899703232,-196899703168⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069953461266,0,false,-29962739840,-29962739776⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069994504270,0,false,-29920563776,-29920563712⟩
    { al := (671283/4096000), au := (268683/1638400), zl := (1999/2000), zu := (7997/8000),
      A := ⟨180196158210,180310109062⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166868100352,166868100416⟩ : DyadicInterval 40),(⟨-196803837184,-196803837120⟩ : DyadicInterval 40),(⟨747290618514,747290637844⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166966001408,166966001472⟩ : DyadicInterval 40),(⟨-196940132096,-196940132032⟩ : DyadicInterval 40),(⟨747271767356,747271786685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166790686272,166790686336⟩ : DyadicInterval 40),(⟨-196696084160,-196696084096⟩ : DyadicInterval 40),(⟨747305515055,747305534385⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166907909824,166907909888⟩ : DyadicInterval 40),(⟨-196859255232,-196859255168⟩ : DyadicInterval 40),(⟨747282954742,747282974071⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34456802,45973332⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34456256,34456320⟩ : DyadicInterval 40),(⟨-34457344,-34457280⟩ : DyadicInterval 40),(⟨762123383016,762123402345⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45972352,45972416⟩ : DyadicInterval 40),(⟨-45974336,-45974272⟩ : DyadicInterval 40),(⟨762123382621,762123401950⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1984,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180151104671,180276309516⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166829390144,166829390208⟩ : DyadicInterval 40),(⟨-196749953984,-196749953920⟩ : DyadicInterval 40),(⟨747298068473,747298087802⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166936963392,166936963456⟩ : DyadicInterval 40),(⟨-196899703232,-196899703168⟩ : DyadicInterval 40),(⟨747277360168,747277379498⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29962739840,-29920563712⟩ : DyadicInterval 40),(⟨777083665472,777104772800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166868100352,166966001472⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196940132096,-196803837120⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2604_ok : ecellOkT e2604 = true := by decide +kernel
theorem e2604_pos {a z : ℝ} (ha1 : ((671283/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((268683/1638400 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2604 e2604_ok ha1 ha2 hz1 hz2 hz

-- box ['268683/1638400', '168033/1024000', '1999/2000', '7997/8000']  interval_lower 131973589/549755813888
noncomputable def e2605 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279821736837,0,true,166966001408,166966001472⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919201518715,0,false,-196940132096,-196940132032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279935687689,0,true,167063893696,167063893760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919087567863,0,false,-197076443968,-197076443904⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279731581782,0,true,166888545280,166888545344⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919291673770,0,false,-196832297600,-196832297536⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279868028667,0,true,167005770560,167005770624⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919155226885,0,false,-196995505920,-196995505856⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546107237,0,true,34478912,34478976⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477148315,0,false,-34480064,-34480000⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557631322,0,true,46002560,46002624⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465624230,0,false,-46004544,-46004480⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625851,0,false,-1984,-1920⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626695,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279776654815,0,true,166927270144,166927270208⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919246600737,0,false,-196886208128,-196886208064⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279901866773,0,true,167034839936,167034840000⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919121388779,0,false,-197035984512,-197035984448⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069916089626,0,false,-30001144576,-30001144512⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069957160909,0,false,-29958937984,-29958937920⟩
    { al := (268683/1638400), au := (168033/1024000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨180310109061,180424059913⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166966001408,166966001472⟩ : DyadicInterval 40),(⟨-196940132096,-196940132032⟩ : DyadicInterval 40),(⟨747271767356,747271786685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167063893696,167063893760⟩ : DyadicInterval 40),(⟨-197076443968,-197076443904⟩ : DyadicInterval 40),(⟨747252904117,747252923447⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166888545280,166888545344⟩ : DyadicInterval 40),(⟨-196832297600,-196832297536⟩ : DyadicInterval 40),(⟨747286682922,747286702251⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167005770560,167005770624⟩ : DyadicInterval 40),(⟨-196995505920,-196995505856⟩ : DyadicInterval 40),(⟨747264105769,747264125099⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34479461,46003546⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34478912,34478976⟩ : DyadicInterval 40),(⟨-34480064,-34480000⟩ : DyadicInterval 40),(⟨762123383046,762123402375⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46002560,46002624⟩ : DyadicInterval 40),(⟨-46004544,-46004480⟩ : DyadicInterval 40),(⟨762123382619,762123401948⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1984,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180265027039,180390238997⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166927270144,166927270208⟩ : DyadicInterval 40),(⟨-196886208128,-196886208064⟩ : DyadicInterval 40),(⟨747279226835,747279246164⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167034839936,167034840000⟩ : DyadicInterval 40),(⟨-197035984512,-197035984448⟩ : DyadicInterval 40),(⟨747258504044,747258523374⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30001144576,-29958937920⟩ : DyadicInterval 40),(⟨777102852576,777123975168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166966001408,167063893760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197076443968,-196940132032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2605_ok : ecellOkT e2605 = true := by decide +kernel
theorem e2605_pos {a z : ℝ} (ha1 : ((268683/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((168033/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2605 e2605_ok ha1 ha2 hz1 hz2 hz

-- box ['671283/4096000', '268683/1638400', '7997/8000', '3999/4000']  interval_lower 131229031/549755813888
noncomputable def e2606 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279707785986,0,true,166868100352,166868100416⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919315469566,0,false,-196803837184,-196803837120⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279821736838,0,true,166966001408,166966001472⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919201518714,0,false,-196940132096,-196940132032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279640212426,0,true,166810040320,166810040384⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919383043126,0,false,-196723021440,-196723021376⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279776659311,0,true,166927273984,166927274048⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919246596241,0,false,-196886213504,-196886213440⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534598949,0,true,22970880,22970944⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488656603,0,false,-22971456,-22971392⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546107925,0,true,34479552,34479616⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477147627,0,false,-34480704,-34480640⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626694,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627297,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279673994612,0,true,166839066752,166839066816⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919349260940,0,false,-196763423040,-196763422976⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279799206604,0,true,166946645184,166946645248⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919224048948,0,false,-196913182720,-196913182656⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069949765710,0,false,-29966537472,-29966537408⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069990813622,0,false,-29924356224,-29924356160⟩
    { al := (671283/4096000), au := (268683/1638400), zl := (7997/8000), zu := (3999/4000),
      A := ⟨180196158210,180310109062⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166868100352,166868100416⟩ : DyadicInterval 40),(⟨-196803837184,-196803837120⟩ : DyadicInterval 40),(⟨747290618514,747290637844⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166966001408,166966001472⟩ : DyadicInterval 40),(⟨-196940132096,-196940132032⟩ : DyadicInterval 40),(⟨747271767356,747271786685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166810040320,166810040384⟩ : DyadicInterval 40),(⟨-196723021440,-196723021376⟩ : DyadicInterval 40),(⟨747301791627,747301810957⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166927273984,166927274048⟩ : DyadicInterval 40),(⟨-196886213504,-196886213440⟩ : DyadicInterval 40),(⟨747279226103,747279245433⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22971173,34480149⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22970880,22970944⟩ : DyadicInterval 40),(⟨-22971456,-22971392⟩ : DyadicInterval 40),(⟨762123383360,762123402689⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34479552,34479616⟩ : DyadicInterval 40),(⟨-34480704,-34480640⟩ : DyadicInterval 40),(⟨762123383046,762123402375⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180162366836,180287578828⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166839066752,166839066816⟩ : DyadicInterval 40),(⟨-196763423040,-196763422976⟩ : DyadicInterval 40),(⟨747296206361,747296225690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166946645184,166946645248⟩ : DyadicInterval 40),(⟨-196913182720,-196913182656⟩ : DyadicInterval 40),(⟨747275495582,747275514911⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29966537472,-29924356160⟩ : DyadicInterval 40),(⟨777085561696,777106671616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166868100352,166966001472⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196940132096,-196803837120⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2606_ok : ecellOkT e2606 = true := by decide +kernel
theorem e2606_pos {a z : ℝ} (ha1 : ((671283/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((268683/1638400 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2606 e2606_ok ha1 ha2 hz1 hz2 hz

-- box ['268683/1638400', '168033/1024000', '7997/8000', '3999/4000']  interval_lower 65940191/274877906944
noncomputable def e2607 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279821736837,0,true,166966001408,166966001472⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919201518715,0,false,-196940132096,-196940132032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279935687689,0,true,167063893696,167063893760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919087567863,0,false,-197076443968,-197076443904⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279754120546,0,true,166907909824,166907909888⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919269135006,0,false,-196859255232,-196859255168⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279890581675,0,true,167025145280,167025145344⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919132673877,0,false,-197022484608,-197022484544⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534614055,0,true,22985984,22986048⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488641497,0,false,-22986560,-22986496⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546130586,0,true,34502208,34502272⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477124966,0,false,-34503360,-34503296⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626693,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627296,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279787924100,0,true,166936952064,166936952128⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919235331452,0,false,-196899687424,-196899687360⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279913143208,0,true,167044526976,167044527040⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919110112344,0,false,-197049474176,-197049474112⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069912389397,0,false,-30004947136,-30004947072⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069953465593,0,false,-29962735360,-29962735296⟩
    { al := (268683/1638400), au := (168033/1024000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨180310109061,180424059913⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166966001408,166966001472⟩ : DyadicInterval 40),(⟨-196940132096,-196940132032⟩ : DyadicInterval 40),(⟨747271767356,747271786685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167063893696,167063893760⟩ : DyadicInterval 40),(⟨-197076443968,-197076443904⟩ : DyadicInterval 40),(⟨747252904117,747252923447⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166907909824,166907909888⟩ : DyadicInterval 40),(⟨-196859255232,-196859255168⟩ : DyadicInterval 40),(⟨747282954742,747282974072⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167025145280,167025145344⟩ : DyadicInterval 40),(⟨-197022484608,-197022484544⟩ : DyadicInterval 40),(⟨747260372361,747260391690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22986279,34502810⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22985984,22986048⟩ : DyadicInterval 40),(⟨-22986560,-22986496⟩ : DyadicInterval 40),(⟨762123383359,762123402688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34502208,34502272⟩ : DyadicInterval 40),(⟨-34503360,-34503296⟩ : DyadicInterval 40),(⟨762123383045,762123402374⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180276296324,180401515432⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166936952064,166936952128⟩ : DyadicInterval 40),(⟨-196899687424,-196899687360⟩ : DyadicInterval 40),(⟨747277362335,747277381665⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167044526976,167044527040⟩ : DyadicInterval 40),(⟨-197049474176,-197049474112⟩ : DyadicInterval 40),(⟨747256637077,747256656407⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30004947136,-29962735296⟩ : DyadicInterval 40),(⟨777104751264,777125876448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166966001408,167063893760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197076443968,-196940132032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2607_ok : ecellOkT e2607 = true := by decide +kernel
theorem e2607_pos {a z : ℝ} (ha1 : ((268683/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((168033/1024000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2607 e2607_ok ha1 ha2 hz1 hz2 hz

-- box ['335217/2048000', '1341717/8192000', '3999/4000', '7999/8000']  interval_lower 129838483/549755813888
noncomputable def e2608 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279479884283,0,true,166672272128,166672272192⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919543371269,0,false,-196531297984,-196531297920⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279593835135,0,true,166770190592,166770190656⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919429420417,0,false,-196667559104,-196667559040⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279434892218,0,true,166633607872,166633607936⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919588363334,0,false,-196477501632,-196477501568⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279571324860,0,true,166750848128,166750848192⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919451930692,0,false,-196640640256,-196640640192⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523098157,0,true,11470272,11470336⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500157395,0,false,-11470464,-11470400⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534584473,0,true,22956416,22956480⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488671079,0,false,-22956992,-22956928⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627296,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627657,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279457383591,0,true,166652936192,166652936256⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919565871961,0,false,-196504393856,-196504393792⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279582588483,0,true,166760526720,166760526784⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919440667069,0,false,-196654109760,-196654109696⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070020761039,0,false,-29893583040,-29893582976⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070061757291,0,false,-29851457664,-29851457600⟩
    { al := (335217/2048000), au := (1341717/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨179968256507,180082207359⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166672272128,166672272192⟩ : DyadicInterval 40),(⟨-196531297984,-196531297920⟩ : DyadicInterval 40),(⟨747328284379,747328303709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166770190592,166770190656⟩ : DyadicInterval 40),(⟨-196667559104,-196667559040⟩ : DyadicInterval 40),(⟨747309457504,747309476833⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166633607872,166633607936⟩ : DyadicInterval 40),(⟨-196477501632,-196477501568⟩ : DyadicInterval 40),(⟨747335714577,747335733907⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166750848128,166750848192⟩ : DyadicInterval 40),(⟨-196640640256,-196640640192⟩ : DyadicInterval 40),(⟨747313177591,747313196921⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11470381,22956697⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11470272,11470336⟩ : DyadicInterval 40),(⟨-11470464,-11470400⟩ : DyadicInterval 40),(⟨762123383528,762123402857⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22956416,22956480⟩ : DyadicInterval 40),(⟨-22956992,-22956928⟩ : DyadicInterval 40),(⟨762123383360,762123402689⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179945755815,180070960707⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166652936192,166652936256⟩ : DyadicInterval 40),(⟨-196504393856,-196504393792⟩ : DyadicInterval 40),(⟨747332000447,747332019777⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166760526720,166760526784⟩ : DyadicInterval 40),(⟨-196654109760,-196654109696⟩ : DyadicInterval 40),(⟨747311316196,747311335525⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29893583040,-29851457600⟩ : DyadicInterval 40),(⟨777049112416,777070194400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166672272128,166770190656⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196667559104,-196531297920⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2608_ok : ecellOkT e2608 = true := by decide +kernel
theorem e2608_pos {a z : ℝ} (ha1 : ((335217/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1341717/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2608 e2608_ok ha1 ha2 hz1 hz2 hz

-- box ['1341717/8192000', '671283/4096000', '3999/4000', '7999/8000']  interval_lower 260972849/1099511627776
noncomputable def e2609 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279593835134,0,true,166770190592,166770190656⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919429420418,0,false,-196667559104,-196667559040⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279707785987,0,true,166868100352,166868100416⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919315469565,0,false,-196803837184,-196803837120⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279548814582,0,true,166731505280,166731505344⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919474440970,0,false,-196613722048,-196613721984⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279685261468,0,true,166848747328,166848747392⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919337994084,0,false,-196776897920,-196776897856⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523105710,0,true,11477824,11477888⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500149842,0,false,-11478016,-11477952⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534599579,0,true,22971520,22971584⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488655973,0,false,-22972096,-22972032⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627296,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627657,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279571320198,0,true,166750844096,166750844160⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919451935354,0,false,-196640634688,-196640634624⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279696532211,0,true,166858431168,166858431232⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919326723341,0,false,-196790377600,-196790377536⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069983427285,0,false,-29931946368,-29931946304⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070024451819,0,false,-29889790528,-29889790464⟩
    { al := (1341717/8192000), au := (671283/4096000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨180082207358,180196158211⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166770190592,166770190656⟩ : DyadicInterval 40),(⟨-196667559104,-196667559040⟩ : DyadicInterval 40),(⟨747309457504,747309476833⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166868100352,166868100416⟩ : DyadicInterval 40),(⟨-196803837184,-196803837120⟩ : DyadicInterval 40),(⟨747290618514,747290637844⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166731505280,166731505344⟩ : DyadicInterval 40),(⟨-196613722048,-196613721984⟩ : DyadicInterval 40),(⟨747316897224,747316916553⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166848747328,166848747392⟩ : DyadicInterval 40),(⟨-196776897920,-196776897856⟩ : DyadicInterval 40),(⟨747294343362,747294362691⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11477934,22971803⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11477824,11477888⟩ : DyadicInterval 40),(⟨-11478016,-11477952⟩ : DyadicInterval 40),(⟨762123383528,762123402857⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22971520,22971584⟩ : DyadicInterval 40),(⟨-22972096,-22972032⟩ : DyadicInterval 40),(⟨762123383360,762123402689⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180059692422,180184904435⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166750844096,166750844160⟩ : DyadicInterval 40),(⟨-196640634688,-196640634624⟩ : DyadicInterval 40),(⟨747313178380,747313197710⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166858431168,166858431232⟩ : DyadicInterval 40),(⟨-196790377600,-196790377536⟩ : DyadicInterval 40),(⟨747292479590,747292498919⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29931946368,-29889790464⟩ : DyadicInterval 40),(⟨777068278848,777089376064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166770190592,166868100416⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196803837184,-196667559040⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2609_ok : ecellOkT e2609 = true := by decide +kernel
theorem e2609_pos {a z : ℝ} (ha1 : ((1341717/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((671283/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2609 e2609_ok ha1 ha2 hz1 hz2 hz

-- box ['335217/2048000', '1341717/8192000', '7999/8000', '1']  interval_lower 259491681/1099511627776
noncomputable def e2610 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279479884283,0,true,166672272128,166672272192⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919543371269,0,false,-196531297984,-196531297920⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279593835135,0,true,166770190592,166770190656⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919429420417,0,false,-196667559104,-196667559040⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279457388250,0,true,166652940160,166652940224⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919565867302,0,false,-196504399424,-196504399360⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523106283,0,true,11478400,11478464⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500149269,0,false,-11478592,-11478528⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627656,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1279468631567,0,true,166662602176,166662602240⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨919554623985,0,false,-196517843008,-196517842944⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1279593843606,0,true,166770197888,166770197952⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨919429411946,0,false,-196667569280,-196667569216⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1070017074340,0,false,-29897371328,-29897371264⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1070058075494,0,false,-29855240832,-29855240768⟩
    { al := (335217/2048000), au := (1341717/8192000), zl := (7999/8000), zu := 1,
      A := ⟨179968256507,180082207359⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166672272128,166672272192⟩ : DyadicInterval 40),(⟨-196531297984,-196531297920⟩ : DyadicInterval 40),(⟨747328284379,747328303709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166770190592,166770190656⟩ : DyadicInterval 40),(⟨-196667559104,-196667559040⟩ : DyadicInterval 40),(⟨747309457504,747309476833⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166652940160,166652940224⟩ : DyadicInterval 40),(⟨-196504399424,-196504399360⟩ : DyadicInterval 40),(⟨747331999697,747332019027⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166770190592,166770190656⟩ : DyadicInterval 40),(⟨-196667559104,-196667559040⟩ : DyadicInterval 40),(⟨747309457504,747309476833⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11478507⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11478400,11478464⟩ : DyadicInterval 40),(⟨-11478592,-11478528⟩ : DyadicInterval 40),(⟨762123383528,762123402857⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨179957003791,180082215830⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166662602176,166662602240⟩ : DyadicInterval 40),(⟨-196517843008,-196517842944⟩ : DyadicInterval 40),(⟨747330142860,747330162189⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166770197888,166770197952⟩ : DyadicInterval 40),(⟨-196667569280,-196667569216⟩ : DyadicInterval 40),(⟨747309456113,747309475442⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29897371328,-29855240768⟩ : DyadicInterval 40),(⟨777051004000,777072088544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨166672272128,166770190656⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196667559104,-196531297920⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2610_ok : ecellOkT e2610 = true := by decide +kernel
theorem e2610_pos {a z : ℝ} (ha1 : ((335217/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1341717/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2610 e2610_ok ha1 ha2 hz1 hz2 hz

-- box ['1341717/8192000', '671283/4096000', '7999/8000', '1']  interval_lower 16299201/68719476736
noncomputable def e2611 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279593835134,0,true,166770190592,166770190656⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919429420418,0,false,-196667559104,-196667559040⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279707785987,0,true,166868100352,166868100416⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919315469565,0,false,-196803837184,-196803837120⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279571324857,0,true,166750848128,166750848192⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919451930695,0,false,-196640640256,-196640640192⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523113834,0,true,11485952,11486016⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500141718,0,false,-11486144,-11486080⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627656,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1279582575295,0,true,166760515392,166760515456⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨919440680257,0,false,-196654093952,-196654093888⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1279707794457,0,true,166868107648,166868107712⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨919315461095,0,false,-196803847296,-196803847232⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1069979735919,0,false,-29935739648,-29935739584⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1070020765360,0,false,-29893578560,-29893578496⟩
    { al := (1341717/8192000), au := (671283/4096000), zl := (7999/8000), zu := 1,
      A := ⟨180082207358,180196158211⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166770190592,166770190656⟩ : DyadicInterval 40),(⟨-196667559104,-196667559040⟩ : DyadicInterval 40),(⟨747309457504,747309476833⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166868100352,166868100416⟩ : DyadicInterval 40),(⟨-196803837184,-196803837120⟩ : DyadicInterval 40),(⟨747290618514,747290637844⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166750848128,166750848192⟩ : DyadicInterval 40),(⟨-196640640256,-196640640192⟩ : DyadicInterval 40),(⟨747313177592,747313196922⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166868100352,166868100416⟩ : DyadicInterval 40),(⟨-196803837184,-196803837120⟩ : DyadicInterval 40),(⟨747290618514,747290637844⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11486058⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11485952,11486016⟩ : DyadicInterval 40),(⟨-11486144,-11486080⟩ : DyadicInterval 40),(⟨762123383528,762123402857⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨180070947519,180196166681⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166760515392,166760515456⟩ : DyadicInterval 40),(⟨-196654093952,-196654093888⟩ : DyadicInterval 40),(⟨747311318357,747311337687⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166868107648,166868107712⟩ : DyadicInterval 40),(⟨-196803847296,-196803847232⟩ : DyadicInterval 40),(⟨747290617095,747290636425⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29935739648,-29893578496⟩ : DyadicInterval 40),(⟨777070172864,777091272704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨166770190592,166868100416⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196803837184,-196667559040⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2611_ok : ecellOkT e2611 = true := by decide +kernel
theorem e2611_pos {a z : ℝ} (ha1 : ((1341717/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((671283/4096000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2611 e2611_ok ha1 ha2 hz1 hz2 hz

-- box ['671283/4096000', '268683/1638400', '3999/4000', '7999/8000']  interval_lower 262271929/1099511627776
noncomputable def e2612 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279707785986,0,true,166868100352,166868100416⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919315469566,0,false,-196803837184,-196803837120⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279821736838,0,true,166966001408,166966001472⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919201518714,0,false,-196940132096,-196940132032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279662736946,0,true,166829393984,166829394048⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919360518606,0,false,-196749959360,-196749959296⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279799198075,0,true,166946637888,166946637952⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919224057477,0,false,-196913172480,-196913172416⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523113262,0,true,11485376,11485440⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500142290,0,false,-11485568,-11485504⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534614685,0,true,22986624,22986688⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488640867,0,false,-22987200,-22987136⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627295,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627657,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279685256802,0,true,166848743360,166848743424⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919337998750,0,false,-196776892352,-196776892288⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279810475948,0,true,166956326976,166956327040⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919212779604,0,false,-196926662400,-196926662336⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069946069912,0,false,-29970335360,-29970335296⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069987122736,0,false,-29928148992,-29928148928⟩
    { al := (671283/4096000), au := (268683/1638400), zl := (3999/4000), zu := (7999/8000),
      A := ⟨180196158210,180310109062⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166868100352,166868100416⟩ : DyadicInterval 40),(⟨-196803837184,-196803837120⟩ : DyadicInterval 40),(⟨747290618514,747290637844⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166966001408,166966001472⟩ : DyadicInterval 40),(⟨-196940132096,-196940132032⟩ : DyadicInterval 40),(⟨747271767356,747271786685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166829393984,166829394048⟩ : DyadicInterval 40),(⟨-196749959360,-196749959296⟩ : DyadicInterval 40),(⟨747298067742,747298087071⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166946637888,166946637952⟩ : DyadicInterval 40),(⟨-196913172480,-196913172416⟩ : DyadicInterval 40),(⟨747275496959,747275516288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11485486,22986909⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11485376,11485440⟩ : DyadicInterval 40),(⟨-11485568,-11485504⟩ : DyadicInterval 40),(⟨762123383528,762123402857⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22986624,22986688⟩ : DyadicInterval 40),(⟨-22987200,-22987136⟩ : DyadicInterval 40),(⟨762123383359,762123402688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180173629026,180298848172⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166848743360,166848743424⟩ : DyadicInterval 40),(⟨-196776892352,-196776892288⟩ : DyadicInterval 40),(⟨747294344115,747294363444⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166956326976,166956327040⟩ : DyadicInterval 40),(⟨-196926662400,-196926662336⟩ : DyadicInterval 40),(⟨747273630833,747273650162⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29970335360,-29928148928⟩ : DyadicInterval 40),(⟨777087458080,777108570560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166868100352,166966001472⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196940132096,-196803837120⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2612_ok : ecellOkT e2612 = true := by decide +kernel
theorem e2612_pos {a z : ℝ} (ha1 : ((671283/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((268683/1638400 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2612 e2612_ok ha1 ha2 hz1 hz2 hz

-- box ['268683/1638400', '168033/1024000', '3999/4000', '7999/8000']  interval_lower 263573981/1099511627776
noncomputable def e2613 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279821736837,0,true,166966001408,166966001472⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919201518715,0,false,-196940132096,-196940132032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279935687689,0,true,167063893696,167063893760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919087567863,0,false,-197076443968,-197076443904⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279776659309,0,true,166927273984,166927274048⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919246596243,0,false,-196886213504,-196886213440⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279913134682,0,true,167044519680,167044519744⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919110120870,0,false,-197049463936,-197049463872⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523120815,0,true,11492928,11492992⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500134737,0,false,-11493120,-11493056⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534629792,0,true,23001728,23001792⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488625760,0,false,-23002304,-23002240⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627294,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627656,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279799193412,0,true,166946633856,166946633920⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919224062140,0,false,-196913166912,-196913166848⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279924419673,0,true,167054214016,167054214080⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919098835879,0,false,-197062964032,-197062963968⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069908688927,0,false,-30008750016,-30008749952⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069949770037,0,false,-29966533056,-29966532992⟩
    { al := (268683/1638400), au := (168033/1024000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨180310109061,180424059913⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166966001408,166966001472⟩ : DyadicInterval 40),(⟨-196940132096,-196940132032⟩ : DyadicInterval 40),(⟨747271767356,747271786685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167063893696,167063893760⟩ : DyadicInterval 40),(⟨-197076443968,-197076443904⟩ : DyadicInterval 40),(⟨747252904117,747252923447⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166927273984,166927274048⟩ : DyadicInterval 40),(⟨-196886213504,-196886213440⟩ : DyadicInterval 40),(⟨747279226104,747279245433⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167044519680,167044519744⟩ : DyadicInterval 40),(⟨-197049463936,-197049463872⟩ : DyadicInterval 40),(⟨747256638456,747256657785⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11493039,23002016⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11492928,11492992⟩ : DyadicInterval 40),(⟨-11493120,-11493056⟩ : DyadicInterval 40),(⟨762123383527,762123402856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23001728,23001792⟩ : DyadicInterval 40),(⟨-23002304,-23002240⟩ : DyadicInterval 40),(⟨762123383358,762123402687⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180287565636,180412791897⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166946633856,166946633920⟩ : DyadicInterval 40),(⟨-196913166912,-196913166848⟩ : DyadicInterval 40),(⟨747275497749,747275517079⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167054214016,167054214080⟩ : DyadicInterval 40),(⟨-197062964032,-197062963968⟩ : DyadicInterval 40),(⟨747254769948,747254789277⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30008750016,-29966532992⟩ : DyadicInterval 40),(⟨777106650112,777127777888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166966001408,167063893760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197076443968,-196940132032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2613_ok : ecellOkT e2613 = true := by decide +kernel
theorem e2613_pos {a z : ℝ} (ha1 : ((268683/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((168033/1024000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2613 e2613_ok ha1 ha2 hz1 hz2 hz

-- box ['671283/4096000', '268683/1638400', '7999/8000', '1']  interval_lower 131042787/549755813888
noncomputable def e2614 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279707785986,0,true,166868100352,166868100416⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919315469566,0,false,-196803837184,-196803837120⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279821736838,0,true,166966001408,166966001472⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919201518714,0,false,-196940132096,-196940132032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279685261466,0,true,166848747328,166848747392⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919337994086,0,false,-196776897920,-196776897856⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523121387,0,true,11493504,11493568⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500134165,0,false,-11493696,-11493632⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627655,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1279696519022,0,true,166858419840,166858419904⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨919326736530,0,false,-196790361856,-196790361792⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1279821745315,0,true,166966008640,166966008704⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨919201510237,0,false,-196940142272,-196940142208⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1069942373876,0,false,-29974133568,-29974133504⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1069983431609,0,false,-29931941952,-29931941888⟩
    { al := (671283/4096000), au := (268683/1638400), zl := (7999/8000), zu := 1,
      A := ⟨180196158210,180310109062⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166868100352,166868100416⟩ : DyadicInterval 40),(⟨-196803837184,-196803837120⟩ : DyadicInterval 40),(⟨747290618514,747290637844⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166966001408,166966001472⟩ : DyadicInterval 40),(⟨-196940132096,-196940132032⟩ : DyadicInterval 40),(⟨747271767356,747271786685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166848747328,166848747392⟩ : DyadicInterval 40),(⟨-196776897920,-196776897856⟩ : DyadicInterval 40),(⟨747294343362,747294362692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166966001408,166966001472⟩ : DyadicInterval 40),(⟨-196940132096,-196940132032⟩ : DyadicInterval 40),(⟨747271767356,747271786685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11493611⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11493504,11493568⟩ : DyadicInterval 40),(⟨-11493696,-11493632⟩ : DyadicInterval 40),(⟨762123383527,762123402856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨180184891246,180310117539⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166858419840,166858419904⟩ : DyadicInterval 40),(⟨-196790361856,-196790361792⟩ : DyadicInterval 40),(⟨747292481781,747292501111⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166966008640,166966008704⟩ : DyadicInterval 40),(⟨-196940142272,-196940142208⟩ : DyadicInterval 40),(⟨747271765998,747271785327⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29974133568,-29931941888⟩ : DyadicInterval 40),(⟨777089354560,777110469664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨166868100352,166966001472⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196940132096,-196803837120⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2614_ok : ecellOkT e2614 = true := by decide +kernel
theorem e2614_pos {a z : ℝ} (ha1 : ((671283/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((268683/1638400 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2614 e2614_ok ha1 ha2 hz1 hz2 hz

-- box ['268683/1638400', '168033/1024000', '7999/8000', '1']  interval_lower 131693721/549755813888
noncomputable def e2615 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279821736837,0,true,166966001408,166966001472⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919201518715,0,false,-196940132096,-196940132032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279935687689,0,true,167063893696,167063893760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919087567863,0,false,-197076443968,-197076443904⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279799198073,0,true,166946637888,166946637952⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919224057479,0,false,-196913172480,-196913172416⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523128941,0,true,11501056,11501120⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500126611,0,false,-11501248,-11501184⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627655,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1279810462755,0,true,166956315648,166956315712⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨919212792797,0,false,-196926646592,-196926646528⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1279935696161,0,true,167063900992,167063901056⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨919087559391,0,false,-197076454080,-197076454016⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1069904988218,0,false,-30012553088,-30012553024⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1069946074240,0,false,-29970330944,-29970330880⟩
    { al := (268683/1638400), au := (168033/1024000), zl := (7999/8000), zu := 1,
      A := ⟨180310109061,180424059913⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166966001408,166966001472⟩ : DyadicInterval 40),(⟨-196940132096,-196940132032⟩ : DyadicInterval 40),(⟨747271767356,747271786685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167063893696,167063893760⟩ : DyadicInterval 40),(⟨-197076443968,-197076443904⟩ : DyadicInterval 40),(⟨747252904117,747252923447⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166946637888,166946637952⟩ : DyadicInterval 40),(⟨-196913172480,-196913172416⟩ : DyadicInterval 40),(⟨747275496959,747275516289⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167063893696,167063893760⟩ : DyadicInterval 40),(⟨-197076443968,-197076443904⟩ : DyadicInterval 40),(⟨747252904117,747252923447⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11501165⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11501056,11501120⟩ : DyadicInterval 40),(⟨-11501248,-11501184⟩ : DyadicInterval 40),(⟨762123383527,762123402856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨180298834979,180424068385⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166956315648,166956315712⟩ : DyadicInterval 40),(⟨-196926646592,-196926646528⟩ : DyadicInterval 40),(⟨747273633001,747273652330⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167063900992,167063901056⟩ : DyadicInterval 40),(⟨-197076454080,-197076454016⟩ : DyadicInterval 40),(⟨747252902694,747252922024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30012553088,-29970330880⟩ : DyadicInterval 40),(⟨777108549056,777129679424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨166966001408,167063893760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197076443968,-196940132032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2615_ok : ecellOkT e2615 = true := by decide +kernel
theorem e2615_pos {a z : ℝ} (ha1 : ((268683/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((168033/1024000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2615 e2615_ok ha1 ha2 hz1 hz2 hz

-- box ['168033/1024000', '1345113/8192000', '999/1000', '7993/8000']  interval_lower 266000385/1099511627776
noncomputable def e2616 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279935687688,0,true,167063893696,167063893760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919087567864,0,false,-197076443968,-197076443904⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280049638540,0,true,167161777280,167161777344⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918973617012,0,false,-197212772736,-197212772672⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279755263628,0,true,166908891904,166908891968⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919267991924,0,false,-196860622464,-196860622400⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279891667781,0,true,167026078336,167026078400⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919131587771,0,false,-197023783872,-197023783808⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592132267,0,true,80501504,80501568⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431123285,0,false,-80507456,-80507392⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099603694123,0,true,92062464,92062528⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099419561429,0,false,-92070208,-92070144⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620066,0,false,-7744,-7680⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621882,0,false,-5952,-5888⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279845471820,0,true,166986392256,166986392320⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919177783732,0,false,-196968523328,-196968523264⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279970662308,0,true,167093937792,167093937856⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919052593244,0,false,-197118285184,-197118285120⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069893511585,0,false,-30024347392,-30024347328⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069934591494,0,false,-29982131072,-29982131008⟩
    { al := (168033/1024000), au := (1345113/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨180424059912,180538010764⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167063893696,167063893760⟩ : DyadicInterval 40),(⟨-197076443968,-197076443904⟩ : DyadicInterval 40),(⟨747252904118,747252923447⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167161777280,167161777344⟩ : DyadicInterval 40),(⟨-197212772736,-197212772672⟩ : DyadicInterval 40),(⟨747234028734,747234048064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166908891904,166908891968⟩ : DyadicInterval 40),(⟨-196860622464,-196860622400⟩ : DyadicInterval 40),(⟨747282765665,747282784994⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167026078336,167026078400⟩ : DyadicInterval 40),(⟨-197023783872,-197023783808⟩ : DyadicInterval 40),(⟨747260192549,747260211879⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨80504491,92066347⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80501504,80501568⟩ : DyadicInterval 40),(⟨-80507456,-80507392⟩ : DyadicInterval 40),(⟨762123380633,762123399962⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨92062464,92062528⟩ : DyadicInterval 40),(⟨-92070208,-92070144⟩ : DyadicInterval 40),(⟨762123379714,762123399044⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7744,-5888⟩ : DyadicInterval 40),(⟨762123386560,762123406752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180333844044,180459034532⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166986392256,166986392320⟩ : DyadicInterval 40),(⟨-196968523328,-196968523264⟩ : DyadicInterval 40),(⟨747267839316,747267858646⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167093937792,167093937856⟩ : DyadicInterval 40),(⟨-197118285184,-197118285120⟩ : DyadicInterval 40),(⟨747247112022,747247131352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30024347392,-29982131008⟩ : DyadicInterval 40),(⟨777114449120,777135576576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167063893696,167161777344⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197212772736,-197076443904⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2616_ok : ecellOkT e2616 = true := by decide +kernel
theorem e2616_pos {a z : ℝ} (ha1 : ((168033/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1345113/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2616 e2616_ok ha1 ha2 hz1 hz2 hz

-- box ['1345113/8192000', '672981/4096000', '999/1000', '7993/8000']  interval_lower 267311199/1099511627776
noncomputable def e2617 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280049638539,0,true,167161777280,167161777344⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918973617013,0,false,-197212772736,-197212772672⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280163589391,0,true,167259652160,167259652224⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918859666161,0,false,-197349118336,-197349118272⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279869100528,0,true,167006691392,167006691456⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919154155024,0,false,-196996788096,-196996788032⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280005518925,0,true,167123879680,167123879744⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919017736627,0,false,-197159986816,-197159986752⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592185143,0,true,80554368,80554432⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431070409,0,false,-80560320,-80560256⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099603754559,0,true,92122880,92122944⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099419500993,0,false,-92130688,-92130624⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620056,0,false,-7744,-7680⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621874,0,false,-5952,-5888⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279959365693,0,true,167084233792,167084233856⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919063889859,0,false,-197104770496,-197104770432⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280084563309,0,true,167191775872,167191775936⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918938692243,0,false,-197254559488,-197254559424⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069856111432,0,false,-30062783552,-30062783488⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069897219619,0,false,-30020536704,-30020536640⟩
    { al := (1345113/8192000), au := (672981/4096000), zl := (999/1000), zu := (7993/8000),
      A := ⟨180538010763,180651961615⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167161777280,167161777344⟩ : DyadicInterval 40),(⟨-197212772736,-197212772672⟩ : DyadicInterval 40),(⟨747234028734,747234048064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167259652160,167259652224⟩ : DyadicInterval 40),(⟨-197349118336,-197349118272⟩ : DyadicInterval 40),(⟨747215141178,747215160508⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167006691392,167006691456⟩ : DyadicInterval 40),(⟨-196996788096,-196996788032⟩ : DyadicInterval 40),(⟨747263928333,747263947663⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167123879680,167123879744⟩ : DyadicInterval 40),(⟨-197159986816,-197159986752⟩ : DyadicInterval 40),(⟨747241338346,747241357675⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨80557367,92126783⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80554368,80554432⟩ : DyadicInterval 40),(⟨-80560320,-80560256⟩ : DyadicInterval 40),(⟨762123380625,762123399955⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨92122880,92122944⟩ : DyadicInterval 40),(⟨-92130688,-92130624⟩ : DyadicInterval 40),(⟨762123379736,762123399066⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7744,-5888⟩ : DyadicInterval 40),(⟨762123386560,762123406752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180447737917,180572935533⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167084233792,167084233856⟩ : DyadicInterval 40),(⟨-197104770496,-197104770432⟩ : DyadicInterval 40),(⟨747248982957,747249002286⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167191775872,167191775936⟩ : DyadicInterval 40),(⟨-197254559488,-197254559424⟩ : DyadicInterval 40),(⟨747228241179,747228260508⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30062783552,-30020536640⟩ : DyadicInterval 40),(⟨777133651936,777154794656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167161777280,167259652224⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197349118336,-197212772672⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2617_ok : ecellOkT e2617 = true := by decide +kernel
theorem e2617_pos {a z : ℝ} (ha1 : ((1345113/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((672981/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2617 e2617_ok ha1 ha2 hz1 hz2 hz

-- box ['168033/1024000', '1345113/8192000', '7993/8000', '3997/4000']  interval_lower 265813649/1099511627776
noncomputable def e2618 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279935687688,0,true,167063893696,167063893760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919087567864,0,false,-197076443968,-197076443904⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280049638540,0,true,167161777280,167161777344⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918973617012,0,false,-197212772736,-197212772672⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279777816635,0,true,166928268288,166928268352⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919245438917,0,false,-196887597824,-196887597760⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279914235033,0,true,167045464960,167045465024⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919109020519,0,false,-197050780288,-197050780224⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580631761,0,true,69001792,69001856⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442623791,0,false,-69006208,-69006144⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592186063,0,true,80555328,80555392⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431069489,0,false,-80561280,-80561216⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621873,0,false,-5952,-5888⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623446,0,false,-4352,-4288⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279856748114,0,true,166996079616,166996079680⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919166507438,0,false,-196982011968,-196982011904⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279981945756,0,true,167103630336,167103630400⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919041309796,0,false,-197131784256,-197131784192⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069889807643,0,false,-30028153856,-30028153792⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069930892468,0,false,-29985932352,-29985932288⟩
    { al := (168033/1024000), au := (1345113/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨180424059912,180538010764⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167063893696,167063893760⟩ : DyadicInterval 40),(⟨-197076443968,-197076443904⟩ : DyadicInterval 40),(⟨747252904118,747252923447⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167161777280,167161777344⟩ : DyadicInterval 40),(⟨-197212772736,-197212772672⟩ : DyadicInterval 40),(⟨747234028734,747234048064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166928268288,166928268352⟩ : DyadicInterval 40),(⟨-196887597824,-196887597760⟩ : DyadicInterval 40),(⟨747279034651,747279053981⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167045464960,167045465024⟩ : DyadicInterval 40),(⟨-197050780288,-197050780224⟩ : DyadicInterval 40),(⟨747256456267,747256475596⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨69003985,80558287⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69001792,69001856⟩ : DyadicInterval 40),(⟨-69006208,-69006144⟩ : DyadicInterval 40),(⟨762123381429,762123400758⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80555328,80555392⟩ : DyadicInterval 40),(⟨-80561280,-80561216⟩ : DyadicInterval 40),(⟨762123380625,762123399954⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5952,-4288⟩ : DyadicInterval 40),(⟨762123385760,762123405856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180345120338,180470317980⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166996079616,166996079680⟩ : DyadicInterval 40),(⟨-196982011968,-196982011904⟩ : DyadicInterval 40),(⟨747265972947,747265992276⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167103630336,167103630400⟩ : DyadicInterval 40),(⟨-197131784256,-197131784192⟩ : DyadicInterval 40),(⟨747245243171,747245262501⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30028153856,-29985932288⟩ : DyadicInterval 40),(⟨777116349760,777137479808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167063893696,167161777344⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197212772736,-197076443904⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2618_ok : ecellOkT e2618 = true := by decide +kernel
theorem e2618_pos {a z : ℝ} (ha1 : ((168033/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1345113/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2618 e2618_ok ha1 ha2 hz1 hz2 hz

-- box ['1345113/8192000', '672981/4096000', '7993/8000', '3997/4000']  interval_lower 267123763/1099511627776
noncomputable def e2619 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280049638539,0,true,167161777280,167161777344⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918973617013,0,false,-197212772736,-197212772672⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280163589391,0,true,167259652160,167259652224⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918859666161,0,false,-197349118336,-197349118272⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279891667779,0,true,167026078336,167026078400⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919131587773,0,false,-197023783872,-197023783808⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280028100420,0,true,167143276736,167143276800⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918995155132,0,false,-197187003584,-197187003520⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580677084,0,true,69047104,69047168⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442578468,0,false,-69051520,-69051456⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592238946,0,true,80608192,80608256⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431016606,0,false,-80614144,-80614080⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621865,0,false,-5952,-5888⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623440,0,false,-4352,-4288⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279970649111,0,true,167093926400,167093926464⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919052606441,0,false,-197118269376,-197118269312⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280095853876,0,true,167201473728,167201473792⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918927401676,0,false,-197268068736,-197268068672⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069852402814,0,false,-30066595008,-30066594944⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069893515918,0,false,-30024342912,-30024342848⟩
    { al := (1345113/8192000), au := (672981/4096000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨180538010763,180651961615⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167161777280,167161777344⟩ : DyadicInterval 40),(⟨-197212772736,-197212772672⟩ : DyadicInterval 40),(⟨747234028734,747234048064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167259652160,167259652224⟩ : DyadicInterval 40),(⟨-197349118336,-197349118272⟩ : DyadicInterval 40),(⟨747215141178,747215160508⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167026078336,167026078400⟩ : DyadicInterval 40),(⟨-197023783872,-197023783808⟩ : DyadicInterval 40),(⟨747260192550,747260211879⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167143276736,167143276800⟩ : DyadicInterval 40),(⟨-197187003584,-197187003520⟩ : DyadicInterval 40),(⟨747237597333,747237616663⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨69049308,80611170⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69047104,69047168⟩ : DyadicInterval 40),(⟨-69051520,-69051456⟩ : DyadicInterval 40),(⟨762123381423,762123400752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80608192,80608256⟩ : DyadicInterval 40),(⟨-80614144,-80614080⟩ : DyadicInterval 40),(⟨762123380617,762123399947⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5952,-4288⟩ : DyadicInterval 40),(⟨762123385760,762123405856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180459021335,180584226100⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167093926400,167093926464⟩ : DyadicInterval 40),(⟨-197118269376,-197118269312⟩ : DyadicInterval 40),(⟨747247114232,747247133561⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167201473728,167201473792⟩ : DyadicInterval 40),(⟨-197268068736,-197268068672⟩ : DyadicInterval 40),(⟨747226369906,747226389236⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30066595008,-30024342848⟩ : DyadicInterval 40),(⟨777135555040,777156700384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167161777280,167259652224⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197349118336,-197212772672⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2619_ok : ecellOkT e2619 = true := by decide +kernel
theorem e2619_pos {a z : ℝ} (ha1 : ((1345113/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((672981/4096000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2619 e2619_ok ha1 ha2 hz1 hz2 hz

-- box ['672981/4096000', '1346811/8192000', '999/1000', '7993/8000']  interval_lower 67156211/274877906944
noncomputable def e2620 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280163589390,0,true,167259652160,167259652224⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918859666162,0,false,-197349118336,-197349118272⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280277540242,0,true,167357518336,167357518400⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918745715310,0,false,-197485480896,-197485480832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279982937428,0,true,167104482176,167104482240⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919040318124,0,false,-197132970624,-197132970560⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280119370069,0,true,167221672256,167221672320⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918903885483,0,false,-197296206592,-197296206528⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592238026,0,true,80607232,80607296⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431017526,0,false,-80613248,-80613184⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099603815000,0,true,92183296,92183360⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099419440552,0,false,-92191104,-92191040⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620046,0,false,-7744,-7680⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621867,0,false,-5952,-5888⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280073259570,0,true,167182066624,167182066688⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918949995982,0,false,-197241034624,-197241034560⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280198464307,0,true,167289605248,167289605312⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918824791245,0,false,-197390850624,-197390850560⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069818687682,0,false,-30101245312,-30101245248⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069859824146,0,false,-30058967936,-30058967872⟩
    { al := (672981/4096000), au := (1346811/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨180651961614,180765912466⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167259652160,167259652224⟩ : DyadicInterval 40),(⟨-197349118336,-197349118272⟩ : DyadicInterval 40),(⟨747215141178,747215160508⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167357518336,167357518400⟩ : DyadicInterval 40),(⟨-197485480896,-197485480832⟩ : DyadicInterval 40),(⟨747196241501,747196260830⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167104482176,167104482240⟩ : DyadicInterval 40),(⟨-197132970624,-197132970560⟩ : DyadicInterval 40),(⟨747245078906,747245098236⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167221672256,167221672320⟩ : DyadicInterval 40),(⟨-197296206592,-197296206528⟩ : DyadicInterval 40),(⟨747222472049,747222491379⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨80610250,92187224⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80607232,80607296⟩ : DyadicInterval 40),(⟨-80613248,-80613184⟩ : DyadicInterval 40),(⟨762123380649,762123399979⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨92183296,92183360⟩ : DyadicInterval 40),(⟨-92191104,-92191040⟩ : DyadicInterval 40),(⟨762123379726,762123399056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7744,-5888⟩ : DyadicInterval 40),(⟨762123386560,762123406752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180561631794,180686836531⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167182066624,167182066688⟩ : DyadicInterval 40),(⟨-197241034624,-197241034560⟩ : DyadicInterval 40),(⟨747230114502,747230133832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167289605248,167289605312⟩ : DyadicInterval 40),(⟨-197390850624,-197390850560⟩ : DyadicInterval 40),(⟨747209358185,747209377514⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30101245312,-30058967872⟩ : DyadicInterval 40),(⟨777152867552,777174025536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167259652160,167357518400⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197485480896,-197349118272⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2620_ok : ecellOkT e2620 = true := by decide +kernel
theorem e2620_pos {a z : ℝ} (ha1 : ((672981/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1346811/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2620 e2620_ok ha1 ha2 hz1 hz2 hz

-- box ['1346811/8192000', '67383/409600', '999/1000', '7993/8000']  interval_lower 67485399/274877906944
noncomputable def e2621 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280277540241,0,true,167357518336,167357518400⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918745715311,0,false,-197485480896,-197485480832⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280391491093,0,true,167455375808,167455375872⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918631764459,0,false,-197621860416,-197621860352⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280096774328,0,true,167202264320,167202264384⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918926481224,0,false,-197269170048,-197269169984⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280233221213,0,true,167319456192,167319456256⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918790034339,0,false,-197432443264,-197432443200⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592290910,0,true,80660160,80660224⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430964642,0,false,-80666112,-80666048⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099603875446,0,true,92243776,92243840⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099419380106,0,false,-92251584,-92251520⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620036,0,false,-7744,-7680⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621859,0,false,-5952,-5888⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280187153445,0,true,167279890752,167279890816⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918836102107,0,false,-197377315584,-197377315520⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280312365305,0,true,167387425984,167387426048⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918710890247,0,false,-197527158720,-197527158656⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069781240333,0,false,-30139732736,-30139732672⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069822405079,0,false,-30097424768,-30097424704⟩
    { al := (1346811/8192000), au := (67383/409600), zl := (999/1000), zu := (7993/8000),
      A := ⟨180765912465,180879863317⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167357518336,167357518400⟩ : DyadicInterval 40),(⟨-197485480896,-197485480832⟩ : DyadicInterval 40),(⟨747196241501,747196260831⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167455375808,167455375872⟩ : DyadicInterval 40),(⟨-197621860416,-197621860352⟩ : DyadicInterval 40),(⟨747177329702,747177349032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167202264320,167202264384⟩ : DyadicInterval 40),(⟨-197269170048,-197269169984⟩ : DyadicInterval 40),(⟨747226217345,747226236674⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167319456192,167319456256⟩ : DyadicInterval 40),(⟨-197432443264,-197432443200⟩ : DyadicInterval 40),(⟨747203593611,747203612941⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨80663134,92247670⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80660160,80660224⟩ : DyadicInterval 40),(⟨-80666112,-80666048⟩ : DyadicInterval 40),(⟨762123380610,762123399939⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨92243776,92243840⟩ : DyadicInterval 40),(⟨-92251584,-92251520⟩ : DyadicInterval 40),(⟨762123379716,762123399045⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7744,-5888⟩ : DyadicInterval 40),(⟨762123386560,762123406752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180675525669,180800737529⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167279890752,167279890816⟩ : DyadicInterval 40),(⟨-197377315584,-197377315520⟩ : DyadicInterval 40),(⟨747211233900,747211253229⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167387425984,167387426048⟩ : DyadicInterval 40),(⟨-197527158720,-197527158656⟩ : DyadicInterval 40),(⟨747190463053,747190482383⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30139732736,-30097424704⟩ : DyadicInterval 40),(⟨777172095968,777193269248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167357518336,167455375872⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197621860416,-197485480832⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2621_ok : ecellOkT e2621 = true := by decide +kernel
theorem e2621_pos {a z : ℝ} (ha1 : ((1346811/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((67383/409600 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2621 e2621_ok ha1 ha2 hz1 hz2 hz

-- box ['672981/4096000', '1346811/8192000', '7993/8000', '3997/4000']  interval_lower 268437279/1099511627776
noncomputable def e2622 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280163589390,0,true,167259652160,167259652224⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918859666162,0,false,-197349118336,-197349118272⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280277540242,0,true,167357518336,167357518400⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918745715310,0,false,-197485480896,-197485480832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280005518923,0,true,167123879680,167123879744⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919017736629,0,false,-197159986816,-197159986752⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280141965808,0,true,167241079872,167241079936⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918881289744,0,false,-197323243776,-197323243712⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580722411,0,true,69092416,69092480⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442533141,0,false,-69096832,-69096768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592291831,0,true,80661056,80661120⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430963721,0,false,-80667072,-80667008⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621858,0,false,-5952,-5888⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623435,0,false,-4352,-4288⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280084550110,0,true,167191764544,167191764608⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918938705442,0,false,-197254543680,-197254543616⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280209761997,0,true,167299308352,167299308416⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918813493555,0,false,-197404370112,-197404370048⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069814974383,0,false,-30105061696,-30105061632⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069856115769,0,false,-30062779072,-30062779008⟩
    { al := (672981/4096000), au := (1346811/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨180651961614,180765912466⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167259652160,167259652224⟩ : DyadicInterval 40),(⟨-197349118336,-197349118272⟩ : DyadicInterval 40),(⟨747215141178,747215160508⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167357518336,167357518400⟩ : DyadicInterval 40),(⟨-197485480896,-197485480832⟩ : DyadicInterval 40),(⟨747196241501,747196260830⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167123879680,167123879744⟩ : DyadicInterval 40),(⟨-197159986816,-197159986752⟩ : DyadicInterval 40),(⟨747241338346,747241357676⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167241079872,167241079936⟩ : DyadicInterval 40),(⟨-197323243776,-197323243712⟩ : DyadicInterval 40),(⟨747218726254,747218745583⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨69094635,80664055⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69092416,69092480⟩ : DyadicInterval 40),(⟨-69096832,-69096768⟩ : DyadicInterval 40),(⟨762123381417,762123400747⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80661056,80661120⟩ : DyadicInterval 40),(⟨-80667072,-80667008⟩ : DyadicInterval 40),(⟨762123380641,762123399971⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5952,-4288⟩ : DyadicInterval 40),(⟨762123385760,762123405856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180572922334,180698134221⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167191764544,167191764608⟩ : DyadicInterval 40),(⟨-197254543680,-197254543616⟩ : DyadicInterval 40),(⟨747228243355,747228262685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167299308352,167299308416⟩ : DyadicInterval 40),(⟨-197404370112,-197404370048⟩ : DyadicInterval 40),(⟨747207484550,747207503879⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30105061696,-30062779008⟩ : DyadicInterval 40),(⟨777154773120,777175933728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167259652160,167357518400⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197485480896,-197349118272⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2622_ok : ecellOkT e2622 = true := by decide +kernel
theorem e2622_pos {a z : ℝ} (ha1 : ((672981/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1346811/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2622 e2622_ok ha1 ha2 hz1 hz2 hz

-- box ['1346811/8192000', '67383/409600', '7993/8000', '3997/4000']  interval_lower 269753745/1099511627776
noncomputable def e2623 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280277540241,0,true,167357518336,167357518400⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918745715311,0,false,-197485480896,-197485480832⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280391491093,0,true,167455375808,167455375872⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918631764459,0,false,-197621860416,-197621860352⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280119370067,0,true,167221672256,167221672320⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918903885485,0,false,-197296206592,-197296206528⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280255831196,0,true,167338874304,167338874368⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918767424356,0,false,-197459500864,-197459500800⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580767742,0,true,69137792,69137856⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442487810,0,false,-69142144,-69142080⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592344722,0,true,80713920,80713984⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430910830,0,false,-80719936,-80719872⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621850,0,false,-5952,-5888⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623429,0,false,-4352,-4288⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280198451105,0,true,167289593920,167289593984⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918824804447,0,false,-197390834816,-197390834752⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280323670116,0,true,167397134336,167397134400⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918699585436,0,false,-197540688384,-197540688320⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069777522352,0,false,-30143554048,-30143553984⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069818692022,0,false,-30101240896,-30101240832⟩
    { al := (1346811/8192000), au := (67383/409600), zl := (7993/8000), zu := (3997/4000),
      A := ⟨180765912465,180879863317⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167357518336,167357518400⟩ : DyadicInterval 40),(⟨-197485480896,-197485480832⟩ : DyadicInterval 40),(⟨747196241501,747196260831⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167455375808,167455375872⟩ : DyadicInterval 40),(⟨-197621860416,-197621860352⟩ : DyadicInterval 40),(⟨747177329702,747177349032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167221672256,167221672320⟩ : DyadicInterval 40),(⟨-197296206592,-197296206528⟩ : DyadicInterval 40),(⟨747222472050,747222491379⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167338874304,167338874368⟩ : DyadicInterval 40),(⟨-197459500864,-197459500800⟩ : DyadicInterval 40),(⟨747199843063,747199862392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨69139966,80716946⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69137792,69137856⟩ : DyadicInterval 40),(⟨-69142144,-69142080⟩ : DyadicInterval 40),(⟨762123381380,762123400709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80713920,80713984⟩ : DyadicInterval 40),(⟨-80719936,-80719872⟩ : DyadicInterval 40),(⟨762123380634,762123399963⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5952,-4288⟩ : DyadicInterval 40),(⟨762123385760,762123405856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180686823329,180812042340⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167289593920,167289593984⟩ : DyadicInterval 40),(⟨-197390834816,-197390834752⟩ : DyadicInterval 40),(⟨747209360364,747209379694⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167397134336,167397134400⟩ : DyadicInterval 40),(⟨-197540688384,-197540688320⟩ : DyadicInterval 40),(⟨747188587026,747188606356⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30143554048,-30101240832⟩ : DyadicInterval 40),(⟨777174004032,777195179904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167357518336,167455375872⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197621860416,-197485480832⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2623_ok : ecellOkT e2623 = true := by decide +kernel
theorem e2623_pos {a z : ℝ} (ha1 : ((1346811/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((67383/409600 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2623 e2623_ok ha1 ha2 hz1 hz2 hz

-- box ['168033/1024000', '1345113/8192000', '3997/4000', '1599/1600']  interval_lower 132813469/549755813888
noncomputable def e2624 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279935687688,0,true,167063893696,167063893760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919087567864,0,false,-197076443968,-197076443904⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280049638540,0,true,167161777280,167161777344⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918973617012,0,false,-197212772736,-197212772672⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279800369643,0,true,166947644416,166947644480⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919222885909,0,false,-196914573824,-196914573760⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279936802284,0,true,167064851200,167064851264⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919086453268,0,false,-197077777344,-197077777280⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569131197,0,true,57501888,57501952⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454124355,0,false,-57504960,-57504896⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580677947,0,true,69048000,69048064⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442577605,0,false,-69052352,-69052288⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623439,0,false,-4352,-4288⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624769,0,false,-3008,-2944⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279868024443,0,true,167005766976,167005767040⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919155231109,0,false,-196995500864,-196995500800⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279993229230,0,true,167113322880,167113322944⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919030026322,0,false,-197145283520,-197145283456⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069886103460,0,false,-30031960576,-30031960512⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069927193199,0,false,-29989733888,-29989733824⟩
    { al := (168033/1024000), au := (1345113/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨180424059912,180538010764⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167063893696,167063893760⟩ : DyadicInterval 40),(⟨-197076443968,-197076443904⟩ : DyadicInterval 40),(⟨747252904118,747252923447⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167161777280,167161777344⟩ : DyadicInterval 40),(⟨-197212772736,-197212772672⟩ : DyadicInterval 40),(⟨747234028734,747234048064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166947644416,166947644480⟩ : DyadicInterval 40),(⟨-196914573824,-196914573760⟩ : DyadicInterval 40),(⟨747275303103,747275322432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167064851200,167064851264⟩ : DyadicInterval 40),(⟨-197077777344,-197077777280⟩ : DyadicInterval 40),(⟨747252719524,747252738853⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57503421,69050171⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57501888,57501952⟩ : DyadicInterval 40),(⟨-57504960,-57504896⟩ : DyadicInterval 40),(⟨762123382080,762123401409⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69048000,69048064⟩ : DyadicInterval 40),(⟨-69052352,-69052288⟩ : DyadicInterval 40),(⟨762123381391,762123400720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4352,-2944⟩ : DyadicInterval 40),(⟨762123385088,762123405056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180356396667,180481601454⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167005766976,167005767040⟩ : DyadicInterval 40),(⟨-196995500864,-196995500800⟩ : DyadicInterval 40),(⟨747264106441,747264125771⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167113322880,167113322944⟩ : DyadicInterval 40),(⟨-197145283520,-197145283456⟩ : DyadicInterval 40),(⟨747243374158,747243393488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30031960576,-29989733824⟩ : DyadicInterval 40),(⟨777118250528,777139383168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167063893696,167161777344⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197212772736,-197076443904⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2624_ok : ecellOkT e2624 = true := by decide +kernel
theorem e2624_pos {a z : ℝ} (ha1 : ((168033/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1345113/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2624 e2624_ok ha1 ha2 hz1 hz2 hz

-- box ['1345113/8192000', '672981/4096000', '3997/4000', '1599/1600']  interval_lower 133468373/549755813888
noncomputable def e2625 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280049638539,0,true,167161777280,167161777344⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918973617013,0,false,-197212772736,-197212772672⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280163589391,0,true,167259652160,167259652224⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918859666161,0,false,-197349118336,-197349118272⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279914235030,0,true,167045464896,167045464960⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919109020522,0,false,-197050780288,-197050780224⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280050681916,0,true,167162673536,167162673600⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918972573636,0,false,-197214021056,-197214020992⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569168968,0,true,57539648,57539712⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454086584,0,false,-57542720,-57542656⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580723274,0,true,69093312,69093376⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442532278,0,false,-69097728,-69097664⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623433,0,false,-4352,-4288⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624765,0,false,-3072,-3008⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279981932555,0,true,167103619008,167103619072⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919041322997,0,false,-197131768448,-197131768384⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280107144474,0,true,167211171520,167211171584⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918916111078,0,false,-197281578176,-197281578112⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069848693953,0,false,-30070406656,-30070406592⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069889811977,0,false,-30028149376,-30028149312⟩
    { al := (1345113/8192000), au := (672981/4096000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨180538010763,180651961615⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167161777280,167161777344⟩ : DyadicInterval 40),(⟨-197212772736,-197212772672⟩ : DyadicInterval 40),(⟨747234028734,747234048064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167259652160,167259652224⟩ : DyadicInterval 40),(⟨-197349118336,-197349118272⟩ : DyadicInterval 40),(⟨747215141178,747215160508⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167045464896,167045464960⟩ : DyadicInterval 40),(⟨-197050780288,-197050780224⟩ : DyadicInterval 40),(⟨747256456305,747256475634⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167162673536,167162673600⟩ : DyadicInterval 40),(⟨-197214021056,-197214020992⟩ : DyadicInterval 40),(⟨747233855812,747233875141⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57541192,69095498⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57539648,57539712⟩ : DyadicInterval 40),(⟨-57542720,-57542656⟩ : DyadicInterval 40),(⟨762123382076,762123401405⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69093312,69093376⟩ : DyadicInterval 40),(⟨-69097728,-69097664⟩ : DyadicInterval 40),(⟨762123381417,762123400747⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4352,-3008⟩ : DyadicInterval 40),(⟨762123385120,762123405056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180470304779,180595516698⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167103619008,167103619072⟩ : DyadicInterval 40),(⟨-197131768448,-197131768384⟩ : DyadicInterval 40),(⟨747245245345,747245264674⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167211171520,167211171584⟩ : DyadicInterval 40),(⟨-197281578176,-197281578112⟩ : DyadicInterval 40),(⟨747224498507,747224517836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30070406656,-30028149312⟩ : DyadicInterval 40),(⟨777137458272,777158606208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167161777280,167259652224⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197349118336,-197212772672⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2625_ok : ecellOkT e2625 = true := by decide +kernel
theorem e2625_pos {a z : ℝ} (ha1 : ((1345113/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((672981/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2625 e2625_ok ha1 ha2 hz1 hz2 hz

-- box ['168033/1024000', '1345113/8192000', '1599/1600', '1999/2000']  interval_lower 265439985/1099511627776
noncomputable def e2626 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279935687688,0,true,167063893696,167063893760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919087567864,0,false,-197076443968,-197076443904⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280049638540,0,true,167161777280,167161777344⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918973617012,0,false,-197212772736,-197212772672⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279822922650,0,true,166967020160,166967020224⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919200332902,0,false,-196941550528,-196941550464⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279959369535,0,true,167084237056,167084237120⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919063886017,0,false,-197104775104,-197104775040⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557630576,0,true,46001792,46001856⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465624976,0,false,-46003776,-46003712⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569169772,0,true,57540480,57540544⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454085780,0,false,-57543552,-57543488⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624764,0,false,-3072,-3008⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625852,0,false,-1984,-1920⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279879300796,0,true,167015454208,167015454272⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919143954756,0,false,-197008989952,-197008989888⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280004512727,0,true,167123015360,167123015424⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919018742825,0,false,-197158782976,-197158782912⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069882399039,0,false,-30035767616,-30035767552⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069923493692,0,false,-29993535680,-29993535616⟩
    { al := (168033/1024000), au := (1345113/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨180424059912,180538010764⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167063893696,167063893760⟩ : DyadicInterval 40),(⟨-197076443968,-197076443904⟩ : DyadicInterval 40),(⟨747252904118,747252923447⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167161777280,167161777344⟩ : DyadicInterval 40),(⟨-197212772736,-197212772672⟩ : DyadicInterval 40),(⟨747234028734,747234048064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166967020160,166967020224⟩ : DyadicInterval 40),(⟨-196941550528,-196941550464⟩ : DyadicInterval 40),(⟨747271571122,747271590451⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167084237056,167084237120⟩ : DyadicInterval 40),(⟨-197104775104,-197104775040⟩ : DyadicInterval 40),(⟨747248982346,747249001676⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨46002800,57541996⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46001792,46001856⟩ : DyadicInterval 40),(⟨-46003776,-46003712⟩ : DyadicInterval 40),(⟨762123382619,762123401948⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57540480,57540544⟩ : DyadicInterval 40),(⟨-57543552,-57543488⟩ : DyadicInterval 40),(⟨762123382076,762123401405⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3072,-1920⟩ : DyadicInterval 40),(⟨762123384576,762123404416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180367673020,180492884951⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167015454208,167015454272⟩ : DyadicInterval 40),(⟨-197008989952,-197008989888⟩ : DyadicInterval 40),(⟨747262239848,747262259178⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167123015360,167123015424⟩ : DyadicInterval 40),(⟨-197158782976,-197158782912⟩ : DyadicInterval 40),(⟨747241505021,747241524351⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30035767616,-29993535616⟩ : DyadicInterval 40),(⟨777120151424,777141286688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167063893696,167161777344⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197212772736,-197076443904⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2626_ok : ecellOkT e2626 = true := by decide +kernel
theorem e2626_pos {a z : ℝ} (ha1 : ((168033/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1345113/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2626 e2626_ok ha1 ha2 hz1 hz2 hz

-- box ['1345113/8192000', '672981/4096000', '1599/1600', '1999/2000']  interval_lower 266749475/1099511627776
noncomputable def e2627 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280049638539,0,true,167161777280,167161777344⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918973617013,0,false,-197212772736,-197212772672⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280163589391,0,true,167259652160,167259652224⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918859666161,0,false,-197349118336,-197349118272⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279936802282,0,true,167064851200,167064851264⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919086453270,0,false,-197077777344,-197077777280⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280073263411,0,true,167182069952,167182070016⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918949992141,0,false,-197241039168,-197241039104⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557660793,0,true,46032000,46032064⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465594759,0,false,-46033984,-46033920⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569207545,0,true,57578240,57578304⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454048007,0,false,-57581312,-57581248⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624760,0,false,-3072,-3008⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625849,0,false,-1984,-1920⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279993216033,0,true,167113311552,167113311616⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919030039519,0,false,-197145267712,-197145267648⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280118435098,0,true,167220869184,167220869248⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918904820454,0,false,-197295087872,-197295087808⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069844984852,0,false,-30074218624,-30074218560⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069886107794,0,false,-30031956160,-30031956096⟩
    { al := (1345113/8192000), au := (672981/4096000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨180538010763,180651961615⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167161777280,167161777344⟩ : DyadicInterval 40),(⟨-197212772736,-197212772672⟩ : DyadicInterval 40),(⟨747234028734,747234048064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167259652160,167259652224⟩ : DyadicInterval 40),(⟨-197349118336,-197349118272⟩ : DyadicInterval 40),(⟨747215141178,747215160508⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167064851200,167064851264⟩ : DyadicInterval 40),(⟨-197077777344,-197077777280⟩ : DyadicInterval 40),(⟨747252719524,747252738854⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167182069952,167182070016⟩ : DyadicInterval 40),(⟨-197241039168,-197241039104⟩ : DyadicInterval 40),(⟨747230113827,747230133157⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨46033017,57579769⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46032000,46032064⟩ : DyadicInterval 40),(⟨-46033984,-46033920⟩ : DyadicInterval 40),(⟨762123382616,762123401945⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57578240,57578304⟩ : DyadicInterval 40),(⟨-57581312,-57581248⟩ : DyadicInterval 40),(⟨762123382072,762123401401⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3072,-1920⟩ : DyadicInterval 40),(⟨762123384576,762123404416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180481588257,180606807322⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167113311552,167113311616⟩ : DyadicInterval 40),(⟨-197145267712,-197145267648⟩ : DyadicInterval 40),(⟨747243376331,747243395661⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167220869184,167220869248⟩ : DyadicInterval 40),(⟨-197295087872,-197295087808⟩ : DyadicInterval 40),(⟨747222627047,747222646376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30074218624,-30031956096⟩ : DyadicInterval 40),(⟨777139361664,777160512192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167161777280,167259652224⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197349118336,-197212772672⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2627_ok : ecellOkT e2627 = true := by decide +kernel
theorem e2627_pos {a z : ℝ} (ha1 : ((1345113/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((672981/4096000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2627 e2627_ok ha1 ha2 hz1 hz2 hz

-- box ['672981/4096000', '1346811/8192000', '3997/4000', '1599/1600']  interval_lower 134124907/549755813888
noncomputable def e2628 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280163589390,0,true,167259652160,167259652224⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918859666162,0,false,-197349118336,-197349118272⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280277540242,0,true,167357518336,167357518400⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918745715310,0,false,-197485480896,-197485480832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280028100418,0,true,167143276736,167143276800⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918995155134,0,false,-197187003584,-197187003520⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280164561547,0,true,167260487168,167260487232⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918858694005,0,false,-197350281664,-197350281600⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569206740,0,true,57577408,57577472⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454048812,0,false,-57580480,-57580416⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580768605,0,true,69138624,69138688⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442486947,0,false,-69143040,-69142976⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623428,0,false,-4352,-4288⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624761,0,false,-3072,-3008⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280095840676,0,true,167201462400,167201462464⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918927414876,0,false,-197268052928,-197268052864⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280221059715,0,true,167309011392,167309011456⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918802195837,0,false,-197417889728,-197417889664⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069811260843,0,false,-30108878336,-30108878272⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069852407151,0,false,-30066590528,-30066590464⟩
    { al := (672981/4096000), au := (1346811/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨180651961614,180765912466⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167259652160,167259652224⟩ : DyadicInterval 40),(⟨-197349118336,-197349118272⟩ : DyadicInterval 40),(⟨747215141178,747215160508⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167357518336,167357518400⟩ : DyadicInterval 40),(⟨-197485480896,-197485480832⟩ : DyadicInterval 40),(⟨747196241501,747196260830⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167143276736,167143276800⟩ : DyadicInterval 40),(⟨-197187003584,-197187003520⟩ : DyadicInterval 40),(⟨747237597334,747237616663⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167260487168,167260487232⟩ : DyadicInterval 40),(⟨-197350281664,-197350281600⟩ : DyadicInterval 40),(⟨747214979984,747214999313⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57578964,69140829⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57577408,57577472⟩ : DyadicInterval 40),(⟨-57580480,-57580416⟩ : DyadicInterval 40),(⟨762123382072,762123401401⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69138624,69138688⟩ : DyadicInterval 40),(⟨-69143040,-69142976⟩ : DyadicInterval 40),(⟨762123381412,762123400741⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4352,-3008⟩ : DyadicInterval 40),(⟨762123385120,762123405056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180584212900,180709431939⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167201462400,167201462464⟩ : DyadicInterval 40),(⟨-197268052928,-197268052864⟩ : DyadicInterval 40),(⟨747226372082,747226391412⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167309011392,167309011456⟩ : DyadicInterval 40),(⟨-197417889728,-197417889664⟩ : DyadicInterval 40),(⟨747205610762,747205630092⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30108878336,-30066590464⟩ : DyadicInterval 40),(⟨777156678848,777177842048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167259652160,167357518400⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197485480896,-197349118272⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2628_ok : ecellOkT e2628 = true := by decide +kernel
theorem e2628_pos {a z : ℝ} (ha1 : ((672981/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1346811/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2628 e2628_ok ha1 ha2 hz1 hz2 hz

-- box ['1346811/8192000', '67383/409600', '3997/4000', '1599/1600']  interval_lower 16847841/68719476736
noncomputable def e2629 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280277540241,0,true,167357518336,167357518400⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918745715311,0,false,-197485480896,-197485480832⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280391491093,0,true,167455375808,167455375872⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918631764459,0,false,-197621860416,-197621860352⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280141965806,0,true,167241079872,167241079936⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918881289746,0,false,-197323243776,-197323243712⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280278441179,0,true,167358292096,167358292160⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918744814373,0,false,-197486559104,-197486559040⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569244516,0,true,57615168,57615232⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454011036,0,false,-57618304,-57618240⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580813939,0,true,69183936,69184000⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442441613,0,false,-69188352,-69188288⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623422,0,false,-4416,-4352⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624757,0,false,-3072,-3008⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280209748795,0,true,167299297024,167299297088⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918813506757,0,false,-197404354304,-197404354240⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280334974956,0,true,167406842624,167406842688⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918688280596,0,false,-197554218240,-197554218176⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069773804128,0,false,-30147375616,-30147375552⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069814978723,0,false,-30105057216,-30105057152⟩
    { al := (1346811/8192000), au := (67383/409600), zl := (3997/4000), zu := (1599/1600),
      A := ⟨180765912465,180879863317⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167357518336,167357518400⟩ : DyadicInterval 40),(⟨-197485480896,-197485480832⟩ : DyadicInterval 40),(⟨747196241501,747196260831⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167455375808,167455375872⟩ : DyadicInterval 40),(⟨-197621860416,-197621860352⟩ : DyadicInterval 40),(⟨747177329702,747177349032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167241079872,167241079936⟩ : DyadicInterval 40),(⟨-197323243776,-197323243712⟩ : DyadicInterval 40),(⟨747218726254,747218745583⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167358292096,167358292160⟩ : DyadicInterval 40),(⟨-197486559104,-197486559040⟩ : DyadicInterval 40),(⟨747196092011,747196111341⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57616740,69186163⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57615168,57615232⟩ : DyadicInterval 40),(⟨-57618304,-57618240⟩ : DyadicInterval 40),(⟨762123382100,762123401429⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69183936,69184000⟩ : DyadicInterval 40),(⟨-69188352,-69188288⟩ : DyadicInterval 40),(⟨762123381406,762123400735⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4416,-3008⟩ : DyadicInterval 40),(⟨762123385120,762123405088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180698121019,180823347180⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167299297024,167299297088⟩ : DyadicInterval 40),(⟨-197404354304,-197404354240⟩ : DyadicInterval 40),(⟨747207486729,747207506059⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167406842624,167406842688⟩ : DyadicInterval 40),(⟨-197554218240,-197554218176⟩ : DyadicInterval 40),(⟨747186710874,747186730203⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30147375616,-30105057152⟩ : DyadicInterval 40),(⟨777175912192,777197090688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167357518336,167455375872⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197621860416,-197485480832⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2629_ok : ecellOkT e2629 = true := by decide +kernel
theorem e2629_pos {a z : ℝ} (ha1 : ((1346811/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((67383/409600 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2629 e2629_ok ha1 ha2 hz1 hz2 hz

-- box ['672981/4096000', '1346811/8192000', '1599/1600', '1999/2000']  interval_lower 268061951/1099511627776
noncomputable def e2630 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280163589390,0,true,167259652160,167259652224⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918859666162,0,false,-197349118336,-197349118272⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280277540242,0,true,167357518336,167357518400⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918745715310,0,false,-197485480896,-197485480832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280050681913,0,true,167162673536,167162673600⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918972573639,0,false,-197214021056,-197214020992⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280187157286,0,true,167279894080,167279894144⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918836098266,0,false,-197377320192,-197377320128⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557691011,0,true,46062208,46062272⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465564541,0,false,-46064256,-46064192⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569245321,0,true,57616000,57616064⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454010231,0,false,-57619072,-57619008⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624756,0,false,-3072,-3008⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625847,0,false,-1984,-1920⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280107131273,0,true,167211160128,167211160192⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918916124279,0,false,-197281562368,-197281562304⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280232357458,0,true,167318714368,167318714432⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918790898094,0,false,-197431409600,-197431409536⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069807547062,0,false,-30112695232,-30112695168⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069848698291,0,false,-30070402240,-30070402176⟩
    { al := (672981/4096000), au := (1346811/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨180651961614,180765912466⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167259652160,167259652224⟩ : DyadicInterval 40),(⟨-197349118336,-197349118272⟩ : DyadicInterval 40),(⟨747215141178,747215160508⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167357518336,167357518400⟩ : DyadicInterval 40),(⟨-197485480896,-197485480832⟩ : DyadicInterval 40),(⟨747196241501,747196260830⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167162673536,167162673600⟩ : DyadicInterval 40),(⟨-197214021056,-197214020992⟩ : DyadicInterval 40),(⟨747233855812,747233875142⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167279894080,167279894144⟩ : DyadicInterval 40),(⟨-197377320192,-197377320128⟩ : DyadicInterval 40),(⟨747211233250,747211252580⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨46063235,57617545⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46062208,46062272⟩ : DyadicInterval 40),(⟨-46064256,-46064192⟩ : DyadicInterval 40),(⟨762123382646,762123401975⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57616000,57616064⟩ : DyadicInterval 40),(⟨-57619072,-57619008⟩ : DyadicInterval 40),(⟨762123382068,762123401397⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3072,-1920⟩ : DyadicInterval 40),(⟨762123384576,762123404416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180595503497,180720729682⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167211160128,167211160192⟩ : DyadicInterval 40),(⟨-197281562368,-197281562304⟩ : DyadicInterval 40),(⟨747224500721,747224520050⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167318714368,167318714432⟩ : DyadicInterval 40),(⟨-197431409600,-197431409536⟩ : DyadicInterval 40),(⟨747203736876,747203756206⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30112695232,-30070402176⟩ : DyadicInterval 40),(⟨777158584704,777179750496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167259652160,167357518400⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197485480896,-197349118272⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2630_ok : ecellOkT e2630 = true := by decide +kernel
theorem e2630_pos {a z : ℝ} (ha1 : ((672981/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1346811/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2630 e2630_ok ha1 ha2 hz1 hz2 hz

-- box ['1346811/8192000', '67383/409600', '1599/1600', '1999/2000']  interval_lower 134688745/549755813888
noncomputable def e2631 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280277540241,0,true,167357518336,167357518400⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918745715311,0,false,-197485480896,-197485480832⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280391491093,0,true,167455375808,167455375872⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918631764459,0,false,-197621860416,-197621860352⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280164561545,0,true,167260487168,167260487232⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918858694007,0,false,-197350281664,-197350281600⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280301051162,0,true,167377709504,167377709568⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918722204390,0,false,-197513618048,-197513617984⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557721232,0,true,46092480,46092544⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465534320,0,false,-46094464,-46094400⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569283101,0,true,57653760,57653824⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453972451,0,false,-57656896,-57656832⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624752,0,false,-3072,-3008⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625844,0,false,-1984,-1920⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280221046512,0,true,167309000064,167309000128⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918802209040,0,false,-197417873984,-197417873920⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280346279821,0,true,167416550848,167416550912⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918676975731,0,false,-197567748288,-197567748224⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069770085663,0,false,-30151197440,-30151197376⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069811265184,0,false,-30108873856,-30108873792⟩
    { al := (1346811/8192000), au := (67383/409600), zl := (1599/1600), zu := (1999/2000),
      A := ⟨180765912465,180879863317⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167357518336,167357518400⟩ : DyadicInterval 40),(⟨-197485480896,-197485480832⟩ : DyadicInterval 40),(⟨747196241501,747196260831⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167455375808,167455375872⟩ : DyadicInterval 40),(⟨-197621860416,-197621860352⟩ : DyadicInterval 40),(⟨747177329702,747177349032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167260487168,167260487232⟩ : DyadicInterval 40),(⟨-197350281664,-197350281600⟩ : DyadicInterval 40),(⟨747214979984,747214999314⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167377709504,167377709568⟩ : DyadicInterval 40),(⟨-197513618048,-197513617984⟩ : DyadicInterval 40),(⟨747192340523,747192359852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨46093456,57655325⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46092480,46092544⟩ : DyadicInterval 40),(⟨-46094464,-46094400⟩ : DyadicInterval 40),(⟨762123382611,762123401940⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57653760,57653824⟩ : DyadicInterval 40),(⟨-57656896,-57656832⟩ : DyadicInterval 40),(⟨762123382096,762123401425⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3072,-1920⟩ : DyadicInterval 40),(⟨762123384576,762123404416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180709418736,180834652045⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167309000064,167309000128⟩ : DyadicInterval 40),(⟨-197417873984,-197417873920⟩ : DyadicInterval 40),(⟨747205612969,747205632298⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167416550848,167416550912⟩ : DyadicInterval 40),(⟨-197567748288,-197567748224⟩ : DyadicInterval 40),(⟨747184834595,747184853924⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30151197440,-30108873792⟩ : DyadicInterval 40),(⟨777177820512,777199001600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167357518336,167455375872⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197621860416,-197485480832⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2631_ok : ecellOkT e2631 = true := by decide +kernel
theorem e2631_pos {a z : ℝ} (ha1 : ((1346811/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((67383/409600 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2631 e2631_ok ha1 ha2 hz1 hz2 hz

-- box ['67383/409600', '1348509/8192000', '999/1000', '7993/8000']  interval_lower 67815357/274877906944
noncomputable def e2632 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280391491092,0,true,167455375808,167455375872⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918631764460,0,false,-197621860416,-197621860352⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280505441944,0,true,167553224576,167553224640⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918517813608,0,false,-197758256768,-197758256704⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280210611228,0,true,167300037696,167300037760⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918812644324,0,false,-197405386368,-197405386304⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280347072357,0,true,167417231424,167417231488⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918676183195,0,false,-197568696832,-197568696768⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592343800,0,true,80713024,80713088⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430911752,0,false,-80719040,-80718976⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099603935896,0,true,92304192,92304256⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099419319656,0,false,-92312000,-92311936⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620026,0,false,-7808,-7744⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621851,0,false,-5952,-5888⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280301047315,0,true,167377706240,167377706304⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918722208237,0,false,-197513613440,-197513613376⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280426266308,0,true,167485237952,167485238016⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918596989244,0,false,-197663483712,-197663483648⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069743769384,0,false,-30178245696,-30178245632⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069784962417,0,false,-30135907200,-30135907136⟩
    { al := (67383/409600), au := (1348509/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨180879863316,180993814168⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167455375808,167455375872⟩ : DyadicInterval 40),(⟨-197621860416,-197621860352⟩ : DyadicInterval 40),(⟨747177329703,747177349032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167553224576,167553224640⟩ : DyadicInterval 40),(⟨-197758256768,-197758256704⟩ : DyadicInterval 40),(⟨747158405726,747158425056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167300037696,167300037760⟩ : DyadicInterval 40),(⟨-197405386368,-197405386304⟩ : DyadicInterval 40),(⟨747207343723,747207363052⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167417231424,167417231488⟩ : DyadicInterval 40),(⟨-197568696832,-197568696768⟩ : DyadicInterval 40),(⟨747184703067,747184722397⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨80716024,92308120⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80713024,80713088⟩ : DyadicInterval 40),(⟨-80719040,-80718976⟩ : DyadicInterval 40),(⟨762123380634,762123399963⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨92304192,92304256⟩ : DyadicInterval 40),(⟨-92312000,-92311936⟩ : DyadicInterval 40),(⟨762123379706,762123399035⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7808,-5888⟩ : DyadicInterval 40),(⟨762123386560,762123406784⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180789419539,180914638532⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167377706240,167377706304⟩ : DyadicInterval 40),(⟨-197513613440,-197513613376⟩ : DyadicInterval 40),(⟨747192341136,747192360466⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167485237952,167485238016⟩ : DyadicInterval 40),(⟨-197663483712,-197663483648⟩ : DyadicInterval 40),(⟨747171555831,747171575160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30178245696,-30135907136⟩ : DyadicInterval 40),(⟨777191337184,777212525728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167455375808,167553224640⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197758256768,-197621860352⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2632_ok : ecellOkT e2632 = true := by decide +kernel
theorem e2632_pos {a z : ℝ} (ha1 : ((67383/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1348509/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2632 e2632_ok ha1 ha2 hz1 hz2 hz

-- box ['1348509/8192000', '674679/4096000', '999/1000', '7993/8000']  interval_lower 272584381/1099511627776
noncomputable def e2633 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280505441943,0,true,167553224576,167553224640⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918517813609,0,false,-197758256768,-197758256704⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280619392795,0,true,167651064640,167651064704⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918403862757,0,false,-197894670080,-197894670016⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280324448128,0,true,167397802432,167397802496⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918698807424,0,false,-197541619520,-197541619456⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280460923501,0,true,167514997952,167514998016⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918562332051,0,false,-197704967296,-197704967232⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592396693,0,true,80765888,80765952⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430858859,0,false,-80771904,-80771840⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099603996350,0,true,92364672,92364736⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099419259202,0,false,-92372480,-92372416⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620016,0,false,-7808,-7744⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621843,0,false,-5952,-5888⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280414941193,0,true,167475512960,167475513024⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918608314359,0,false,-197649928192,-197649928128⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280540167306,0,true,167583041216,167583041280⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918483088246,0,false,-197799825536,-197799825472⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069706274838,0,false,-30216784256,-30216784192⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069747496158,0,false,-30174415232,-30174415168⟩
    { al := (1348509/8192000), au := (674679/4096000), zl := (999/1000), zu := (7993/8000),
      A := ⟨180993814167,181107765019⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167553224576,167553224640⟩ : DyadicInterval 40),(⟨-197758256768,-197758256704⟩ : DyadicInterval 40),(⟨747158405727,747158425056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167651064640,167651064704⟩ : DyadicInterval 40),(⟨-197894670080,-197894670016⟩ : DyadicInterval 40),(⟨747139469626,747139488956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167397802432,167397802496⟩ : DyadicInterval 40),(⟨-197541619520,-197541619456⟩ : DyadicInterval 40),(⟨747188457936,747188477266⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167514997952,167514998016⟩ : DyadicInterval 40),(⟨-197704967296,-197704967232⟩ : DyadicInterval 40),(⟨747165800416,747165819746⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨80768917,92368574⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80765888,80765952⟩ : DyadicInterval 40),(⟨-80771904,-80771840⟩ : DyadicInterval 40),(⟨762123380626,762123399956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨92364672,92364736⟩ : DyadicInterval 40),(⟨-92372480,-92372416⟩ : DyadicInterval 40),(⟨762123379695,762123399025⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7808,-5888⟩ : DyadicInterval 40),(⟨762123386560,762123406784⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180903313417,181028539530⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167475512960,167475513024⟩ : DyadicInterval 40),(⟨-197649928192,-197649928128⟩ : DyadicInterval 40),(⟨747173436285,747173455614⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167583041216,167583041280⟩ : DyadicInterval 40),(⟨-197799825536,-197799825472⟩ : DyadicInterval 40),(⟨747152636452,747152655782⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30216784256,-30174415168⟩ : DyadicInterval 40),(⟨777210591200,777231795008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167553224576,167651064704⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197894670080,-197758256704⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2633_ok : ecellOkT e2633 = true := by decide +kernel
theorem e2633_pos {a z : ℝ} (ha1 : ((1348509/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((674679/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2633 e2633_ok ha1 ha2 hz1 hz2 hz

-- box ['67383/409600', '1348509/8192000', '7993/8000', '3997/4000']  interval_lower 271073103/1099511627776
noncomputable def e2634 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280391491092,0,true,167455375808,167455375872⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918631764460,0,false,-197621860416,-197621860352⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280505441944,0,true,167553224576,167553224640⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918517813608,0,false,-197758256768,-197758256704⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280233221211,0,true,167319456192,167319456256⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918790034341,0,false,-197432443264,-197432443200⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280369696584,0,true,167436660032,167436660096⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918653558968,0,false,-197595774848,-197595774784⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580813076,0,true,69183104,69183168⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442442476,0,false,-69187520,-69187456⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592397615,0,true,80766848,80766912⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430857937,0,false,-80772864,-80772800⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621842,0,false,-5952,-5888⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623423,0,false,-4416,-4352⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280312352101,0,true,167387414592,167387414656⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918710903451,0,false,-197527142912,-197527142848⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280437578238,0,true,167494951552,167494951616⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918585677314,0,false,-197677023552,-197677023488⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069740046717,0,false,-30182071936,-30182071872⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069781244677,0,false,-30139728256,-30139728192⟩
    { al := (67383/409600), au := (1348509/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨180879863316,180993814168⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167455375808,167455375872⟩ : DyadicInterval 40),(⟨-197621860416,-197621860352⟩ : DyadicInterval 40),(⟨747177329703,747177349032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167553224576,167553224640⟩ : DyadicInterval 40),(⟨-197758256768,-197758256704⟩ : DyadicInterval 40),(⟨747158405726,747158425056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167319456192,167319456256⟩ : DyadicInterval 40),(⟨-197432443264,-197432443200⟩ : DyadicInterval 40),(⟨747203593612,747203612941⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167436660032,167436660096⟩ : DyadicInterval 40),(⟨-197595774848,-197595774784⟩ : DyadicInterval 40),(⟨747180947759,747180967089⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨69185300,80769839⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69183104,69183168⟩ : DyadicInterval 40),(⟨-69187520,-69187456⟩ : DyadicInterval 40),(⟨762123381406,762123400735⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80766848,80766912⟩ : DyadicInterval 40),(⟨-80772864,-80772800⟩ : DyadicInterval 40),(⟨762123380626,762123399955⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5952,-4352⟩ : DyadicInterval 40),(⟨762123385792,762123405856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180800724325,180925950462⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167387414592,167387414656⟩ : DyadicInterval 40),(⟨-197527142912,-197527142848⟩ : DyadicInterval 40),(⟨747190465273,747190484602⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167494951552,167494951616⟩ : DyadicInterval 40),(⟨-197677023552,-197677023488⟩ : DyadicInterval 40),(⟨747169677409,747169696738⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30182071936,-30139728192⟩ : DyadicInterval 40),(⟨777193247712,777214438848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167455375808,167553224640⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197758256768,-197621860352⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2634_ok : ecellOkT e2634 = true := by decide +kernel
theorem e2634_pos {a z : ℝ} (ha1 : ((67383/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1348509/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2634 e2634_ok ha1 ha2 hz1 hz2 hz

-- box ['1348509/8192000', '674679/4096000', '7993/8000', '3997/4000']  interval_lower 136197809/549755813888
noncomputable def e2635 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280505441943,0,true,167553224576,167553224640⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918517813609,0,false,-197758256768,-197758256704⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280619392795,0,true,167651064640,167651064704⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918403862757,0,false,-197894670080,-197894670016⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280347072355,0,true,167417231424,167417231488⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918676183197,0,false,-197568696832,-197568696768⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280483561972,0,true,167534437056,167534437120⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918539693580,0,false,-197732065664,-197732065600⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580858414,0,true,69228416,69228480⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442397138,0,false,-69232832,-69232768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592450514,0,true,80819712,80819776⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430805038,0,false,-80825728,-80825664⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621834,0,false,-5952,-5888⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623417,0,false,-4416,-4352⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280426253101,0,true,167485226624,167485226688⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918597002451,0,false,-197663467904,-197663467840⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280551486361,0,true,167592760128,167592760192⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918471769191,0,false,-197813375616,-197813375552⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069702547482,0,false,-30220615488,-30220615424⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069743773731,0,false,-30178241216,-30178241152⟩
    { al := (1348509/8192000), au := (674679/4096000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨180993814167,181107765019⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167553224576,167553224640⟩ : DyadicInterval 40),(⟨-197758256768,-197758256704⟩ : DyadicInterval 40),(⟨747158405727,747158425056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167651064640,167651064704⟩ : DyadicInterval 40),(⟨-197894670080,-197894670016⟩ : DyadicInterval 40),(⟨747139469626,747139488956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167417231424,167417231488⟩ : DyadicInterval 40),(⟨-197568696832,-197568696768⟩ : DyadicInterval 40),(⟨747184703067,747184722397⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167534437056,167534437120⟩ : DyadicInterval 40),(⟨-197732065664,-197732065600⟩ : DyadicInterval 40),(⟨747162040316,747162059645⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨69230638,80822738⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69228416,69228480⟩ : DyadicInterval 40),(⟨-69232832,-69232768⟩ : DyadicInterval 40),(⟨762123381400,762123400730⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80819712,80819776⟩ : DyadicInterval 40),(⟨-80825728,-80825664⟩ : DyadicInterval 40),(⟨762123380618,762123399948⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5952,-4352⟩ : DyadicInterval 40),(⟨762123385792,762123405856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180914625325,181039858585⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167485226624,167485226688⟩ : DyadicInterval 40),(⟨-197663467904,-197663467840⟩ : DyadicInterval 40),(⟨747171558016,747171577345⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167592760128,167592760192⟩ : DyadicInterval 40),(⟨-197813375616,-197813375552⟩ : DyadicInterval 40),(⟨747150755622,747150774951⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30220615488,-30178241152⟩ : DyadicInterval 40),(⟨777212504192,777233710624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167553224576,167651064704⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197894670080,-197758256704⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2635_ok : ecellOkT e2635 = true := by decide +kernel
theorem e2635_pos {a z : ℝ} (ha1 : ((1348509/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((674679/4096000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2635 e2635_ok ha1 ha2 hz1 hz2 hz

-- box ['674679/4096000', '1350207/8192000', '999/1000', '7993/8000']  interval_lower 273910407/1099511627776
noncomputable def e2636 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280619392794,0,true,167651064640,167651064704⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918403862758,0,false,-197894670080,-197894670016⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280733343646,0,true,167748895936,167748896000⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918289911906,0,false,-198031100352,-198031100288⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280438285028,0,true,167495558464,167495558528⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918584970524,0,false,-197677869568,-197677869504⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280574774645,0,true,167612755776,167612755840⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918448480907,0,false,-197841254592,-197841254528⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592449591,0,true,80818816,80818880⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430805961,0,false,-80824832,-80824768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099604056808,0,true,92425088,92425152⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099419198744,0,false,-92432960,-92432896⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620006,0,false,-7808,-7744⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621836,0,false,-5952,-5888⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280528835070,0,true,167573310976,167573311040⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918494420482,0,false,-197786259904,-197786259840⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280654068303,0,true,167680835840,167680835904⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918369187249,0,false,-197936184320,-197936184256⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069668756694,0,false,-30255348480,-30255348416⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069710006303,0,false,-30212948864,-30212948800⟩
    { al := (674679/4096000), au := (1350207/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨181107765018,181221715870⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167651064640,167651064704⟩ : DyadicInterval 40),(⟨-197894670080,-197894670016⟩ : DyadicInterval 40),(⟨747139469626,747139488956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167748895936,167748896000⟩ : DyadicInterval 40),(⟨-198031100352,-198031100288⟩ : DyadicInterval 40),(⟨747120521437,747120540767⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167495558464,167495558528⟩ : DyadicInterval 40),(⟨-197677869568,-197677869504⟩ : DyadicInterval 40),(⟨747169560050,747169579379⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167612755776,167612755840⟩ : DyadicInterval 40),(⟨-197841254592,-197841254528⟩ : DyadicInterval 40),(⟨747146885630,747146904960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨80821815,92429032⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80818816,80818880⟩ : DyadicInterval 40),(⟨-80824832,-80824768⟩ : DyadicInterval 40),(⟨762123380618,762123399948⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨92425088,92425152⟩ : DyadicInterval 40),(⟨-92432960,-92432896⟩ : DyadicInterval 40),(⟨762123379717,762123399047⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7808,-5888⟩ : DyadicInterval 40),(⟨762123386560,762123406784⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181017207294,181142440527⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167573310976,167573311040⟩ : DyadicInterval 40),(⟨-197786259904,-197786259840⟩ : DyadicInterval 40),(⟨747154519334,747154538663⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167680835840,167680835904⟩ : DyadicInterval 40),(⟨-197936184320,-197936184256⟩ : DyadicInterval 40),(⟨747133704933,747133724263⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30255348480,-30212948800⟩ : DyadicInterval 40),(⟨777229858016,777251077120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167651064640,167748896000⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198031100352,-197894670016⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2636_ok : ecellOkT e2636 = true := by decide +kernel
theorem e2636_pos {a z : ℝ} (ha1 : ((674679/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1350207/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2636 e2636_ok ha1 ha2 hz1 hz2 hz

-- box ['1350207/8192000', '84441/512000', '999/1000', '7993/8000']  interval_lower 2150309/8589934592
noncomputable def e2637 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280733343645,0,true,167748895936,167748896000⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918289911907,0,false,-198031100352,-198031100288⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280847294497,0,true,167846718592,167846718656⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918175961055,0,false,-198167547520,-198167547456⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280552121929,0,true,167593305792,167593305856⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918471133623,0,false,-197814136448,-197814136384⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280688625789,0,true,167710504960,167710505024⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918334629763,0,false,-197977558848,-197977558784⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592502491,0,true,80871680,80871744⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430753061,0,false,-80877696,-80877632⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099604117273,0,true,92485568,92485632⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099419138279,0,false,-92493440,-92493376⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619995,0,false,-7808,-7744⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621828,0,false,-5952,-5888⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280642728942,0,true,167671100352,167671100416⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918380526610,0,false,-197922608448,-197922608384⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280767969304,0,true,167778621760,167778621824⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918255286248,0,false,-198072560064,-198072560000⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069631214950,0,false,-30293938304,-30293938240⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069672492854,0,false,-30251508096,-30251508032⟩
    { al := (1350207/8192000), au := (84441/512000), zl := (999/1000), zu := (7993/8000),
      A := ⟨181221715869,181335666721⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167748895936,167748896000⟩ : DyadicInterval 40),(⟨-198031100352,-198031100288⟩ : DyadicInterval 40),(⟨747120521438,747120540767⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167846718592,167846718656⟩ : DyadicInterval 40),(⟨-198167547520,-198167547456⟩ : DyadicInterval 40),(⟨747101561057,747101580387⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167593305792,167593305856⟩ : DyadicInterval 40),(⟨-197814136448,-197814136384⟩ : DyadicInterval 40),(⟨747150650034,747150669364⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167710504960,167710505024⟩ : DyadicInterval 40),(⟨-197977558848,-197977558784⟩ : DyadicInterval 40),(⟨747127958724,747127978054⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨80874715,92489497⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80871680,80871744⟩ : DyadicInterval 40),(⟨-80877696,-80877632⟩ : DyadicInterval 40),(⟨762123380611,762123399940⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨92485568,92485632⟩ : DyadicInterval 40),(⟨-92493440,-92493376⟩ : DyadicInterval 40),(⟨762123379707,762123399037⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7808,-5888⟩ : DyadicInterval 40),(⟨762123386560,762123406784⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181131101166,181256341528⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167671100352,167671100416⟩ : DyadicInterval 40),(⟨-197922608448,-197922608384⟩ : DyadicInterval 40),(⟨747135590193,747135609522⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167778621760,167778621824⟩ : DyadicInterval 40),(⟨-198072560064,-198072560000⟩ : DyadicInterval 40),(⟨747114761309,747114780638⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30293938304,-30251508032⟩ : DyadicInterval 40),(⟨777249137632,777270372032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167748895936,167846718656⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198167547520,-198031100288⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2637_ok : ecellOkT e2637 = true := by decide +kernel
theorem e2637_pos {a z : ℝ} (ha1 : ((1350207/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((84441/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2637 e2637_ok ha1 ha2 hz1 hz2 hz

-- box ['674679/4096000', '1350207/8192000', '7993/8000', '3997/4000']  interval_lower 273721175/1099511627776
noncomputable def e2638 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280619392794,0,true,167651064640,167651064704⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918403862758,0,false,-197894670080,-197894670016⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280733343646,0,true,167748895936,167748896000⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918289911906,0,false,-198031100352,-198031100288⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280460923499,0,true,167514997952,167514998016⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918562332053,0,false,-197704967296,-197704967232⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280597427360,0,true,167632205440,167632205504⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918425828192,0,false,-197868373440,-197868373376⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580903754,0,true,69273792,69273856⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442351798,0,false,-69278208,-69278144⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592503416,0,true,80872640,80872704⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430752136,0,false,-80878656,-80878592⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621827,0,false,-5952,-5888⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623412,0,false,-4416,-4352⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280540154097,0,true,167583029888,167583029952⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918483101455,0,false,-197799809728,-197799809664⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280665394479,0,true,167690559936,167690560000⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918357861073,0,false,-197949744640,-197949744576⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069665024646,0,false,-30259184640,-30259184576⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069706279189,0,false,-30216779776,-30216779712⟩
    { al := (674679/4096000), au := (1350207/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨181107765018,181221715870⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167651064640,167651064704⟩ : DyadicInterval 40),(⟨-197894670080,-197894670016⟩ : DyadicInterval 40),(⟨747139469626,747139488956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167748895936,167748896000⟩ : DyadicInterval 40),(⟨-198031100352,-198031100288⟩ : DyadicInterval 40),(⟨747120521437,747120540767⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167514997952,167514998016⟩ : DyadicInterval 40),(⟨-197704967296,-197704967232⟩ : DyadicInterval 40),(⟨747165800417,747165819746⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167632205440,167632205504⟩ : DyadicInterval 40),(⟨-197868373440,-197868373376⟩ : DyadicInterval 40),(⟨747143120748,747143140077⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨69275978,80875640⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69273792,69273856⟩ : DyadicInterval 40),(⟨-69278208,-69278144⟩ : DyadicInterval 40),(⟨762123381395,762123400724⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80872640,80872704⟩ : DyadicInterval 40),(⟨-80878656,-80878592⟩ : DyadicInterval 40),(⟨762123380610,762123399940⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5952,-4352⟩ : DyadicInterval 40),(⟨762123385792,762123405856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181028526321,181153766703⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167583029888,167583029952⟩ : DyadicInterval 40),(⟨-197799809728,-197799809664⟩ : DyadicInterval 40),(⟨747152638641,747152657970⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167690559936,167690560000⟩ : DyadicInterval 40),(⟨-197949744640,-197949744576⟩ : DyadicInterval 40),(⟨747131821766,747131841095⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30259184640,-30216779712⟩ : DyadicInterval 40),(⟨777231773472,777252995200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167651064640,167748896000⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198031100352,-197894670016⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2638_ok : ecellOkT e2638 = true := by decide +kernel
theorem e2638_pos {a z : ℝ} (ha1 : ((674679/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1350207/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2638 e2638_ok ha1 ha2 hz1 hz2 hz

-- box ['1350207/8192000', '84441/512000', '7993/8000', '3997/4000']  interval_lower 275049939/1099511627776
noncomputable def e2639 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280733343645,0,true,167748895936,167748896000⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918289911907,0,false,-198031100352,-198031100288⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280847294497,0,true,167846718592,167846718656⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918175961055,0,false,-198167547520,-198167547456⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280574774643,0,true,167612755776,167612755840⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918448480909,0,false,-197841254592,-197841254528⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280711292748,0,true,167729965056,167729965120⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918311962804,0,false,-198004698048,-198004697984⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580949099,0,true,69319104,69319168⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442306453,0,false,-69323520,-69323456⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592556322,0,true,80925504,80925568⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430699230,0,false,-80931584,-80931520⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621819,0,false,-6016,-5952⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623406,0,false,-4416,-4352⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280654055090,0,true,167680824512,167680824576⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918369200462,0,false,-197936168512,-197936168448⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280779302601,0,true,167788351104,167788351168⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918243952951,0,false,-198086130496,-198086130432⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069627478207,0,false,-30297779392,-30297779328⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069668761049,0,false,-30255344000,-30255343936⟩
    { al := (1350207/8192000), au := (84441/512000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨181221715869,181335666721⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167748895936,167748896000⟩ : DyadicInterval 40),(⟨-198031100352,-198031100288⟩ : DyadicInterval 40),(⟨747120521438,747120540767⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167846718592,167846718656⟩ : DyadicInterval 40),(⟨-198167547520,-198167547456⟩ : DyadicInterval 40),(⟨747101561057,747101580387⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167612755776,167612755840⟩ : DyadicInterval 40),(⟨-197841254592,-197841254528⟩ : DyadicInterval 40),(⟨747146885631,747146904960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167729965056,167729965120⟩ : DyadicInterval 40),(⟨-198004698048,-198004697984⟩ : DyadicInterval 40),(⟨747124189074,747124208403⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨69321323,80928546⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69319104,69319168⟩ : DyadicInterval 40),(⟨-69323520,-69323456⟩ : DyadicInterval 40),(⟨762123381389,762123400718⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80925504,80925568⟩ : DyadicInterval 40),(⟨-80931584,-80931520⟩ : DyadicInterval 40),(⟨762123380635,762123399964⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6016,-4352⟩ : DyadicInterval 40),(⟨762123385792,762123405888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181142427314,181267674825⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167680824512,167680824576⟩ : DyadicInterval 40),(⟨-197936168512,-197936168448⟩ : DyadicInterval 40),(⟨747133707126,747133726455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167788351104,167788351168⟩ : DyadicInterval 40),(⟨-198086130496,-198086130432⟩ : DyadicInterval 40),(⟨747112875710,747112895040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30297779392,-30255343936⟩ : DyadicInterval 40),(⟨777251055584,777272292576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167748895936,167846718656⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198167547520,-198031100288⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2639_ok : ecellOkT e2639 = true := by decide +kernel
theorem e2639_pos {a z : ℝ} (ha1 : ((1350207/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((84441/512000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2639 e2639_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B043

end


