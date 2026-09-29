-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B009
-- name    : CK_CKLaneC2R_EpCells_B009
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:16:56.279761+00:00
-- url     : https://prove2.me/theorems/24e8fb97-4d1e-44ac-a089-9421e2023b62
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B009` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B009` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B009` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B009 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B009.lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheckT

-- ===== source module CKLaneC2R.EpCells.B009 =====
section

namespace CKLaneC2R.EpCells.B009

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['1020429/1024000', '2041707/2048000', '1999/2000', '1']  interval_lower 1859907535513785/549755813888
noncomputable def e540 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2195188923498,0,true,760204544256,760204562752⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨3834332054,8,false,-6221725379520,-6221725225344⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2195644726903,0,true,760432820352,760432838912⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨3378528649,8,false,-6360874012864,-6360873858688⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2194641084850,0,true,759930112256,759930130624⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨4382170702,7,false,-6074886752448,-6074886605568⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1116042696046,0,true,16408028352,16408028416⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1082980559506,0,false,-16656599744,-16656599680⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099263084503,0,false,-248571392,-248571328⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨2194916441167,0,true,760068056640,760068075072⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨4106814385,8,false,-6146241277760,-6146241123584⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨2195644740823,0,true,760432827328,760432845888⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨3378514729,8,false,-6360878543040,-6360878388864⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨6746648156,7,false,-5600445696576,-5600445561664⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨8198289302,7,false,-5386173201792,-5386173066880⟩
    { al := (1020429/1024000), au := (2041707/2048000), zl := (1999/2000), zu := 1,
      A := ⟨1095677295722,1096133099127⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760204544256,760204562752⟩ : DyadicInterval 40),(⟨-6221725379520,-6221725225344⟩ : DyadicInterval 40),(⟨14092879104,14092917102⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760432820352,760432838912⟩ : DyadicInterval 40),(⟨-6360874012864,-6360873858688⟩ : DyadicInterval 40),(⟨12631556189,12631594223⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759930112256,759930130624⟩ : DyadicInterval 40),(⟨-6074886752448,-6074886605568⟩ : DyadicInterval 40),(⟨15813542626,15813580516⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760432820352,760432838912⟩ : DyadicInterval 40),(⟨-6360874012864,-6360873858688⟩ : DyadicInterval 40),(⟨12631556189,12631594223⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,16531068270⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨16408028352,16408028416⟩ : DyadicInterval 40),(⟨-16656599744,-16656599680⟩ : DyadicInterval 40),(⟨761999107244,761999126574⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-248571392,0⟩ : DyadicInterval 40),(⟨762123383616,762247688576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨1095404813391,1096133113047⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760068056640,760068075072⟩ : DyadicInterval 40),(⟨-6146241277760,-6146241123584⟩ : DyadicInterval 40),(⟨14953275808,14953313759⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760432827328,760432845888⟩ : DyadicInterval 40),(⟨-6360878543040,-6360878388864⟩ : DyadicInterval 40),(⟨12631511105,12631549139⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5600445696576,-5386173066880⟩ : DyadicInterval 40),(⟨3455209917056,3562346251168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨760204544256,760432838912⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-6360874012864,-6221725225344⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e540_ok : ecellOkT e540 = true := by decide +kernel
theorem e540_pos {a z : ℝ} (ha1 : ((1020429/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((2041707/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e540 e540_ok ha1 ha2 hz1 hz2 hz

-- box ['2041707/2048000', '510639/512000', '1999/2000', '1']  interval_lower 1361385988963205/1099511627776
noncomputable def e541 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2195644726902,0,true,760432820352,760432838912⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨3378528650,8,false,-6360874012544,-6360873858368⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2196100530308,0,true,760661049024,760661067712⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨2922725244,8,false,-6520219438144,-6520219283968⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2195096660352,0,true,760158331136,760158349632⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨3926595200,8,false,-6195581807232,-6195581653056⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1118264092017,0,true,18594345344,18594345408⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1080759163535,0,false,-18914220224,-18914220160⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099191799493,0,false,-319874816,-319874752⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨2195372283856,0,true,760296380736,760296399232⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨3650971696,8,false,-6275603536512,-6275603382336⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨2196100544137,0,true,760661055936,760661074624⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨2922711415,8,false,-6520224640512,-6520224486336⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨5837653706,7,false,-5759563565376,-5759563430464⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨7289820197,7,false,-5515307136512,-5515307001600⟩
    { al := (2041707/2048000), au := (510639/512000), zl := (1999/2000), zu := 1,
      A := ⟨1096133099126,1096588902532⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760432820352,760432838912⟩ : DyadicInterval 40),(⟨-6360874012544,-6360873858368⟩ : DyadicInterval 40),(⟨12631556191,12631594225⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760661049024,760661067712⟩ : DyadicInterval 40),(⟨-6520219438144,-6520219283968⟩ : DyadicInterval 40),(⟨11139345352,11139383485⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760158331136,760158349632⟩ : DyadicInterval 40),(⟨-6195581807232,-6195581653056⟩ : DyadicInterval 40),(⟨14385264301,14385302305⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760661049024,760661067712⟩ : DyadicInterval 40),(⟨-6520219438144,-6520219283968⟩ : DyadicInterval 40),(⟨11139345352,11139383485⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,18752464241⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨18594345344,18594345408⟩ : DyadicInterval 40),(⟨-18914220224,-18914220160⟩ : DyadicInterval 40),(⟨761963461693,761963481023⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-319874816,0⟩ : DyadicInterval 40),(⟨762123383616,762283340288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨1095860656080,1096588916361⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760296380736,760296399232⟩ : DyadicInterval 40),(⟨-6275603536512,-6275603382336⟩ : DyadicInterval 40),(⟨13508475651,13508513638⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760661055936,760661074624⟩ : DyadicInterval 40),(⟨-6520224640512,-6520224486336⟩ : DyadicInterval 40),(⟨11139299576,11139337710⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5759563565376,-5515307001600⟩ : DyadicInterval 40),(⟨3519776884416,3641905185568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨760432820352,760661067712⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-6520219438144,-6360873858368⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e541_ok : ecellOkT e541 = true := by decide +kernel
theorem e541_pos {a z : ℝ} (ha1 : ((2041707/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((510639/512000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e541 e541_ok ha1 ha2 hz1 hz2 hz

-- box ['510639/512000', '408681/409600', '999/1000', '1999/2000']  interval_lower 4554614129856025/549755813888
noncomputable def e542 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2196100530307,0,true,760661049024,760661067712⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨2922725245,8,false,-6520219437760,-6520219283584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2196556333712,0,true,760889230336,760889249088⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨2466921840,8,false,-6706636499200,-6706636344512⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2195003941404,0,true,760111887744,760111906176⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨4019314148,8,false,-6169920757184,-6169920603008⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨2196007811360,0,true,760614626880,760614645504⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨3015444192,8,false,-6485880961088,-6485880806912⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1115694603903,0,true,16065038720,16065038784⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1083328651649,0,false,-16303251008,-16303250944⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1139180052666,0,true,38969600384,38969600448⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1059843202886,0,false,-40401698944,-40401698880⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1098080461525,0,false,-1432098496,-1432098432⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099273441377,0,false,-238212224,-238212160⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨2195558949157,0,true,760389864640,760389883200⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨3464306395,8,false,-6333306909760,-6333306755584⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨2196284138341,0,true,760752971392,760752990080⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨2739117211,8,false,-6591556633280,-6591556479104⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨5471410698,7,false,-5830803642880,-5830803507904⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨6917697564,7,false,-5572917025792,-5572916890880⟩
    { al := (510639/512000), au := (408681/409600), zl := (999/1000), zu := (1999/2000),
      A := ⟨1096588902531,1097044705936⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760661049024,760661067712⟩ : DyadicInterval 40),(⟨-6520219437760,-6520219283584⟩ : DyadicInterval 40),(⟨11139345355,11139383488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760889230336,760889249088⟩ : DyadicInterval 40),(⟨-6706636499200,-6706636344512⟩ : DyadicInterval 40),(⟨9611400175,9611438345⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760111887744,760111906176⟩ : DyadicInterval 40),(⟨-6169920757184,-6169920603008⟩ : DyadicInterval 40),(⟨14678000015,14678037960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760614626880,760614645504⟩ : DyadicInterval 40),(⟨-6485880961088,-6485880806912⟩ : DyadicInterval 40),(⟨11445605568,11445643643⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨16182976127,39668424890⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨16065038720,16065038784⟩ : DyadicInterval 40),(⟨-16303251008,-16303250944⟩ : DyadicInterval 40),(⟨762004286093,762004305423⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨38969600384,38969600448⟩ : DyadicInterval 40),(⟨-40401698944,-40401698880⟩ : DyadicInterval 40),(⟨761407645142,761407664471⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1432098496,-238212160⟩ : DyadicInterval 40),(⟨762242489696,762839452128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨1096047321381,1096772510565⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760389864640,760389883200⟩ : DyadicInterval 40),(⟨-6333306909760,-6333306755584⟩ : DyadicInterval 40),(⟨12908797706,12908835745⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760752971392,760752990080⟩ : DyadicInterval 40),(⟨-6591556633280,-6591556479104⟩ : DyadicInterval 40),(⟨10528476496,10528514618⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5830803642880,-5572916890880⟩ : DyadicInterval 40),(⟨3548581829056,3677525224320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨760661049024,760889249088⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-6706636499200,-6520219283584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e542_ok : ecellOkT e542 = true := by decide +kernel
theorem e542_pos {a z : ℝ} (ha1 : ((510639/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((408681/409600 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e542 e542_ok ha1 ha2 hz1 hz2 hz

-- box ['408681/409600', '1022127/1024000', '999/1000', '1999/2000']  interval_lower 5488800855581391/1099511627776
noncomputable def e543 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2196556333711,0,true,760889230336,760889249088⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨2466921841,8,false,-6706636498752,-6706636344064⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2197012137116,0,true,761117364352,761117383168⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨2011118436,9,false,-6931244918912,-6931244745472⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2195459289004,0,true,760339954816,760339973312⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨3563966548,8,false,-6302122906816,-6302122752640⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨2196463386863,0,true,760842703744,760842722496⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨2559868689,8,false,-6665971271360,-6665971116992⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1117810180957,0,true,18147955456,18147955520⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1081213074595,0,false,-18452530240,-18452530176⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1146004716147,0,true,45536963584,45536963648⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1053018539405,0,false,-47504693696,-47504693632⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1097545657420,0,false,-1967730112,-1967730048⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099207095255,0,false,-304574720,-304574656⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨2196015394239,0,true,760618423552,760618442176⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨3007861313,8,false,-6488649363904,-6488649209728⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨2196740175979,0,true,760981250880,760981269632⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨2283079573,8,false,-6791789207040,-6791789048512⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨4561418448,7,false,-6030807937088,-6030807797696⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨6007494219,7,false,-5728030921088,-5728030786176⟩
    { al := (408681/409600), au := (1022127/1024000), zl := (999/1000), zu := (1999/2000),
      A := ⟨1097044705935,1097500509340⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760889230336,760889249088⟩ : DyadicInterval 40),(⟨-6706636498752,-6706636344064⟩ : DyadicInterval 40),(⟨9611400178,9611438348⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761117364352,761117383168⟩ : DyadicInterval 40),(⟨-6931244918912,-6931244745472⟩ : DyadicInterval 40),(⟨8041056240,8041094464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760339954816,760339973312⟩ : DyadicInterval 40),(⟨-6302122906816,-6302122752640⟩ : DyadicInterval 40),(⟨13229574339,13229612320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760842703744,760842722496⟩ : DyadicInterval 40),(⟨-6665971271360,-6665971116992⟩ : DyadicInterval 40),(⟨9926166872,9926205048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨18298553181,46493088371⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨18147955456,18147955520⟩ : DyadicInterval 40),(⟨-18452530240,-18452530176⟩ : DyadicInterval 40),(⟨761971110301,761971129631⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45536963584,45536963648⟩ : DyadicInterval 40),(⟨-47504693696,-47504693632⟩ : DyadicInterval 40),(⟨761140105248,761140124577⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1967730112,-304574656⟩ : DyadicInterval 40),(⟨762275670944,763107267936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨1096503766463,1097228548203⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760618423552,760618442176⟩ : DyadicInterval 40),(⟨-6488649363904,-6488649209728⟩ : DyadicInterval 40),(⟨11420612709,11420650784⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760981250880,760981269632⟩ : DyadicInterval 40),(⟨-6791789207040,-6791789048512⟩ : DyadicInterval 40),(⟨8983584322,8983622485⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6030807937088,-5728030786176⟩ : DyadicInterval 40),(⟨3626138776704,3777527371424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨760889230336,761117383168⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-6931244918912,-6706636344064⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e543_ok : ecellOkT e543 = true := by decide +kernel
theorem e543_pos {a z : ℝ} (ha1 : ((408681/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1022127/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e543 e543_ok ha1 ha2 hz1 hz2 hz

-- box ['54531/256000', '437097/2048000', '999/1000', '3997/4000']  interval_lower 7086151/1099511627776
noncomputable def e544 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1333720489394,0,true,212322612160,212322612224⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨865302766158,0,false,-263379127616,-263379127552⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1334176292799,0,true,212698309760,212698309824⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨864846962753,0,false,-263958454528,-263958454464⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1333486280532,0,true,212129514752,212129514816⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨865536975020,0,false,-263081566400,-263081566336⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1334000294301,0,true,212553257600,212553257664⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨865022961251,0,false,-263734723968,-263734723904⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099602448323,0,true,90816768,90816832⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099420807229,0,false,-90824320,-90824256⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099632975388,0,true,121340864,121340928⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099390280164,0,false,-121354368,-121354304⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511614383,0,false,-13440,-13376⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620275,0,false,-7552,-7488⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1333603380999,0,true,212226064448,212226064512⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨865419874553,0,false,-263230331904,-263230331840⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1334088303202,0,true,212625793984,212625794048⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨864934952350,0,false,-263846595840,-263846595776⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1049465575270,0,false,-51220801792,-51220801728⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1049672274065,0,false,-51004267392,-51004267328⟩
    { al := (54531/256000), au := (437097/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨234208861618,234664665023⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212322612160,212322612224⟩ : DyadicInterval 40),(⟨-263379127616,-263379127552⟩ : DyadicInterval 40),(⟨736986618678,736986638008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212698309760,212698309824⟩ : DyadicInterval 40),(⟨-263958454528,-263958454464⟩ : DyadicInterval 40),(⟨736887918411,736887937740⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212129514752,212129514816⟩ : DyadicInterval 40),(⟨-263081566400,-263081566336⟩ : DyadicInterval 40),(⟨737037257558,737037276887⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212553257600,212553257664⟩ : DyadicInterval 40),(⟨-263734723968,-263734723904⟩ : DyadicInterval 40),(⟨736926052808,736926072138⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨90820547,121347612⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨90816768,90816832⟩ : DyadicInterval 40),(⟨-90824320,-90824256⟩ : DyadicInterval 40),(⟨762123379825,762123399155⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨121340864,121340928⟩ : DyadicInterval 40),(⟨-121354368,-121354304⟩ : DyadicInterval 40),(⟨762123376911,762123396240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-13440,-7488⟩ : DyadicInterval 40),(⟨762123387360,762123409600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨234091753223,234576675426⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212226064448,212226064512⟩ : DyadicInterval 40),(⟨-263230331904,-263230331840⟩ : DyadicInterval 40),(⟨737011945494,737011964823⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212625793984,212625794048⟩ : DyadicInterval 40),(⟨-263846595840,-263846595776⟩ : DyadicInterval 40),(⟨736906987239,736907006568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-51220801792,-51004267328⟩ : DyadicInterval 40),(⟨787625517280,787733803776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨212322612160,212698309824⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-263958454528,-263379127552⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e544_ok : ecellOkT e544 = true := by decide +kernel
theorem e544_pos {a z : ℝ} (ha1 : ((54531/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((437097/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e544 e544_ok ha1 ha2 hz1 hz2 hz

-- box ['54531/256000', '437097/2048000', '3997/4000', '1999/2000']  interval_lower 5802579/1099511627776
noncomputable def e545 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1333720489394,0,true,212322612160,212322612224⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨865302766158,0,false,-263379127616,-263379127552⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1334176292799,0,true,212698309760,212698309824⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨864846962753,0,false,-263958454528,-263958454464⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1333544832747,0,true,212177792320,212177792384⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨865478422805,0,false,-263155949184,-263155949120⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1334058960467,0,true,212601610432,212601610496⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨864964295085,0,false,-263809295744,-263809295680⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099572175241,0,true,60545792,60545856⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099451080311,0,false,-60549184,-60549120⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099602639335,0,true,91007744,91007808⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099420616217,0,false,-91015360,-91015296⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620242,0,false,-7552,-7488⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624442,0,false,-3392,-3328⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1333632656258,0,true,212250200640,212250200704⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨865390599294,0,false,-263267526592,-263267526528⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1334117635675,0,true,212649968576,212649968640⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨864905619877,0,false,-263883884096,-263883884032⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1049453058542,0,false,-51233915456,-51233915392⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1049659807575,0,false,-51017325888,-51017325824⟩
    { al := (54531/256000), au := (437097/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨234208861618,234664665023⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212322612160,212322612224⟩ : DyadicInterval 40),(⟨-263379127616,-263379127552⟩ : DyadicInterval 40),(⟨736986618678,736986638008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212698309760,212698309824⟩ : DyadicInterval 40),(⟨-263958454528,-263958454464⟩ : DyadicInterval 40),(⟨736887918411,736887937740⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212177792320,212177792384⟩ : DyadicInterval 40),(⟨-263155949184,-263155949120⟩ : DyadicInterval 40),(⟨737024602726,737024622056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212601610432,212601610496⟩ : DyadicInterval 40),(⟨-263809295744,-263809295680⟩ : DyadicInterval 40),(⟨736913344623,736913363953⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨60547465,91011559⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨60545792,60545856⟩ : DyadicInterval 40),(⟨-60549184,-60549120⟩ : DyadicInterval 40),(⟨762123381913,762123401242⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨91007744,91007808⟩ : DyadicInterval 40),(⟨-91015360,-91015296⟩ : DyadicInterval 40),(⟨762123379826,762123399155⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7552,-3328⟩ : DyadicInterval 40),(⟨762123385280,762123406656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨234121028482,234606007899⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212250200640,212250200704⟩ : DyadicInterval 40),(⟨-263267526592,-263267526528⟩ : DyadicInterval 40),(⟨737005615415,737005634745⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212649968576,212649968640⟩ : DyadicInterval 40),(⟨-263883884096,-263883884032⟩ : DyadicInterval 40),(⟨736900631216,736900650546⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-51233915456,-51017325824⟩ : DyadicInterval 40),(⟨787632046528,787740360608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨212322612160,212698309824⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-263958454528,-263379127552⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e545_ok : ecellOkT e545 = true := by decide +kernel
theorem e545_pos {a z : ℝ} (ha1 : ((54531/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((437097/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e545 e545_ok ha1 ha2 hz1 hz2 hz

-- box ['437097/2048000', '218973/1024000', '999/1000', '3997/4000']  interval_lower 17255889/1099511627776
noncomputable def e546 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1334176292798,0,true,212698309760,212698309824⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨864846962754,0,false,-263958454528,-263958454464⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1334632096203,0,true,213073878976,213073879040⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨864391159349,0,false,-264538086848,-264538086784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1333941628132,0,true,212504902592,212504902656⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨865081627420,0,false,-263660157184,-263660157120⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1334455755852,0,true,212928594688,212928594752⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨864567499700,0,false,-264313803584,-264313803520⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099602637248,0,true,91005696,91005760⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099420618304,0,false,-91013248,-91013184⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099633227396,0,true,121592896,121592960⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099390028156,0,false,-121606400,-121606336⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511614327,0,false,-13504,-13440⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620243,0,false,-7552,-7488⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1334058956509,0,true,212601607168,212601607232⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨864964299043,0,false,-263809290688,-263809290624⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1334543935685,0,true,213001247168,213001247232⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨864479319867,0,false,-264425951744,-264425951680⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1049270971501,0,false,-51424704576,-51424704512⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1049478096501,0,false,-51207683520,-51207683456⟩
    { al := (437097/2048000), au := (218973/1024000), zl := (999/1000), zu := (3997/4000),
      A := ⟨234664665022,235120468427⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212698309760,212698309824⟩ : DyadicInterval 40),(⟨-263958454528,-263958454464⟩ : DyadicInterval 40),(⟨736887918411,736887937740⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213073878976,213073879040⟩ : DyadicInterval 40),(⟨-264538086848,-264538086784⟩ : DyadicInterval 40),(⟨736789020206,736789039535⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212504902592,212504902656⟩ : DyadicInterval 40),(⟨-263660157184,-263660157120⟩ : DyadicInterval 40),(⟨736938757719,736938777049⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212928594688,212928594752⟩ : DyadicInterval 40),(⟨-264313803584,-264313803520⟩ : DyadicInterval 40),(⟨736827305247,736827324576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨91009472,121599620⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨91005696,91005760⟩ : DyadicInterval 40),(⟨-91013248,-91013184⟩ : DyadicInterval 40),(⟨762123379794,762123399124⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨121592896,121592960⟩ : DyadicInterval 40),(⟨-121606400,-121606336⟩ : DyadicInterval 40),(⟨762123376855,762123396185⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-13504,-7488⟩ : DyadicInterval 40),(⟨762123387360,762123409632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨234547328733,235032307909⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212601607168,212601607232⟩ : DyadicInterval 40),(⟨-263809290688,-263809290624⟩ : DyadicInterval 40),(⟨736913345472,736913364801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213001247168,213001247232⟩ : DyadicInterval 40),(⟨-264425951744,-264425951680⟩ : DyadicInterval 40),(⟨736808164332,736808183661⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-51424704576,-51207683456⟩ : DyadicInterval 40),(⟨787727225344,787835755168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨212698309760,213073879040⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-264538086848,-263958454464⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e546_ok : ecellOkT e546 = true := by decide +kernel
theorem e546_pos {a z : ℝ} (ha1 : ((437097/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((218973/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e546 e546_ok ha1 ha2 hz1 hz2 hz

-- box ['437097/2048000', '218973/1024000', '3997/4000', '1999/2000']  interval_lower 15963679/1099511627776
noncomputable def e547 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1334176292798,0,true,212698309760,212698309824⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨864846962754,0,false,-263958454528,-263958454464⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1334632096203,0,true,213073878976,213073879040⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨864391159349,0,false,-264538086848,-264538086784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1334000294299,0,true,212553257600,212553257664⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨865022961253,0,false,-263734723968,-263734723904⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1334514535969,0,true,212977024896,212977024960⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨864508719583,0,false,-264388559552,-264388559488⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099572301195,0,true,60671744,60671808⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099450954357,0,false,-60675136,-60675072⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099602828345,0,true,91196736,91196800⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099420427207,0,false,-91204352,-91204288⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620211,0,false,-7616,-7552⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624428,0,false,-3392,-3328⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1334088288738,0,true,212625782080,212625782144⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨864934966814,0,false,-263846577408,-263846577344⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1334573325130,0,true,213025460480,213025460544⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨864449930422,0,false,-264463332160,-264463332096⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1049258406102,0,false,-51437871680,-51437871616⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1049465581443,0,false,-51220795328,-51220795264⟩
    { al := (437097/2048000), au := (218973/1024000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨234664665022,235120468427⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212698309760,212698309824⟩ : DyadicInterval 40),(⟨-263958454528,-263958454464⟩ : DyadicInterval 40),(⟨736887918411,736887937740⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213073878976,213073879040⟩ : DyadicInterval 40),(⟨-264538086848,-264538086784⟩ : DyadicInterval 40),(⟨736789020206,736789039535⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212553257600,212553257664⟩ : DyadicInterval 40),(⟨-263734723968,-263734723904⟩ : DyadicInterval 40),(⟨736926052809,736926072138⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212977024896,212977024960⟩ : DyadicInterval 40),(⟨-264388559552,-264388559488⟩ : DyadicInterval 40),(⟨736814546857,736814566187⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨60673419,91200569⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨60671744,60671808⟩ : DyadicInterval 40),(⟨-60675136,-60675072⟩ : DyadicInterval 40),(⟨762123381899,762123401229⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨91196736,91196800⟩ : DyadicInterval 40),(⟨-91204352,-91204288⟩ : DyadicInterval 40),(⟨762123379794,762123399124⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7616,-3328⟩ : DyadicInterval 40),(⟨762123385280,762123406688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨234576660962,235061697354⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212625782080,212625782144⟩ : DyadicInterval 40),(⟨-263846577408,-263846577344⟩ : DyadicInterval 40),(⟨736906990345,736907009674⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213025460480,213025460544⟩ : DyadicInterval 40),(⟨-264463332160,-264463332096⟩ : DyadicInterval 40),(⟨736801783198,736801802527⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-51437871680,-51220795264⟩ : DyadicInterval 40),(⟨787733781248,787842338720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨212698309760,213073879040⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-264538086848,-263958454464⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e547_ok : ecellOkT e547 = true := by decide +kernel
theorem e547_pos {a z : ℝ} (ha1 : ((437097/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((218973/1024000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e547 e547_ok ha1 ha2 hz1 hz2 hz

-- box ['54531/256000', '437097/2048000', '1999/2000', '3999/4000']  interval_lower 1129419/274877906944
noncomputable def e548 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1333720489394,0,true,212322612160,212322612224⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨865302766158,0,false,-263379127616,-263379127552⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1334176292799,0,true,212698309760,212698309824⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨864846962753,0,false,-263958454528,-263958454464⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1333603384963,0,true,212226067712,212226067776⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨865419870589,0,false,-263230336960,-263230336896⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1334117626633,0,true,212649961152,212649961216⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨864905628919,0,false,-263883872576,-263883872512⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541901640,0,true,30273408,30273472⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481353912,0,false,-30274304,-30274240⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099572302758,0,true,60673280,60673344⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099450952794,0,false,-60676672,-60676608⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624427,0,false,-3392,-3328⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626943,0,false,-896,-832⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1333661931757,0,true,212274336512,212274336576⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨865361323795,0,false,-263304722880,-263304722816⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1334146968393,0,true,212674142848,212674142912⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨864876287159,0,false,-263921173952,-263921173888⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1049440540144,0,false,-51247031040,-51247030976⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1049647339424,0,false,-51030386304,-51030386240⟩
    { al := (54531/256000), au := (437097/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨234208861618,234664665023⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212322612160,212322612224⟩ : DyadicInterval 40),(⟨-263379127616,-263379127552⟩ : DyadicInterval 40),(⟨736986618678,736986638008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212698309760,212698309824⟩ : DyadicInterval 40),(⟨-263958454528,-263958454464⟩ : DyadicInterval 40),(⟨736887918411,736887937740⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212226067712,212226067776⟩ : DyadicInterval 40),(⟨-263230336960,-263230336896⟩ : DyadicInterval 40),(⟨737011944647,737011963976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212649961152,212649961216⟩ : DyadicInterval 40),(⟨-263883872576,-263883872512⟩ : DyadicInterval 40),(⟨736900633149,736900652479⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨30273864,60674982⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨30273408,30273472⟩ : DyadicInterval 40),(⟨-30274304,-30274240⟩ : DyadicInterval 40),(⟨762123383166,762123402495⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨60673280,60673344⟩ : DyadicInterval 40),(⟨-60676672,-60676608⟩ : DyadicInterval 40),(⟨762123381899,762123401228⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3392,-832⟩ : DyadicInterval 40),(⟨762123384032,762123404576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨234150303981,234635340617⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212274336512,212274336576⟩ : DyadicInterval 40),(⟨-263304722880,-263304722816⟩ : DyadicInterval 40),(⟨736999284476,736999303805⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212674142848,212674142912⟩ : DyadicInterval 40),(⟨-263921173952,-263921173888⟩ : DyadicInterval 40),(⟨736894274325,736894293654⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-51247031040,-51030386240⟩ : DyadicInterval 40),(⟨787638576736,787746918400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨212322612160,212698309824⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-263958454528,-263379127552⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e548_ok : ecellOkT e548 = true := by decide +kernel
theorem e548_pos {a z : ℝ} (ha1 : ((54531/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((437097/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e548 e548_ok ha1 ha2 hz1 hz2 hz

-- box ['54531/256000', '437097/2048000', '3999/4000', '1']  interval_lower 1615981/549755813888
noncomputable def e549 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1333720489394,0,true,212322612160,212322612224⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨865302766158,0,false,-263379127616,-263379127552⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1334176292799,0,true,212698309760,212698309824⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨864846962753,0,false,-263958454528,-263958454464⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1333661937178,0,true,212274340992,212274341056⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨865361318374,0,false,-263304729728,-263304729664⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541965657,0,true,30337408,30337472⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481289895,0,false,-30338304,-30338240⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626938,0,false,-896,-832⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1333691207501,0,true,212298472064,212298472128⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨865332048051,0,false,-263341920704,-263341920640⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1334176301352,0,true,212698316800,212698316864⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨864846954200,0,false,-263958465408,-263958465344⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1049428020078,0,false,-51260148544,-51260148480⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1049634869610,0,false,-51043448576,-51043448512⟩
    { al := (54531/256000), au := (437097/2048000), zl := (3999/4000), zu := 1,
      A := ⟨234208861618,234664665023⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212322612160,212322612224⟩ : DyadicInterval 40),(⟨-263379127616,-263379127552⟩ : DyadicInterval 40),(⟨736986618678,736986638008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212698309760,212698309824⟩ : DyadicInterval 40),(⟨-263958454528,-263958454464⟩ : DyadicInterval 40),(⟨736887918411,736887937740⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212274340992,212274341056⟩ : DyadicInterval 40),(⟨-263304729728,-263304729664⟩ : DyadicInterval 40),(⟨736999283281,736999302611⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212698309760,212698309824⟩ : DyadicInterval 40),(⟨-263958454528,-263958454464⟩ : DyadicInterval 40),(⟨736887918411,736887937740⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,30337881⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨30337408,30337472⟩ : DyadicInterval 40),(⟨-30338304,-30338240⟩ : DyadicInterval 40),(⟨762123383162,762123402491⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-896,0⟩ : DyadicInterval 40),(⟨762123383616,762123403328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨234179579725,234664673576⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212298472064,212298472128⟩ : DyadicInterval 40),(⟨-263341920704,-263341920640⟩ : DyadicInterval 40),(⟨736992952648,736992971978⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212698316800,212698316864⟩ : DyadicInterval 40),(⟨-263958465408,-263958465344⟩ : DyadicInterval 40),(⟨736887916564,736887935894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-51260148544,-51043448512⟩ : DyadicInterval 40),(⟨787645107872,787753477152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨212322612160,212698309824⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-263958454528,-263379127552⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e549_ok : ecellOkT e549 = true := by decide +kernel
theorem e549_pos {a z : ℝ} (ha1 : ((54531/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((437097/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e549 e549_ok ha1 ha2 hz1 hz2 hz

-- box ['437097/2048000', '218973/1024000', '1999/2000', '3999/4000']  interval_lower 3667541/274877906944
noncomputable def e550 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1334176292798,0,true,212698309760,212698309824⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨864846962754,0,false,-263958454528,-263958454464⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1334632096203,0,true,213073878976,213073879040⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨864391159349,0,false,-264538086848,-264538086784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1334058960465,0,true,212601610432,212601610496⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨864964295087,0,false,-263809295744,-263809295680⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1334573316087,0,true,213025452992,213025453056⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨864449939465,0,false,-264463320640,-264463320576⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541964619,0,true,30336384,30336448⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481290933,0,false,-30337280,-30337216⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099572428768,0,true,60799296,60799360⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099450826784,0,false,-60802688,-60802624⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624413,0,false,-3392,-3328⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626939,0,false,-896,-832⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1334117621210,0,true,212649956672,212649956736⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨864905634342,0,false,-263883865728,-263883865664⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1334602714821,0,true,213049673408,213049673472⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨864420540731,0,false,-264500714176,-264500714112⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1049245839027,0,false,-51451040704,-51451040640⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1049453064716,0,false,-51233908992,-51233908928⟩
    { al := (437097/2048000), au := (218973/1024000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨234664665022,235120468427⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212698309760,212698309824⟩ : DyadicInterval 40),(⟨-263958454528,-263958454464⟩ : DyadicInterval 40),(⟨736887918411,736887937740⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213073878976,213073879040⟩ : DyadicInterval 40),(⟨-264538086848,-264538086784⟩ : DyadicInterval 40),(⟨736789020206,736789039535⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212601610432,212601610496⟩ : DyadicInterval 40),(⟨-263809295744,-263809295680⟩ : DyadicInterval 40),(⟨736913344623,736913363953⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213025452992,213025453056⟩ : DyadicInterval 40),(⟨-264463320640,-264463320576⟩ : DyadicInterval 40),(⟨736801785177,736801804506⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨30336843,60800992⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨30336384,30336448⟩ : DyadicInterval 40),(⟨-30337280,-30337216⟩ : DyadicInterval 40),(⟨762123383162,762123402491⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨60799296,60799360⟩ : DyadicInterval 40),(⟨-60802688,-60802624⟩ : DyadicInterval 40),(⟨762123381885,762123401214⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3392,-832⟩ : DyadicInterval 40),(⟨762123384032,762123404576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨234605993434,235091087045⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212649956672,212649956736⟩ : DyadicInterval 40),(⟨-263883865728,-263883865664⟩ : DyadicInterval 40),(⟨736900634349,736900653678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213049673408,213049673472⟩ : DyadicInterval 40),(⟨-264500714176,-264500714112⟩ : DyadicInterval 40),(⟨736795401225,736795420555⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-51451040704,-51233908928⟩ : DyadicInterval 40),(⟨787740338080,787848923232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨212698309760,213073879040⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-264538086848,-263958454464⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e550_ok : ecellOkT e550 = true := by decide +kernel
theorem e550_pos {a z : ℝ} (ha1 : ((437097/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((218973/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e550 e550_ok ha1 ha2 hz1 hz2 hz

-- box ['437097/2048000', '218973/1024000', '3999/4000', '1']  interval_lower 3343951/274877906944
noncomputable def e551 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1334176292798,0,true,212698309760,212698309824⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨864846962754,0,false,-263958454528,-263958454464⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1334632096203,0,true,213073878976,213073879040⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨864391159349,0,false,-264538086848,-264538086784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1334117626631,0,true,212649961152,212649961216⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨864905628921,0,false,-263883872576,-263883872512⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099542028664,0,true,30400448,30400512⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481226888,0,false,-30401344,-30401280⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626935,0,false,-896,-832⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1334146953927,0,true,212674130944,212674131008⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨864876301625,0,false,-263921155584,-263921155520⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1334632104756,0,true,213073886016,213073886080⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨864391150796,0,false,-264538097728,-264538097664⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1049233270277,0,false,-51464211648,-51464211584⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1049440546319,0,false,-51247024576,-51247024512⟩
    { al := (437097/2048000), au := (218973/1024000), zl := (3999/4000), zu := 1,
      A := ⟨234664665022,235120468427⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212698309760,212698309824⟩ : DyadicInterval 40),(⟨-263958454528,-263958454464⟩ : DyadicInterval 40),(⟨736887918411,736887937740⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213073878976,213073879040⟩ : DyadicInterval 40),(⟨-264538086848,-264538086784⟩ : DyadicInterval 40),(⟨736789020206,736789039535⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212649961152,212649961216⟩ : DyadicInterval 40),(⟨-263883872576,-263883872512⟩ : DyadicInterval 40),(⟨736900633149,736900652479⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213073878976,213073879040⟩ : DyadicInterval 40),(⟨-264538086848,-264538086784⟩ : DyadicInterval 40),(⟨736789020206,736789039535⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,30400888⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨30400448,30400512⟩ : DyadicInterval 40),(⟨-30401344,-30401280⟩ : DyadicInterval 40),(⟨762123383159,762123402488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-896,0⟩ : DyadicInterval 40),(⟨762123383616,762123403328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨234635326151,235120476980⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212674130944,212674131008⟩ : DyadicInterval 40),(⟨-263921155584,-263921155520⟩ : DyadicInterval 40),(⟨736894277458,736894296788⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213073886016,213073886080⟩ : DyadicInterval 40),(⟨-264538097728,-264538097664⟩ : DyadicInterval 40),(⟨736789018352,736789037682⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-51464211648,-51247024512⟩ : DyadicInterval 40),(⟨787746895872,787855508704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨212698309760,213073879040⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-264538086848,-263958454464⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e551_ok : ecellOkT e551 = true := by decide +kernel
theorem e551_pos {a z : ℝ} (ha1 : ((437097/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((218973/1024000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e551 e551_ok ha1 ha2 hz1 hz2 hz

-- box ['218973/1024000', '87759/409600', '999/1000', '3997/4000']  interval_lower 27512581/1099511627776
noncomputable def e552 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1334632096202,0,true,213073878976,213073879040⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨864391159350,0,false,-264538086848,-264538086784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1335087899608,0,true,213449319936,213449320000⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨863935355944,0,false,-265118024896,-265118024832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1334396975733,0,true,212880162304,212880162368⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨864626279819,0,false,-264239052608,-264239052544⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1334911217405,0,true,213303803712,213303803776⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨864112038147,0,false,-264893188288,-264893188224⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099602826249,0,true,91194688,91194752⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099420429303,0,false,-91202304,-91202240⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099633479503,0,true,121844928,121844992⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099389776049,0,false,-121858496,-121858432⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511614271,0,false,-13568,-13504⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620212,0,false,-7616,-7552⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1334514532012,0,true,212977021632,212977021696⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨864508723540,0,false,-264388554560,-264388554496⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1334999568173,0,true,213376572160,213376572224⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨864023687379,0,false,-265005613184,-265005613120⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1049075990106,0,false,-51629040960,-51629040896⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1049283541411,0,false,-51411532864,-51411532800⟩
    { al := (218973/1024000), au := (87759/409600), zl := (999/1000), zu := (3997/4000),
      A := ⟨235120468426,235576271832⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213073878976,213073879040⟩ : DyadicInterval 40),(⟨-264538086848,-264538086784⟩ : DyadicInterval 40),(⟨736789020206,736789039535⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213449319936,213449320000⟩ : DyadicInterval 40),(⟨-265118024896,-265118024832⟩ : DyadicInterval 40),(⟨736689924001,736689943331⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212880162304,212880162368⟩ : DyadicInterval 40),(⟨-264239052608,-264239052544⟩ : DyadicInterval 40),(⟨736840060334,736840079663⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213303803712,213303803776⟩ : DyadicInterval 40),(⟨-264893188288,-264893188224⟩ : DyadicInterval 40),(⟨736728359953,736728379282⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨91198473,121851727⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨91194688,91194752⟩ : DyadicInterval 40),(⟨-91202304,-91202240⟩ : DyadicInterval 40),(⟨762123379795,762123399124⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨121844928,121844992⟩ : DyadicInterval 40),(⟨-121858496,-121858432⟩ : DyadicInterval 40),(⟨762123376831,762123396161⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-13568,-7552⟩ : DyadicInterval 40),(⟨762123387392,762123409664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨235002904236,235487940397⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212977021632,212977021696⟩ : DyadicInterval 40),(⟨-264388554560,-264388554496⟩ : DyadicInterval 40),(⟨736814547735,736814567064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213376572160,213376572224⟩ : DyadicInterval 40),(⟨-265005613184,-265005613120⟩ : DyadicInterval 40),(⟨736709143628,736709162958⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-51629040960,-51411532800⟩ : DyadicInterval 40),(⟨787829150016,787937923360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨213073878976,213449320000⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-265118024896,-264538086784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e552_ok : ecellOkT e552 = true := by decide +kernel
theorem e552_pos {a z : ℝ} (ha1 : ((218973/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((87759/409600 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e552 e552_ok ha1 ha2 hz1 hz2 hz

-- box ['218973/1024000', '87759/409600', '3997/4000', '1999/2000']  interval_lower 13105847/549755813888
noncomputable def e553 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1334632096202,0,true,213073878976,213073879040⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨864391159350,0,false,-264538086848,-264538086784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1335087899608,0,true,213449319936,213449320000⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨863935355944,0,false,-265118024896,-265118024832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1334455755850,0,true,212928594688,212928594752⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨864567499702,0,false,-264313803520,-264313803456⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1334970111473,0,true,213352311232,213352311296⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨864053144079,0,false,-264968128704,-264968128640⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099572427199,0,true,60797696,60797760⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099450828353,0,false,-60801152,-60801088⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099603017431,0,true,91385856,91385920⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099420238121,0,false,-91393472,-91393408⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620179,0,false,-7616,-7552⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624414,0,false,-3392,-3328⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1334543921214,0,true,213001235264,213001235328⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨864479334338,0,false,-264425933376,-264425933312⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1335029014586,0,true,213400824128,213400824192⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨863994240966,0,false,-265043085760,-265043085696⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1049063375944,0,false,-51642261632,-51642261568⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1049270977689,0,false,-51424698048,-51424697984⟩
    { al := (218973/1024000), au := (87759/409600), zl := (3997/4000), zu := (1999/2000),
      A := ⟨235120468426,235576271832⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213073878976,213073879040⟩ : DyadicInterval 40),(⟨-264538086848,-264538086784⟩ : DyadicInterval 40),(⟨736789020206,736789039535⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213449319936,213449320000⟩ : DyadicInterval 40),(⟨-265118024896,-265118024832⟩ : DyadicInterval 40),(⟨736689924001,736689943331⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212928594688,212928594752⟩ : DyadicInterval 40),(⟨-264313803520,-264313803456⟩ : DyadicInterval 40),(⟨736827305222,736827324552⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213352311232,213352311296⟩ : DyadicInterval 40),(⟨-264968128704,-264968128640⟩ : DyadicInterval 40),(⟨736715551288,736715570617⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨60799423,91389655⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨60797696,60797760⟩ : DyadicInterval 40),(⟨-60801152,-60801088⟩ : DyadicInterval 40),(⟨762123381917,762123401247⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨91385856,91385920⟩ : DyadicInterval 40),(⟨-91393472,-91393408⟩ : DyadicInterval 40),(⟨762123379763,762123399093⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7616,-3328⟩ : DyadicInterval 40),(⟨762123385280,762123406688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨235032293438,235517386810⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213001235264,213001235328⟩ : DyadicInterval 40),(⟨-264425933376,-264425933312⟩ : DyadicInterval 40),(⟨736808167477,736808186807⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213400824128,213400824192⟩ : DyadicInterval 40),(⟨-265043085760,-265043085696⟩ : DyadicInterval 40),(⟨736702737316,736702756646⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-51642261632,-51424697984⟩ : DyadicInterval 40),(⟨787835732608,787944533696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨213073878976,213449320000⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-265118024896,-264538086784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e553_ok : ecellOkT e553 = true := by decide +kernel
theorem e553_pos {a z : ℝ} (ha1 : ((218973/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((87759/409600 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e553 e553_ok ha1 ha2 hz1 hz2 hz

-- box ['87759/409600', '109911/512000', '999/1000', '3997/4000']  interval_lower 18928475/549755813888
noncomputable def e554 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1335087899607,0,true,213449319936,213449320000⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨863935355945,0,false,-265118024896,-265118024832⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1335543703012,0,true,213824632768,213824632832⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨863479552540,0,false,-265698268992,-265698268928⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1334852323335,0,true,213255294016,213255294080⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨864170932217,0,false,-264818252992,-264818252928⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1335366678956,0,true,213678884736,213678884800⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨863656576596,0,false,-265472878528,-265472878464⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099603015325,0,true,91383744,91383808⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099420240227,0,false,-91391360,-91391296⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099633731712,0,true,122097152,122097216⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099389523840,0,false,-122110720,-122110656⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511614216,0,false,-13568,-13504⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620181,0,false,-7616,-7552⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1334970107518,0,true,213352307968,213352308032⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨864053148034,0,false,-264968123712,-264968123648⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1335455200657,0,true,213751769152,213751769216⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨863568054895,0,false,-265585580288,-265585580224⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1048880631088,0,false,-51833811136,-51833811072⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1049088608791,0,false,-51615815680,-51615815616⟩
    { al := (87759/409600), au := (109911/512000), zl := (999/1000), zu := (3997/4000),
      A := ⟨235576271831,236032075236⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213449319936,213449320000⟩ : DyadicInterval 40),(⟨-265118024896,-265118024832⟩ : DyadicInterval 40),(⟨736689924001,736689943331⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213824632768,213824632832⟩ : DyadicInterval 40),(⟨-265698268992,-265698268928⟩ : DyadicInterval 40),(⟨736590629734,736590649064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213255294016,213255294080⟩ : DyadicInterval 40),(⟨-264818252992,-264818252928⟩ : DyadicInterval 40),(⟨736741165340,736741184669⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213678884736,213678884800⟩ : DyadicInterval 40),(⟨-265472878528,-265472878464⟩ : DyadicInterval 40),(⟨736629216956,736629236285⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨91387549,122103936⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨91383744,91383808⟩ : DyadicInterval 40),(⟨-91391360,-91391296⟩ : DyadicInterval 40),(⟨762123379763,762123399093⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨122097152,122097216⟩ : DyadicInterval 40),(⟨-122110720,-122110656⟩ : DyadicInterval 40),(⟨762123376775,762123396105⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-13568,-7552⟩ : DyadicInterval 40),(⟨762123387392,762123409664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨235458479742,235943572881⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213352307968,213352308032⟩ : DyadicInterval 40),(⟨-264968123712,-264968123648⟩ : DyadicInterval 40),(⟨736715552168,736715571497⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213751769152,213751769216⟩ : DyadicInterval 40),(⟨-265585580288,-265585580224⟩ : DyadicInterval 40),(⟨736609924953,736609944283⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-51833811136,-51615815616⟩ : DyadicInterval 40),(⟨787931291424,788040308448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨213449319936,213824632832⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-265698268992,-265118024832⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e554_ok : ecellOkT e554 = true := by decide +kernel
theorem e554_pos {a z : ℝ} (ha1 : ((87759/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((109911/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e554 e554_ok ha1 ha2 hz1 hz2 hz

-- box ['87759/409600', '109911/512000', '3997/4000', '1999/2000']  interval_lower 4568409/137438953472
noncomputable def e555 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1335087899607,0,true,213449319936,213449320000⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨863935355945,0,false,-265118024896,-265118024832⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1335543703012,0,true,213824632768,213824632832⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨863479552540,0,false,-265698268992,-265698268928⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1334911217403,0,true,213303803712,213303803776⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨864112038149,0,false,-264893188288,-264893188224⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1335425686975,0,true,213727469568,213727469632⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨863597568577,0,false,-265548003520,-265548003456⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099572553252,0,true,60923776,60923840⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099450702300,0,false,-60927168,-60927104⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099603206592,0,true,91574976,91575040⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099420048960,0,false,-91582656,-91582592⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620148,0,false,-7680,-7616⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624401,0,false,-3392,-3328⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1334999553688,0,true,213376560256,213376560320⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨864023701864,0,false,-265005594752,-265005594688⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1335484704047,0,true,213776059712,213776059776⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨863538551505,0,false,-265623145216,-265623145152⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1048867968065,0,false,-51847085504,-51847085440⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1049075996311,0,false,-51629034432,-51629034368⟩
    { al := (87759/409600), au := (109911/512000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨235576271831,236032075236⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213449319936,213449320000⟩ : DyadicInterval 40),(⟨-265118024896,-265118024832⟩ : DyadicInterval 40),(⟨736689924001,736689943331⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213824632768,213824632832⟩ : DyadicInterval 40),(⟨-265698268992,-265698268928⟩ : DyadicInterval 40),(⟨736590629734,736590649064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213303803712,213303803776⟩ : DyadicInterval 40),(⟨-264893188288,-264893188224⟩ : DyadicInterval 40),(⟨736728359954,736728379283⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213727469568,213727469632⟩ : DyadicInterval 40),(⟨-265548003520,-265548003456⟩ : DyadicInterval 40),(⟨736616357852,736616377181⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨60925476,91578816⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨60923776,60923840⟩ : DyadicInterval 40),(⟨-60927168,-60927104⟩ : DyadicInterval 40),(⟨762123381871,762123401201⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨91574976,91575040⟩ : DyadicInterval 40),(⟨-91582656,-91582592⟩ : DyadicInterval 40),(⟨762123379764,762123399093⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7680,-3328⟩ : DyadicInterval 40),(⟨762123385280,762123406720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨235487925912,235973076271⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213376560256,213376560320⟩ : DyadicInterval 40),(⟨-265005594752,-265005594688⟩ : DyadicInterval 40),(⟨736709146764,736709166094⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213776059712,213776059776⟩ : DyadicInterval 40),(⟨-265623145216,-265623145152⟩ : DyadicInterval 40),(⟨736603493469,736603512798⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-51847085504,-51629034368⟩ : DyadicInterval 40),(⟨787937900800,788046945632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨213449319936,213824632832⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-265698268992,-265118024832⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e555_ok : ecellOkT e555 = true := by decide +kernel
theorem e555_pos {a z : ℝ} (ha1 : ((87759/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((109911/512000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e555 e555_ok ha1 ha2 hz1 hz2 hz

-- box ['218973/1024000', '87759/409600', '1999/2000', '3999/4000']  interval_lower 778433/34359738368
noncomputable def e556 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1334632096202,0,true,213073878976,213073879040⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨864391159350,0,false,-264538086848,-264538086784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1335087899608,0,true,213449319936,213449320000⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨863935355944,0,false,-265118024896,-265118024832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1334514535967,0,true,212977024896,212977024960⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨864508719585,0,false,-264388559552,-264388559488⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1335029005541,0,true,213400816640,213400816704⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨863994250011,0,false,-265043074240,-265043074176⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099542027622,0,true,30399424,30399488⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481227930,0,false,-30400320,-30400256⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099572554828,0,true,60925312,60925376⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099450700724,0,false,-60928768,-60928704⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624399,0,false,-3392,-3328⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626936,0,false,-896,-832⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1334573310655,0,true,213025448512,213025448576⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨864449944897,0,false,-264463313728,-264463313664⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1335058461248,0,true,213425075712,213425075776⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨863964794304,0,false,-265080560000,-265080559936⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1049050760098,0,false,-51655484224,-51655484160⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1049258412292,0,false,-51437865216,-51437865152⟩
    { al := (218973/1024000), au := (87759/409600), zl := (1999/2000), zu := (3999/4000),
      A := ⟨235120468426,235576271832⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213073878976,213073879040⟩ : DyadicInterval 40),(⟨-264538086848,-264538086784⟩ : DyadicInterval 40),(⟨736789020206,736789039535⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213449319936,213449320000⟩ : DyadicInterval 40),(⟨-265118024896,-265118024832⟩ : DyadicInterval 40),(⟨736689924001,736689943331⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212977024896,212977024960⟩ : DyadicInterval 40),(⟨-264388559552,-264388559488⟩ : DyadicInterval 40),(⟨736814546858,736814566187⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213400816640,213400816704⟩ : DyadicInterval 40),(⟨-265043074240,-265043074176⟩ : DyadicInterval 40),(⟨736702739303,736702758633⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨30399846,60927052⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨30399424,30399488⟩ : DyadicInterval 40),(⟨-30400320,-30400256⟩ : DyadicInterval 40),(⟨762123383159,762123402488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨60925312,60925376⟩ : DyadicInterval 40),(⟨-60928768,-60928704⟩ : DyadicInterval 40),(⟨762123381903,762123401232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3392,-832⟩ : DyadicInterval 40),(⟨762123384032,762123404576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨235061682879,235546833472⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213025448512,213025448576⟩ : DyadicInterval 40),(⟨-264463313728,-264463313664⟩ : DyadicInterval 40),(⟨736801786358,736801805688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213425075712,213425075776⟩ : DyadicInterval 40),(⟨-265080560000,-265080559936⟩ : DyadicInterval 40),(⟨736696330183,736696349512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-51655484224,-51437865152⟩ : DyadicInterval 40),(⟨787842316192,787951144992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨213073878976,213449320000⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-265118024896,-264538086784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e556_ok : ecellOkT e556 = true := by decide +kernel
theorem e556_pos {a z : ℝ} (ha1 : ((218973/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((87759/409600 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e556 e556_ok ha1 ha2 hz1 hz2 hz

-- box ['218973/1024000', '87759/409600', '3999/4000', '1']  interval_lower 23606677/1099511627776
noncomputable def e557 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1334632096202,0,true,213073878976,213073879040⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨864391159350,0,false,-264538086848,-264538086784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1335087899608,0,true,213449319936,213449320000⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨863935355944,0,false,-265118024896,-265118024832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1334573316084,0,true,213025452992,213025453056⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨864449939468,0,false,-264463320640,-264463320576⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099542091695,0,true,30463488,30463552⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481163857,0,false,-30464384,-30464320⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626931,0,false,-896,-832⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1334602700345,0,true,213049661504,213049661568⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨864420555207,0,false,-264500695744,-264500695680⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1335087908158,0,true,213449326976,213449327040⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨863935347394,0,false,-265118035776,-265118035712⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1049038142569,0,false,-51668708736,-51668708672⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1049245845219,0,false,-51451034240,-51451034176⟩
    { al := (218973/1024000), au := (87759/409600), zl := (3999/4000), zu := 1,
      A := ⟨235120468426,235576271832⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213073878976,213073879040⟩ : DyadicInterval 40),(⟨-264538086848,-264538086784⟩ : DyadicInterval 40),(⟨736789020206,736789039535⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213449319936,213449320000⟩ : DyadicInterval 40),(⟨-265118024896,-265118024832⟩ : DyadicInterval 40),(⟨736689924001,736689943331⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213025452992,213025453056⟩ : DyadicInterval 40),(⟨-264463320640,-264463320576⟩ : DyadicInterval 40),(⟨736801785178,736801804507⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213449319936,213449320000⟩ : DyadicInterval 40),(⟨-265118024896,-265118024832⟩ : DyadicInterval 40),(⟨736689924001,736689943331⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,30463919⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨30463488,30463552⟩ : DyadicInterval 40),(⟨-30464384,-30464320⟩ : DyadicInterval 40),(⟨762123383155,762123402484⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-896,0⟩ : DyadicInterval 40),(⟨762123383616,762123403328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨235091072569,235576280382⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213049661504,213049661568⟩ : DyadicInterval 40),(⟨-264500695744,-264500695680⟩ : DyadicInterval 40),(⟨736795404348,736795423678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213449326976,213449327040⟩ : DyadicInterval 40),(⟨-265118035776,-265118035712⟩ : DyadicInterval 40),(⟨736689922141,736689941470⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-51668708736,-51451034176⟩ : DyadicInterval 40),(⟨787848900704,787957757248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨213073878976,213449320000⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-265118024896,-264538086784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e557_ok : ecellOkT e557 = true := by decide +kernel
theorem e557_pos {a z : ℝ} (ha1 : ((218973/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((87759/409600 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e557 e557_ok ha1 ha2 hz1 hz2 hz

-- box ['87759/409600', '109911/512000', '1999/2000', '3999/4000']  interval_lower 17618279/549755813888
noncomputable def e558 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1335087899607,0,true,213449319936,213449320000⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨863935355945,0,false,-265118024896,-265118024832⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1335543703012,0,true,213824632768,213824632832⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨863479552540,0,false,-265698268992,-265698268928⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1334970111471,0,true,213352311232,213352311296⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨864053144081,0,false,-264968128704,-264968128640⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1335484694994,0,true,213776052224,213776052288⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨863538560558,0,false,-265623133696,-265623133632⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099542090650,0,true,30462400,30462464⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481164902,0,false,-30463360,-30463296⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099572680939,0,true,61051456,61051520⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099450574613,0,false,-61054912,-61054848⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624385,0,false,-3392,-3328⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626933,0,false,-896,-832⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1335029000100,0,true,213400812160,213400812224⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨863994255452,0,false,-265043067328,-265043067264⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1335514207680,0,true,213800349888,213800349952⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨863509047872,0,false,-265660711744,-265660711680⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1048855303354,0,false,-51860361792,-51860361728⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1049063382151,0,false,-51642255104,-51642255040⟩
    { al := (87759/409600), au := (109911/512000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨235576271831,236032075236⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213449319936,213449320000⟩ : DyadicInterval 40),(⟨-265118024896,-265118024832⟩ : DyadicInterval 40),(⟨736689924001,736689943331⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213824632768,213824632832⟩ : DyadicInterval 40),(⟨-265698268992,-265698268928⟩ : DyadicInterval 40),(⟨736590629734,736590649064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213352311232,213352311296⟩ : DyadicInterval 40),(⟨-264968128704,-264968128640⟩ : DyadicInterval 40),(⟨736715551288,736715570617⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213776052224,213776052288⟩ : DyadicInterval 40),(⟨-265623133696,-265623133632⟩ : DyadicInterval 40),(⟨736603495466,736603514796⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨30462874,61053163⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨30462400,30462464⟩ : DyadicInterval 40),(⟨-30463360,-30463296⟩ : DyadicInterval 40),(⟨762123383187,762123402517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨61051456,61051520⟩ : DyadicInterval 40),(⟨-61054912,-61054848⟩ : DyadicInterval 40),(⟨762123381889,762123401218⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3392,-832⟩ : DyadicInterval 40),(⟨762123384032,762123404576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨235517372324,236002579904⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213400812160,213400812224⟩ : DyadicInterval 40),(⟨-265043067328,-265043067264⟩ : DyadicInterval 40),(⟨736702740491,736702759821⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213800349888,213800349952⟩ : DyadicInterval 40),(⟨-265660711744,-265660711680⟩ : DyadicInterval 40),(⟨736597061133,736597080462⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-51860361792,-51642255040⟩ : DyadicInterval 40),(⟨787944511136,788053583776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨213449319936,213824632832⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-265698268992,-265118024832⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e558_ok : ecellOkT e558 = true := by decide +kernel
theorem e558_pos {a z : ℝ} (ha1 : ((87759/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((109911/512000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e558 e558_ok ha1 ha2 hz1 hz2 hz

-- box ['87759/409600', '109911/512000', '3999/4000', '1']  interval_lower 33924575/1099511627776
noncomputable def e559 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1335087899607,0,true,213449319936,213449320000⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨863935355945,0,false,-265118024896,-265118024832⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1335543703012,0,true,213824632768,213824632832⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨863479552540,0,false,-265698268992,-265698268928⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1335029005539,0,true,213400816640,213400816704⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨863994250013,0,false,-265043074240,-265043074176⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099542154753,0,true,30526528,30526592⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481100799,0,false,-30527424,-30527360⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626928,0,false,-896,-832⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1335058446762,0,true,213425063808,213425063872⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨863964808790,0,false,-265080541568,-265080541504⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1335543711564,0,true,213824639808,213824639872⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨863479543988,0,false,-265698279872,-265698279808⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1048842636953,0,false,-51873640064,-51873640000⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1049050766306,0,false,-51655477696,-51655477632⟩
    { al := (87759/409600), au := (109911/512000), zl := (3999/4000), zu := 1,
      A := ⟨235576271831,236032075236⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213449319936,213449320000⟩ : DyadicInterval 40),(⟨-265118024896,-265118024832⟩ : DyadicInterval 40),(⟨736689924001,736689943331⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213824632768,213824632832⟩ : DyadicInterval 40),(⟨-265698268992,-265698268928⟩ : DyadicInterval 40),(⟨736590629734,736590649064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213400816640,213400816704⟩ : DyadicInterval 40),(⟨-265043074240,-265043074176⟩ : DyadicInterval 40),(⟨736702739304,736702758633⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213824632768,213824632832⟩ : DyadicInterval 40),(⟨-265698268992,-265698268928⟩ : DyadicInterval 40),(⟨736590629734,736590649064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,30526977⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨30526528,30526592⟩ : DyadicInterval 40),(⟨-30527424,-30527360⟩ : DyadicInterval 40),(⟨762123383152,762123402481⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-896,0⟩ : DyadicInterval 40),(⟨762123383616,762123403328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨235546818986,236032083788⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213425063808,213425063872⟩ : DyadicInterval 40),(⟨-265080541568,-265080541504⟩ : DyadicInterval 40),(⟨736696333320,736696352650⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213824639808,213824639872⟩ : DyadicInterval 40),(⟨-265698279872,-265698279808⟩ : DyadicInterval 40),(⟨736590627866,736590647195⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-51873640064,-51655477632⟩ : DyadicInterval 40),(⟨787951122432,788060222912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨213449319936,213824632832⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-265698268992,-265118024832⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e559_ok : ecellOkT e559 = true := by decide +kernel
theorem e559_pos {a z : ℝ} (ha1 : ((87759/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((109911/512000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e559 e559_ok ha1 ha2 hz1 hz2 hz

-- box ['109911/512000', '440493/2048000', '999/1000', '3997/4000']  interval_lower 24144737/549755813888
noncomputable def e560 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1335543703011,0,true,213824632768,213824632832⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨863479552541,0,false,-265698268992,-265698268928⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1335999506416,0,true,214199817536,214199817600⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨863023749136,0,false,-266278819456,-266278819392⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1335307670935,0,true,213630297728,213630297792⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨863715584617,0,false,-265397758656,-265397758592⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1335822140508,0,true,214053837824,214053837888⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨863201115044,0,false,-266052874560,-266052874496⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099603204477,0,true,91572864,91572928⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099420051075,0,false,-91580544,-91580480⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099633984021,0,true,122349376,122349440⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099389271531,0,false,-122363072,-122363008⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511614159,0,false,-13632,-13568⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620149,0,false,-7680,-7616⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1335425683019,0,true,213727466304,213727466368⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨863597572533,0,false,-265547998528,-265547998464⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1335910833140,0,true,214126838080,214126838144⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨863112422412,0,false,-266165853504,-266165853440⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1048684894447,0,false,-52039015424,-52039015360⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1048893298643,0,false,-51820532160,-51820532096⟩
    { al := (109911/512000), au := (440493/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨236032075235,236487878640⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213824632768,213824632832⟩ : DyadicInterval 40),(⟨-265698268992,-265698268928⟩ : DyadicInterval 40),(⟨736590629734,736590649064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214199817536,214199817600⟩ : DyadicInterval 40),(⟨-266278819456,-266278819392⟩ : DyadicInterval 40),(⟨736491137381,736491156711⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213630297728,213630297792⟩ : DyadicInterval 40),(⟨-265397758656,-265397758592⟩ : DyadicInterval 40),(⟨736642072753,736642092083⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214053837824,214053837888⟩ : DyadicInterval 40),(⟨-266052874560,-266052874496⟩ : DyadicInterval 40),(⟨736529876205,736529895534⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨91576701,122356245⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨91572864,91572928⟩ : DyadicInterval 40),(⟨-91580544,-91580480⟩ : DyadicInterval 40),(⟨762123379764,762123399094⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨122349376,122349440⟩ : DyadicInterval 40),(⟨-122363072,-122363008⟩ : DyadicInterval 40),(⟨762123376783,762123396113⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-13632,-7616⟩ : DyadicInterval 40),(⟨762123387424,762123409696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨235914055243,236399205364⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213727466304,213727466368⟩ : DyadicInterval 40),(⟨-265547998528,-265547998464⟩ : DyadicInterval 40),(⟨736616358736,736616378065⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214126838080,214126838144⟩ : DyadicInterval 40),(⟨-266165853504,-266165853440⟩ : DyadicInterval 40),(⟨736510508411,736510527740⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-52039015424,-51820532096⟩ : DyadicInterval 40),(⟨788033649664,788142910592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨213824632768,214199817600⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-266278819456,-265698268928⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e560_ok : ecellOkT e560 = true := by decide +kernel
theorem e560_pos {a z : ℝ} (ha1 : ((109911/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((440493/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e560 e560_ok ha1 ha2 hz1 hz2 hz

-- box ['109911/512000', '440493/2048000', '3997/4000', '1999/2000']  interval_lower 46970939/1099511627776
noncomputable def e561 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1335543703011,0,true,213824632768,213824632832⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨863479552541,0,false,-265698268992,-265698268928⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1335999506416,0,true,214199817536,214199817600⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨863023749136,0,false,-266278819456,-266278819392⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1335366678954,0,true,213678884736,213678884800⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨863656576598,0,false,-265472878528,-265472878464⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1335881262477,0,true,214102499904,214102499968⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨863141993075,0,false,-266128184384,-266128184320⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099572679356,0,true,61049856,61049920⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099450576196,0,false,-61053312,-61053248⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099603395829,0,true,91764160,91764224⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099419859723,0,false,-91771904,-91771840⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620116,0,false,-7680,-7616⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624387,0,false,-3392,-3328⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1335455186162,0,true,213751757184,213751757248⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨863568069390,0,false,-265585561856,-265585561792⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1335940393502,0,true,214151167232,214151167296⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨863082862050,0,false,-266203510848,-266203510784⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1048672182470,0,false,-52052343616,-52052343552⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1048880637310,0,false,-51833804608,-51833804544⟩
    { al := (109911/512000), au := (440493/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨236032075235,236487878640⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213824632768,213824632832⟩ : DyadicInterval 40),(⟨-265698268992,-265698268928⟩ : DyadicInterval 40),(⟨736590629734,736590649064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214199817536,214199817600⟩ : DyadicInterval 40),(⟨-266278819456,-266278819392⟩ : DyadicInterval 40),(⟨736491137381,736491156711⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213678884736,213678884800⟩ : DyadicInterval 40),(⟨-265472878528,-265472878464⟩ : DyadicInterval 40),(⟨736629216956,736629236286⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214102499904,214102499968⟩ : DyadicInterval 40),(⟨-266128184384,-266128184320⟩ : DyadicInterval 40),(⟨736516966590,736516985920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨61051580,91768053⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨61049856,61049920⟩ : DyadicInterval 40),(⟨-61053312,-61053248⟩ : DyadicInterval 40),(⟨762123381889,762123401219⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨91764160,91764224⟩ : DyadicInterval 40),(⟨-91771904,-91771840⟩ : DyadicInterval 40),(⟨762123379764,762123399094⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7680,-3328⟩ : DyadicInterval 40),(⟨762123385280,762123406720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨235943558386,236428765726⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213751757184,213751757248⟩ : DyadicInterval 40),(⟨-265585561856,-265585561792⟩ : DyadicInterval 40),(⟨736609928143,736609947472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214151167232,214151167296⟩ : DyadicInterval 40),(⟨-266203510848,-266203510784⟩ : DyadicInterval 40),(⟨736504051674,736504071003⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-52052343616,-51833804544⟩ : DyadicInterval 40),(⟨788040285888,788149574688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨213824632768,214199817600⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-266278819456,-265698268928⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e561_ok : ecellOkT e561 = true := by decide +kernel
theorem e561_pos {a z : ℝ} (ha1 : ((109911/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((440493/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e561 e561_ok ha1 ha2 hz1 hz2 hz

-- box ['440493/2048000', '220671/1024000', '999/1000', '3997/4000']  interval_lower 14702593/274877906944
noncomputable def e562 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1335999506415,0,true,214199817536,214199817600⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨863023749137,0,false,-266278819456,-266278819392⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1336455309820,0,true,214574874304,214574874368⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨862567945732,0,false,-266859676608,-266859676544⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1335763018536,0,true,214005173632,214005173696⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨863260237016,0,false,-265977569856,-265977569792⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1336277602059,0,true,214428663104,214428663168⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨862745653493,0,false,-266633176640,-266633176576⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099603393703,0,true,91762048,91762112⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099419861849,0,false,-91769792,-91769728⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099634236432,0,true,122601792,122601856⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099389019120,0,false,-122615552,-122615488⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511614103,0,false,-13696,-13632⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620118,0,false,-7680,-7616⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1335881258529,0,true,214102496640,214102496704⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨863141997023,0,false,-266128179328,-266128179264⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1336366465627,0,true,214501779136,214501779200⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨862656789925,0,false,-266746433152,-266746433088⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1048488780180,0,false,-52244654016,-52244653952⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1048697610961,0,false,-52025682688,-52025682624⟩
    { al := (440493/2048000), au := (220671/1024000), zl := (999/1000), zu := (3997/4000),
      A := ⟨236487878639,236943682044⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214199817536,214199817600⟩ : DyadicInterval 40),(⟨-266278819456,-266278819392⟩ : DyadicInterval 40),(⟨736491137381,736491156711⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214574874304,214574874368⟩ : DyadicInterval 40),(⟨-266859676608,-266859676544⟩ : DyadicInterval 40),(⟨736391446918,736391466248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214005173632,214005173696⟩ : DyadicInterval 40),(⟨-265977569856,-265977569792⟩ : DyadicInterval 40),(⟨736542782448,736542801777⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214428663104,214428663168⟩ : DyadicInterval 40),(⟨-266633176640,-266633176576⟩ : DyadicInterval 40),(⟨736430337614,736430356943⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨91765927,122608656⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨91762048,91762112⟩ : DyadicInterval 40),(⟨-91769792,-91769728⟩ : DyadicInterval 40),(⟨762123379764,762123399094⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨122601792,122601856⟩ : DyadicInterval 40),(⟨-122615552,-122615488⟩ : DyadicInterval 40),(⟨762123376759,762123396088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-13696,-7616⟩ : DyadicInterval 40),(⟨762123387424,762123409728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨236369630753,236854837851⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214102496640,214102496704⟩ : DyadicInterval 40),(⟨-266128179328,-266128179264⟩ : DyadicInterval 40),(⟨736516967450,736516986780⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214501779136,214501779200⟩ : DyadicInterval 40),(⟨-266746433152,-266746433088⟩ : DyadicInterval 40),(⟨736410893897,736410913227⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-52244654016,-52025682624⟩ : DyadicInterval 40),(⟨788136224928,788245729888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨214199817536,214574874368⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-266859676608,-266278819392⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e562_ok : ecellOkT e562 = true := by decide +kernel
theorem e562_pos {a z : ℝ} (ha1 : ((440493/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((220671/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e562 e562_ok ha1 ha2 hz1 hz2 hz

-- box ['440493/2048000', '220671/1024000', '3997/4000', '1999/2000']  interval_lower 7185343/137438953472
noncomputable def e563 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1335999506415,0,true,214199817536,214199817600⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨863023749137,0,false,-266278819456,-266278819392⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1336455309820,0,true,214574874304,214574874368⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨862567945732,0,false,-266859676608,-266859676544⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1335822140505,0,true,214053837824,214053837888⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨863201115047,0,false,-266052874560,-266052874496⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1336336837980,0,true,214477402368,214477402432⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨862686417572,0,false,-266708671488,-266708671424⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099572805511,0,true,61176000,61176064⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099450450041,0,false,-61179456,-61179392⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099603585141,0,true,91953472,91953536⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099419670411,0,false,-91961216,-91961152⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620085,0,false,-7744,-7680⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624373,0,false,-3456,-3392⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1335910818634,0,true,214126826112,214126826176⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨863112436918,0,false,-266165835072,-266165835008⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1336396082960,0,true,214526146880,214526146944⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨862627172592,0,false,-266784182976,-266784182912⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1048476019156,0,false,-52258036096,-52258036032⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1048684900686,0,false,-52039008896,-52039008832⟩
    { al := (440493/2048000), au := (220671/1024000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨236487878639,236943682044⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214199817536,214199817600⟩ : DyadicInterval 40),(⟨-266278819456,-266278819392⟩ : DyadicInterval 40),(⟨736491137381,736491156711⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214574874304,214574874368⟩ : DyadicInterval 40),(⟨-266859676608,-266859676544⟩ : DyadicInterval 40),(⟨736391446918,736391466248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214053837824,214053837888⟩ : DyadicInterval 40),(⟨-266052874560,-266052874496⟩ : DyadicInterval 40),(⟨736529876206,736529895535⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214477402368,214477402432⟩ : DyadicInterval 40),(⟨-266708671488,-266708671424⟩ : DyadicInterval 40),(⟨736417377389,736417396719⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨61177735,91957365⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨61176000,61176064⟩ : DyadicInterval 40),(⟨-61179456,-61179392⟩ : DyadicInterval 40),(⟨762123381875,762123401205⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨91953472,91953536⟩ : DyadicInterval 40),(⟨-91961216,-91961152⟩ : DyadicInterval 40),(⟨762123379732,762123399062⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7744,-3392⟩ : DyadicInterval 40),(⟨762123385312,762123406752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨236399190858,236884455184⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214126826112,214126826176⟩ : DyadicInterval 40),(⟨-266165835072,-266165835008⟩ : DyadicInterval 40),(⟨736510511615,736510530944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214526146880,214526146944⟩ : DyadicInterval 40),(⟨-266784182976,-266784182912⟩ : DyadicInterval 40),(⟨736404411827,736404431157⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-52258036096,-52039008832⟩ : DyadicInterval 40),(⟨788142888032,788252420928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨214199817536,214574874368⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-266859676608,-266278819392⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e563_ok : ecellOkT e563 = true := by decide +kernel
theorem e563_pos {a z : ℝ} (ha1 : ((440493/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((220671/1024000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e563 e563_ok ha1 ha2 hz1 hz2 hz

-- box ['109911/512000', '440493/2048000', '1999/2000', '3999/4000']  interval_lower 45651155/1099511627776
noncomputable def e564 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1335543703011,0,true,213824632768,213824632832⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨863479552541,0,false,-265698268992,-265698268928⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1335999506416,0,true,214199817536,214199817600⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨863023749136,0,false,-266278819456,-266278819392⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1335425686973,0,true,213727469568,213727469632⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨863597568579,0,false,-265548003520,-265548003456⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1335940384447,0,true,214151159808,214151159872⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨863082871105,0,false,-266203499328,-266203499264⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099542153704,0,true,30525504,30525568⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481101848,0,false,-30526400,-30526336⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099572807100,0,true,61177600,61177664⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099450448452,0,false,-61181056,-61180992⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624371,0,false,-3456,-3392⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626929,0,false,-896,-832⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1335484689551,0,true,213776047744,213776047808⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨863538566001,0,false,-265623126784,-265623126720⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1335969954114,0,true,214175496064,214175496128⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨863053301438,0,false,-266241169792,-266241169728⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1048659468797,0,false,-52065673728,-52065673664⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1048867974288,0,false,-51847078976,-51847078912⟩
    { al := (109911/512000), au := (440493/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨236032075235,236487878640⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213824632768,213824632832⟩ : DyadicInterval 40),(⟨-265698268992,-265698268928⟩ : DyadicInterval 40),(⟨736590629734,736590649064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214199817536,214199817600⟩ : DyadicInterval 40),(⟨-266278819456,-266278819392⟩ : DyadicInterval 40),(⟨736491137381,736491156711⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213727469568,213727469632⟩ : DyadicInterval 40),(⟨-265548003520,-265548003456⟩ : DyadicInterval 40),(⟨736616357852,736616377182⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214151159808,214151159872⟩ : DyadicInterval 40),(⟨-266203499328,-266203499264⟩ : DyadicInterval 40),(⟨736504053641,736504072970⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨30525928,61179324⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨30525504,30525568⟩ : DyadicInterval 40),(⟨-30526400,-30526336⟩ : DyadicInterval 40),(⟨762123383152,762123402481⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨61177600,61177664⟩ : DyadicInterval 40),(⟨-61181056,-61180992⟩ : DyadicInterval 40),(⟨762123381875,762123401204⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3456,-832⟩ : DyadicInterval 40),(⟨762123384032,762123404608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨235973061775,236458326338⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213776047744,213776047808⟩ : DyadicInterval 40),(⟨-265623126784,-265623126720⟩ : DyadicInterval 40),(⟨736603496659,736603515988⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214175496064,214175496128⟩ : DyadicInterval 40),(⟨-266241169792,-266241169728⟩ : DyadicInterval 40),(⟨736497594038,736497613368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-52065673728,-51847078912⟩ : DyadicInterval 40),(⟨788046923072,788156239744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨213824632768,214199817600⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-266278819456,-265698268928⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e564_ok : ecellOkT e564 = true := by decide +kernel
theorem e564_pos {a z : ℝ} (ha1 : ((109911/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((440493/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e564 e564_ok ha1 ha2 hz1 hz2 hz

-- box ['109911/512000', '440493/2048000', '3999/4000', '1']  interval_lower 44330487/1099511627776
noncomputable def e565 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1335543703011,0,true,213824632768,213824632832⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨863479552541,0,false,-265698268992,-265698268928⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1335999506416,0,true,214199817536,214199817600⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨863023749136,0,false,-266278819456,-266278819392⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1335484694992,0,true,213776052224,213776052288⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨863538560560,0,false,-265623133696,-265623133632⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099542217835,0,true,30589632,30589696⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481037717,0,false,-30590528,-30590464⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626924,0,false,-896,-832⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1335514193183,0,true,213800337984,213800338048⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨863509062369,0,false,-265660693312,-265660693248⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1335999514972,0,true,214199824576,214199824640⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨863023740580,0,false,-266278830336,-266278830272⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1048646753428,0,false,-52079005760,-52079005696⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1048855309579,0,false,-51860355264,-51860355200⟩
    { al := (109911/512000), au := (440493/2048000), zl := (3999/4000), zu := 1,
      A := ⟨236032075235,236487878640⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213824632768,213824632832⟩ : DyadicInterval 40),(⟨-265698268992,-265698268928⟩ : DyadicInterval 40),(⟨736590629734,736590649064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214199817536,214199817600⟩ : DyadicInterval 40),(⟨-266278819456,-266278819392⟩ : DyadicInterval 40),(⟨736491137381,736491156711⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213776052224,213776052288⟩ : DyadicInterval 40),(⟨-265623133696,-265623133632⟩ : DyadicInterval 40),(⟨736603495466,736603514796⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214199817536,214199817600⟩ : DyadicInterval 40),(⟨-266278819456,-266278819392⟩ : DyadicInterval 40),(⟨736491137381,736491156711⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,30590059⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨30589632,30589696⟩ : DyadicInterval 40),(⟨-30590528,-30590464⟩ : DyadicInterval 40),(⟨762123383148,762123402477⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-896,0⟩ : DyadicInterval 40),(⟨762123383616,762123403328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨236002565407,236487887196⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨213800337984,213800338048⟩ : DyadicInterval 40),(⟨-265660693312,-265660693248⟩ : DyadicInterval 40),(⟨736597064285,736597083615⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214199824576,214199824640⟩ : DyadicInterval 40),(⟨-266278830336,-266278830272⟩ : DyadicInterval 40),(⟨736491135505,736491154834⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-52079005760,-51860355200⟩ : DyadicInterval 40),(⟨788053561216,788162905760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨213824632768,214199817600⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-266278819456,-265698268928⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e565_ok : ecellOkT e565 = true := by decide +kernel
theorem e565_pos {a z : ℝ} (ha1 : ((109911/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((440493/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e565 e565_ok ha1 ha2 hz1 hz2 hz

-- box ['440493/2048000', '220671/1024000', '1999/2000', '3999/4000']  interval_lower 56154429/1099511627776
noncomputable def e566 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1335999506415,0,true,214199817536,214199817600⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨863023749137,0,false,-266278819456,-266278819392⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1336455309820,0,true,214574874304,214574874368⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨862567945732,0,false,-266859676608,-266859676544⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1335881262475,0,true,214102499904,214102499968⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨863141993077,0,false,-266128184320,-266128184256⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1336396073900,0,true,214526139392,214526139456⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨862627181652,0,false,-266784171456,-266784171392⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099542216782,0,true,30588544,30588608⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481038770,0,false,-30589440,-30589376⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099572933312,0,true,61303808,61303872⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099450322240,0,false,-61307264,-61307200⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624357,0,false,-3456,-3392⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626925,0,false,-896,-832⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1335940379000,0,true,214151155328,214151155392⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨863082876552,0,false,-266203492416,-266203492352⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1336425700540,0,true,214550514240,214550514304⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨862597555012,0,false,-266821934464,-266821934400⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1048463256430,0,false,-52271420160,-52271420096⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1048672188708,0,false,-52052337088,-52052337024⟩
    { al := (440493/2048000), au := (220671/1024000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨236487878639,236943682044⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214199817536,214199817600⟩ : DyadicInterval 40),(⟨-266278819456,-266278819392⟩ : DyadicInterval 40),(⟨736491137381,736491156711⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214574874304,214574874368⟩ : DyadicInterval 40),(⟨-266859676608,-266859676544⟩ : DyadicInterval 40),(⟨736391446918,736391466248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214102499904,214102499968⟩ : DyadicInterval 40),(⟨-266128184320,-266128184256⟩ : DyadicInterval 40),(⟨736516966565,736516985895⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214526139392,214526139456⟩ : DyadicInterval 40),(⟨-266784171456,-266784171392⟩ : DyadicInterval 40),(⟨736404413842,736404433171⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨30589006,61305536⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨30588544,30588608⟩ : DyadicInterval 40),(⟨-30589440,-30589376⟩ : DyadicInterval 40),(⟨762123383148,762123402478⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨61303808,61303872⟩ : DyadicInterval 40),(⟨-61307264,-61307200⟩ : DyadicInterval 40),(⟨762123381861,762123401190⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3456,-832⟩ : DyadicInterval 40),(⟨762123384032,762123404608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨236428751224,236914072764⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214151155328,214151155392⟩ : DyadicInterval 40),(⟨-266203492416,-266203492352⟩ : DyadicInterval 40),(⟨736504054839,736504074169⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214550514240,214550514304⟩ : DyadicInterval 40),(⟨-266821934464,-266821934400⟩ : DyadicInterval 40),(⟨736397928916,736397948246⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-52271420160,-52052337024⟩ : DyadicInterval 40),(⟨788149552128,788259112960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨214199817536,214574874368⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-266859676608,-266278819392⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e566_ok : ecellOkT e566 = true := by decide +kernel
theorem e566_pos {a z : ℝ} (ha1 : ((440493/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((220671/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e566 e566_ok ha1 ha2 hz1 hz2 hz

-- box ['440493/2048000', '220671/1024000', '3999/4000', '1']  interval_lower 54824727/1099511627776
noncomputable def e567 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1335999506415,0,true,214199817536,214199817600⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨863023749137,0,false,-266278819456,-266278819392⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1336455309820,0,true,214574874304,214574874368⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨862567945732,0,false,-266859676608,-266859676544⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1335940384445,0,true,214151159808,214151159872⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨863082871107,0,false,-266203499328,-266203499264⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099542280943,0,true,30652736,30652800⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099480974609,0,false,-30653632,-30653568⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626921,0,false,-896,-832⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1335969939607,0,true,214175484160,214175484224⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨863053315945,0,false,-266241151360,-266241151296⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1336455318376,0,true,214574881344,214574881408⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨862567937176,0,false,-266859687552,-266859687488⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1048450491998,0,false,-52284806144,-52284806080⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1048659475038,0,false,-52065667136,-52065667072⟩
    { al := (440493/2048000), au := (220671/1024000), zl := (3999/4000), zu := 1,
      A := ⟨236487878639,236943682044⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214199817536,214199817600⟩ : DyadicInterval 40),(⟨-266278819456,-266278819392⟩ : DyadicInterval 40),(⟨736491137381,736491156711⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214574874304,214574874368⟩ : DyadicInterval 40),(⟨-266859676608,-266859676544⟩ : DyadicInterval 40),(⟨736391446918,736391466248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214151159808,214151159872⟩ : DyadicInterval 40),(⟨-266203499328,-266203499264⟩ : DyadicInterval 40),(⟨736504053641,736504072970⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214574874304,214574874368⟩ : DyadicInterval 40),(⟨-266859676608,-266859676544⟩ : DyadicInterval 40),(⟨736391446918,736391466248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,30653167⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨30652736,30652800⟩ : DyadicInterval 40),(⟨-30653632,-30653568⟩ : DyadicInterval 40),(⟨762123383145,762123402474⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-896,0⟩ : DyadicInterval 40),(⟨762123383616,762123403328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨236458311831,236943690600⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214175484160,214175484224⟩ : DyadicInterval 40),(⟨-266241151360,-266241151296⟩ : DyadicInterval 40),(⟨736497597205,736497616535⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214574881344,214574881408⟩ : DyadicInterval 40),(⟨-266859687552,-266859687488⟩ : DyadicInterval 40),(⟨736391445059,736391464389⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-52284806144,-52065667072⟩ : DyadicInterval 40),(⟨788156217152,788265805952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨214199817536,214574874368⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-266859676608,-266278819392⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e567_ok : ecellOkT e567 = true := by decide +kernel
theorem e567_pos {a z : ℝ} (ha1 : ((440493/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((220671/1024000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e567 e567_ok ha1 ha2 hz1 hz2 hz

-- box ['220671/1024000', '442191/2048000', '999/1000', '3997/4000']  interval_lower 69419819/1099511627776
noncomputable def e568 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1336455309819,0,true,214574874304,214574874368⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨862567945733,0,false,-266859676608,-266859676544⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1336911113225,0,true,214949803200,214949803264⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨862112142327,0,false,-267440840832,-267440840768⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1336218366136,0,true,214379921728,214379921792⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨862804889416,0,false,-266557687040,-266557686976⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1336733063612,0,true,214803360640,214803360704⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨862290191940,0,false,-267213785216,-267213785152⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099603583006,0,true,91951360,91951424⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099419672546,0,false,-91959104,-91959040⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099634488942,0,true,122854272,122854336⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099388766610,0,false,-122868032,-122867968⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511614047,0,false,-13760,-13696⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620086,0,false,-7744,-7680⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1336336834030,0,true,214477399104,214477399168⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨862686421522,0,false,-266708666432,-266708666368⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1336822098109,0,true,214876592320,214876592384⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨862201157443,0,false,-267327319488,-267327319424⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1048292288291,0,false,-52450727168,-52450727104⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1048501545754,0,false,-52231267328,-52231267264⟩
    { al := (220671/1024000), au := (442191/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨236943682043,237399485449⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214574874304,214574874368⟩ : DyadicInterval 40),(⟨-266859676608,-266859676544⟩ : DyadicInterval 40),(⟨736391446918,736391466248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214949803200,214949803264⟩ : DyadicInterval 40),(⟨-267440840832,-267440840768⟩ : DyadicInterval 40),(⟨736291558306,736291577635⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214379921728,214379921792⟩ : DyadicInterval 40),(⟨-266557687040,-266557686976⟩ : DyadicInterval 40),(⟨736443294488,736443313818⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214803360640,214803360704⟩ : DyadicInterval 40),(⟨-267213785216,-267213785152⟩ : DyadicInterval 40),(⟨736330601207,736330620537⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨91955230,122861166⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨91951360,91951424⟩ : DyadicInterval 40),(⟨-91959104,-91959040⟩ : DyadicInterval 40),(⟨762123379733,762123399062⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨122854272,122854336⟩ : DyadicInterval 40),(⟨-122868032,-122867968⟩ : DyadicInterval 40),(⟨762123376703,762123396032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-13760,-7680⟩ : DyadicInterval 40),(⟨762123387456,762123409760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨236825206254,237310470333⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214477399104,214477399168⟩ : DyadicInterval 40),(⟨-266708666432,-266708666368⟩ : DyadicInterval 40),(⟨736417378254,736417397583⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214876592320,214876592384⟩ : DyadicInterval 40),(⟨-267327319488,-267327319424⟩ : DyadicInterval 40),(⟨736311081404,736311100734⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-52450727168,-52231267264⟩ : DyadicInterval 40),(⟨788239017248,788348766464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨214574874304,214949803264⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-267440840832,-266859676544⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e568_ok : ecellOkT e568 = true := by decide +kernel
theorem e568_pos {a z : ℝ} (ha1 : ((220671/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((442191/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e568 e568_ok ha1 ha2 hz1 hz2 hz

-- box ['220671/1024000', '442191/2048000', '3997/4000', '1999/2000']  interval_lower 68083673/1099511627776
noncomputable def e569 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1336455309819,0,true,214574874304,214574874368⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨862567945733,0,false,-266859676608,-266859676544⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1336911113225,0,true,214949803200,214949803264⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨862112142327,0,false,-267440840832,-267440840768⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1336277602057,0,true,214428663104,214428663168⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨862745653495,0,false,-266633176640,-266633176576⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1336792413483,0,true,214852177024,214852177088⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨862230842069,0,false,-267289465216,-267289465152⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099572931716,0,true,61302208,61302272⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099450323836,0,false,-61305664,-61305600⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099603774530,0,true,92142848,92142912⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099419481022,0,false,-92150656,-92150592⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620053,0,false,-7744,-7680⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624358,0,false,-3456,-3392⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1336366451111,0,true,214501767168,214501767232⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨862656804441,0,false,-266746414656,-266746414592⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1336851772415,0,true,214900998656,214900998720⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨862171483137,0,false,-267365161984,-267365161920⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1048279478124,0,false,-52464163328,-52464163264⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1048488786435,0,false,-52244647488,-52244647424⟩
    { al := (220671/1024000), au := (442191/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨236943682043,237399485449⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214574874304,214574874368⟩ : DyadicInterval 40),(⟨-266859676608,-266859676544⟩ : DyadicInterval 40),(⟨736391446918,736391466248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214949803200,214949803264⟩ : DyadicInterval 40),(⟨-267440840832,-267440840768⟩ : DyadicInterval 40),(⟨736291558306,736291577635⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214428663104,214428663168⟩ : DyadicInterval 40),(⟨-266633176640,-266633176576⟩ : DyadicInterval 40),(⟨736430337615,736430356944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214852177024,214852177088⟩ : DyadicInterval 40),(⟨-267289465216,-267289465152⟩ : DyadicInterval 40),(⟨736317590250,736317609580⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨61303940,92146754⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨61302208,61302272⟩ : DyadicInterval 40),(⟨-61305664,-61305600⟩ : DyadicInterval 40),(⟨762123381861,762123401191⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨92142848,92142912⟩ : DyadicInterval 40),(⟨-92150656,-92150592⟩ : DyadicInterval 40),(⟨762123379733,762123399062⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7744,-3392⟩ : DyadicInterval 40),(⟨762123385312,762123406752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨236854823335,237340144639⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214501767168,214501767232⟩ : DyadicInterval 40),(⟨-266746414656,-266746414592⟩ : DyadicInterval 40),(⟨736410897091,736410916421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214900998656,214900998720⟩ : DyadicInterval 40),(⟨-267365161984,-267365161920⟩ : DyadicInterval 40),(⟨736304573970,736304593299⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-52464163328,-52244647424⟩ : DyadicInterval 40),(⟨788245707328,788355484544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨214574874304,214949803264⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-267440840832,-266859676544⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e569_ok : ecellOkT e569 = true := by decide +kernel
theorem e569_pos {a z : ℝ} (ha1 : ((220671/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((442191/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e569 e569_ok ha1 ha2 hz1 hz2 hz

-- box ['442191/2048000', '2769/12800', '999/1000', '3997/4000']  interval_lower 80118633/1099511627776
noncomputable def e570 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1336911113224,0,true,214949803200,214949803264⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨862112142328,0,false,-267440840832,-267440840768⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1337366916629,0,true,215324604288,215324604352⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨861656338923,0,false,-268022312384,-268022312320⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1336673713738,0,true,214754542144,214754542208⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨862349541814,0,false,-267138110400,-267138110336⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1337188525163,0,true,215177930560,215177930624⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨861834730389,0,false,-267794700544,-267794700480⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099603772384,0,true,92140736,92140800⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099419483168,0,false,-92148480,-92148416⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099634741556,0,true,123106880,123106944⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099388513996,0,false,-123120704,-123120640⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511613990,0,false,-13824,-13760⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620054,0,false,-7744,-7680⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1336792409536,0,true,214852173760,214852173824⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨862230846016,0,false,-267289460160,-267289460096⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1337277730594,0,true,215251277824,215251277888⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨861745524958,0,false,-267908512896,-267908512832⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1048095418778,0,false,-52657235072,-52657235008⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1048305103016,0,false,-52437286400,-52437286336⟩
    { al := (442191/2048000), au := (2769/12800), zl := (999/1000), zu := (3997/4000),
      A := ⟨237399485448,237855288853⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214949803200,214949803264⟩ : DyadicInterval 40),(⟨-267440840832,-267440840768⟩ : DyadicInterval 40),(⟨736291558306,736291577635⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215324604288,215324604352⟩ : DyadicInterval 40),(⟨-268022312384,-268022312320⟩ : DyadicInterval 40),(⟨736191471495,736191490824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214754542144,214754542208⟩ : DyadicInterval 40),(⟨-267138110400,-267138110336⟩ : DyadicInterval 40),(⟨736343608762,736343628091⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215177930560,215177930624⟩ : DyadicInterval 40),(⟨-267794700544,-267794700480⟩ : DyadicInterval 40),(⟨736230666898,736230686228⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨92144608,123113780⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨92140736,92140800⟩ : DyadicInterval 40),(⟨-92148480,-92148416⟩ : DyadicInterval 40),(⟨762123379701,762123399031⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨123106880,123106944⟩ : DyadicInterval 40),(⟨-123120704,-123120640⟩ : DyadicInterval 40),(⟨762123376678,762123396008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-13824,-7680⟩ : DyadicInterval 40),(⟨762123387456,762123409792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨237280781760,237766102818⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214852173760,214852173824⟩ : DyadicInterval 40),(⟨-267289460160,-267289460096⟩ : DyadicInterval 40),(⟨736317591118,736317610447⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215251277824,215251277888⟩ : DyadicInterval 40),(⟨-267908512896,-267908512832⟩ : DyadicInterval 40),(⟨736211070853,736211090182⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-52657235072,-52437286336⟩ : DyadicInterval 40),(⟨788342026784,788452020416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨214949803200,215324604352⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-268022312384,-267440840768⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e570_ok : ecellOkT e570 = true := by decide +kernel
theorem e570_pos {a z : ℝ} (ha1 : ((442191/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((2769/12800 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e570 e570_ok ha1 ha2 hz1 hz2 hz

-- box ['442191/2048000', '2769/12800', '3997/4000', '1999/2000']  interval_lower 78773557/1099511627776
noncomputable def e571 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1336911113224,0,true,214949803200,214949803264⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨862112142328,0,false,-267440840832,-267440840768⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1337366916629,0,true,215324604288,215324604352⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨861656338923,0,false,-268022312384,-268022312320⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1336733063609,0,true,214803360640,214803360704⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨862290191943,0,false,-267213785216,-267213785152⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1337247988985,0,true,215226824000,215226824064⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨861775266567,0,false,-267870565888,-267870565824⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099573057972,0,true,61428416,61428480⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099450197580,0,false,-61431936,-61431872⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099603963995,0,true,92332288,92332352⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099419291557,0,false,-92340160,-92340096⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620021,0,false,-7808,-7744⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624344,0,false,-3456,-3392⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1336822083582,0,true,214876580416,214876580480⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨862201171970,0,false,-267327300992,-267327300928⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1337307461874,0,true,215275722688,215275722752⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨861715793678,0,false,-267946448064,-267946448000⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1048082559373,0,false,-52670725376,-52670725312⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1048292294563,0,false,-52450720576,-52450720512⟩
    { al := (442191/2048000), au := (2769/12800), zl := (3997/4000), zu := (1999/2000),
      A := ⟨237399485448,237855288853⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214949803200,214949803264⟩ : DyadicInterval 40),(⟨-267440840832,-267440840768⟩ : DyadicInterval 40),(⟨736291558306,736291577635⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215324604288,215324604352⟩ : DyadicInterval 40),(⟨-268022312384,-268022312320⟩ : DyadicInterval 40),(⟨736191471495,736191490824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214803360640,214803360704⟩ : DyadicInterval 40),(⟨-267213785216,-267213785152⟩ : DyadicInterval 40),(⟨736330601208,736330620538⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215226824000,215226824064⟩ : DyadicInterval 40),(⟨-267870565888,-267870565824⟩ : DyadicInterval 40),(⟨736217605109,736217624439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨61430196,92336219⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨61428416,61428480⟩ : DyadicInterval 40),(⟨-61431936,-61431872⟩ : DyadicInterval 40),(⟨762123381879,762123401208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨92332288,92332352⟩ : DyadicInterval 40),(⟨-92340160,-92340096⟩ : DyadicInterval 40),(⟨762123379733,762123399062⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7808,-3392⟩ : DyadicInterval 40),(⟨762123385312,762123406784⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨237310455806,237795834098⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214876580416,214876580480⟩ : DyadicInterval 40),(⟨-267327300992,-267327300928⟩ : DyadicInterval 40),(⟨736311084574,736311103904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215275722688,215275722752⟩ : DyadicInterval 40),(⟨-267946448064,-267946448000⟩ : DyadicInterval 40),(⟨736204537987,736204557316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-52670725376,-52450720512⟩ : DyadicInterval 40),(⟨788348743872,788458765568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨214949803200,215324604352⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-268022312384,-267440840768⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e571_ok : ecellOkT e571 = true := by decide +kernel
theorem e571_pos {a z : ℝ} (ha1 : ((442191/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((2769/12800 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e571 e571_ok ha1 ha2 hz1 hz2 hz

-- box ['220671/1024000', '442191/2048000', '1999/2000', '3999/4000']  interval_lower 2085815/34359738368
noncomputable def e572 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1336455309819,0,true,214574874304,214574874368⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨862567945733,0,false,-266859676608,-266859676544⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1336911113225,0,true,214949803200,214949803264⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨862112142327,0,false,-267440840832,-267440840768⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1336336837977,0,true,214477402304,214477402368⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨862686417575,0,false,-266708671488,-266708671424⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1336851763354,0,true,214900991168,214900991232⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨862171492198,0,false,-267365150400,-267365150336⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099542279887,0,true,30651648,30651712⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099480975665,0,false,-30652544,-30652480⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099573059574,0,true,61430080,61430144⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099450195978,0,false,-61433536,-61433472⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624343,0,false,-3456,-3392⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626922,0,false,-896,-832⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1336396068437,0,true,214526134912,214526134976⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨862627187115,0,false,-266784164480,-266784164416⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1336881446970,0,true,214925404608,214925404672⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨862141808582,0,false,-267403006016,-267403005952⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1048266666248,0,false,-52477601408,-52477601344⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1048476025415,0,false,-52258029568,-52258029504⟩
    { al := (220671/1024000), au := (442191/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨236943682043,237399485449⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214574874304,214574874368⟩ : DyadicInterval 40),(⟨-266859676608,-266859676544⟩ : DyadicInterval 40),(⟨736391446918,736391466248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214949803200,214949803264⟩ : DyadicInterval 40),(⟨-267440840832,-267440840768⟩ : DyadicInterval 40),(⟨736291558306,736291577635⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214477402304,214477402368⟩ : DyadicInterval 40),(⟨-266708671488,-266708671424⟩ : DyadicInterval 40),(⟨736417377429,736417396758⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214900991168,214900991232⟩ : DyadicInterval 40),(⟨-267365150400,-267365150336⟩ : DyadicInterval 40),(⟨736304575967,736304595297⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨30652111,61431798⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨30651648,30651712⟩ : DyadicInterval 40),(⟨-30652544,-30652480⟩ : DyadicInterval 40),(⟨762123383145,762123402474⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨61430080,61430144⟩ : DyadicInterval 40),(⟨-61433536,-61433472⟩ : DyadicInterval 40),(⟨762123381847,762123401176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3456,-832⟩ : DyadicInterval 40),(⟨762123384032,762123404608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨236884440661,237369819194⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214526134912,214526134976⟩ : DyadicInterval 40),(⟨-266784164480,-266784164416⟩ : DyadicInterval 40),(⟨736404415023,736404434353⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214925404608,214925404672⟩ : DyadicInterval 40),(⟨-267403006016,-267403005952⟩ : DyadicInterval 40),(⟨736298065637,736298084966⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-52477601408,-52258029504⟩ : DyadicInterval 40),(⟨788252398368,788362203584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨214574874304,214949803264⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-267440840832,-266859676544⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e572_ok : ecellOkT e572 = true := by decide +kernel
theorem e572_pos {a z : ℝ} (ha1 : ((220671/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((442191/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e572 e572_ok ha1 ha2 hz1 hz2 hz

-- box ['220671/1024000', '442191/2048000', '3999/4000', '1']  interval_lower 16351913/274877906944
noncomputable def e573 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1336455309819,0,true,214574874304,214574874368⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨862567945733,0,false,-266859676608,-266859676544⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1336911113225,0,true,214949803200,214949803264⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨862112142327,0,false,-267440840832,-267440840768⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1336396073898,0,true,214526139392,214526139456⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨862627181654,0,false,-266784171456,-266784171392⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099542344075,0,true,30715840,30715904⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099480911477,0,false,-30716736,-30716672⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626917,0,false,-896,-832⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1336425686023,0,true,214550502336,214550502400⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨862597569529,0,false,-266821915968,-266821915904⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1336911121780,0,true,214949810240,214949810304⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨862112133772,0,false,-267440851712,-267440851648⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1048253852660,0,false,-52491041472,-52491041408⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1048463262687,0,false,-52271413632,-52271413568⟩
    { al := (220671/1024000), au := (442191/2048000), zl := (3999/4000), zu := 1,
      A := ⟨236943682043,237399485449⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214574874304,214574874368⟩ : DyadicInterval 40),(⟨-266859676608,-266859676544⟩ : DyadicInterval 40),(⟨736391446918,736391466248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214949803200,214949803264⟩ : DyadicInterval 40),(⟨-267440840832,-267440840768⟩ : DyadicInterval 40),(⟨736291558306,736291577635⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214526139392,214526139456⟩ : DyadicInterval 40),(⟨-266784171456,-266784171392⟩ : DyadicInterval 40),(⟨736404413842,736404433172⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214949803200,214949803264⟩ : DyadicInterval 40),(⟨-267440840832,-267440840768⟩ : DyadicInterval 40),(⟨736291558306,736291577635⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,30716299⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨30715840,30715904⟩ : DyadicInterval 40),(⟨-30716736,-30716672⟩ : DyadicInterval 40),(⟨762123383141,762123402470⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-896,0⟩ : DyadicInterval 40),(⟨762123383616,762123403328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨236914058247,237399494004⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214550502336,214550502400⟩ : DyadicInterval 40),(⟨-266821915968,-266821915904⟩ : DyadicInterval 40),(⟨736397932073,736397951403⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214949810240,214949810304⟩ : DyadicInterval 40),(⟨-267440851712,-267440851648⟩ : DyadicInterval 40),(⟨736291556414,736291575744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-52491041472,-52271413568⟩ : DyadicInterval 40),(⟨788259090400,788368923616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨214574874304,214949803264⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-267440840832,-266859676544⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e573_ok : ecellOkT e573 = true := by decide +kernel
theorem e573_pos {a z : ℝ} (ha1 : ((220671/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((442191/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e573 e573_ok ha1 ha2 hz1 hz2 hz

-- box ['442191/2048000', '2769/12800', '1999/2000', '3999/4000']  interval_lower 151225/2147483648
noncomputable def e574 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1336911113224,0,true,214949803200,214949803264⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨862112142328,0,false,-267440840832,-267440840768⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1337366916629,0,true,215324604288,215324604352⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨861656338923,0,false,-268022312384,-268022312320⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1336792413481,0,true,214852177024,214852177088⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨862230842071,0,false,-267289465216,-267289465152⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1337307452807,0,true,215275715200,215275715264⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨861715802745,0,false,-267946436544,-267946436480⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099542343016,0,true,30714752,30714816⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099480912536,0,false,-30715712,-30715648⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099573185888,0,true,61556352,61556416⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099450069664,0,false,-61559872,-61559808⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624329,0,false,-3456,-3392⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626918,0,false,-896,-832⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1336851757889,0,true,214900986688,214900986752⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨862171497663,0,false,-267365143424,-267365143360⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1337337193398,0,true,215300167168,215300167232⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨861686062154,0,false,-267984384832,-267984384768⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1048069698255,0,false,-52684217664,-52684217600⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1048279484397,0,false,-52464156736,-52464156672⟩
    { al := (442191/2048000), au := (2769/12800), zl := (1999/2000), zu := (3999/4000),
      A := ⟨237399485448,237855288853⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214949803200,214949803264⟩ : DyadicInterval 40),(⟨-267440840832,-267440840768⟩ : DyadicInterval 40),(⟨736291558306,736291577635⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215324604288,215324604352⟩ : DyadicInterval 40),(⟨-268022312384,-268022312320⟩ : DyadicInterval 40),(⟨736191471495,736191490824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214852177024,214852177088⟩ : DyadicInterval 40),(⟨-267289465216,-267289465152⟩ : DyadicInterval 40),(⟨736317590251,736317609580⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215275715200,215275715264⟩ : DyadicInterval 40),(⟨-267946436544,-267946436480⟩ : DyadicInterval 40),(⟨736204540018,736204559348⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨30715240,61558112⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨30714752,30714816⟩ : DyadicInterval 40),(⟨-30715712,-30715648⟩ : DyadicInterval 40),(⟨762123383173,762123402502⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨61556352,61556416⟩ : DyadicInterval 40),(⟨-61559872,-61559808⟩ : DyadicInterval 40),(⟨762123381865,762123401194⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3456,-832⟩ : DyadicInterval 40),(⟨762123384032,762123404608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨237340130113,237825565622⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214900986688,214900986752⟩ : DyadicInterval 40),(⟨-267365143424,-267365143360⟩ : DyadicInterval 40),(⟨736304577155,736304596484⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215300167168,215300167232⟩ : DyadicInterval 40),(⟨-267984384832,-267984384768⟩ : DyadicInterval 40),(⟨736198004240,736198023570⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-52684217664,-52464156672⟩ : DyadicInterval 40),(⟨788355461952,788465511712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨214949803200,215324604352⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-268022312384,-267440840768⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e574_ok : ecellOkT e574 = true := by decide +kernel
theorem e574_pos {a z : ℝ} (ha1 : ((442191/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((2769/12800 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e574 e574_ok ha1 ha2 hz1 hz2 hz

-- box ['442191/2048000', '2769/12800', '3999/4000', '1']  interval_lower 4754965/68719476736
noncomputable def e575 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1336911113224,0,true,214949803200,214949803264⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨862112142328,0,false,-267440840832,-267440840768⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1337366916629,0,true,215324604288,215324604352⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨861656338923,0,false,-268022312384,-268022312320⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1336851763352,0,true,214900991168,214900991232⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨862171492200,0,false,-267365150400,-267365150336⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099542407234,0,true,30779008,30779072⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099480848318,0,false,-30779904,-30779840⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626914,0,false,-896,-832⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1336881432443,0,true,214925392640,214925392704⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨862141823109,0,false,-267402987520,-267402987456⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1337366925184,0,true,215324611328,215324611392⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨861656330368,0,false,-268022323264,-268022323200⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1048056835415,0,false,-52697711936,-52697711872⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1048266672522,0,false,-52477594816,-52477594752⟩
    { al := (442191/2048000), au := (2769/12800), zl := (3999/4000), zu := 1,
      A := ⟨237399485448,237855288853⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214949803200,214949803264⟩ : DyadicInterval 40),(⟨-267440840832,-267440840768⟩ : DyadicInterval 40),(⟨736291558306,736291577635⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215324604288,215324604352⟩ : DyadicInterval 40),(⟨-268022312384,-268022312320⟩ : DyadicInterval 40),(⟨736191471495,736191490824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214900991168,214900991232⟩ : DyadicInterval 40),(⟨-267365150400,-267365150336⟩ : DyadicInterval 40),(⟨736304575968,736304595298⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215324604288,215324604352⟩ : DyadicInterval 40),(⟨-268022312384,-268022312320⟩ : DyadicInterval 40),(⟨736191471495,736191490824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,30779458⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨30779008,30779072⟩ : DyadicInterval 40),(⟨-30779904,-30779840⟩ : DyadicInterval 40),(⟨762123383138,762123402467⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-896,0⟩ : DyadicInterval 40),(⟨762123383616,762123403328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨237369804667,237855297408⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨214925392640,214925392704⟩ : DyadicInterval 40),(⟨-267402987520,-267402987456⟩ : DyadicInterval 40),(⟨736298068848,736298088177⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215324611328,215324611392⟩ : DyadicInterval 40),(⟨-268022323264,-268022323200⟩ : DyadicInterval 40),(⟨736191469596,736191488926⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-52697711936,-52477594752⟩ : DyadicInterval 40),(⟨788362180992,788472258848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨214949803200,215324604352⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-268022312384,-267440840768⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e575_ok : ecellOkT e575 = true := by decide +kernel
theorem e575_pos {a z : ℝ} (ha1 : ((442191/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((2769/12800 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e575 e575_ok ha1 ha2 hz1 hz2 hz

-- box ['2769/12800', '443889/2048000', '999/1000', '3997/4000']  interval_lower 90907183/1099511627776
noncomputable def e576 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1337366916628,0,true,215324604288,215324604352⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨861656338924,0,false,-268022312384,-268022312320⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1337822720033,0,true,215699277632,215699277696⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨861200535519,0,false,-268604091584,-268604091520⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1337129061339,0,true,215129034944,215129035008⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨861894194213,0,false,-267718840384,-267718840320⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1337643986714,0,true,215552372928,215552372992⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨861379268838,0,false,-268375922944,-268375922880⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099603961840,0,true,92330176,92330240⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099419293712,0,false,-92337984,-92337920⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099634994272,0,true,123359552,123359616⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099388261280,0,false,-123373440,-123373376⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511613934,0,false,-13888,-13824⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620023,0,false,-7808,-7744⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1337247985035,0,true,215226820736,215226820800⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨861775270517,0,false,-267870560832,-267870560768⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1337733363080,0,true,215625835712,215625835776⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨861289892472,0,false,-268490013696,-268490013632⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1047898171639,0,false,-52864177984,-52864177920⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1048108282750,0,false,-52643740096,-52643740032⟩
    { al := (2769/12800), au := (443889/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨237855288852,238311092257⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215324604288,215324604352⟩ : DyadicInterval 40),(⟨-268022312384,-268022312320⟩ : DyadicInterval 40),(⟨736191471495,736191490825⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215699277632,215699277696⟩ : DyadicInterval 40),(⟨-268604091584,-268604091520⟩ : DyadicInterval 40),(⟨736091186461,736091205790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215129034944,215129035008⟩ : DyadicInterval 40),(⟨-267718840384,-267718840320⟩ : DyadicInterval 40),(⟨736243725294,736243744624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215552372928,215552372992⟩ : DyadicInterval 40),(⟨-268375922944,-268375922880⟩ : DyadicInterval 40),(⟨736130534660,736130553990⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨92334064,123366496⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨92330176,92330240⟩ : DyadicInterval 40),(⟨-92337984,-92337920⟩ : DyadicInterval 40),(⟨762123379701,762123399031⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨123359552,123359616⟩ : DyadicInterval 40),(⟨-123373440,-123373376⟩ : DyadicInterval 40),(⟨762123376653,762123395983⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-13888,-7744⟩ : DyadicInterval 40),(⟨762123387488,762123409824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨237736357259,238221735304⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215226820736,215226820800⟩ : DyadicInterval 40),(⟨-267870560832,-267870560768⟩ : DyadicInterval 40),(⟨736217605981,736217625310⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215625835712,215625835776⟩ : DyadicInterval 40),(⟨-268490013696,-268490013632⟩ : DyadicInterval 40),(⟨736110862218,736110881547⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-52864177984,-52643740032⟩ : DyadicInterval 40),(⟨788445253632,788555491872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨215324604288,215699277696⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-268604091584,-268022312320⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e576_ok : ecellOkT e576 = true := by decide +kernel
theorem e576_pos {a z : ℝ} (ha1 : ((2769/12800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((443889/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e576 e576_ok ha1 ha2 hz1 hz2 hz

-- box ['2769/12800', '443889/2048000', '3997/4000', '1999/2000']  interval_lower 44776485/549755813888
noncomputable def e577 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1337366916628,0,true,215324604288,215324604352⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨861656338924,0,false,-268022312384,-268022312320⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1337822720033,0,true,215699277632,215699277696⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨861200535519,0,false,-268604091584,-268604091520⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1337188525161,0,true,215177930560,215177930624⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨861834730391,0,false,-267794700544,-267794700480⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1337703564488,0,true,215601343360,215601343424⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨861319691064,0,false,-268451973888,-268451973824⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099573184279,0,true,61554752,61554816⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099450071273,0,false,-61558272,-61558208⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099604153536,0,true,92521856,92521920⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099419102016,0,false,-92529664,-92529600⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619989,0,false,-7808,-7744⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624330,0,false,-3456,-3392⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1337277716057,0,true,215251265920,215251265984⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨861745539495,0,false,-267908494400,-267908494336⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1337763151329,0,true,215650319040,215650319104⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨861260104223,0,false,-268528041664,-268528041600⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1047885262905,0,false,-52877722624,-52877722560⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1048095425066,0,false,-52657228480,-52657228416⟩
    { al := (2769/12800), au := (443889/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨237855288852,238311092257⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215324604288,215324604352⟩ : DyadicInterval 40),(⟨-268022312384,-268022312320⟩ : DyadicInterval 40),(⟨736191471495,736191490825⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215699277632,215699277696⟩ : DyadicInterval 40),(⟨-268604091584,-268604091520⟩ : DyadicInterval 40),(⟨736091186461,736091205790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215177930560,215177930624⟩ : DyadicInterval 40),(⟨-267794700544,-267794700480⟩ : DyadicInterval 40),(⟨736230666898,736230686228⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215601343360,215601343424⟩ : DyadicInterval 40),(⟨-268451973888,-268451973824⟩ : DyadicInterval 40),(⟨736117421967,736117441296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨61556503,92525760⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨61554752,61554816⟩ : DyadicInterval 40),(⟨-61558272,-61558208⟩ : DyadicInterval 40),(⟨762123381865,762123401194⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨92521856,92521920⟩ : DyadicInterval 40),(⟨-92529664,-92529600⟩ : DyadicInterval 40),(⟨762123379669,762123398999⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7808,-3392⟩ : DyadicInterval 40),(⟨762123385312,762123406784⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨237766088281,238251523553⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215251265920,215251265984⟩ : DyadicInterval 40),(⟨-267908494400,-267908494336⟩ : DyadicInterval 40),(⟨736211074037,736211093367⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215650319040,215650319104⟩ : DyadicInterval 40),(⟨-268528041664,-268528041600⟩ : DyadicInterval 40),(⟨736104303903,736104323233⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-52877722624,-52657228416⟩ : DyadicInterval 40),(⟨788451997824,788562264192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨215324604288,215699277696⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-268604091584,-268022312320⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e577_ok : ecellOkT e577 = true := by decide +kernel
theorem e577_pos {a z : ℝ} (ha1 : ((2769/12800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((443889/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e577 e577_ok ha1 ha2 hz1 hz2 hz

-- box ['443889/2048000', '222369/1024000', '999/1000', '3997/4000']  interval_lower 25446477/274877906944
noncomputable def e578 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1337822720032,0,true,215699277632,215699277696⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨861200535520,0,false,-268604091584,-268604091520⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1338278523438,0,true,216073823360,216073823424⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨860744732114,0,false,-269186178752,-269186178688⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1337584408939,0,true,215503400320,215503400384⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨861438846613,0,false,-268299877184,-268299877120⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1338099448267,0,true,215926687808,215926687872⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨860923807285,0,false,-268957452736,-268957452672⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099604151371,0,true,92519680,92519744⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099419104181,0,false,-92527552,-92527488⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099635247087,0,true,123612352,123612416⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099388008465,0,false,-123626304,-123626240⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511613877,0,false,-13952,-13888⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619991,0,false,-7808,-7744⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1337703560545,0,true,215601340096,215601340160⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨861319695007,0,false,-268451968832,-268451968768⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1338188995570,0,true,216000266048,216000266112⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨860834259982,0,false,-269071822208,-269071822144⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1047700546876,0,false,-53071556160,-53071556096⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1047911084951,0,false,-52850628736,-52850628672⟩
    { al := (443889/2048000), au := (222369/1024000), zl := (999/1000), zu := (3997/4000),
      A := ⟨238311092256,238766895662⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215699277632,215699277696⟩ : DyadicInterval 40),(⟨-268604091584,-268604091520⟩ : DyadicInterval 40),(⟨736091186461,736091205790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216073823360,216073823424⟩ : DyadicInterval 40),(⟨-269186178752,-269186178688⟩ : DyadicInterval 40),(⟨735990703137,735990722467⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215503400320,215503400384⟩ : DyadicInterval 40),(⟨-268299877184,-268299877120⟩ : DyadicInterval 40),(⟨736143643933,736143663263⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215926687808,215926687872⟩ : DyadicInterval 40),(⟨-268957452736,-268957452672⟩ : DyadicInterval 40),(⟨736030204468,736030223797⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨92523595,123619311⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨92519680,92519744⟩ : DyadicInterval 40),(⟨-92527552,-92527488⟩ : DyadicInterval 40),(⟨762123379701,762123399031⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨123612352,123612416⟩ : DyadicInterval 40),(⟨-123626304,-123626240⟩ : DyadicInterval 40),(⟨762123376629,762123395958⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-13952,-7744⟩ : DyadicInterval 40),(⟨762123387488,762123409856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨238191932769,238677367794⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215601340096,215601340160⟩ : DyadicInterval 40),(⟨-268451968832,-268451968768⟩ : DyadicInterval 40),(⟨736117422840,736117442170⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216000266048,216000266112⟩ : DyadicInterval 40),(⟨-269071822208,-269071822144⟩ : DyadicInterval 40),(⟨736010455474,736010474803⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-53071556160,-52850628672⟩ : DyadicInterval 40),(⟨788548697952,788659180960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨215699277632,216073823424⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-269186178752,-268604091520⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e578_ok : ecellOkT e578 = true := by decide +kernel
theorem e578_pos {a z : ℝ} (ha1 : ((443889/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((222369/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e578 e578_ok ha1 ha2 hz1 hz2 hz

-- box ['443889/2048000', '222369/1024000', '3997/4000', '1999/2000']  interval_lower 100422671/1099511627776
noncomputable def e579 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1337822720032,0,true,215699277632,215699277696⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨861200535520,0,false,-268604091584,-268604091520⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1338278523438,0,true,216073823360,216073823424⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨860744732114,0,false,-269186178752,-269186178688⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1337643986712,0,true,215552372928,215552372992⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨861379268840,0,false,-268375922880,-268375922816⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1338159139991,0,true,215975735168,215975735232⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨860864115561,0,false,-269033689472,-269033689408⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099573310636,0,true,61681088,61681152⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099449944916,0,false,-61684608,-61684544⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099604343154,0,true,92711424,92711488⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099418912398,0,false,-92719296,-92719232⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619957,0,false,-7872,-7808⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624316,0,false,-3520,-3456⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1337733348537,0,true,215625823744,215625823808⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨861289907015,0,false,-268489995136,-268489995072⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1338218840786,0,true,216024787840,216024787904⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨860804414766,0,false,-269109943040,-269109942976⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1047687588717,0,false,-53085155200,-53085155136⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1047898177942,0,false,-52864171392,-52864171328⟩
    { al := (443889/2048000), au := (222369/1024000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨238311092256,238766895662⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215699277632,215699277696⟩ : DyadicInterval 40),(⟨-268604091584,-268604091520⟩ : DyadicInterval 40),(⟨736091186461,736091205790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216073823360,216073823424⟩ : DyadicInterval 40),(⟨-269186178752,-269186178688⟩ : DyadicInterval 40),(⟨735990703137,735990722467⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215552372928,215552372992⟩ : DyadicInterval 40),(⟨-268375922880,-268375922816⟩ : DyadicInterval 40),(⟨736130534635,736130553965⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215975735168,215975735232⟩ : DyadicInterval 40),(⟨-269033689472,-269033689408⟩ : DyadicInterval 40),(⟨736017040772,736017060102⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨61682860,92715378⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨61681088,61681152⟩ : DyadicInterval 40),(⟨-61684608,-61684544⟩ : DyadicInterval 40),(⟨762123381851,762123401180⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨92711424,92711488⟩ : DyadicInterval 40),(⟨-92719296,-92719232⟩ : DyadicInterval 40),(⟨762123379669,762123398999⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7872,-3456⟩ : DyadicInterval 40),(⟨762123385344,762123406816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨238221720761,238707213010⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215625823744,215625823808⟩ : DyadicInterval 40),(⟨-268489995136,-268489995072⟩ : DyadicInterval 40),(⟨736110865430,736110884760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216024787840,216024787904⟩ : DyadicInterval 40),(⟨-269109943040,-269109942976⟩ : DyadicInterval 40),(⟨736003871630,736003890960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-53085155200,-52864171328⟩ : DyadicInterval 40),(⟨788555469280,788665980480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨215699277632,216073823424⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-269186178752,-268604091520⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e579_ok : ecellOkT e579 = true := by decide +kernel
theorem e579_pos {a z : ℝ} (ha1 : ((443889/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((222369/1024000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e579 e579_ok ha1 ha2 hz1 hz2 hz

-- box ['2769/12800', '443889/2048000', '1999/2000', '3999/4000']  interval_lower 88197599/1099511627776
noncomputable def e580 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1337366916628,0,true,215324604288,215324604352⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨861656338924,0,false,-268022312384,-268022312320⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1337822720033,0,true,215699277632,215699277696⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨861200535519,0,false,-268604091584,-268604091520⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1337247988983,0,true,215226824000,215226824064⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨861775266569,0,false,-267870565888,-267870565824⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1337763142261,0,true,215650311552,215650311616⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨861260113291,0,false,-268528030080,-268528030016⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099542406172,0,true,30777920,30777984⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099480849380,0,false,-30778880,-30778816⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099573312252,0,true,61682688,61682752⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099449943300,0,false,-61686208,-61686144⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624315,0,false,-3520,-3456⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626915,0,false,-896,-832⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1337307447336,0,true,215275710720,215275710784⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨861715808216,0,false,-267946429504,-267946429440⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1337792939828,0,true,215674802048,215674802112⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨861230315724,0,false,-268566071232,-268566071168⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1047872352447,0,false,-52891269184,-52891269120⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1048082565662,0,false,-52670718784,-52670718720⟩
    { al := (2769/12800), au := (443889/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨237855288852,238311092257⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215324604288,215324604352⟩ : DyadicInterval 40),(⟨-268022312384,-268022312320⟩ : DyadicInterval 40),(⟨736191471495,736191490825⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215699277632,215699277696⟩ : DyadicInterval 40),(⟨-268604091584,-268604091520⟩ : DyadicInterval 40),(⟨736091186461,736091205790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215226824000,215226824064⟩ : DyadicInterval 40),(⟨-267870565888,-267870565824⟩ : DyadicInterval 40),(⟨736217605110,736217624440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215650311552,215650311616⟩ : DyadicInterval 40),(⟨-268528030080,-268528030016⟩ : DyadicInterval 40),(⟨736104305918,736104325248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨30778396,61684476⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨30777920,30777984⟩ : DyadicInterval 40),(⟨-30778880,-30778816⟩ : DyadicInterval 40),(⟨762123383170,762123402499⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨61682688,61682752⟩ : DyadicInterval 40),(⟨-61686208,-61686144⟩ : DyadicInterval 40),(⟨762123381851,762123401180⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3520,-832⟩ : DyadicInterval 40),(⟨762123384032,762123404640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨237795819560,238281312052⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215275710720,215275710784⟩ : DyadicInterval 40),(⟨-267946429504,-267946429440⟩ : DyadicInterval 40),(⟨736204541186,736204560516⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215674802048,215674802112⟩ : DyadicInterval 40),(⟨-268566071232,-268566071168⟩ : DyadicInterval 40),(⟨736097744662,736097763991⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-52891269184,-52670718720⟩ : DyadicInterval 40),(⟨788458742976,788569037472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨215324604288,215699277696⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-268604091584,-268022312320⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e580_ok : ecellOkT e580 = true := by decide +kernel
theorem e580_pos {a z : ℝ} (ha1 : ((2769/12800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((443889/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e580 e580_ok ha1 ha2 hz1 hz2 hz

-- box ['2769/12800', '443889/2048000', '3999/4000', '1']  interval_lower 21710273/274877906944
noncomputable def e581 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1337366916628,0,true,215324604288,215324604352⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨861656338924,0,false,-268022312384,-268022312320⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1337822720033,0,true,215699277632,215699277696⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨861200535519,0,false,-268604091584,-268604091520⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1337307452805,0,true,215275715200,215275715264⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨861715802747,0,false,-267946436544,-267946436480⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099542470418,0,true,30842176,30842240⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099480785134,0,false,-30843136,-30843072⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626910,0,false,-896,-832⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1337337178859,0,true,215300155200,215300155264⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨861686076693,0,false,-267984366336,-267984366272⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1337822728586,0,true,215699284672,215699284736⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨861200526966,0,false,-268604102464,-268604102400⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1047859440264,0,false,-52904817792,-52904817728⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1048069704545,0,false,-52684211072,-52684211008⟩
    { al := (2769/12800), au := (443889/2048000), zl := (3999/4000), zu := 1,
      A := ⟨237855288852,238311092257⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215324604288,215324604352⟩ : DyadicInterval 40),(⟨-268022312384,-268022312320⟩ : DyadicInterval 40),(⟨736191471495,736191490825⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215699277632,215699277696⟩ : DyadicInterval 40),(⟨-268604091584,-268604091520⟩ : DyadicInterval 40),(⟨736091186461,736091205790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215275715200,215275715264⟩ : DyadicInterval 40),(⟨-267946436544,-267946436480⟩ : DyadicInterval 40),(⟨736204540019,736204559348⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215699277632,215699277696⟩ : DyadicInterval 40),(⟨-268604091584,-268604091520⟩ : DyadicInterval 40),(⟨736091186461,736091205790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,30842642⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨30842176,30842240⟩ : DyadicInterval 40),(⟨-30843136,-30843072⟩ : DyadicInterval 40),(⟨762123383166,762123402495⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-896,0⟩ : DyadicInterval 40),(⟨762123383616,762123403328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨237825551083,238311100810⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215300155200,215300155264⟩ : DyadicInterval 40),(⟨-267984366336,-267984366272⟩ : DyadicInterval 40),(⟨736198007466,736198026796⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215699284672,215699284736⟩ : DyadicInterval 40),(⟨-268604102464,-268604102400⟩ : DyadicInterval 40),(⟨736091184555,736091203884⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-52904817792,-52684211008⟩ : DyadicInterval 40),(⟨788465489120,788575811776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨215324604288,215699277696⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-268604091584,-268022312320⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e581_ok : ecellOkT e581 = true := by decide +kernel
theorem e581_pos {a z : ℝ} (ha1 : ((2769/12800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((443889/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e581 e581_ok ha1 ha2 hz1 hz2 hz

-- box ['443889/2048000', '222369/1024000', '1999/2000', '3999/4000']  interval_lower 99057985/1099511627776
noncomputable def e582 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1337822720032,0,true,215699277632,215699277696⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨861200535520,0,false,-268604091584,-268604091520⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1338278523438,0,true,216073823360,216073823424⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨860744732114,0,false,-269186178752,-269186178688⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1337703564485,0,true,215601343360,215601343424⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨861319691067,0,false,-268451973888,-268451973824⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1338218831715,0,true,216024780352,216024780416⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨860804423837,0,false,-269109931456,-269109931392⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099542469352,0,true,30841088,30841152⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099480786200,0,false,-30842048,-30841984⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099573438666,0,true,61809152,61809216⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099449816886,0,false,-61812672,-61812608⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624301,0,false,-3520,-3456⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626911,0,false,-896,-832⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1337763136780,0,true,215650307072,215650307136⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨861260118772,0,false,-268528023104,-268528023040⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1338248686263,0,true,216049309248,216049309312⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨860774569289,0,false,-269148065536,-269148065472⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1047674628825,0,false,-53098756224,-53098756160⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1047885269211,0,false,-52877715968,-52877715904⟩
    { al := (443889/2048000), au := (222369/1024000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨238311092256,238766895662⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215699277632,215699277696⟩ : DyadicInterval 40),(⟨-268604091584,-268604091520⟩ : DyadicInterval 40),(⟨736091186461,736091205790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216073823360,216073823424⟩ : DyadicInterval 40),(⟨-269186178752,-269186178688⟩ : DyadicInterval 40),(⟨735990703137,735990722467⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215601343360,215601343424⟩ : DyadicInterval 40),(⟨-268451973888,-268451973824⟩ : DyadicInterval 40),(⟨736117421968,736117441297⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216024780352,216024780416⟩ : DyadicInterval 40),(⟨-269109931456,-269109931392⟩ : DyadicInterval 40),(⟨736003873654,736003892983⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨30841576,61810890⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨30841088,30841152⟩ : DyadicInterval 40),(⟨-30842048,-30841984⟩ : DyadicInterval 40),(⟨762123383166,762123402495⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨61809152,61809216⟩ : DyadicInterval 40),(⟨-61812672,-61812608⟩ : DyadicInterval 40),(⟨762123381837,762123401166⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3520,-832⟩ : DyadicInterval 40),(⟨762123384032,762123404640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨238251509004,238737058487⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215650307072,215650307136⟩ : DyadicInterval 40),(⟨-268528023104,-268528023040⟩ : DyadicInterval 40),(⟨736104307118,736104326448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216049309248,216049309312⟩ : DyadicInterval 40),(⟨-269148065536,-269148065472⟩ : DyadicInterval 40),(⟨735997286914,735997306243⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-53098756224,-52877715904⟩ : DyadicInterval 40),(⟨788562241568,788672780992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨215699277632,216073823424⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-269186178752,-268604091520⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e582_ok : ecellOkT e582 = true := by decide +kernel
theorem e582_pos {a z : ℝ} (ha1 : ((443889/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((222369/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e582 e582_ok ha1 ha2 hz1 hz2 hz

-- box ['443889/2048000', '222369/1024000', '3999/4000', '1']  interval_lower 48846261/549755813888
noncomputable def e583 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1337822720032,0,true,215699277632,215699277696⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨861200535520,0,false,-268604091584,-268604091520⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1338278523438,0,true,216073823360,216073823424⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨860744732114,0,false,-269186178752,-269186178688⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1337763142258,0,true,215650311552,215650311616⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨861260113294,0,false,-268528030080,-268528030016⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099542533626,0,true,30905408,30905472⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099480721926,0,false,-30906304,-30906240⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626907,0,false,-896,-832⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1337792925280,0,true,215674790080,215674790144⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨861230330272,0,false,-268566052672,-268566052608⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1338278531996,0,true,216073830400,216073830464⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨860744723556,0,false,-269186189696,-269186189632⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1047661667202,0,false,-53112359296,-53112359232⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1047872358754,0,false,-52891262592,-52891262528⟩
    { al := (443889/2048000), au := (222369/1024000), zl := (3999/4000), zu := 1,
      A := ⟨238311092256,238766895662⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215699277632,215699277696⟩ : DyadicInterval 40),(⟨-268604091584,-268604091520⟩ : DyadicInterval 40),(⟨736091186461,736091205790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216073823360,216073823424⟩ : DyadicInterval 40),(⟨-269186178752,-269186178688⟩ : DyadicInterval 40),(⟨735990703137,735990722467⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215650311552,215650311616⟩ : DyadicInterval 40),(⟨-268528030080,-268528030016⟩ : DyadicInterval 40),(⟨736104305919,736104325248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216073823360,216073823424⟩ : DyadicInterval 40),(⟨-269186178752,-269186178688⟩ : DyadicInterval 40),(⟨735990703137,735990722467⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,30905850⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨30905408,30905472⟩ : DyadicInterval 40),(⟨-30906304,-30906240⟩ : DyadicInterval 40),(⟨762123383131,762123402460⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-896,0⟩ : DyadicInterval 40),(⟨762123383616,762123403328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨238281297504,238766904220⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215674790080,215674790144⟩ : DyadicInterval 40),(⟨-268566052672,-268566052608⟩ : DyadicInterval 40),(⟨736097747877,736097767207⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216073830400,216073830464⟩ : DyadicInterval 40),(⟨-269186189696,-269186189632⟩ : DyadicInterval 40),(⟨735990701248,735990720577⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-53112359296,-52891262528⟩ : DyadicInterval 40),(⟨788569014880,788679582528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨215699277632,216073823424⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-269186178752,-268604091520⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e583_ok : ecellOkT e583 = true := by decide +kernel
theorem e583_pos {a z : ℝ} (ha1 : ((443889/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((222369/1024000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e583 e583_ok ha1 ha2 hz1 hz2 hz

-- box ['222369/1024000', '445587/2048000', '1999/2000', '3999/4000']  interval_lower 110009295/1099511627776
noncomputable def e584 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1338278523437,0,true,216073823360,216073823424⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨860744732115,0,false,-269186178752,-269186178688⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1338734326842,0,true,216448241536,216448241600⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨860288928710,0,false,-269768574336,-269768574272⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1338159139989,0,true,215975735168,215975735232⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨860864115563,0,false,-269033689472,-269033689408⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1338674521168,0,true,216399121664,216399121728⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨860348734384,0,false,-269692140992,-269692140928⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099542532557,0,true,30904320,30904384⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099480722995,0,false,-30905216,-30905152⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099573565133,0,true,61935552,61935616⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099449690419,0,false,-61939136,-61939072⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624286,0,false,-3520,-3456⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626908,0,false,-896,-832⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1338218826228,0,true,216024775872,216024775936⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨860804429324,0,false,-269109924480,-269109924416⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1338704432689,0,true,216423689024,216423689088⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨860318822863,0,false,-269730368064,-269730368000⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1047476527394,0,false,-53306679040,-53306678976⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1047687595039,0,false,-53085148608,-53085148544⟩
    { al := (222369/1024000), au := (445587/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨238766895661,239222699066⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216073823360,216073823424⟩ : DyadicInterval 40),(⟨-269186178752,-269186178688⟩ : DyadicInterval 40),(⟨735990703137,735990722467⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216448241536,216448241600⟩ : DyadicInterval 40),(⟨-269768574336,-269768574272⟩ : DyadicInterval 40),(⟨735890021549,735890040879⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215975735168,215975735232⟩ : DyadicInterval 40),(⟨-269033689472,-269033689408⟩ : DyadicInterval 40),(⟨736017040773,736017060102⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216399121664,216399121728⟩ : DyadicInterval 40),(⟨-269692140992,-269692140928⟩ : DyadicInterval 40),(⟨735903243199,735903262528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨30904781,61937357⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨30904320,30904384⟩ : DyadicInterval 40),(⟨-30905216,-30905152⟩ : DyadicInterval 40),(⟨762123383131,762123402460⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨61935552,61935616⟩ : DyadicInterval 40),(⟨-61939136,-61939072⟩ : DyadicInterval 40),(⟨762123381854,762123401184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3520,-832⟩ : DyadicInterval 40),(⟨762123384032,762123404640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨238707198452,239192804913⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216024775872,216024775936⟩ : DyadicInterval 40),(⟨-269109924480,-269109924416⟩ : DyadicInterval 40),(⟨736003874860,736003894189⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216423689024,216423689088⟩ : DyadicInterval 40),(⟨-269730368064,-269730368000⟩ : DyadicInterval 40),(⟨735896630857,735896650187⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-53306679040,-53085148544⟩ : DyadicInterval 40),(⟨788665957888,788776742400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨216073823360,216448241600⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-269768574336,-269186178688⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e584_ok : ecellOkT e584 = true := by decide +kernel
theorem e584_pos {a z : ℝ} (ha1 : ((222369/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((445587/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e584 e584_ok ha1 ha2 hz1 hz2 hz

-- box ['222369/1024000', '445587/2048000', '3999/4000', '1']  interval_lower 108634493/1099511627776
noncomputable def e585 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1338278523437,0,true,216073823360,216073823424⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨860744732115,0,false,-269186178752,-269186178688⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1338734326842,0,true,216448241536,216448241600⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨860288928710,0,false,-269768574336,-269768574272⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1338218831713,0,true,216024780352,216024780416⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨860804423839,0,false,-269109931456,-269109931392⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099542596861,0,true,30968640,30968704⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099480658691,0,false,-30969536,-30969472⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626903,0,false,-896,-832⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1338248671704,0,true,216049297344,216049297408⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨860774583848,0,false,-269148046976,-269148046912⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1338734335393,0,true,216448248576,216448248640⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨860288920159,0,false,-269768585216,-269768585152⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1047463516238,0,false,-53320336640,-53320336576⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1047674635148,0,false,-53098749632,-53098749568⟩
    { al := (222369/1024000), au := (445587/2048000), zl := (3999/4000), zu := 1,
      A := ⟨238766895661,239222699066⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216073823360,216073823424⟩ : DyadicInterval 40),(⟨-269186178752,-269186178688⟩ : DyadicInterval 40),(⟨735990703137,735990722467⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216448241536,216448241600⟩ : DyadicInterval 40),(⟨-269768574336,-269768574272⟩ : DyadicInterval 40),(⟨735890021549,735890040879⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216024780352,216024780416⟩ : DyadicInterval 40),(⟨-269109931456,-269109931392⟩ : DyadicInterval 40),(⟨736003873654,736003892984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216448241536,216448241600⟩ : DyadicInterval 40),(⟨-269768574336,-269768574272⟩ : DyadicInterval 40),(⟨735890021549,735890040879⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,30969085⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨30968640,30968704⟩ : DyadicInterval 40),(⟨-30969536,-30969472⟩ : DyadicInterval 40),(⟨762123383127,762123402456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-896,0⟩ : DyadicInterval 40),(⟨762123383616,762123403328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨238737043928,239222707617⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216049297344,216049297408⟩ : DyadicInterval 40),(⟨-269148046976,-269148046912⟩ : DyadicInterval 40),(⟨735997290106,735997309435⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216448248576,216448248640⟩ : DyadicInterval 40),(⟨-269768585216,-269768585152⟩ : DyadicInterval 40),(⟨735890019629,735890038958⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-53320336640,-53098749568⟩ : DyadicInterval 40),(⟨788672758400,788783571200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨216073823360,216448241600⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-269768574336,-269186178688⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e585_ok : ecellOkT e585 = true := by decide +kernel
theorem e585_pos {a z : ℝ} (ha1 : ((222369/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((445587/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e585 e585_ok ha1 ha2 hz1 hz2 hz

-- box ['510639/512000', '408681/409600', '1999/2000', '3999/4000']  interval_lower 6000202229091941/1099511627776
noncomputable def e586 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2196100530307,0,true,760661049024,760661067712⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨2922725245,8,false,-6520219437760,-6520219283584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2196556333712,0,true,760889230336,760889249088⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨2466921840,8,false,-6706636499200,-6706636344512⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2195552235855,0,true,760386502720,760386521216⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨3471019697,8,false,-6331178284288,-6331178130112⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨2196282072537,0,true,760751937216,760751955904⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨2741183015,8,false,-6590727709504,-6590727555328⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1108191549778,0,true,8645840064,8645840128⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1090831705774,0,false,-8714364544,-8714364480⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1120256099572,0,true,20551206016,20551206080⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1078767155980,0,false,-20942661440,-20942661376⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099120242092,0,false,-391455360,-391455296⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443105494,0,false,-68524480,-68524416⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨2195828167198,0,true,760524677824,760524696384⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨3195088354,8,false,-6422254867968,-6422254713792⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨2196419752193,0,true,760820860800,760820879488⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨2603503359,8,false,-6647387303744,-6647387149504⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨5200841953,7,false,-5886566424000,-5886566288960⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨6380892050,7,false,-5661730170944,-5661730036032⟩
    { al := (510639/512000), au := (408681/409600), zl := (1999/2000), zu := (3999/4000),
      A := ⟨1096588902531,1097044705936⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760661049024,760661067712⟩ : DyadicInterval 40),(⟨-6520219437760,-6520219283584⟩ : DyadicInterval 40),(⟨11139345355,11139383488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760889230336,760889249088⟩ : DyadicInterval 40),(⟨-6706636499200,-6706636344512⟩ : DyadicInterval 40),(⟨9611400175,9611438345⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760386502720,760386521216⟩ : DyadicInterval 40),(⟨-6331178284288,-6331178130112⟩ : DyadicInterval 40),(⟨12930450519,12930488494⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760751937216,760751955904⟩ : DyadicInterval 40),(⟨-6590727709504,-6590727555328⟩ : DyadicInterval 40),(⟨10535382990,10535421113⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨8679922002,20744471796⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨8645840064,8645840128⟩ : DyadicInterval 40),(⟨-8714364544,-8714364480⟩ : DyadicInterval 40),(⟨762089122086,762089141415⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨20551206016,20551206080⟩ : DyadicInterval 40),(⟨-20942661440,-20942661376⟩ : DyadicInterval 40),(⟨761927679131,761927698460⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-391455360,-68524416⟩ : DyadicInterval 40),(⟨762157645824,762319130560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨1096316539422,1096908124417⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760524677824,760524696384⟩ : DyadicInterval 40),(⟨-6422254867968,-6422254713792⟩ : DyadicInterval 40),(⟨12034963785,12035001808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760820860800,760820879488⟩ : DyadicInterval 40),(⟨-6647387303744,-6647387149504⟩ : DyadicInterval 40),(⟨10073350201,10073388315⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5886566424000,-5661730036032⟩ : DyadicInterval 40),(⟨3592988401632,3705406614880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨760661049024,760889249088⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-6706636499200,-6520219283584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e586_ok : ecellOkT e586 = true := by decide +kernel
theorem e586_pos {a z : ℝ} (ha1 : ((510639/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((408681/409600 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e586 e586_ok ha1 ha2 hz1 hz2 hz

-- box ['1022127/1024000', '2045103/2048000', '999/1000', '3997/4000']  interval_lower 19811509040668985/1099511627776
noncomputable def e587 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2197012137115,0,true,761117364352,761117383168⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨2011118437,9,false,-6931244918400,-6931244744960⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2197467940520,0,true,761345451008,761345469888⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨1555315032,9,false,-7213833574592,-7213833401152⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2195914636605,0,true,760567974528,760567993152⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨3108618947,8,false,-6452421269312,-6452421115136⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨2196644473287,0,true,760933348736,760933367488⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨2378782265,8,false,-6746639428544,-6746639272896⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1131186735495,0,true,31227431552,31227431616⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1067836520057,0,false,-32140317824,-32140317760⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1152618881707,0,true,51864552000,51864552064⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1046404373845,0,false,-54432669888,-54432669824⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1096946506726,0,false,-2568117888,-2568117824⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1098599120420,0,false,-912886272,-912886208⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨2196472133025,0,true,760847081920,760847100672⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨2551122527,8,false,-6669734344256,-6669734189888⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨2197062397376,0,true,761142517184,761142536000⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨1960858176,9,false,-6959072217728,-6959072044288⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨3918219376,8,false,-6197929681536,-6197929527360⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨5096325857,7,false,-5908887243072,-5908887107968⟩
    { al := (1022127/1024000), au := (2045103/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨1097500509339,1097956312744⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761117364352,761117383168⟩ : DyadicInterval 40),(⟨-6931244918400,-6931244744960⟩ : DyadicInterval 40),(⟨8041056244,8041094466⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761345451008,761345469888⟩ : DyadicInterval 40),(⟨-7213833574592,-7213833401152⟩ : DyadicInterval 40),(⟨6418561478,6418599733⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760567974528,760567993152⟩ : DyadicInterval 40),(⟨-6452421269312,-6452421115136⟩ : DyadicInterval 40),(⟨11751933201,11751971282⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760933348736,760933367488⟩ : DyadicInterval 40),(⟨-6746639428544,-6746639272896⟩ : DyadicInterval 40),(⟨9311294793,9311332958⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨31675107719,53107253931⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31227431552,31227431616⟩ : DyadicInterval 40),(⟨-32140317824,-32140317760⟩ : DyadicInterval 40),(⟨761667066769,761667086098⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨51864552000,51864552064⟩ : DyadicInterval 40),(⟨-54432669888,-54432669824⟩ : DyadicInterval 40),(⟨760840323871,760840343200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2568117888,-912886208⟩ : DyadicInterval 40),(⟨762579826720,763407461824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨1096960505249,1097550769600⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760847081920,760847100672⟩ : DyadicInterval 40),(⟨-6669734344256,-6669734189888⟩ : DyadicInterval 40),(⟨9896620755,9896658930⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761142517184,761142536000⟩ : DyadicInterval 40),(⟨-6959072217728,-6959072044288⟩ : DyadicInterval 40),(⟨7864924827,7864963046⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6197929681536,-5908887107968⟩ : DyadicInterval 40),(⟨3716566937600,3861088243648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨761117364352,761345469888⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-7213833574592,-6931244744960⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e587_ok : ecellOkT e587 = true := by decide +kernel
theorem e587_pos {a z : ℝ} (ha1 : ((1022127/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((2045103/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e587 e587_ok ha1 ha2 hz1 hz2 hz

-- box ['1022127/1024000', '2045103/2048000', '3997/4000', '1999/2000']  interval_lower 355454001451919/1099511627776
noncomputable def e588 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2197012137115,0,true,761117364352,761117383168⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨2011118437,9,false,-6931244918400,-6931244744960⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2197467940520,0,true,761345451008,761345469888⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨1555315032,9,false,-7213833574592,-7213833401152⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2196189011732,0,true,760705347712,760705366400⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨2834243820,8,false,-6554019868480,-6554019714304⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨2196918962365,0,true,761070733312,761070752128⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨2104293187,9,false,-6881449544192,-6881449370752⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1121648367300,0,true,21916843840,21916843904⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1077374888252,0,false,-22362618688,-22362618624⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1141914870324,0,true,41606023104,41606023168⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1057108385228,0,false,-43242543744,-43242543680⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1097876324489,0,false,-1636520640,-1636520576⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099065943325,0,false,-445774848,-445774784⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨2196605710850,0,true,760913946368,760913965120⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨2417544702,8,false,-6728867212544,-6728867057472⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨2197196376018,0,true,761209564288,761209583104⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨1826879534,9,false,-7036887826176,-7036887652736⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨3650723639,8,false,-6275678242880,-6275678088704⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨4829773842,7,false,-5967953246976,-5967953111104⟩
    { al := (1022127/1024000), au := (2045103/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨1097500509339,1097956312744⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761117364352,761117383168⟩ : DyadicInterval 40),(⟨-6931244918400,-6931244744960⟩ : DyadicInterval 40),(⟨8041056244,8041094466⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761345451008,761345469888⟩ : DyadicInterval 40),(⟨-7213833574592,-7213833401152⟩ : DyadicInterval 40),(⟨6418561478,6418599733⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760705347712,760705366400⟩ : DyadicInterval 40),(⟨-6554019868480,-6554019714304⟩ : DyadicInterval 40),(⟨10845709397,10845747526⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761070733312,761070752128⟩ : DyadicInterval 40),(⟨-6881449544192,-6881449370752⟩ : DyadicInterval 40),(⟨8365925235,8365963465⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22136739524,42403242548⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21916843840,21916843904⟩ : DyadicInterval 40),(⟨-22362618688,-22362618624⟩ : DyadicInterval 40),(⟨761900526290,761900545620⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨41606023104,41606023168⟩ : DyadicInterval 40),(⟨-43242543744,-43242543680⟩ : DyadicInterval 40),(⟨761305529132,761305548462⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1636520640,-445774784⟩ : DyadicInterval 40),(⟨762346271008,762941663200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨1097094083074,1097684748242⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760913946368,760913965120⟩ : DyadicInterval 40),(⟨-6728867212544,-6728867057472⟩ : DyadicInterval 40),(⟨9443474404,9443512571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761209564288,761209583104⟩ : DyadicInterval 40),(⟨-7036887826176,-7036887652736⟩ : DyadicInterval 40),(⟨7392215056,7392253267⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6275678242880,-5967953111104⟩ : DyadicInterval 40),(⟨3746099939168,3899962524320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨761117364352,761345469888⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-7213833574592,-6931244744960⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e588_ok : ecellOkT e588 = true := by decide +kernel
theorem e588_pos {a z : ℝ} (ha1 : ((1022127/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((2045103/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e588 e588_ok ha1 ha2 hz1 hz2 hz

-- box ['2045103/2048000', '999/1000', '999/1000', '3997/4000']  interval_lower 1955108094731701/549755813888
noncomputable def e589 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2197467940519,0,true,761345451008,761345469888⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨1555315033,9,false,-7213833573888,-7213833400448⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2197923743925,0,true,761573490368,761573509376⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627,9,false,-7595157425088,-7595157240640⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2196369984206,0,true,760795947008,760795965696⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨2653271346,8,false,-6626567649664,-6626567495424⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨2197099934839,0,true,761161302528,761161321344⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1923320713,9,false,-6980324669376,-6980324495936⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1137151189389,0,true,37009640128,37009640192⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1061872066163,0,false,-38298910208,-38298910144⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1166510160278,0,true,65036570176,65036570240⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1032513095274,0,false,-69126711296,-69126711232⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1095429084905,0,false,-4090141056,-4090140992⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1098223113346,0,false,-1289270080,-1289270016⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨2196929354582,0,true,761075934400,761075953216⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨2093900970,9,false,-6886893021248,-6886892847808⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨2197519649246,0,true,761371323392,761371342272⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨1503606306,9,false,-7251009922432,-7251009748992⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨3005156397,8,false,-6489638579968,-6489638425792⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨4183814333,8,false,-6125817067392,-6125816913216⟩
    { al := (2045103/2048000), au := (999/1000), zl := (999/1000), zu := (3997/4000),
      A := ⟨1097956312743,1098412116149⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761345451008,761345469888⟩ : DyadicInterval 40),(⟨-7213833573888,-7213833400448⟩ : DyadicInterval 40),(⟨6418561481,6418599736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761573490368,761573509376⟩ : DyadicInterval 40),(⟨-7595157425088,-7595157240640⟩ : DyadicInterval 40),(⟨4728239611,4728277967⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760795947008,760795965696⟩ : DyadicInterval 40),(⟨-6626567649664,-6626567495424⟩ : DyadicInterval 40),(⟨10240775131,10240813248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761161302528,761161321344⟩ : DyadicInterval 40),(⟨-6980324669376,-6980324495936⟩ : DyadicInterval 40),(⟨7732959298,7732997514⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨37639561613,66998532502⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨37009640128,37009640192⟩ : DyadicInterval 40),(⟨-38298910208,-38298910144⟩ : DyadicInterval 40),(⟨761479000472,761479019802⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65036570176,65036570240⟩ : DyadicInterval 40),(⟨-69126711296,-69126711232⟩ : DyadicInterval 40),(⟨760080847056,760080866385⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4090141056,-1289270016⟩ : DyadicInterval 40),(⟨762768018624,764168473408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨1097417726806,1098008021470⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761075934400,761075953216⟩ : DyadicInterval 40),(⟨-6886893021248,-6886892847808⟩ : DyadicInterval 40),(⟨8329795081,8329833310⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761371323392,761371342272⟩ : DyadicInterval 40),(⟨-7251009922432,-7251009748992⟩ : DyadicInterval 40),(⟨6230594926,6230633177⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6489638579968,-6125816913216⟩ : DyadicInterval 40),(⟨3825031840224,4006942692864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨761345451008,761573509376⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-7595157425088,-7213833400448⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e589_ok : ecellOkT e589 = true := by decide +kernel
theorem e589_pos {a z : ℝ} (ha1 : ((2045103/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e589 e589_ok ha1 ha2 hz1 hz2 hz

-- box ['6993/40960', '700149/4096000', '999/1000', '3997/4000']  interval_lower 160643/137438953472
noncomputable def e590 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1287228542156,0,true,173310942272,173310942336⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨911794713396,0,false,-205835740800,-205835740736⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1287456443859,0,true,173505591808,173505591872⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨911566811693,0,false,-206110596416,-206110596352⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1287040825241,0,true,173150588480,173150588544⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨911982430311,0,false,-205609400704,-205609400640⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1287315485248,0,true,173385203968,173385204032⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨911707770304,0,false,-205940588416,-205940588352⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099583539264,0,true,71909120,71909184⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099439716288,0,false,-71913856,-71913792⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099607632348,0,true,96000320,96000384⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099415623204,0,false,-96008768,-96008704⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619393,0,false,-8384,-8320⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623073,0,false,-4736,-4672⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1287134679808,0,true,173230764992,173230765056⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨911888575744,0,false,-205722560256,-205722560192⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1287385973601,0,true,173445407232,173445407296⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨911637281951,0,false,-206025600064,-206025600000⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067409402635,0,false,-32580192768,-32580192704⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067495222707,0,false,-32491795200,-32491795136⟩
    { al := (6993/40960), au := (700149/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨187716914380,187944816083⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173310942272,173310942336⟩ : DyadicInterval 40),(⟨-205835740800,-205835740736⟩ : DyadicInterval 40),(⟨746020392743,746020412073⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173505591808,173505591872⟩ : DyadicInterval 40),(⟨-206110596416,-206110596352⟩ : DyadicInterval 40),(⟨745981074506,745981093836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173150588480,173150588544⟩ : DyadicInterval 40),(⟨-205609400704,-205609400640⟩ : DyadicInterval 40),(⟨746052741619,746052760949⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173385203968,173385204032⟩ : DyadicInterval 40),(⟨-205940588416,-205940588352⟩ : DyadicInterval 40),(⟨746005398800,746005418129⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨71911488,96004572⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨71909120,71909184⟩ : DyadicInterval 40),(⟨-71913856,-71913792⟩ : DyadicInterval 40),(⟨762123381216,762123400545⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨96000320,96000384⟩ : DyadicInterval 40),(⟨-96008768,-96008704⟩ : DyadicInterval 40),(⟨762123379392,762123398722⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8384,-4672⟩ : DyadicInterval 40),(⟨762123385952,762123407072⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨187623052032,187874345825⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173230764992,173230765056⟩ : DyadicInterval 40),(⟨-205722560256,-205722560192⟩ : DyadicInterval 40),(⟨746036571977,746036591306⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173445407232,173445407296⟩ : DyadicInterval 40),(⟨-206025600064,-206025600000⟩ : DyadicInterval 40),(⟨745993237446,745993256775⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32580192768,-32491795136⟩ : DyadicInterval 40),(⟨778369281184,778413499264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨173310942272,173505591872⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-206110596416,-205835740736⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e590_ok : ecellOkT e590 = true := by decide +kernel
theorem e590_pos {a z : ℝ} (ha1 : ((6993/40960 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((700149/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e590 e590_ok ha1 ha2 hz1 hz2 hz

-- box ['700149/4096000', '350499/2048000', '999/1000', '3997/4000']  interval_lower 1896707/549755813888
noncomputable def e591 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1287456443858,0,true,173505591808,173505591872⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨911566811694,0,false,-206110596416,-206110596352⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1287684345562,0,true,173700206848,173700206912⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨911338909990,0,false,-206385520768,-206385520704⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1287268499041,0,true,173345071744,173345071808⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨911754756511,0,false,-205883924928,-205883924864⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1287543216024,0,true,173579694336,173579694400⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨911480039528,0,false,-206215264064,-206215264000⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099583630361,0,true,72000192,72000256⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099439625191,0,false,-72004992,-72004928⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099607753831,0,true,96121792,96121856⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099415501721,0,false,-96130304,-96130240⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619372,0,false,-8448,-8384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623061,0,false,-4736,-4672⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1287362467562,0,true,173425331392,173425331456⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨911660787990,0,false,-205997250176,-205997250112⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1287613789839,0,true,173639960000,173639960064⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨911409465713,0,false,-206300400000,-206300399936⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067331501182,0,false,-32660440000,-32660439936⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067417435121,0,false,-32571918720,-32571918656⟩
    { al := (700149/4096000), au := (350499/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨187944816082,188172717786⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173505591808,173505591872⟩ : DyadicInterval 40),(⟨-206110596416,-206110596352⟩ : DyadicInterval 40),(⟨745981074506,745981093836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173700206848,173700206912⟩ : DyadicInterval 40),(⟨-206385520768,-206385520704⟩ : DyadicInterval 40),(⟨745941707639,745941726969⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173345071744,173345071808⟩ : DyadicInterval 40),(⟨-205883924928,-205883924864⟩ : DyadicInterval 40),(⟨746013502772,746013522102⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173579694336,173579694400⟩ : DyadicInterval 40),(⟨-206215264064,-206215264000⟩ : DyadicInterval 40),(⟨745966091557,745966110887⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨72002585,96126055⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨72000192,72000256⟩ : DyadicInterval 40),(⟨-72004992,-72004928⟩ : DyadicInterval 40),(⟨762123381236,762123400565⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨96121792,96121856⟩ : DyadicInterval 40),(⟨-96130304,-96130240⟩ : DyadicInterval 40),(⟨762123379403,762123398733⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8448,-4672⟩ : DyadicInterval 40),(⟨762123385952,762123407104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨187850839786,188102162063⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173425331392,173425331456⟩ : DyadicInterval 40),(⟨-205997250176,-205997250112⟩ : DyadicInterval 40),(⟨745997293456,745997312786⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173639960000,173639960064⟩ : DyadicInterval 40),(⟨-206300400000,-206300399936⟩ : DyadicInterval 40),(⟨745953900335,745953919665⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32660440000,-32571918656⟩ : DyadicInterval 40),(⟨778409342944,778453622880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨173505591808,173700206912⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-206385520768,-206110596352⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e591_ok : ecellOkT e591 = true := by decide +kernel
theorem e591_pos {a z : ℝ} (ha1 : ((700149/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((350499/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e591 e591_ok ha1 ha2 hz1 hz2 hz

-- box ['6993/40960', '700149/4096000', '3997/4000', '1999/2000']  interval_lower 784889/1099511627776
noncomputable def e592 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1287228542156,0,true,173310942272,173310942336⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨911794713396,0,false,-205835740800,-205835740736⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1287456443859,0,true,173505591808,173505591872⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨911566811693,0,false,-206110596416,-206110596352⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1287087754470,0,true,173190679168,173190679232⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨911935501082,0,false,-205665981376,-205665981312⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1287362471452,0,true,173425334720,173425334784⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨911660784100,0,false,-205997254848,-205997254784⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099559568942,0,true,47940096,47940160⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099463686610,0,false,-47942272,-47942208⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099583631661,0,true,72001472,72001536⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099439623891,0,false,-72006272,-72006208⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623060,0,false,-4736,-4672⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625686,0,false,-2112,-2048⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1287158143990,0,true,173250808704,173250808768⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨911865111562,0,false,-205750852608,-205750852544⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1287409466390,0,true,173465471424,173465471488⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨911613789162,0,false,-206053934720,-206053934656⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067401373674,0,false,-32588463232,-32588463168⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067487214248,0,false,-32500043904,-32500043840⟩
    { al := (6993/40960), au := (700149/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨187716914380,187944816083⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173310942272,173310942336⟩ : DyadicInterval 40),(⟨-205835740800,-205835740736⟩ : DyadicInterval 40),(⟨746020392743,746020412073⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173505591808,173505591872⟩ : DyadicInterval 40),(⟨-206110596416,-206110596352⟩ : DyadicInterval 40),(⟨745981074506,745981093836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173190679168,173190679232⟩ : DyadicInterval 40),(⟨-205665981376,-205665981312⟩ : DyadicInterval 40),(⟨746044657474,746044676804⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173425334720,173425334784⟩ : DyadicInterval 40),(⟨-205997254848,-205997254784⟩ : DyadicInterval 40),(⟨745997292774,745997312103⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨47941166,72003885⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨47940096,47940160⟩ : DyadicInterval 40),(⟨-47942272,-47942208⟩ : DyadicInterval 40),(⟨762123382549,762123401878⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨72001472,72001536⟩ : DyadicInterval 40),(⟨-72006272,-72006208⟩ : DyadicInterval 40),(⟨762123381236,762123400565⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4736,-2048⟩ : DyadicInterval 40),(⟨762123384640,762123405248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨187646516214,187897838614⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173250808704,173250808768⟩ : DyadicInterval 40),(⟨-205750852608,-205750852544⟩ : DyadicInterval 40),(⟨746032528159,746032547489⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173465471424,173465471488⟩ : DyadicInterval 40),(⟨-206053934720,-206053934656⟩ : DyadicInterval 40),(⟨745989183192,745989202521⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32588463232,-32500043840⟩ : DyadicInterval 40),(⟨778373405536,778417634496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨173310942272,173505591872⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-206110596416,-205835740736⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e592_ok : ecellOkT e592 = true := by decide +kernel
theorem e592_pos {a z : ℝ} (ha1 : ((6993/40960 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((700149/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e592 e592_ok ha1 ha2 hz1 hz2 hz

-- box ['700149/4096000', '350499/2048000', '3997/4000', '1999/2000']  interval_lower 3290941/1099511627776
noncomputable def e593 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1287456443858,0,true,173505591808,173505591872⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨911566811694,0,false,-206110596416,-206110596352⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1287684345562,0,true,173700206848,173700206912⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨911338909990,0,false,-206385520768,-206385520704⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1287315485245,0,true,173385203968,173385204032⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨911707770307,0,false,-205940588416,-205940588352⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1287590259204,0,true,173619866624,173619866688⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨911432996348,0,false,-206272013376,-206272013312⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099559629674,0,true,48000832,48000896⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099463625878,0,false,-48003008,-48002944⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099583722775,0,true,72092608,72092672⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099439532777,0,false,-72097408,-72097344⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623048,0,false,-4736,-4672⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625681,0,false,-2112,-2048⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1287385960227,0,true,173445395840,173445395904⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨911637295325,0,false,-206025583936,-206025583872⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1287637311115,0,true,173660044928,173660044992⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨911385944437,0,false,-206328776128,-206328776064⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067323452737,0,false,-32668731136,-32668731072⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067409407207,0,false,-32580188032,-32580187968⟩
    { al := (700149/4096000), au := (350499/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨187944816082,188172717786⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173505591808,173505591872⟩ : DyadicInterval 40),(⟨-206110596416,-206110596352⟩ : DyadicInterval 40),(⟨745981074506,745981093836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173700206848,173700206912⟩ : DyadicInterval 40),(⟨-206385520768,-206385520704⟩ : DyadicInterval 40),(⟨745941707639,745941726969⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173385203968,173385204032⟩ : DyadicInterval 40),(⟨-205940588416,-205940588352⟩ : DyadicInterval 40),(⟨746005398800,746005418130⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173619866624,173619866688⟩ : DyadicInterval 40),(⟨-206272013376,-206272013312⟩ : DyadicInterval 40),(⟨745957965670,745957985000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨48001898,72094999⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨48000832,48000896⟩ : DyadicInterval 40),(⟨-48003008,-48002944⟩ : DyadicInterval 40),(⟨762123382544,762123401873⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨72092608,72092672⟩ : DyadicInterval 40),(⟨-72097408,-72097344⟩ : DyadicInterval 40),(⟨762123381224,762123400553⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4736,-2048⟩ : DyadicInterval 40),(⟨762123384640,762123405248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨187874332451,188125683339⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173445395840,173445395904⟩ : DyadicInterval 40),(⟨-206025583936,-206025583872⟩ : DyadicInterval 40),(⟨745993239737,745993259066⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173660044928,173660044992⟩ : DyadicInterval 40),(⟨-206328776128,-206328776064⟩ : DyadicInterval 40),(⟨745949836176,745949855506⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32668731136,-32580187968⟩ : DyadicInterval 40),(⟨778413477600,778457768448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨173505591808,173700206912⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-206385520768,-206110596352⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e593_ok : ecellOkT e593 = true := by decide +kernel
theorem e593_pos {a z : ℝ} (ha1 : ((700149/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((350499/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e593 e593_ok ha1 ha2 hz1 hz2 hz

-- box ['350499/2048000', '701847/4096000', '999/1000', '3997/4000']  interval_lower 6314573/1099511627776
noncomputable def e594 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1287684345561,0,true,173700206848,173700206912⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨911338909991,0,false,-206385520768,-206385520704⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1287912247264,0,true,173894787456,173894787520⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨911111008288,0,false,-206660513856,-206660513792⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1287496172843,0,true,173539520576,173539520640⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨911527082709,0,false,-206158517696,-206158517632⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1287770946800,0,true,173774150336,173774150400⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨911252308752,0,false,-206490008320,-206490008256⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099583721473,0,true,72091328,72091392⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099439534079,0,false,-72096064,-72096000⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099607875334,0,true,96243328,96243392⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099415380218,0,false,-96251776,-96251712⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619350,0,false,-8448,-8384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623049,0,false,-4736,-4672⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1287590255311,0,true,173619863296,173619863360⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨911433000241,0,false,-206272008640,-206272008576⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1287841606083,0,true,173834478272,173834478336⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨911181649469,0,false,-206575268736,-206575268672⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067253505321,0,false,-32740790400,-32740790336⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067339553156,0,false,-32652145344,-32652145280⟩
    { al := (350499/2048000), au := (701847/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨188172717785,188400619488⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173700206848,173700206912⟩ : DyadicInterval 40),(⟨-206385520768,-206385520704⟩ : DyadicInterval 40),(⟨745941707639,745941726969⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173894787456,173894787520⟩ : DyadicInterval 40),(⟨-206660513856,-206660513792⟩ : DyadicInterval 40),(⟨745902292093,745902311422⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173539520576,173539520640⟩ : DyadicInterval 40),(⟨-206158517696,-206158517632⟩ : DyadicInterval 40),(⟨745974215379,745974234709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173774150336,173774150400⟩ : DyadicInterval 40),(⟨-206490008320,-206490008256⟩ : DyadicInterval 40),(⟨745926735698,745926755027⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨72093697,96247558⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨72091328,72091392⟩ : DyadicInterval 40),(⟨-72096064,-72096000⟩ : DyadicInterval 40),(⟨762123381192,762123400522⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨96243328,96243392⟩ : DyadicInterval 40),(⟨-96251776,-96251712⟩ : DyadicInterval 40),(⟨762123379350,762123398680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8448,-4672⟩ : DyadicInterval 40),(⟨762123385952,762123407104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨188078627535,188329978307⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173619863296,173619863360⟩ : DyadicInterval 40),(⟨-206272008640,-206272008576⟩ : DyadicInterval 40),(⟨745957966329,745957985658⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173834478272,173834478336⟩ : DyadicInterval 40),(⟨-206575268736,-206575268672⟩ : DyadicInterval 40),(⟨745914514685,745914534014⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32740790400,-32652145280⟩ : DyadicInterval 40),(⟨778449456256,778493798080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨173700206848,173894787520⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-206660513856,-206385520704⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e594_ok : ecellOkT e594 = true := by decide +kernel
theorem e594_pos {a z : ℝ} (ha1 : ((350499/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((701847/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e594 e594_ok ha1 ha2 hz1 hz2 hz

-- box ['701847/4096000', '87837/512000', '999/1000', '3997/4000']  interval_lower 8849011/1099511627776
noncomputable def e595 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1287912247263,0,true,173894787456,173894787520⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨911111008289,0,false,-206660513856,-206660513792⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1288140148966,0,true,174089333632,174089333696⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨910883106586,0,false,-206935575744,-206935575680⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1287723846643,0,true,173733935040,173733935104⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨911299408909,0,false,-206433179008,-206433178944⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1287998677576,0,true,173968571968,173968572032⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨911024577976,0,false,-206764821248,-206764821184⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099583812599,0,true,72182400,72182464⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099439442953,0,false,-72187200,-72187136⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099607996856,0,true,96364800,96364864⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099415258696,0,false,-96373312,-96373248⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619329,0,false,-8448,-8384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623037,0,false,-4800,-4736⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1287818043064,0,true,173814360832,173814360896⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨911205212488,0,false,-206546835904,-206546835840⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1288069422326,0,true,174028962176,174028962240⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨910953833226,0,false,-206850206144,-206850206080⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067175415054,0,false,-32821243904,-32821243840⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067261576806,0,false,-32732475008,-32732474944⟩
    { al := (701847/4096000), au := (87837/512000), zl := (999/1000), zu := (3997/4000),
      A := ⟨188400619487,188628521190⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173894787456,173894787520⟩ : DyadicInterval 40),(⟨-206660513856,-206660513792⟩ : DyadicInterval 40),(⟨745902292093,745902311422⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174089333632,174089333696⟩ : DyadicInterval 40),(⟨-206935575744,-206935575680⟩ : DyadicInterval 40),(⟨745862827884,745862847213⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173733935040,173733935104⟩ : DyadicInterval 40),(⟨-206433179008,-206433178944⟩ : DyadicInterval 40),(⟨745934879394,745934898724⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173968571968,173968572032⟩ : DyadicInterval 40),(⟨-206764821248,-206764821184⟩ : DyadicInterval 40),(⟨745887331237,745887350567⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨72184823,96369080⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨72182400,72182464⟩ : DyadicInterval 40),(⟨-72187200,-72187136⟩ : DyadicInterval 40),(⟨762123381212,762123400542⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨96364800,96364864⟩ : DyadicInterval 40),(⟨-96373312,-96373248⟩ : DyadicInterval 40),(⟨762123379361,762123398690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8448,-4736⟩ : DyadicInterval 40),(⟨762123385984,762123407104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨188306415288,188557794550⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173814360832,173814360896⟩ : DyadicInterval 40),(⟨-206546835904,-206546835840⟩ : DyadicInterval 40),(⟨745918590612,745918609941⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174028962176,174028962240⟩ : DyadicInterval 40),(⟨-206850206144,-206850206080⟩ : DyadicInterval 40),(⟨745875080357,745875099687⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32821243904,-32732474944⟩ : DyadicInterval 40),(⟨778489621088,778534024832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨173894787456,174089333696⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-206935575744,-206660513792⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e595_ok : ecellOkT e595 = true := by decide +kernel
theorem e595_pos {a z : ℝ} (ha1 : ((701847/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((87837/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e595 e595_ok ha1 ha2 hz1 hz2 hz

-- box ['350499/2048000', '701847/4096000', '3997/4000', '1999/2000']  interval_lower 5810039/1099511627776
noncomputable def e596 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1287684345561,0,true,173700206848,173700206912⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨911338909991,0,false,-206385520768,-206385520704⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1287912247264,0,true,173894787456,173894787520⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨911111008288,0,false,-206660513856,-206660513792⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1287543216022,0,true,173579694336,173579694400⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨911480039530,0,false,-206215264064,-206215264000⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1287818046955,0,true,173814364160,173814364224⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨911205208597,0,false,-206546840576,-206546840512⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099559690417,0,true,48061568,48061632⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099463565135,0,false,-48063744,-48063680⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099583813903,0,true,72183744,72183808⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099439441649,0,false,-72188544,-72188480⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623036,0,false,-4800,-4736⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625676,0,false,-2112,-2048⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1287613776461,0,true,173639948544,173639948608⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨911409479091,0,false,-206300383872,-206300383808⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1287865155844,0,true,173854584000,173854584064⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨911158099708,0,false,-206603686272,-206603686208⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067245437369,0,false,-32749102272,-32749102208⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067331505760,0,false,-32660435328,-32660435264⟩
    { al := (350499/2048000), au := (701847/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨188172717785,188400619488⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173700206848,173700206912⟩ : DyadicInterval 40),(⟨-206385520768,-206385520704⟩ : DyadicInterval 40),(⟨745941707639,745941726969⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173894787456,173894787520⟩ : DyadicInterval 40),(⟨-206660513856,-206660513792⟩ : DyadicInterval 40),(⟨745902292093,745902311422⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173579694336,173579694400⟩ : DyadicInterval 40),(⟨-206215264064,-206215264000⟩ : DyadicInterval 40),(⟨745966091557,745966110887⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173814364160,173814364224⟩ : DyadicInterval 40),(⟨-206546840576,-206546840512⟩ : DyadicInterval 40),(⟨745918589926,745918609255⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨48062641,72186127⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨48061568,48061632⟩ : DyadicInterval 40),(⟨-48063744,-48063680⟩ : DyadicInterval 40),(⟨762123382539,762123401868⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨72183744,72183808⟩ : DyadicInterval 40),(⟨-72188544,-72188480⟩ : DyadicInterval 40),(⟨762123381212,762123400541⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4800,-2048⟩ : DyadicInterval 40),(⟨762123384640,762123405280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨188102148685,188353528068⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173639948544,173639948608⟩ : DyadicInterval 40),(⟨-206300383872,-206300383808⟩ : DyadicInterval 40),(⟨745953902670,745953921999⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173854584000,173854584064⟩ : DyadicInterval 40),(⟨-206603686272,-206603686208⟩ : DyadicInterval 40),(⟨745910440532,745910459861⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32749102272,-32660435264⟩ : DyadicInterval 40),(⟨778453601248,778497954016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨173700206848,173894787520⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-206660513856,-206385520704⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e596_ok : ecellOkT e596 = true := by decide +kernel
theorem e596_pos {a z : ℝ} (ha1 : ((350499/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((701847/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e596 e596_ok ha1 ha2 hz1 hz2 hz

-- box ['701847/4096000', '87837/512000', '3997/4000', '1999/2000']  interval_lower 2085589/274877906944
noncomputable def e597 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1287912247263,0,true,173894787456,173894787520⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨911111008289,0,false,-206660513856,-206660513792⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1288140148966,0,true,174089333632,174089333696⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨910883106586,0,false,-206935575744,-206935575680⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1287770946798,0,true,173774150336,173774150400⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨911252308754,0,false,-206490008320,-206490008256⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1288045834706,0,true,174008827328,174008827392⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨910977420846,0,false,-206821736512,-206821736448⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099559751168,0,true,48122304,48122368⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099463504384,0,false,-48124480,-48124416⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099583905046,0,true,72274880,72274944⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099439350506,0,false,-72279680,-72279616⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623024,0,false,-4800,-4736⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625670,0,false,-2112,-2048⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1287841592699,0,true,173834466880,173834466944⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨911181662853,0,false,-206575252544,-206575252480⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1288093000573,0,true,174049088640,174049088704⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨910930254979,0,false,-206878665216,-206878665152⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067167327572,0,false,-32829576512,-32829576448⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067253509907,0,false,-32740785664,-32740785600⟩
    { al := (701847/4096000), au := (87837/512000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨188400619487,188628521190⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173894787456,173894787520⟩ : DyadicInterval 40),(⟨-206660513856,-206660513792⟩ : DyadicInterval 40),(⟨745902292093,745902311422⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174089333632,174089333696⟩ : DyadicInterval 40),(⟨-206935575744,-206935575680⟩ : DyadicInterval 40),(⟨745862827884,745862847213⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173774150336,173774150400⟩ : DyadicInterval 40),(⟨-206490008320,-206490008256⟩ : DyadicInterval 40),(⟨745926735698,745926755028⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174008827328,174008827392⟩ : DyadicInterval 40),(⟨-206821736512,-206821736448⟩ : DyadicInterval 40),(⟨745879165556,745879184886⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨48123392,72277270⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨48122304,48122368⟩ : DyadicInterval 40),(⟨-48124480,-48124416⟩ : DyadicInterval 40),(⟨762123382533,762123401862⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨72274880,72274944⟩ : DyadicInterval 40),(⟨-72279680,-72279616⟩ : DyadicInterval 40),(⟨762123381200,762123400529⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4800,-2048⟩ : DyadicInterval 40),(⟨762123384640,762123405280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨188329964923,188581372797⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173834466880,173834466944⟩ : DyadicInterval 40),(⟨-206575252544,-206575252480⟩ : DyadicInterval 40),(⟨745914516962,745914536292⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨174049088640,174049088704⟩ : DyadicInterval 40),(⟨-206878665216,-206878665152⟩ : DyadicInterval 40),(⟨745870996275,745871015605⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32829576512,-32740785600⟩ : DyadicInterval 40),(⟨778493776416,778538191136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨173894787456,174089333696⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-206935575744,-206660513792⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e597_ok : ecellOkT e597 = true := by decide +kernel
theorem e597_pos {a z : ℝ} (ha1 : ((701847/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((87837/512000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e597 e597_ok ha1 ha2 hz1 hz2 hz

-- box ['6993/40960', '700149/4096000', '1999/2000', '3999/4000']  interval_lower 283871/1099511627776
noncomputable def e598 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1287228542156,0,true,173310942272,173310942336⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨911794713396,0,false,-205835740800,-205835740736⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1287456443859,0,true,173505591808,173505591872⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨911566811693,0,false,-206110596416,-206110596352⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1287134683698,0,true,173230768320,173230768384⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨911888571854,0,false,-205722564928,-205722564864⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1287409457656,0,true,173465464000,173465464064⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨911613797896,0,false,-206053924160,-206053924096⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535598361,0,true,23970304,23970368⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487657191,0,false,-23970880,-23970816⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099559630713,0,true,48001856,48001920⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099463624839,0,false,-48004032,-48003968⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625680,0,false,-2112,-2048⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627254,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1287181608291,0,true,173270852096,173270852160⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨911841647261,0,false,-205779145856,-205779145792⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1287432959306,0,true,173485535360,173485535424⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨911590296246,0,false,-206082270272,-206082270208⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067393343665,0,false,-32596734848,-32596734784⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067479204747,0,false,-32508293696,-32508293632⟩
    { al := (6993/40960), au := (700149/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨187716914380,187944816083⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173310942272,173310942336⟩ : DyadicInterval 40),(⟨-205835740800,-205835740736⟩ : DyadicInterval 40),(⟨746020392743,746020412073⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173505591808,173505591872⟩ : DyadicInterval 40),(⟨-206110596416,-206110596352⟩ : DyadicInterval 40),(⟨745981074506,745981093836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173230768320,173230768384⟩ : DyadicInterval 40),(⟨-205722564928,-205722564864⟩ : DyadicInterval 40),(⟨746036571296,746036590625⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173465464000,173465464064⟩ : DyadicInterval 40),(⟨-206053924160,-206053924096⟩ : DyadicInterval 40),(⟨745989184667,745989203997⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23970585,48002937⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23970304,23970368⟩ : DyadicInterval 40),(⟨-23970880,-23970816⟩ : DyadicInterval 40),(⟨762123383317,762123402646⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨48001856,48001920⟩ : DyadicInterval 40),(⟨-48004032,-48003968⟩ : DyadicInterval 40),(⟨762123382544,762123401873⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2112,-512⟩ : DyadicInterval 40),(⟨762123383872,762123403936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨187669980515,187921331530⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173270852096,173270852160⟩ : DyadicInterval 40),(⟨-205779145856,-205779145792⟩ : DyadicInterval 40),(⟨746028483849,746028503178⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173485535360,173485535424⟩ : DyadicInterval 40),(⟨-206082270272,-206082270208⟩ : DyadicInterval 40),(⟨745985128402,745985147731⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32596734848,-32508293632⟩ : DyadicInterval 40),(⟨778377530432,778421770304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨173310942272,173505591872⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-206110596416,-205835740736⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e598_ok : ecellOkT e598 = true := by decide +kernel
theorem e598_pos {a z : ℝ} (ha1 : ((6993/40960 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((700149/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e598 e598_ok ha1 ha2 hz1 hz2 hz

-- box ['700149/4096000', '350499/2048000', '1999/2000', '3999/4000']  interval_lower 696999/274877906944
noncomputable def e599 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1287456443858,0,true,173505591808,173505591872⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨911566811694,0,false,-206110596416,-206110596352⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1287684345562,0,true,173700206848,173700206912⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨911338909990,0,false,-206385520768,-206385520704⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1287362471449,0,true,173425334720,173425334784⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨911660784103,0,false,-205997254848,-205997254784⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1287637302383,0,true,173660037504,173660037568⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨911385953169,0,false,-206328765568,-206328765504⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535628727,0,true,24000640,24000704⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487626825,0,false,-24001216,-24001152⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099559691456,0,true,48062592,48062656⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099463564096,0,false,-48064768,-48064704⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625674,0,false,-2112,-2048⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627253,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1287409453016,0,true,173465460032,173465460096⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨911613802536,0,false,-206053918592,-206053918528⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1287660832522,0,true,173680129664,173680129728⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨911362423030,0,false,-206357153152,-206357153088⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067315403241,0,false,-32677023424,-32677023360⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067401378246,0,false,-32588458496,-32588458432⟩
    { al := (700149/4096000), au := (350499/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨187944816082,188172717786⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173505591808,173505591872⟩ : DyadicInterval 40),(⟨-206110596416,-206110596352⟩ : DyadicInterval 40),(⟨745981074506,745981093836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173700206848,173700206912⟩ : DyadicInterval 40),(⟨-206385520768,-206385520704⟩ : DyadicInterval 40),(⟨745941707639,745941726969⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173425334720,173425334784⟩ : DyadicInterval 40),(⟨-205997254848,-205997254784⟩ : DyadicInterval 40),(⟨745997292775,745997312104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173660037504,173660037568⟩ : DyadicInterval 40),(⟨-206328765568,-206328765504⟩ : DyadicInterval 40),(⟨745949837655,745949856985⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨24000951,48063680⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24000640,24000704⟩ : DyadicInterval 40),(⟨-24001216,-24001152⟩ : DyadicInterval 40),(⟨762123383316,762123402645⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨48062592,48062656⟩ : DyadicInterval 40),(⟨-48064768,-48064704⟩ : DyadicInterval 40),(⟨762123382538,762123401868⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2112,-512⟩ : DyadicInterval 40),(⟨762123383872,762123403936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨187897825240,188149204746⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173465460032,173465460096⟩ : DyadicInterval 40),(⟨-206053918592,-206053918528⟩ : DyadicInterval 40),(⟨745989185483,745989204812⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173680129664,173680129728⟩ : DyadicInterval 40),(⟨-206357153152,-206357153088⟩ : DyadicInterval 40),(⟨745945771441,745945790770⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32677023424,-32588458432⟩ : DyadicInterval 40),(⟨778417612832,778461914592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨173505591808,173700206912⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-206385520768,-206110596352⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e599_ok : ecellOkT e599 = true := by decide +kernel
theorem e599_pos {a z : ℝ} (ha1 : ((700149/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((350499/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e599 e599_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B009

end


