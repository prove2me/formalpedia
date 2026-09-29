-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B003__2
-- name    : CK_CKLaneC2R_EpCells_B003__2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:33:14.594229+00:00
-- url     : https://prove2.me/theorems/c7bbda8e-c3ec-46d0-a201-f83ad349a698
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B003 (+1 modules: CKLaneC2R.EpCells.B004)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B003 (+1 modules: CKLaneC2R.EpCells.B004)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B003 (+1 modules: CKLaneC2R.EpCells.B004)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B003 (+1 modules: CKLaneC2R.EpCells.B004) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B003 (+1 modules: CKLaneC2R/EpCells/B004).lean)

import Definitions.Def_CK_CKLaneC2R_EpCells_B003__2_q00

-- ===== source module CKLaneC2R.EpCells.B004 =====
section

namespace CKLaneC2R.EpCells.B004

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['346323/1024000', '86793/256000', '999/1000', '1']  interval_lower 695188547/137438953472
noncomputable def e240 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1471373117489,0,true,320320669568,320320669632⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨727650138063,0,false,-453879535040,-453879534976⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1472284724298,0,true,321001674176,321001674240⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨726738531254,0,false,-455257876992,-455257876864⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1471001255999,0,true,320042753856,320042753920⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨728021999553,0,false,-453317779392,-453317779328⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099715236048,0,true,203589376,203589440⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099308019504,0,false,-203627136,-203627072⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511590071,0,false,-37760,-37696⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1471187185555,0,true,320181719616,320181719680⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨727836069997,0,false,-453598619584,-453598619520⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1472284733031,0,true,321001680704,321001680768⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨726738522521,0,false,-455257890176,-455257890112⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨973128436829,0,false,-134256209408,-134256209344⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨973871555620,0,false,-133416899904,-133416899840⟩
    { al := (346323/1024000), au := (86793/256000), zl := (999/1000), zu := 1,
      A := ⟨371861489713,372773096522⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨320320669568,320320669632⟩ : DyadicInterval 40),(⟨-453879535040,-453879534976⟩ : DyadicInterval 40),(⟨697983217918,697983237247⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨321001674176,321001674240⟩ : DyadicInterval 40),(⟨-455257876992,-455257876864⟩ : DyadicInterval 40),(⟨697661845828,697661865178⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨320042753856,320042753920⟩ : DyadicInterval 40),(⟨-453317779392,-453317779328⟩ : DyadicInterval 40),(⟨698114066526,698114085856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨321001674176,321001674240⟩ : DyadicInterval 40),(⟨-455257876992,-455257876864⟩ : DyadicInterval 40),(⟨697661845828,697661865178⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,203608272⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203589376,203589440⟩ : DyadicInterval 40),(⟨-203627136,-203627072⟩ : DyadicInterval 40),(⟨762123364727,762123384057⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37760,0⟩ : DyadicInterval 40),(⟨762123383616,762123421760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨371675557779,372773105255⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨320181719616,320181719680⟩ : DyadicInterval 40),(⟨-453598619584,-453598619520⟩ : DyadicInterval 40),(⟨698048660395,698048679725⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨321001680704,321001680768⟩ : DyadicInterval 40),(⟨-455257890176,-455257890112⟩ : DyadicInterval 40),(⟨697661842752,697661862082⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-134256209408,-133416899840⟩ : DyadicInterval 40),(⟨828831833536,829251507584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨320320669568,321001674240⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-455257876992,-453879534976⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e240_ok : ecellOkT e240 = true := by decide +kernel
theorem e240_pos {a z : ℝ} (ha1 : ((346323/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((86793/256000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e240 e240_ok ha1 ha2 hz1 hz2 hz

-- box ['86793/256000', '348021/1024000', '999/1000', '1']  interval_lower 2770593/536870912
noncomputable def e241 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1472284724297,0,true,321001674176,321001674240⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨726738531255,0,false,-455257876992,-455257876864⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1473196331107,0,true,321682257280,321682257344⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨725826924445,0,false,-456637948928,-456637948864⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1471911951200,0,true,320723249600,320723249664⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨727111304352,0,false,-454694038336,-454694038272⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099715828279,0,true,204181504,204181568⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099307427273,0,false,-204219520,-204219456⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511589852,0,false,-37952,-37888⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1472098336589,0,true,320862469824,320862469888⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨726924918963,0,false,-454975919744,-454975919680⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1473196339834,0,true,321682263808,321682263872⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨725826915718,0,false,-456637962112,-456637962048⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨972509547490,0,false,-134955698304,-134955698240⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨973254795127,0,false,-134113449856,-134113449792⟩
    { al := (86793/256000), au := (348021/1024000), zl := (999/1000), zu := 1,
      A := ⟨372773096521,373684703331⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨321001674176,321001674240⟩ : DyadicInterval 40),(⟨-455257876992,-455257876864⟩ : DyadicInterval 40),(⟨697661845828,697661865179⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨321682257280,321682257344⟩ : DyadicInterval 40),(⟨-456637948928,-456637948864⟩ : DyadicInterval 40),(⟨697339619764,697339639093⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨320723249600,320723249664⟩ : DyadicInterval 40),(⟨-454694038336,-454694038272⟩ : DyadicInterval 40),(⟨697793364093,697793383423⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨321682257280,321682257344⟩ : DyadicInterval 40),(⟨-456637948928,-456637948864⟩ : DyadicInterval 40),(⟨697339619764,697339639093⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,204200503⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204181504,204181568⟩ : DyadicInterval 40),(⟨-204219520,-204219456⟩ : DyadicInterval 40),(⟨762123364635,762123383965⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37952,0⟩ : DyadicInterval 40),(⟨762123383616,762123421856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨372586708813,373684712058⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨320862469824,320862469888⟩ : DyadicInterval 40),(⟨-454975919744,-454975919680⟩ : DyadicInterval 40),(⟨697727623227,697727642556⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨321682263808,321682263872⟩ : DyadicInterval 40),(⟨-456637962112,-456637962048⟩ : DyadicInterval 40),(⟨697339616653,697339635983⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-134955698304,-134113449792⟩ : DyadicInterval 40),(⟨829180108512,829601252032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨321001674176,321682257344⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-456637948928,-455257876864⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e241_ok : ecellOkT e241 = true := by decide +kernel
theorem e241_pos {a z : ℝ} (ha1 : ((86793/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((348021/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e241 e241_ok ha1 ha2 hz1 hz2 hz

-- box ['348021/1024000', '34887/102400', '999/1000', '1']  interval_lower 2894024823/549755813888
noncomputable def e242 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1473196331106,0,true,321682257280,321682257344⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨725826924446,0,false,-456637948928,-456637948864⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1474107937915,0,true,322362419392,322362419456⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨724915317637,0,false,-458019755264,-458019755200⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1472822646402,0,true,321403324480,321403324544⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨726200609150,0,false,-456072022080,-456072022016⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099716421310,0,true,204774464,204774528⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099306834242,0,false,-204812672,-204812608⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511589631,0,false,-38208,-38144⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1473009487641,0,true,321542798912,321542798976⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨726013767911,0,false,-456354947392,-456354947328⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1474107946651,0,true,322362425920,322362425984⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨724915308901,0,false,-458019768512,-458019768448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨971889146512,0,false,-135657342592,-135657342528⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨972636524504,0,false,-134812148416,-134812148352⟩
    { al := (348021/1024000), au := (34887/102400), zl := (999/1000), zu := 1,
      A := ⟨373684703330,374596310139⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨321682257280,321682257344⟩ : DyadicInterval 40),(⟨-456637948928,-456637948864⟩ : DyadicInterval 40),(⟨697339619764,697339639093⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨322362419392,322362419456⟩ : DyadicInterval 40),(⟨-458019755264,-458019755200⟩ : DyadicInterval 40),(⟨697016539147,697016558477⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨321403324480,321403324544⟩ : DyadicInterval 40),(⟨-456072022080,-456072022016⟩ : DyadicInterval 40),(⟨697471809580,697471828909⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨322362419392,322362419456⟩ : DyadicInterval 40),(⟨-458019755264,-458019755200⟩ : DyadicInterval 40),(⟨697016539147,697016558477⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,204793534⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204774464,204774528⟩ : DyadicInterval 40),(⟨-204812672,-204812608⟩ : DyadicInterval 40),(⟨762123364510,762123383840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38208,0⟩ : DyadicInterval 40),(⟨762123383616,762123421984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨373497859865,374596318875⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨321542798912,321542798976⟩ : DyadicInterval 40),(⟨-456354947392,-456354947328⟩ : DyadicInterval 40),(⟨697405732995,697405752324⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨322362425920,322362425984⟩ : DyadicInterval 40),(⟨-458019768512,-458019768448⟩ : DyadicInterval 40),(⟨697016536038,697016555368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-135657342592,-134812148352⟩ : DyadicInterval 40),(⟨829529457792,829952074176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨321682257280,322362419456⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-458019755264,-456637948864⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e242_ok : ecellOkT e242 = true := by decide +kernel
theorem e242_pos {a z : ℝ} (ha1 : ((348021/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((34887/102400 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e242 e242_ok ha1 ha2 hz1 hz2 hz

-- box ['34887/102400', '349719/1024000', '999/1000', '1']  interval_lower 5903104049/1099511627776
noncomputable def e243 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1474107937914,0,true,322362419392,322362419456⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨724915317638,0,false,-458019755264,-458019755200⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1475019544724,0,true,323042160960,323042161024⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨724003710828,0,false,-459403300352,-459403300288⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1473733341603,0,true,322082978944,322082979008⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨725289913949,0,false,-457451734976,-457451734848⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099717015141,0,true,205368128,205368192⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099306240411,0,false,-205406592,-205406528⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511589409,0,false,-38400,-38336⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1473920638691,0,true,322222707264,322222707328⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨725102616861,0,false,-457735706816,-457735706752⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1475019561646,0,true,323042173568,323042173632⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨724003693906,0,false,-459403326080,-459403326016⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨971267228319,0,false,-136361152448,-136361152384⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨972016743763,0,false,-135512999488,-135512999424⟩
    { al := (34887/102400), au := (349719/1024000), zl := (999/1000), zu := 1,
      A := ⟨374596310138,375507916948⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨322362419392,322362419456⟩ : DyadicInterval 40),(⟨-458019755264,-458019755200⟩ : DyadicInterval 40),(⟨697016539148,697016558477⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨323042160960,323042161024⟩ : DyadicInterval 40),(⟨-459403300352,-459403300288⟩ : DyadicInterval 40),(⟨696692603499,696692622828⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨322082978944,322082979008⟩ : DyadicInterval 40),(⟨-457451734976,-457451734848⟩ : DyadicInterval 40),(⟨697149402479,697149421830⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨323042160960,323042161024⟩ : DyadicInterval 40),(⟨-459403300352,-459403300288⟩ : DyadicInterval 40),(⟨696692603499,696692622828⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,205387365⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205368128,205368192⟩ : DyadicInterval 40),(⟨-205406592,-205406528⟩ : DyadicInterval 40),(⟨762123364417,762123383747⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38400,0⟩ : DyadicInterval 40),(⟨762123383616,762123422080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨374409010915,375507933870⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨322222707264,322222707328⟩ : DyadicInterval 40),(⟨-457735706816,-457735706752⟩ : DyadicInterval 40),(⟨697082989237,697083008566⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨323042173568,323042173632⟩ : DyadicInterval 40),(⟨-459403326080,-459403326016⟩ : DyadicInterval 40),(⟨696692597491,696692616821⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-136361152448,-135512999424⟩ : DyadicInterval 40),(⟨829879883328,830303979104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨322362419392,323042161024⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-459403300352,-458019755200⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e243_ok : ecellOkT e243 = true := by decide +kernel
theorem e243_pos {a z : ℝ} (ha1 : ((34887/102400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((349719/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e243 e243_ok ha1 ha2 hz1 hz2 hz

-- box ['349719/1024000', '43821/128000', '999/1000', '1']  interval_lower 6019427291/1099511627776
noncomputable def e244 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1475019544723,0,true,323042160960,323042161024⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨724003710829,0,false,-459403300352,-459403300288⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1475931151533,0,true,323721482624,323721482688⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨723092104019,0,false,-460788588608,-460788588544⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1474644036805,0,true,322762213568,322762213632⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨724379218747,0,false,-458833181312,-458833181248⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099717609778,0,true,205962688,205962752⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099305645774,0,false,-206001344,-206001280⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511589187,0,false,-38592,-38528⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1474831789743,0,true,322902195456,322902195520⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨724191465809,0,false,-459118202368,-459118202304⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1475931168467,0,true,323721495232,323721495296⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨723092087085,0,false,-460788614400,-460788614272⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨970643804067,0,false,-137067119104,-137067119040⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨971395452904,0,false,-136216006848,-136216006784⟩
    { al := (349719/1024000), au := (43821/128000), zl := (999/1000), zu := 1,
      A := ⟨375507916947,376419523757⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨323042160960,323042161024⟩ : DyadicInterval 40),(⟨-459403300352,-459403300288⟩ : DyadicInterval 40),(⟨696692603499,696692622829⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨323721482624,323721482688⟩ : DyadicInterval 40),(⟨-460788588608,-460788588544⟩ : DyadicInterval 40),(⟨696367812201,696367831531⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨322762213568,322762213632⟩ : DyadicInterval 40),(⟨-458833181312,-458833181248⟩ : DyadicInterval 40),(⟨696826142257,696826161586⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨323721482624,323721482688⟩ : DyadicInterval 40),(⟨-460788588608,-460788588544⟩ : DyadicInterval 40),(⟨696367812201,696367831531⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,205982002⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205962688,205962752⟩ : DyadicInterval 40),(⟨-206001344,-206001280⟩ : DyadicInterval 40),(⟨762123364291,762123383620⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38592,0⟩ : DyadicInterval 40),(⟨762123383616,762123422176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨375320161967,376419540691⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨322902195456,322902195520⟩ : DyadicInterval 40),(⟨-459118202368,-459118202304⟩ : DyadicInterval 40),(⟨696759391369,696759410699⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨323721495232,323721495296⟩ : DyadicInterval 40),(⟨-460788614400,-460788614272⟩ : DyadicInterval 40),(⟨696367806158,696367825508⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-137067119104,-136216006784⟩ : DyadicInterval 40),(⟨830231387008,830656962432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨323042160960,323721482688⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-460788588608,-459403300288⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e244_ok : ecellOkT e244 = true := by decide +kernel
theorem e244_pos {a z : ℝ} (ha1 : ((349719/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((43821/128000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e244 e244_ok ha1 ha2 hz1 hz2 hz

-- box ['43821/128000', '351417/1024000', '999/1000', '1']  interval_lower 6136989477/1099511627776
noncomputable def e245 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1475931151532,0,true,323721482624,323721482688⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨723092104020,0,false,-460788588608,-460788588544⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1476842758341,0,true,324400384768,324400384832⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨722180497211,0,false,-462175624448,-462175624320⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1475554732008,0,true,323441028864,323441028928⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨723468523544,0,false,-460216365568,-460216365504⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099718205225,0,true,206558016,206558080⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099305050327,0,false,-206596864,-206596800⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511588964,0,false,-38848,-38784⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1475742940802,0,true,323581263936,323581264000⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨723280314750,0,false,-460502438400,-460502438336⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1476842775269,0,true,324400397376,324400397440⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨722180480283,0,false,-462175650176,-462175650112⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨970018868198,0,false,-137775252736,-137775252672⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨970772651921,0,false,-136921174400,-136921174336⟩
    { al := (43821/128000), au := (351417/1024000), zl := (999/1000), zu := 1,
      A := ⟨376419523756,377331130565⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨323721482624,323721482688⟩ : DyadicInterval 40),(⟨-460788588608,-460788588544⟩ : DyadicInterval 40),(⟨696367812201,696367831531⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨324400384768,324400384832⟩ : DyadicInterval 40),(⟨-462175624448,-462175624320⟩ : DyadicInterval 40),(⟨696042164781,696042184132⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨323441028864,323441028928⟩ : DyadicInterval 40),(⟨-460216365568,-460216365504⟩ : DyadicInterval 40),(⟨696502028346,696502047675⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨324400384768,324400384832⟩ : DyadicInterval 40),(⟨-462175624448,-462175624320⟩ : DyadicInterval 40),(⟨696042164781,696042184132⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,206577449⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨206558016,206558080⟩ : DyadicInterval 40),(⟨-206596864,-206596800⟩ : DyadicInterval 40),(⟨762123364163,762123383493⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38848,0⟩ : DyadicInterval 40),(⟨762123383616,762123422304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨376231313026,377331147493⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨323581263936,323581264000⟩ : DyadicInterval 40),(⟨-460502438400,-460502438336⟩ : DyadicInterval 40),(⟨696434938886,696434958215⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨324400397376,324400397440⟩ : DyadicInterval 40),(⟨-462175650176,-462175650112⟩ : DyadicInterval 40),(⟨696042158729,696042178058⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-137775252736,-136921174336⟩ : DyadicInterval 40),(⟨830583970784,831011029248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨323721482624,324400384832⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-462175624448,-460788588544⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e245_ok : ecellOkT e245 = true := by decide +kernel
theorem e245_pos {a z : ℝ} (ha1 : ((43821/128000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((351417/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e245 e245_ok ha1 ha2 hz1 hz2 hz

-- box ['351417/1024000', '176133/512000', '999/1000', '1']  interval_lower 3127900443/549755813888
noncomputable def e246 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1476842758340,0,true,324400384768,324400384832⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨722180497212,0,false,-462175624448,-462175624320⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1477754365150,0,true,325078868032,325078868096⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨721268890402,0,false,-463564412160,-463564412096⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1476465427209,0,true,324119425280,324119425344⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨722557828343,0,false,-461601292096,-461601292032⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099718801483,0,true,207154176,207154240⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099304454069,0,false,-207193280,-207193216⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511588739,0,false,-39040,-38976⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1476654091835,0,true,324259913344,324259913408⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨722369163717,0,false,-461888419328,-461888419264⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1477754382083,0,true,325078880640,325078880704⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨721268873469,0,false,-463564438016,-463564437952⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨969392420692,0,false,-138485557312,-138485557248⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨970148340838,0,false,-137628505984,-137628505920⟩
    { al := (351417/1024000), au := (176133/512000), zl := (999/1000), zu := 1,
      A := ⟨377331130564,378242737374⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨324400384768,324400384832⟩ : DyadicInterval 40),(⟨-462175624448,-462175624320⟩ : DyadicInterval 40),(⟨696042164781,696042184132⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨325078868032,325078868096⟩ : DyadicInterval 40),(⟨-463564412160,-463564412096⟩ : DyadicInterval 40),(⟨695715660625,695715679954⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨324119425280,324119425344⟩ : DyadicInterval 40),(⟨-461601292096,-461601292032⟩ : DyadicInterval 40),(⟨696177060260,696177079589⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨325078868032,325078868096⟩ : DyadicInterval 40),(⟨-463564412160,-463564412096⟩ : DyadicInterval 40),(⟨695715660625,695715679954⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,207173707⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207154176,207154240⟩ : DyadicInterval 40),(⟨-207193280,-207193216⟩ : DyadicInterval 40),(⟨762123364067,762123383396⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39040,0⟩ : DyadicInterval 40),(⟨762123383616,762123422400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨377142464059,378242754307⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨324259913344,324259913408⟩ : DyadicInterval 40),(⟨-461888419328,-461888419264⟩ : DyadicInterval 40),(⟨696109631177,696109650507⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨325078880640,325078880704⟩ : DyadicInterval 40),(⟨-463564438016,-463564437952⟩ : DyadicInterval 40),(⟨695715654560,695715673889⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-138485557312,-137628505920⟩ : DyadicInterval 40),(⟨830937636576,831366181536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨324400384768,325078868096⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-463564412160,-462175624320⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e246_ok : ecellOkT e246 = true := by decide +kernel
theorem e246_pos {a z : ℝ} (ha1 : ((351417/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((176133/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e246 e246_ok ha1 ha2 hz1 hz2 hz

-- box ['176133/512000', '70623/204800', '999/1000', '1']  interval_lower 1593967775/274877906944
noncomputable def e247 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1477754365149,0,true,325078868032,325078868096⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨721268890403,0,false,-463564412160,-463564412096⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1478665971958,0,true,325756932864,325756932928⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨720357283594,0,false,-464954956352,-464954956288⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1477376122411,0,true,324797403456,324797403520⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨721647133141,0,false,-462987965184,-462987965120⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099719398559,0,true,207751104,207751168⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099303856993,0,false,-207790464,-207790400⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511588514,0,false,-39296,-39232⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1477565242902,0,true,324938144064,324938144128⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨721458012650,0,false,-463276149568,-463276149504⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1478665988888,0,true,325756945472,325756945536⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨720357266664,0,false,-464954982144,-464954982080⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨968764461562,0,false,-139198036672,-139198036608⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨969522519613,0,false,-138338005440,-138338005376⟩
    { al := (176133/512000), au := (70623/204800), zl := (999/1000), zu := 1,
      A := ⟨378242737373,379154344182⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨325078868032,325078868096⟩ : DyadicInterval 40),(⟨-463564412160,-463564412096⟩ : DyadicInterval 40),(⟨695715660625,695715679954⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨325756932864,325756932928⟩ : DyadicInterval 40),(⟨-464954956352,-464954956288⟩ : DyadicInterval 40),(⟨695388299221,695388318550⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨324797403456,324797403520⟩ : DyadicInterval 40),(⟨-462987965184,-462987965120⟩ : DyadicInterval 40),(⟨695851237331,695851256661⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨325756932864,325756932928⟩ : DyadicInterval 40),(⟨-464954956352,-464954956288⟩ : DyadicInterval 40),(⟨695388299221,695388318550⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,207770783⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207751104,207751168⟩ : DyadicInterval 40),(⟨-207790464,-207790400⟩ : DyadicInterval 40),(⟨762123363970,762123383299⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39296,0⟩ : DyadicInterval 40),(⟨762123383616,762123422528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨378053615126,379154361112⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨324938144064,324938144128⟩ : DyadicInterval 40),(⟨-463276149568,-463276149504⟩ : DyadicInterval 40),(⟨695783467764,695783487094⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨325756945472,325756945536⟩ : DyadicInterval 40),(⟨-464954982144,-464954982080⟩ : DyadicInterval 40),(⟨695388293104,695388312433⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-139198036672,-138338005376⟩ : DyadicInterval 40),(⟨831292386304,831722421216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨325078868032,325756932928⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-464954956352,-463564412096⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e247_ok : ecellOkT e247 = true := by decide +kernel
theorem e247_pos {a z : ℝ} (ha1 : ((176133/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((70623/204800 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e247 e247_ok ha1 ha2 hz1 hz2 hz

-- box ['70623/204800', '88491/256000', '999/1000', '1']  interval_lower 6497210589/1099511627776
noncomputable def e248 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1478665971957,0,true,325756932864,325756932928⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨720357283595,0,false,-464954956352,-464954956224⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1479577578767,0,true,326434579776,326434579840⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨719445676785,0,false,-466347261312,-466347261248⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1478286817612,0,true,325474963776,325474963840⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨720736437940,0,false,-464376389376,-464376389248⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099719996453,0,true,208348928,208348992⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099303259099,0,false,-208388480,-208388416⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511588288,0,false,-39552,-39488⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1478476393945,0,true,325615956736,325615956800⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨720546861607,0,false,-464665633472,-464665633408⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1479577595699,0,true,326434592384,326434592448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨719445659853,0,false,-466347287168,-466347287104⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨968134990799,0,false,-139912694784,-139912694720⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨968895188287,0,false,-139049676736,-139049676672⟩
    { al := (70623/204800), au := (88491/256000), zl := (999/1000), zu := 1,
      A := ⟨379154344181,380065950991⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨325756932864,325756932928⟩ : DyadicInterval 40),(⟨-464954956352,-464954956224⟩ : DyadicInterval 40),(⟨695388299200,695388318550⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨326434579776,326434579840⟩ : DyadicInterval 40),(⟨-466347261312,-466347261248⟩ : DyadicInterval 40),(⟨695060079983,695060099313⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨325474963776,325474963840⟩ : DyadicInterval 40),(⟨-464376389376,-464376389248⟩ : DyadicInterval 40),(⟨695524559120,695524578470⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨326434579776,326434579840⟩ : DyadicInterval 40),(⟨-466347261312,-466347261248⟩ : DyadicInterval 40),(⟨695060079983,695060099313⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,208368677⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208348928,208348992⟩ : DyadicInterval 40),(⟨-208388480,-208388416⟩ : DyadicInterval 40),(⟨762123363839,762123383169⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39552,0⟩ : DyadicInterval 40),(⟨762123383616,762123422656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨378964766169,380065967923⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨325615956736,325615956800⟩ : DyadicInterval 40),(⟨-464665633472,-464665633408⟩ : DyadicInterval 40),(⟨695456448010,695456467340⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨326434592384,326434592448⟩ : DyadicInterval 40),(⟨-466347287168,-466347287104⟩ : DyadicInterval 40),(⟨695060073855,695060093185⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-139912694784,-139049676672⟩ : DyadicInterval 40),(⟨831648221952,832079750272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨325756932864,326434579840⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-466347261312,-464954956224⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e248_ok : ecellOkT e248 = true := by decide +kernel
theorem e248_pos {a z : ℝ} (ha1 : ((70623/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((88491/256000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e248 e248_ok ha1 ha2 hz1 hz2 hz

-- box ['253197/256000', '1013637/1024000', '999/1000', '1']  interval_lower 889682075382629/1099511627776
noncomputable def e249 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2186984462221,0,true,756087449792,756087466752⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨12038793331,6,false,-4963731247936,-4963731132288⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2187896069030,0,true,756545666816,756545683904⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨11127186522,6,false,-5050309941568,-5050309825920⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2185896989386,0,true,755540584320,755540601024⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨13126266166,6,false,-4868644316416,-4868644200768⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1111373703519,0,true,11798545280,11798545344⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1087649552033,0,false,-11926526720,-11926526656⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099383653830,0,false,-127981440,-127981376⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨2186442970431,0,true,755815179840,755815196672⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨12580285121,6,false,-4915356361984,-4915356246336⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨2187896083666,0,true,756545674112,756545691264⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨11127171886,6,false,-5050311387840,-5050311272128⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨22141735636,5,false,-4293765694592,-4293765598208⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨25016630361,5,false,-4159541163072,-4159541066688⟩
    { al := (253197/256000), au := (1013637/1024000), zl := (999/1000), zu := 1,
      A := ⟨1087472834445,1088384441254⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨756087449792,756087466752⟩ : DyadicInterval 40),(⟨-4963731247936,-4963731132288⟩ : DyadicInterval 40),(⟨37349689390,37349726156⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨756545666816,756545683904⟩ : DyadicInterval 40),(⟨-5050309941568,-5050309825920⟩ : DyadicInterval 40),(⟨34960728836,34960765688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨755540584320,755540601024⟩ : DyadicInterval 40),(⟨-4868644316416,-4868644200768⟩ : DyadicInterval 40),(⟨40154299622,40154336183⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨756545666816,756545683904⟩ : DyadicInterval 40),(⟨-5050309941568,-5050309825920⟩ : DyadicInterval 40),(⟨34960728836,34960765688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11862075743⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11798545280,11798545344⟩ : DyadicInterval 40),(⟨-11926526720,-11926526656⟩ : DyadicInterval 40),(⟨762059395361,762059414690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-127981440,0⟩ : DyadicInterval 40),(⟨762123383616,762187393600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨1086931342655,1088384455890⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨755815179840,755815196672⟩ : DyadicInterval 40),(⟨-4915356361984,-4915356246336⟩ : DyadicInterval 40),(⟨38752115648,38752152311⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨756545674112,756545691264⟩ : DyadicInterval 40),(⟨-5050311387840,-5050311272128⟩ : DyadicInterval 40),(⟨34960690183,34960727099⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4293765694592,-4159541066688⟩ : DyadicInterval 40),(⟨2841893916960,2909006250176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨756087449792,756545683904⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-5050309941568,-4963731132288⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e249_ok : ecellOkT e249 = true := by decide +kernel
theorem e249_pos {a z : ℝ} (ha1 : ((253197/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1013637/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e249 e249_ok ha1 ha2 hz1 hz2 hz

-- box ['1013637/1024000', '507243/512000', '999/1000', '1']  interval_lower 951346030175723/1099511627776
noncomputable def e250 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2187896069029,0,true,756545666816,756545683904⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨11127186523,6,false,-5050309941504,-5050309825856⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2188807675839,0,true,757003692864,757003710144⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨10215579713,6,false,-5144293306432,-5144293190592⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2186807684587,0,true,755998570816,755998587712⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨12215570965,6,false,-4947703410368,-4947703294720⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1112268934712,0,true,12683864832,12683864896⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1086754320840,0,false,-12831894080,-12831894016⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099363608531,0,false,-148029248,-148029184⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨2187354268431,0,true,756273355008,756273372032⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨11668987121,6,false,-4998035531392,-4998035415744⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨2188807690427,0,true,757003700224,757003717504⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨10215565125,6,false,-5144294876544,-5144294760704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨20336217410,5,false,-4387291157248,-4387291060672⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨23214132660,5,false,-4241762157248,-4241762060864⟩
    { al := (1013637/1024000), au := (507243/512000), zl := (999/1000), zu := 1,
      A := ⟨1088384441253,1089296048063⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨756545666816,756545683904⟩ : DyadicInterval 40),(⟨-5050309941504,-5050309825856⟩ : DyadicInterval 40),(⟨34960728838,34960765691⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨757003692864,757003710144⟩ : DyadicInterval 40),(⟨-5144293306432,-5144293190592⟩ : DyadicInterval 40),(⟨32534194326,32534231330⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨755998570816,755998587712⟩ : DyadicInterval 40),(⟨-4947703410368,-4947703294720⟩ : DyadicInterval 40),(⟨37808851509,37808888220⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨757003692864,757003710144⟩ : DyadicInterval 40),(⟨-5144293306432,-5144293190592⟩ : DyadicInterval 40),(⟨32534194326,32534231330⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,12757306936⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨12683864832,12683864896⟩ : DyadicInterval 40),(⟨-12831894080,-12831894016⟩ : DyadicInterval 40),(⟨762049372288,762049391618⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-148029248,0⟩ : DyadicInterval 40),(⟨762123383616,762197417504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨1087842640655,1089296062651⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨756273355008,756273372032⟩ : DyadicInterval 40),(⟨-4998035531392,-4998035415744⟩ : DyadicInterval 40),(⟨36384911551,36384948364⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨757003700224,757003717504⟩ : DyadicInterval 40),(⟨-5144294876544,-5144294760704⟩ : DyadicInterval 40),(⟨32534155146,32534192149⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4387291157248,-4241762060864⟩ : DyadicInterval 40),(⟨2883004414048,2955768981504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨756545666816,757003710144⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-5144293306432,-5050309825856⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e250_ok : ecellOkT e250 = true := by decide +kernel
theorem e250_pos {a z : ℝ} (ha1 : ((1013637/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((507243/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e250 e250_ok ha1 ha2 hz1 hz2 hz

-- box ['507243/512000', '203067/204800', '999/1000', '1']  interval_lower 498111704290235/549755813888
noncomputable def e251 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2188807675838,0,true,757003692864,757003710144⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨10215579714,6,false,-5144293306304,-5144293190464⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2189719282648,0,true,757461528256,757461545728⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨9303972904,6,false,-5247067381824,-5247067263488⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2187718379789,0,true,756456366720,756456383744⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨11304875763,6,false,-5032890636096,-5032890520448⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1113327194659,0,true,13729489600,13729489664⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1085696060893,0,false,-13903098496,-13903098432⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099338032623,0,false,-173608896,-173608832⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨2188265589294,0,true,756731350912,756731368064⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨10757666258,6,false,-5087443428224,-5087443312576⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨2189719297204,0,true,757461535552,757461553024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨9303958348,6,false,-5247069102016,-5247068983680⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨18529187523,5,false,-4489607547584,-4489607448192⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨21410079075,5,false,-4330712058176,-4330711961792⟩
    { al := (507243/512000), au := (203067/204800), zl := (999/1000), zu := 1,
      A := ⟨1089296048062,1090207654872⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨757003692864,757003710144⟩ : DyadicInterval 40),(⟨-5144293306304,-5144293190464⟩ : DyadicInterval 40),(⟨32534194328,32534231331⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨757461528256,757461545728⟩ : DyadicInterval 40),(⟨-5247067381824,-5247067263488⟩ : DyadicInterval 40),(⟨30066741269,30066778434⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨756456366720,756456383744⟩ : DyadicInterval 40),(⟨-5032890636096,-5032890520448⟩ : DyadicInterval 40),(⟨35429235143,35429271940⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨757461528256,757461545728⟩ : DyadicInterval 40),(⟨-5247067381824,-5247067263488⟩ : DyadicInterval 40),(⟨30066741269,30066778434⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,13815566883⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨13729489600,13729489664⟩ : DyadicInterval 40),(⟨-13903098496,-13903098432⟩ : DyadicInterval 40),(⟨762036583710,762036603039⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-173608896,0⟩ : DyadicInterval 40),(⟨762123383616,762210207328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨1088753961518,1090207669428⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨756731350912,756731368064⟩ : DyadicInterval 40),(⟨-5087443428224,-5087443312576⟩ : DyadicInterval 40),(⟨33981836332,33981873231⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨757461535552,757461553024⟩ : DyadicInterval 40),(⟨-5247069102016,-5247068983680⟩ : DyadicInterval 40),(⟨30066701536,30066738701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4489607547584,-4330711961792⟩ : DyadicInterval 40),(⟨2927479364512,3006927176672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨757003692864,757461545728⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-5247067381824,-5144293190464⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e251_ok : ecellOkT e251 = true := by decide +kernel
theorem e251_pos {a z : ℝ} (ha1 : ((507243/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((203067/204800 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e251 e251_ok ha1 ha2 hz1 hz2 hz

-- box ['203067/204800', '127023/128000', '999/1000', '1']  interval_lower 249766439185337/274877906944
noncomputable def e252 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2189719282647,0,true,757461528256,757461545728⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨9303972905,6,false,-5247067381696,-5247067263360⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2190630889456,0,true,757919173056,757919190720⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨8392366096,7,false,-5360447946112,-5360447811200⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2188629074991,0,true,756913972032,756913989248⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨10394180561,6,false,-5125236449600,-5125236333824⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1114599156063,0,true,14984949824,14984949888⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1084424099489,0,false,-15192000896,-15192000832⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099304596304,0,false,-207051008,-207050944⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨2189176939044,0,true,757189170560,757189187904⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨9846316508,6,false,-5184773532864,-5184773416640⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨2190630903961,0,true,757919180352,757919197952⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨8392351591,7,false,-5360449846464,-5360449711552⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨16720646046,6,false,-4602530646976,-4602530531328⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨19604457552,5,false,-4427584343232,-4427584246208⟩
    { al := (203067/204800), au := (127023/128000), zl := (999/1000), zu := 1,
      A := ⟨1090207654871,1091119261680⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨757461528256,757461545728⟩ : DyadicInterval 40),(⟨-5247067381696,-5247067263360⟩ : DyadicInterval 40),(⟨30066741271,30066778436⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨757919173056,757919190720⟩ : DyadicInterval 40),(⟨-5360447946112,-5360447811200⟩ : DyadicInterval 40),(⟨27554366960,27554404337⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨756913972032,756913989248⟩ : DyadicInterval 40),(⟨-5125236449600,-5125236333824⟩ : DyadicInterval 40),(⟨33012707675,33012744622⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨757919173056,757919190720⟩ : DyadicInterval 40),(⟨-5360447946112,-5360447811200⟩ : DyadicInterval 40),(⟨27554366960,27554404337⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,15087528287⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨14984949824,14984949888⟩ : DyadicInterval 40),(⟨-15192000896,-15192000832⟩ : DyadicInterval 40),(⟨762019864620,762019883950⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-207051008,0⟩ : DyadicInterval 40),(⟨762123383616,762226928384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨1089665311268,1091119276185⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨757189170560,757189187904⟩ : DyadicInterval 40),(⟨-5184773532864,-5184773416640⟩ : DyadicInterval 40),(⟨31539846350,31539883402⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨757919180352,757919197952⟩ : DyadicInterval 40),(⟨-5360449846464,-5360449711552⟩ : DyadicInterval 40),(⟨27554326651,27554363964⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4602530646976,-4427584246208⟩ : DyadicInterval 40),(⟨2975915506720,3063388726368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨757461528256,757919190720⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-5360447946112,-5247067263360⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e252_ok : ecellOkT e252 = true := by decide +kernel
theorem e252_pos {a z : ℝ} (ha1 : ((203067/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((127023/128000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e252 e252_ok ha1 ha2 hz1 hz2 hz

-- box ['127023/128000', '1017033/1024000', '999/1000', '1']  interval_lower 226552788709599/274877906944
noncomputable def e253 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2190630889455,0,true,757919173056,757919190720⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨8392366097,7,false,-5360447945984,-5360447811072⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2191542496265,0,true,758376627520,758376645248⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨7480759287,7,false,-5486878807744,-5486878672832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2189539770193,0,true,757371387008,757371404352⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨9483485359,6,false,-5226055274112,-5226055156864⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1116159318702,0,true,16522917568,16522917632⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1082863936850,0,false,-16775008960,-16775008896⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099259565309,0,false,-252091392,-252091328⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨2190088326073,0,true,757646818368,757646835904⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨8934929479,6,false,-5291568192064,-5291568068864⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨2191542510685,0,true,758376634752,758376652480⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨7480744867,7,false,-5486880927168,-5486880792256⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨14910593006,6,false,-4728504273280,-4728504157632⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨17797251300,5,false,-4533921355264,-4533921250560⟩
    { al := (127023/128000), au := (1017033/1024000), zl := (999/1000), zu := 1,
      A := ⟨1091119261679,1092030868489⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨757919173056,757919190720⟩ : DyadicInterval 40),(⟨-5360447945984,-5360447811072⟩ : DyadicInterval 40),(⟨27554366962,27554404339⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨758376627520,758376645248⟩ : DyadicInterval 40),(⟨-5486878807744,-5486878672832⟩ : DyadicInterval 40),(⟨24992194323,24992231714⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨757371387008,757371404352⟩ : DyadicInterval 40),(⟨-5226055274112,-5226055156864⟩ : DyadicInterval 40),(⟨30556043885,30556080925⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨758376627520,758376645248⟩ : DyadicInterval 40),(⟨-5486878807744,-5486878672832⟩ : DyadicInterval 40),(⟨24992194323,24992231714⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,16647690926⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨16522917568,16522917632⟩ : DyadicInterval 40),(⟨-16775008960,-16775008896⟩ : DyadicInterval 40),(⟨761997347516,761997366845⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-252091392,0⟩ : DyadicInterval 40),(⟨762123383616,762249448576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨1090576698297,1092030882909⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨757646818368,757646835904⟩ : DyadicInterval 40),(⟨-5291568192064,-5291568068864⟩ : DyadicInterval 40),(⟨29055327604,29055364835⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨758376634752,758376652480⟩ : DyadicInterval 40),(⟨-5486880927168,-5486880792256⟩ : DyadicInterval 40),(⟨24992153372,24992190764⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4728504273280,-4533921250560⟩ : DyadicInterval 40),(⟨3029084008896,3126375539520⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨757919173056,758376645248⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-5486878807744,-5360447811072⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e253_ok : ecellOkT e253 = true := by decide +kernel
theorem e253_pos {a z : ℝ} (ha1 : ((127023/128000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1017033/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e253 e253_ok ha1 ha2 hz1 hz2 hz

-- box ['1017033/1024000', '508941/512000', '999/1000', '1']  interval_lower 299384880761919/549755813888
noncomputable def e254 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2191542496264,0,true,758376627520,758376645248⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨7480759288,7,false,-5486878807552,-5486878672640⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2192454103073,0,true,758833891648,758833909632⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨6569152479,7,false,-5629759761280,-5629759626368⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2190450465395,0,true,757828611712,757828629312⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨8572790157,7,false,-5337060500736,-5337060365824⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1118122053579,0,true,18454679936,18454680000⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1080901201973,0,false,-18769726784,-18769726720⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099196626151,0,false,-315046784,-315046720⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨2190999762470,0,true,758104300608,758104318272⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨8023493082,7,false,-5409869477696,-5409869342784⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨2192454117431,0,true,758833898880,758833916800⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨6569138121,7,false,-5629762164416,-5629762029504⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨13099028293,6,false,-4870928246464,-4870928130816⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨15988436132,6,false,-4651765157952,-4651765042304⟩
    { al := (1017033/1024000), au := (508941/512000), zl := (999/1000), zu := 1,
      A := ⟨1092030868488,1092942475297⟩, Z := ⟨1098412116148,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨758376627520,758376645248⟩ : DyadicInterval 40),(⟨-5486878807552,-5486878672640⟩ : DyadicInterval 40),(⟨24992194325,24992231717⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨758833891648,758833909632⟩ : DyadicInterval 40),(⟨-5629759761280,-5629759626368⟩ : DyadicInterval 40),(⟨22374149399,22374186998⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨757828611712,757828629312⟩ : DyadicInterval 40),(⟨-5337060500736,-5337060365824⟩ : DyadicInterval 40),(⟨28055396331,28055433654⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨758833891648,758833909632⟩ : DyadicInterval 40),(⟨-5629759761280,-5629759626368⟩ : DyadicInterval 40),(⟨22374149399,22374186998⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,18610425803⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨18454679936,18454680000⟩ : DyadicInterval 40),(⟨-18769726784,-18769726720⟩ : DyadicInterval 40),(⟨761965875264,761965894594⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-315046784,0⟩ : DyadicInterval 40),(⟨762123383616,762280926272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨1091488134694,1092942489655⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨758104300608,758104318272⟩ : DyadicInterval 40),(⟨-5409869477696,-5409869342784⟩ : DyadicInterval 40),(⟨26523917838,26523955195⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨758833898880,758833916800⟩ : DyadicInterval 40),(⟨-5629762164416,-5629762029504⟩ : DyadicInterval 40),(⟨22374107718,22374145253⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4870928246464,-4651765042304⟩ : DyadicInterval 40),(⟨3088005904768,3197587526112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨758376627520,758833909632⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-5629759761280,-5486878672640⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e254_ok : ecellOkT e254 = true := by decide +kernel
theorem e254_pos {a z : ℝ} (ha1 : ((1017033/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((508941/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e254 e254_ok ha1 ha2 hz1 hz2 hz

-- box ['55341/204800', '138777/512000', '999/1000', '1999/2000']  interval_lower 342725/1099511627776
noncomputable def e255 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1396621359185,0,true,262992074688,262992074752⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨802401896367,0,false,-346359121024,-346359120960⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1397532965995,0,true,263709516992,263709517056⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨801490289557,0,false,-347608983552,-347608983488⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1396324249453,0,true,262758145600,262758145664⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨802699006099,0,false,-345952074176,-345952074112⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1397383955327,0,true,263592276352,263592276416⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨801639300225,0,false,-347404584640,-347404584576⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590085038,0,true,78454400,78454464⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433170514,0,false,-78460096,-78460032⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099669084205,0,true,157445120,157445184⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099354171347,0,false,-157467712,-157467648⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511605227,0,false,-22592,-22528⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622178,0,false,-5632,-5568⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1396472801113,0,true,262875113792,262875113856⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨802550454439,0,false,-346155574400,-346155574336⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1397458470309,0,true,263650905856,263650905920⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨801564785243,0,false,-347506792576,-347506792512⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1018773672184,0,false,-83855886720,-83855886656⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1019306983967,0,false,-83280460544,-83280460480⟩
    { al := (55341/204800), au := (138777/512000), zl := (999/1000), zu := (1999/2000),
      A := ⟨297109731409,298021338219⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨262992074688,262992074752⟩ : DyadicInterval 40),(⟨-346359121024,-346359120960⟩ : DyadicInterval 40),(⟨721477549977,721477569306⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨263709516992,263709517056⟩ : DyadicInterval 40),(⟨-347608983552,-347608983488⟩ : DyadicInterval 40),(⟨721224535239,721224554569⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨262758145600,262758145664⟩ : DyadicInterval 40),(⟨-345952074176,-345952074112⟩ : DyadicInterval 40),(⟨721559836023,721559855352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨263592276352,263592276416⟩ : DyadicInterval 40),(⟨-347404584640,-347404584576⟩ : DyadicInterval 40),(⟨721265948611,721265967940⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨78457262,157456429⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78454400,78454464⟩ : DyadicInterval 40),(⟨-78460096,-78460032⟩ : DyadicInterval 40),(⟨762123380801,762123400130⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157445120,157445184⟩ : DyadicInterval 40),(⟨-157467712,-157467648⟩ : DyadicInterval 40),(⟨762123372298,762123391628⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-22592,-5568⟩ : DyadicInterval 40),(⟨762123386400,762123414176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨296961173337,297946842533⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨262875113792,262875113856⟩ : DyadicInterval 40),(⟨-346155574400,-346155574336⟩ : DyadicInterval 40),(⟨721518704754,721518724084⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨263650905856,263650905920⟩ : DyadicInterval 40),(⟨-347506792576,-347506792512⟩ : DyadicInterval 40),(⟨721245241947,721245261277⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-83855886720,-83280460480⟩ : DyadicInterval 40),(⟨803763613856,804051346240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨262992074688,263709517056⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-347608983552,-346359120960⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e255_ok : ecellOkT e255 = true := by decide +kernel
theorem e255_pos {a z : ℝ} (ha1 : ((55341/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((138777/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e255 e255_ok ha1 ha2 hz1 hz2 hz

-- box ['138777/512000', '278403/1024000', '999/1000', '1999/2000']  interval_lower 10953599/274877906944
noncomputable def e256 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1397532965994,0,true,263709516992,263709517056⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨801490289558,0,false,-347608983552,-347608983488⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1398444572804,0,true,264426491520,264426491584⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨800578682748,0,false,-348860268544,-348860268480⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1397234944655,0,true,263475023168,263475023232⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨801788310897,0,false,-347200223744,-347200223680⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1398295106332,0,true,264308968896,264308968960⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨800728149220,0,false,-348655011008,-348655010944⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590353343,0,true,78722688,78722752⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432902209,0,false,-78728448,-78728384⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099669621416,0,true,157982272,157982336⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099353634136,0,false,-158005056,-158004992⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511605073,0,false,-22720,-22656⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622140,0,false,-5696,-5632⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1397383952130,0,true,263592273856,263592273920⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨801639303422,0,false,-347404580288,-347404580224⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1398369849224,0,true,264367739392,264367739456⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨800653406328,0,false,-348757648256,-348757648192⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1018278983872,0,false,-84389908800,-84389908736⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1018814053167,0,false,-83812306432,-83812306368⟩
    { al := (138777/512000), au := (278403/1024000), zl := (999/1000), zu := (1999/2000),
      A := ⟨298021338218,298932945028⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨263709516992,263709517056⟩ : DyadicInterval 40),(⟨-347608983552,-347608983488⟩ : DyadicInterval 40),(⟨721224535240,721224554569⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨264426491520,264426491584⟩ : DyadicInterval 40),(⟨-348860268544,-348860268480⟩ : DyadicInterval 40),(⟨720970704748,720970724077⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨263475023168,263475023232⟩ : DyadicInterval 40),(⟨-347200223744,-347200223680⟩ : DyadicInterval 40),(⟨721307340224,721307359554⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨264308968896,264308968960⟩ : DyadicInterval 40),(⟨-348655011008,-348655010944⟩ : DyadicInterval 40),(⟨721012378537,721012397866⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨78725567,157993640⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78722688,78722752⟩ : DyadicInterval 40),(⟨-78728448,-78728384⟩ : DyadicInterval 40),(⟨762123380795,762123400124⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157982272,157982336⟩ : DyadicInterval 40),(⟨-158005056,-158004992⟩ : DyadicInterval 40),(⟨762123372240,762123391570⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-22720,-5632⟩ : DyadicInterval 40),(⟨762123386432,762123414240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨297872324354,298858221448⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨263592273856,263592273920⟩ : DyadicInterval 40),(⟨-347404580288,-347404580224⟩ : DyadicInterval 40),(⟨721265949498,721265968828⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨264367739392,264367739456⟩ : DyadicInterval 40),(⟨-348757648256,-348757648192⟩ : DyadicInterval 40),(⟨720991541682,720991561012⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-84389908800,-83812306368⟩ : DyadicInterval 40),(⟨804029536800,804318357280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨263709516992,264426491584⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-348860268544,-347608983488⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e256_ok : ecellOkT e256 = true := by decide +kernel
theorem e256_pos {a z : ℝ} (ha1 : ((138777/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((278403/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e256 e256_ok ha1 ha2 hz1 hz2 hz

-- box ['138777/512000', '278403/1024000', '1999/2000', '1']  interval_lower 18246719/549755813888
noncomputable def e257 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1397532965994,0,true,263709516992,263709517056⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨801490289558,0,false,-347608983552,-347608983488⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1398444572804,0,true,264426491520,264426491584⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨800578682748,0,false,-348860268544,-348860268480⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1397383955324,0,true,263592276352,263592276416⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨801639300228,0,false,-347404584640,-347404584576⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590627009,0,true,78996352,78996416⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432628543,0,false,-79002112,-79002048⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622099,0,false,-5696,-5632⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1397458454439,0,true,263650893376,263650893440⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨801564801113,0,false,-347506770816,-347506770752⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1398444581437,0,true,264426498304,264426498368⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨800578674115,0,false,-348860280384,-348860280320⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1018238352871,0,false,-84433782016,-84433781952⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1018773680786,0,false,-83855877440,-83855877376⟩
    { al := (138777/512000), au := (278403/1024000), zl := (1999/2000), zu := 1,
      A := ⟨298021338218,298932945028⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨263709516992,263709517056⟩ : DyadicInterval 40),(⟨-347608983552,-347608983488⟩ : DyadicInterval 40),(⟨721224535240,721224554569⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨264426491520,264426491584⟩ : DyadicInterval 40),(⟨-348860268544,-348860268480⟩ : DyadicInterval 40),(⟨720970704748,720970724077⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨263592276352,263592276416⟩ : DyadicInterval 40),(⟨-347404584640,-347404584576⟩ : DyadicInterval 40),(⟨721265948611,721265967941⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨264426491520,264426491584⟩ : DyadicInterval 40),(⟨-348860268544,-348860268480⟩ : DyadicInterval 40),(⟨720970704748,720970724077⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,78999233⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78996352,78996416⟩ : DyadicInterval 40),(⟨-79002112,-79002048⟩ : DyadicInterval 40),(⟨762123380755,762123400085⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5696,0⟩ : DyadicInterval 40),(⟨762123383616,762123405728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨297946826663,298932953661⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨263650893376,263650893440⟩ : DyadicInterval 40),(⟨-347506770816,-347506770752⟩ : DyadicInterval 40),(⟨721245246357,721245265686⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨264426498304,264426498368⟩ : DyadicInterval 40),(⟨-348860280384,-348860280320⟩ : DyadicInterval 40),(⟨720970702336,720970721666⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-84433782016,-83855877376⟩ : DyadicInterval 40),(⟨804051322304,804340293888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨263709516992,264426491584⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-348860268544,-347608983488⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e257_ok : ecellOkT e257 = true := by decide +kernel
theorem e257_pos {a z : ℝ} (ha1 : ((138777/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((278403/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e257 e257_ok ha1 ha2 hz1 hz2 hz

-- box ['278403/1024000', '69813/256000', '999/1000', '1999/2000']  interval_lower 43953785/549755813888
noncomputable def e258 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1398444572803,0,true,264426491520,264426491584⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨800578682749,0,false,-348860268480,-348860268416⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1399356179612,0,true,265142998848,265142998912⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨799667075940,0,false,-350112979072,-350112979008⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1398145639857,0,true,264191433664,264191433728⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨800877615695,0,false,-348449791808,-348449791744⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1399206257337,0,true,265025194560,265025194624⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨799816998215,0,false,-349906860992,-349906860928⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590621927,0,true,78991296,78991360⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432633625,0,false,-78996992,-78996928⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099670159184,0,true,158519936,158520000⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099353096368,0,false,-158542848,-158542784⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511604918,0,false,-22912,-22848⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622101,0,false,-5696,-5632⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1398295103158,0,true,264308966400,264308966464⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨800728152394,0,false,-348655006656,-348655006592⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1399281228149,0,true,265084105856,265084105920⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨799742027403,0,false,-350009928512,-350009928448⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1017782784680,0,false,-84925822592,-84925822528⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1018319612243,0,false,-84346040256,-84346040192⟩
    { al := (278403/1024000), au := (69813/256000), zl := (999/1000), zu := (1999/2000),
      A := ⟨298932945027,299844551836⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨264426491520,264426491584⟩ : DyadicInterval 40),(⟨-348860268480,-348860268416⟩ : DyadicInterval 40),(⟨720970704724,720970724054⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨265142998848,265142998912⟩ : DyadicInterval 40),(⟨-350112979072,-350112979008⟩ : DyadicInterval 40),(⟨720716058064,720716077394⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨264191433664,264191433728⟩ : DyadicInterval 40),(⟨-348449791808,-348449791744⟩ : DyadicInterval 40),(⟨721054030426,721054049756⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨265025194560,265025194624⟩ : DyadicInterval 40),(⟨-349906860992,-349906860928⟩ : DyadicInterval 40),(⟨720757993196,720758012525⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨78994151,158531408⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78991296,78991360⟩ : DyadicInterval 40),(⟨-78996992,-78996928⟩ : DyadicInterval 40),(⟨762123380724,762123400053⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158519936,158520000⟩ : DyadicInterval 40),(⟨-158542848,-158542784⟩ : DyadicInterval 40),(⟨762123372150,762123391479⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-22912,-5632⟩ : DyadicInterval 40),(⟨762123386432,762123414336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨298783475382,299769600373⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨264308966400,264308966464⟩ : DyadicInterval 40),(⟨-348655006656,-348655006592⟩ : DyadicInterval 40),(⟨721012379424,721012398753⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨265084105856,265084105920⟩ : DyadicInterval 40),(⟨-350009928512,-350009928448⟩ : DyadicInterval 40),(⟨720737025706,720737045035⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-84925822592,-84346040192⟩ : DyadicInterval 40),(⟨804296403712,804586314176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨264426491520,265142998912⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-350112979072,-348860268416⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e258_ok : ecellOkT e258 = true := by decide +kernel
theorem e258_pos {a z : ℝ} (ha1 : ((278403/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((69813/256000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e258 e258_ok ha1 ha2 hz1 hz2 hz

-- box ['278403/1024000', '69813/256000', '1999/2000', '1']  interval_lower 80504313/1099511627776
noncomputable def e259 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1398444572803,0,true,264426491520,264426491584⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨800578682749,0,false,-348860268480,-348860268416⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1399356179612,0,true,265142998848,265142998912⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨799667075940,0,false,-350112979072,-350112979008⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1398295106330,0,true,264308968896,264308968960⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨800728149222,0,false,-348655011008,-348655010944⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590895915,0,true,79265280,79265344⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432359637,0,false,-79271040,-79270976⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622061,0,false,-5760,-5696⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1398369833338,0,true,264367726912,264367726976⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨800653422214,0,false,-348757626432,-348757626368⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1399356188261,0,true,265143005632,265143005696⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨799667067291,0,false,-350112990976,-350112990912⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1017741905490,0,false,-84969985344,-84969985280⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1018278992509,0,false,-84389899520,-84389899456⟩
    { al := (278403/1024000), au := (69813/256000), zl := (1999/2000), zu := 1,
      A := ⟨298932945027,299844551836⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨264426491520,264426491584⟩ : DyadicInterval 40),(⟨-348860268480,-348860268416⟩ : DyadicInterval 40),(⟨720970704724,720970724054⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨265142998848,265142998912⟩ : DyadicInterval 40),(⟨-350112979072,-350112979008⟩ : DyadicInterval 40),(⟨720716058064,720716077394⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨264308968896,264308968960⟩ : DyadicInterval 40),(⟨-348655011008,-348655010944⟩ : DyadicInterval 40),(⟨721012378537,721012397867⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨265142998848,265142998912⟩ : DyadicInterval 40),(⟨-350112979072,-350112979008⟩ : DyadicInterval 40),(⟨720716058064,720716077394⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,79268139⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79265280,79265344⟩ : DyadicInterval 40),(⟨-79271040,-79270976⟩ : DyadicInterval 40),(⟨762123380717,762123400046⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5760,0⟩ : DyadicInterval 40),(⟨762123383616,762123405760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨298858205562,299844560485⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨264367726912,264367726976⟩ : DyadicInterval 40),(⟨-348757626432,-348757626368⟩ : DyadicInterval 40),(⟨720991546101,720991565431⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨265143005632,265143005696⟩ : DyadicInterval 40),(⟨-350112990976,-350112990912⟩ : DyadicInterval 40),(⟨720716055657,720716074986⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-84969985344,-84389899456⟩ : DyadicInterval 40),(⟨804318333344,804608395552⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨264426491520,265142998912⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-350112979072,-348860268416⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e259_ok : ecellOkT e259 = true := by decide +kernel
theorem e259_pos {a z : ℝ} (ha1 : ((278403/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((69813/256000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e259 e259_ok ha1 ha2 hz1 hz2 hz

-- box ['69813/256000', '280101/1024000', '999/1000', '1999/2000']  interval_lower 8289281/68719476736
noncomputable def e260 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1399356179611,0,true,265142998848,265142998912⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨799667075941,0,false,-350112979072,-350112979008⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1400267786421,0,true,265859039488,265859039552⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨798755469131,0,false,-351367118528,-351367118464⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1399056335059,0,true,264907377664,264907377728⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨799966920493,0,false,-349700781568,-349700781504⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1400117408342,0,true,265740953984,265740954048⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨798905847210,0,false,-351160137984,-351160137920⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590890788,0,true,79260096,79260160⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432364764,0,false,-79265920,-79265856⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099670697514,0,true,159058176,159058240⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099352558038,0,false,-159081280,-159081216⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511604762,0,false,-23040,-22976⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622062,0,false,-5760,-5696⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1399206254185,0,true,265025192064,265025192128⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨799817001367,0,false,-349906856704,-349906856640⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1400192607058,0,true,265800005952,265800006016⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨798830648494,0,false,-351263636672,-351263636608⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1017285074624,0,false,-85463630720,-85463630656⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1017823661202,0,false,-84881664576,-84881664512⟩
    { al := (69813/256000), au := (280101/1024000), zl := (999/1000), zu := (1999/2000),
      A := ⟨299844551835,300756158645⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨265142998848,265142998912⟩ : DyadicInterval 40),(⟨-350112979072,-350112979008⟩ : DyadicInterval 40),(⟨720716058065,720716077394⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨265859039488,265859039552⟩ : DyadicInterval 40),(⟨-351367118528,-351367118464⟩ : DyadicInterval 40),(⟨720460594904,720460614234⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨264907377664,264907377728⟩ : DyadicInterval 40),(⟨-349700781568,-349700781504⟩ : DyadicInterval 40),(⟨720799906244,720799925573⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨265740953984,265740954048⟩ : DyadicInterval 40),(⟨-351160137984,-351160137920⟩ : DyadicInterval 40),(⟨720502792223,720502811553⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨79263012,159069738⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79260096,79260160⟩ : DyadicInterval 40),(⟨-79265920,-79265856⟩ : DyadicInterval 40),(⟨762123380749,762123400079⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159058176,159058240⟩ : DyadicInterval 40),(⟨-159081280,-159081216⟩ : DyadicInterval 40),(⟨762123372090,762123391420⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-23040,-5696⟩ : DyadicInterval 40),(⟨762123386464,762123414400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨299694626409,300680979282⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨265025192064,265025192128⟩ : DyadicInterval 40),(⟨-349906856704,-349906856640⟩ : DyadicInterval 40),(⟨720757994106,720758013435⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨265800005952,265800006016⟩ : DyadicInterval 40),(⟨-351263636672,-351263636608⟩ : DyadicInterval 40),(⟨720481693595,720481712924⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-85463630720,-84881664512⟩ : DyadicInterval 40),(⟨804564215872,804855218240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨265142998848,265859039552⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-351367118528,-350112979008⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e260_ok : ecellOkT e260 = true := by decide +kernel
theorem e260_pos {a z : ℝ} (ha1 : ((69813/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((280101/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e260 e260_ok ha1 ha2 hz1 hz2 hz

-- box ['69813/256000', '280101/1024000', '1999/2000', '1']  interval_lower 125142243/1099511627776
noncomputable def e261 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1399356179611,0,true,265142998848,265142998912⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨799667075941,0,false,-350112979072,-350112979008⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1400267786421,0,true,265859039488,265859039552⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨798755469131,0,false,-351367118528,-351367118464⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1399206257335,0,true,265025194560,265025194624⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨799816998217,0,false,-349906860992,-349906860928⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591165104,0,true,79534400,79534464⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432090448,0,false,-79540224,-79540160⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622022,0,false,-5760,-5696⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1399281212240,0,true,265084093376,265084093440⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨799742043312,0,false,-350009906624,-350009906560⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1400267795063,0,true,265859046272,265859046336⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨798755460489,0,false,-351367130432,-351367130368⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1017243946492,0,false,-85508084096,-85508084032⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1017782793356,0,false,-84925813248,-84925813184⟩
    { al := (69813/256000), au := (280101/1024000), zl := (1999/2000), zu := 1,
      A := ⟨299844551835,300756158645⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨265142998848,265142998912⟩ : DyadicInterval 40),(⟨-350112979072,-350112979008⟩ : DyadicInterval 40),(⟨720716058065,720716077394⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨265859039488,265859039552⟩ : DyadicInterval 40),(⟨-351367118528,-351367118464⟩ : DyadicInterval 40),(⟨720460594904,720460614234⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨265025194560,265025194624⟩ : DyadicInterval 40),(⟨-349906860992,-349906860928⟩ : DyadicInterval 40),(⟨720757993196,720758012526⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨265859039488,265859039552⟩ : DyadicInterval 40),(⟨-351367118528,-351367118464⟩ : DyadicInterval 40),(⟨720460594904,720460614234⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,79537328⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79534400,79534464⟩ : DyadicInterval 40),(⟨-79540224,-79540160⟩ : DyadicInterval 40),(⟨762123380710,762123400039⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5760,0⟩ : DyadicInterval 40),(⟨762123383616,762123405760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨299769584464,300756167287⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨265084093376,265084093440⟩ : DyadicInterval 40),(⟨-350009906624,-350009906560⟩ : DyadicInterval 40),(⟨720737030136,720737049466⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨265859046272,265859046336⟩ : DyadicInterval 40),(⟨-351367130432,-351367130368⟩ : DyadicInterval 40),(⟨720460592482,720460611812⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-85508084096,-84925813184⟩ : DyadicInterval 40),(⟨804586290208,804877444928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨265142998848,265859039552⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-351367118528,-350112979008⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e261_ok : ecellOkT e261 = true := by decide +kernel
theorem e261_pos {a z : ℝ} (ha1 : ((69813/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((280101/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e261 e261_ok ha1 ha2 hz1 hz2 hz

-- box ['280101/1024000', '5619/20480', '999/1000', '1999/2000']  interval_lower 44495537/274877906944
noncomputable def e262 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1400267786420,0,true,265859039488,265859039552⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨798755469132,0,false,-351367118528,-351367118464⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1401179393229,0,true,266574614144,266574614208⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨797843862323,0,false,-352622690176,-352622690112⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1399967030261,0,true,265622855808,265622855872⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨799056225291,0,false,-350953196288,-350953196224⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1401028559347,0,true,266456247808,266456247872⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨797994696205,0,false,-352414845056,-352414844992⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591159930,0,true,79529216,79529280⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432095622,0,false,-79535040,-79534976⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099671236406,0,true,159596992,159597056⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099352019146,0,false,-159620224,-159620160⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511604606,0,false,-23232,-23168⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622024,0,false,-5760,-5696⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1400117405208,0,true,265740951552,265740951616⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨798905850344,0,false,-351160133632,-351160133568⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1401103985977,0,true,266515440192,266515440256⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨797919269575,0,false,-352518776064,-352518776000⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1016785853689,0,false,-86003335872,-86003335808⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1017326200044,0,false,-85419182080,-85419182016⟩
    { al := (280101/1024000), au := (5619/20480), zl := (999/1000), zu := (1999/2000),
      A := ⟨300756158644,301667765453⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨265859039488,265859039552⟩ : DyadicInterval 40),(⟨-351367118528,-351367118464⟩ : DyadicInterval 40),(⟨720460594904,720460614234⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨266574614144,266574614208⟩ : DyadicInterval 40),(⟨-352622690176,-352622690112⟩ : DyadicInterval 40),(⟨720204314805,720204334134⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨265622855808,265622855872⟩ : DyadicInterval 40),(⟨-350953196288,-350953196224⟩ : DyadicInterval 40),(⟨720544967268,720544986598⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨266456247808,266456247872⟩ : DyadicInterval 40),(⟨-352414845056,-352414844992⟩ : DyadicInterval 40),(⟨720246775133,720246794462⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨79532154,159608630⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79529216,79529280⟩ : DyadicInterval 40),(⟨-79535040,-79534976⟩ : DyadicInterval 40),(⟨762123380710,762123400040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159596992,159597056⟩ : DyadicInterval 40),(⟨-159620224,-159620160⟩ : DyadicInterval 40),(⟨762123371998,762123391328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-23232,-5696⟩ : DyadicInterval 40),(⟨762123386464,762123414496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨300605777432,301592358201⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨265740951552,265740951616⟩ : DyadicInterval 40),(⟨-351160133632,-351160133568⟩ : DyadicInterval 40),(⟨720502793070,720502812399⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨266515440192,266515440256⟩ : DyadicInterval 40),(⟨-352518776064,-352518776000⟩ : DyadicInterval 40),(⟨720225545028,720225564358⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-86003335872,-85419182016⟩ : DyadicInterval 40),(⟨804832974624,805125070816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨265859039488,266574614208⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-352622690176,-351367118464⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e262_ok : ecellOkT e262 = true := by decide +kernel
theorem e262_pos {a z : ℝ} (ha1 : ((280101/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((5619/20480 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e262 e262_ok ha1 ha2 hz1 hz2 hz

-- box ['280101/1024000', '5619/20480', '1999/2000', '1']  interval_lower 170411817/1099511627776
noncomputable def e263 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1400267786420,0,true,265859039488,265859039552⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨798755469132,0,false,-351367118528,-351367118464⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1401179393229,0,true,266574614144,266574614208⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨797843862323,0,false,-352622690176,-352622690112⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1400117408340,0,true,265740953984,265740954048⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨798905847212,0,false,-351160137920,-351160137856⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591434573,0,true,79803840,79803904⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431820979,0,false,-79809728,-79809664⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621983,0,false,-5824,-5760⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1400192591134,0,true,265799993408,265799993472⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨798830664418,0,false,-351263614784,-351263614720⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1401179401863,0,true,266574620928,266574620992⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨797843853689,0,false,-352622702080,-352622702016⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1016744475866,0,false,-86048081088,-86048081024⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1017285083334,0,false,-85463621312,-85463621248⟩
    { al := (280101/1024000), au := (5619/20480), zl := (1999/2000), zu := 1,
      A := ⟨300756158644,301667765453⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨265859039488,265859039552⟩ : DyadicInterval 40),(⟨-351367118528,-351367118464⟩ : DyadicInterval 40),(⟨720460594904,720460614234⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨266574614144,266574614208⟩ : DyadicInterval 40),(⟨-352622690176,-352622690112⟩ : DyadicInterval 40),(⟨720204314805,720204334134⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨265740953984,265740954048⟩ : DyadicInterval 40),(⟨-351160137920,-351160137856⟩ : DyadicInterval 40),(⟨720502792201,720502811530⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨266574614144,266574614208⟩ : DyadicInterval 40),(⟨-352622690176,-352622690112⟩ : DyadicInterval 40),(⟨720204314805,720204334134⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,79806797⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79803840,79803904⟩ : DyadicInterval 40),(⟨-79809728,-79809664⟩ : DyadicInterval 40),(⟨762123380703,762123400032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5824,0⟩ : DyadicInterval 40),(⟨762123383616,762123405792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨300680963358,301667774087⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨265799993408,265799993472⟩ : DyadicInterval 40),(⟨-351263614784,-351263614720⟩ : DyadicInterval 40),(⟨720481698099,720481717429⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨266574620928,266574620992⟩ : DyadicInterval 40),(⟨-352622702080,-352622702016⟩ : DyadicInterval 40),(⟨720204312370,720204331700⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-86048081088,-85463621248⟩ : DyadicInterval 40),(⟨804855194240,805147443424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨265859039488,266574614208⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-352622690176,-351367118464⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e263_ok : ecellOkT e263 = true := by decide +kernel
theorem e263_pos {a z : ℝ} (ha1 : ((280101/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((5619/20480 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e263 e263_ok ha1 ha2 hz1 hz2 hz

-- box ['5619/20480', '281799/1024000', '999/1000', '1999/2000']  interval_lower 223974419/1099511627776
noncomputable def e264 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1401179393228,0,true,266574614144,266574614208⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨797843862324,0,false,-352622690176,-352622690112⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1402091000038,0,true,267289723456,267289723520⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨796932255514,0,false,-353879697216,-353879697152⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1400877725462,0,true,266337868672,266337868736⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨798145530090,0,false,-352207039232,-352207039168⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1401939710353,0,true,267171076544,267171076608⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨797083545199,0,false,-353670985600,-353670985536⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591429353,0,true,79798656,79798720⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431826199,0,false,-79804480,-79804416⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099671775864,0,true,160136384,160136448⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099351479688,0,false,-160159808,-160159744⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511604449,0,false,-23360,-23296⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621985,0,false,-5824,-5760⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1401028556231,0,true,266456245376,266456245440⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨797994699321,0,false,-352414840768,-352414840704⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1402015364899,0,true,267230409216,267230409280⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨797007890653,0,false,-353775349824,-353775349760⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1016285121878,0,false,-86544940608,-86544940544⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1016827228769,0,false,-85958595392,-85958595328⟩
    { al := (5619/20480), au := (281799/1024000), zl := (999/1000), zu := (1999/2000),
      A := ⟨301667765452,302579372262⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨266574614144,266574614208⟩ : DyadicInterval 40),(⟨-352622690176,-352622690112⟩ : DyadicInterval 40),(⟨720204314805,720204334135⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨267289723456,267289723520⟩ : DyadicInterval 40),(⟨-353879697216,-353879697152⟩ : DyadicInterval 40),(⟨719947217318,719947236647⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨266337868672,266337868736⟩ : DyadicInterval 40),(⟨-352207039232,-352207039168⟩ : DyadicInterval 40),(⟨720289213127,720289232456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨267171076544,267171076608⟩ : DyadicInterval 40),(⟨-353670985600,-353670985536⟩ : DyadicInterval 40),(⟨719989941627,719989960956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨79801577,160148088⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79798656,79798720⟩ : DyadicInterval 40),(⟨-79804480,-79804416⟩ : DyadicInterval 40),(⟨762123380671,762123400001⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160136384,160136448⟩ : DyadicInterval 40),(⟨-160159808,-160159744⟩ : DyadicInterval 40),(⟨762123371937,762123391267⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-23360,-5760⟩ : DyadicInterval 40),(⟨762123386496,762123414560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨301516928455,302503737123⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨266456245376,266456245440⟩ : DyadicInterval 40),(⟨-352414840768,-352414840704⟩ : DyadicInterval 40),(⟨720246776003,720246795332⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨267230409216,267230409280⟩ : DyadicInterval 40),(⟨-353775349824,-353775349760⟩ : DyadicInterval 40),(⟨719968579537,719968598866⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-86544940608,-85958595328⟩ : DyadicInterval 40),(⟨805102681280,805395873184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨266574614144,267289723520⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-353879697216,-352622690112⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e264_ok : ecellOkT e264 = true := by decide +kernel
theorem e264_pos {a z : ℝ} (ha1 : ((5619/20480 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((281799/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e264 e264_ok ha1 ha2 hz1 hz2 hz

-- box ['5619/20480', '281799/1024000', '1999/2000', '1']  interval_lower 27039867/137438953472
noncomputable def e265 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1401179393228,0,true,266574614144,266574614208⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨797843862324,0,false,-352622690176,-352622690112⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1402091000038,0,true,267289723456,267289723520⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨796932255514,0,false,-353879697216,-353879697152⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1401028559345,0,true,266456247808,266456247872⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨797994696207,0,false,-352414845056,-352414844992⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591704326,0,true,80073600,80073664⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431551226,0,false,-80079488,-80079424⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621944,0,false,-5888,-5824⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1401103970028,0,true,266515427648,266515427712⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨797919285524,0,false,-352518754048,-352518753984⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1402091008682,0,true,267289730240,267289730304⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨796932246870,0,false,-353879709120,-353879709056⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1016243493600,0,false,-86589978880,-86589978816⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1016785862439,0,false,-86003326400,-86003326336⟩
    { al := (5619/20480), au := (281799/1024000), zl := (1999/2000), zu := 1,
      A := ⟨301667765452,302579372262⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨266574614144,266574614208⟩ : DyadicInterval 40),(⟨-352622690176,-352622690112⟩ : DyadicInterval 40),(⟨720204314805,720204334135⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨267289723456,267289723520⟩ : DyadicInterval 40),(⟨-353879697216,-353879697152⟩ : DyadicInterval 40),(⟨719947217318,719947236647⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨266456247808,266456247872⟩ : DyadicInterval 40),(⟨-352414845056,-352414844992⟩ : DyadicInterval 40),(⟨720246775133,720246794463⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨267289723456,267289723520⟩ : DyadicInterval 40),(⟨-353879697216,-353879697152⟩ : DyadicInterval 40),(⟨719947217318,719947236647⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,80076550⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80073600,80073664⟩ : DyadicInterval 40),(⟨-80079488,-80079424⟩ : DyadicInterval 40),(⟨762123380663,762123399993⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5888,0⟩ : DyadicInterval 40),(⟨762123383616,762123405824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨301592342252,302579380906⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨266515427648,266515427712⟩ : DyadicInterval 40),(⟨-352518754048,-352518753984⟩ : DyadicInterval 40),(⟨720225549522,720225568851⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨267289730240,267289730304⟩ : DyadicInterval 40),(⟨-353879709120,-353879709056⟩ : DyadicInterval 40),(⟨719947214865,719947234194⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-86589978880,-86003326336⟩ : DyadicInterval 40),(⟨805125046784,805418392320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨266574614144,267289723520⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-353879697216,-352622690112⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e265_ok : ecellOkT e265 = true := by decide +kernel
theorem e265_pos {a z : ℝ} (ha1 : ((5619/20480 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((281799/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e265 e265_ok ha1 ha2 hz1 hz2 hz

-- box ['281799/1024000', '35331/128000', '999/1000', '1999/2000']  interval_lower 270610365/1099511627776
noncomputable def e266 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1402091000037,0,true,267289723456,267289723520⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨796932255515,0,false,-353879697216,-353879697152⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1403002606846,0,true,268004367936,268004368000⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨796020648706,0,false,-355138142912,-355138142848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1401788420664,0,true,267052416832,267052416896⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨797234834888,0,false,-353462313664,-353462313600⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1402850861357,0,true,267885440896,267885440960⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨796172394195,0,false,-354928562880,-354928562816⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591699057,0,true,80068352,80068416⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431556495,0,false,-80074240,-80074176⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099672315889,0,true,160676352,160676416⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099350939663,0,false,-160699904,-160699840⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511604292,0,false,-23488,-23424⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621945,0,false,-5888,-5824⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1401939707256,0,true,267171074112,267171074176⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨797083548296,0,false,-353670981376,-353670981312⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1402926743822,0,true,267944913600,267944913664⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨796096511730,0,false,-355033361344,-355033361280⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1015782879193,0,false,-87088447680,-87088447616⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1016326747374,0,false,-86499907200,-86499907136⟩
    { al := (281799/1024000), au := (35331/128000), zl := (999/1000), zu := (1999/2000),
      A := ⟨302579372261,303490979070⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨267289723456,267289723520⟩ : DyadicInterval 40),(⟨-353879697216,-353879697152⟩ : DyadicInterval 40),(⟨719947217318,719947236648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨268004367936,268004368000⟩ : DyadicInterval 40),(⟨-355138142912,-355138142848⟩ : DyadicInterval 40),(⟨719689302091,719689321421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨267052416832,267052416896⟩ : DyadicInterval 40),(⟨-353462313664,-353462313600⟩ : DyadicInterval 40),(⟨720032643438,720032662768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨267885440896,267885440960⟩ : DyadicInterval 40),(⟨-354928562880,-354928562816⟩ : DyadicInterval 40),(⟨719732291236,719732310565⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨80071281,160688113⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80068352,80068416⟩ : DyadicInterval 40),(⟨-80074240,-80074176⟩ : DyadicInterval 40),(⟨762123380664,762123399994⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160676352,160676416⟩ : DyadicInterval 40),(⟨-160699904,-160699840⟩ : DyadicInterval 40),(⟨762123371843,762123391173⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-23488,-5824⟩ : DyadicInterval 40),(⟨762123386528,762123414624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨302428079480,303415116046⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨267171074112,267171074176⟩ : DyadicInterval 40),(⟨-353670981376,-353670981312⟩ : DyadicInterval 40),(⟨719989942520,719989961850⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨267944913600,267944913664⟩ : DyadicInterval 40),(⟨-355033361344,-355033361280⟩ : DyadicInterval 40),(⟨719710796776,719710816105⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-87088447680,-86499907136⟩ : DyadicInterval 40),(⟨805373337184,805667626720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨267289723456,268004368000⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-355138142912,-353879697152⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e266_ok : ecellOkT e266 = true := by decide +kernel
theorem e266_pos {a z : ℝ} (ha1 : ((281799/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((35331/128000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e266 e266_ok ha1 ha2 hz1 hz2 hz

-- box ['281799/1024000', '35331/128000', '1999/2000', '1']  interval_lower 262869261/1099511627776
noncomputable def e267 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1402091000037,0,true,267289723456,267289723520⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨796932255515,0,false,-353879697216,-353879697152⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1403002606846,0,true,268004367936,268004368000⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨796020648706,0,false,-355138142912,-355138142848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1401939710350,0,true,267171076544,267171076608⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨797083545202,0,false,-353670985600,-353670985536⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591974361,0,true,80343616,80343680⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431281191,0,false,-80349568,-80349504⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621904,0,false,-5888,-5824⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1402015348929,0,true,267230396672,267230396736⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨797007906623,0,false,-353775327808,-353775327744⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1403002615498,0,true,268004374720,268004374784⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨796020640054,0,false,-355138154880,-355138154816⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1015740999706,0,false,-87133780160,-87133780096⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1016285130667,0,false,-86544931072,-86544931008⟩
    { al := (281799/1024000), au := (35331/128000), zl := (1999/2000), zu := 1,
      A := ⟨302579372261,303490979070⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨267289723456,267289723520⟩ : DyadicInterval 40),(⟨-353879697216,-353879697152⟩ : DyadicInterval 40),(⟨719947217318,719947236648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨268004367936,268004368000⟩ : DyadicInterval 40),(⟨-355138142912,-355138142848⟩ : DyadicInterval 40),(⟨719689302091,719689321421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨267171076544,267171076608⟩ : DyadicInterval 40),(⟨-353670985600,-353670985536⟩ : DyadicInterval 40),(⟨719989941627,719989960957⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨268004367936,268004368000⟩ : DyadicInterval 40),(⟨-355138142912,-355138142848⟩ : DyadicInterval 40),(⟨719689302091,719689321421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,80346585⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80343616,80343680⟩ : DyadicInterval 40),(⟨-80349568,-80349504⟩ : DyadicInterval 40),(⟨762123380656,762123399985⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5888,0⟩ : DyadicInterval 40),(⟨762123383616,762123405824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨302503721153,303490987722⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨267230396672,267230396736⟩ : DyadicInterval 40),(⟨-353775327808,-353775327744⟩ : DyadicInterval 40),(⟨719968584065,719968603395⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨268004374720,268004374784⟩ : DyadicInterval 40),(⟨-355138154880,-355138154816⟩ : DyadicInterval 40),(⟨719689299643,719689318973⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-87133780160,-86544931008⟩ : DyadicInterval 40),(⟨805395849120,805690292960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨267289723456,268004368000⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-355138142912,-353879697152⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e267_ok : ecellOkT e267 = true := by decide +kernel
theorem e267_pos {a z : ℝ} (ha1 : ((281799/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((35331/128000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e267 e267_ok ha1 ha2 hz1 hz2 hz

-- box ['35331/128000', '283497/1024000', '999/1000', '1999/2000']  interval_lower 317896205/1099511627776
noncomputable def e268 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1403002606845,0,true,268004367936,268004368000⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨796020648707,0,false,-355138142912,-355138142848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1403914213655,0,true,268718548224,268718548288⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨795109041897,0,false,-356398030656,-356398030592⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1402699115865,0,true,267766500992,267766501056⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨796324139687,0,false,-354719022784,-354719022720⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1403762012363,0,true,268599341376,268599341440⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨795261243189,0,false,-356187580160,-356187580096⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591969046,0,true,80338304,80338368⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431286506,0,false,-80344256,-80344192⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099672856483,0,true,161216832,161216896⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099350399069,0,false,-161240576,-161240512⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511604133,0,false,-23680,-23616⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621906,0,false,-5888,-5824⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1402850858293,0,true,267885438464,267885438528⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨796172397259,0,false,-354928558656,-354928558592⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1403838122740,0,true,268658954048,268658954112⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨795185132812,0,false,-356292813824,-356292813760⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1015279125638,0,false,-87633859776,-87633859712⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1015824755854,0,false,-87043120192,-87043120128⟩
    { al := (35331/128000), au := (283497/1024000), zl := (999/1000), zu := (1999/2000),
      A := ⟨303490979069,304402585879⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨268004367936,268004368000⟩ : DyadicInterval 40),(⟨-355138142912,-355138142848⟩ : DyadicInterval 40),(⟨719689302091,719689321421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨268718548224,268718548288⟩ : DyadicInterval 40),(⟨-356398030656,-356398030592⟩ : DyadicInterval 40),(⟨719430568731,719430588060⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨267766500992,267766501056⟩ : DyadicInterval 40),(⟨-354719022784,-354719022720⟩ : DyadicInterval 40),(⟨719775257711,719775277041⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨268599341376,268599341440⟩ : DyadicInterval 40),(⟨-356187580160,-356187580096⟩ : DyadicInterval 40),(⟨719473823604,719473842934⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨80341270,161228707⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80338304,80338368⟩ : DyadicInterval 40),(⟨-80344256,-80344192⟩ : DyadicInterval 40),(⟨762123380657,762123399986⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161216832,161216896⟩ : DyadicInterval 40),(⟨-161240576,-161240512⟩ : DyadicInterval 40),(⟨762123371781,762123391111⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-23680,-5824⟩ : DyadicInterval 40),(⟨762123386528,762123414720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨303339230517,304326494964⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨267885438464,267885438528⟩ : DyadicInterval 40),(⟨-354928558656,-354928558592⟩ : DyadicInterval 40),(⟨719732292126,719732311456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨268658954048,268658954112⟩ : DyadicInterval 40),(⟨-356292813824,-356292813760⟩ : DyadicInterval 40),(⟨719452196245,719452215575⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-87633859776,-87043120128⟩ : DyadicInterval 40),(⟨805644943680,805940332768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨268004367936,268718548288⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-356398030656,-355138142848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e268_ok : ecellOkT e268 = true := by decide +kernel
theorem e268_pos {a z : ℝ} (ha1 : ((35331/128000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((283497/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e268 e268_ok ha1 ha2 hz1 hz2 hz

-- box ['35331/128000', '283497/1024000', '1999/2000', '1']  interval_lower 310068463/1099511627776
noncomputable def e269 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1403002606845,0,true,268004367936,268004368000⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨796020648707,0,false,-355138142912,-355138142848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1403914213655,0,true,268718548224,268718548288⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨795109041897,0,false,-356398030656,-356398030592⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1402850861355,0,true,267885440896,267885440960⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨796172394197,0,false,-354928562880,-354928562816⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592244683,0,true,80613888,80613952⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431010869,0,false,-80619904,-80619840⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621865,0,false,-5952,-5888⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1402926727835,0,true,267944901120,267944901184⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨796096527717,0,false,-355033339264,-355033339200⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1403914222310,0,true,268718554944,268718555008⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨795109033242,0,false,-356398042624,-356398042560⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1015236994185,0,false,-87679487616,-87679487552⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1015782888018,0,false,-87088438144,-87088438080⟩
    { al := (35331/128000), au := (283497/1024000), zl := (1999/2000), zu := 1,
      A := ⟨303490979069,304402585879⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨268004367936,268004368000⟩ : DyadicInterval 40),(⟨-355138142912,-355138142848⟩ : DyadicInterval 40),(⟨719689302091,719689321421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨268718548224,268718548288⟩ : DyadicInterval 40),(⟨-356398030656,-356398030592⟩ : DyadicInterval 40),(⟨719430568731,719430588060⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨267885440896,267885440960⟩ : DyadicInterval 40),(⟨-354928562880,-354928562816⟩ : DyadicInterval 40),(⟨719732291237,719732310566⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨268718548224,268718548288⟩ : DyadicInterval 40),(⟨-356398030656,-356398030592⟩ : DyadicInterval 40),(⟨719430568731,719430588060⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,80616907⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80613888,80613952⟩ : DyadicInterval 40),(⟨-80619904,-80619840⟩ : DyadicInterval 40),(⟨762123380648,762123399978⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5952,0⟩ : DyadicInterval 40),(⟨762123383616,762123405856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨303415100059,304402594534⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨267944901120,267944901184⟩ : DyadicInterval 40),(⟨-355033339264,-355033339200⟩ : DyadicInterval 40),(⟨719710801273,719710820603⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨268718554944,268718555008⟩ : DyadicInterval 40),(⟨-356398042624,-356398042560⟩ : DyadicInterval 40),(⟨719430566307,719430585637⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-87679487616,-87088438080⟩ : DyadicInterval 40),(⟨805667602656,805963146688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨268004367936,268718548288⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-356398030656,-355138142848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e269_ok : ecellOkT e269 = true := by decide +kernel
theorem e269_pos {a z : ℝ} (ha1 : ((35331/128000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((283497/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e269 e269_ok ha1 ha2 hz1 hz2 hz

-- box ['283497/1024000', '142173/512000', '999/1000', '1999/2000']  interval_lower 182918533/549755813888
noncomputable def e270 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1403914213654,0,true,268718548224,268718548288⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨795109041898,0,false,-356398030656,-356398030592⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1404825820464,0,true,269432264896,269432264960⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨794197435088,0,false,-357659363712,-357659363648⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1403609811068,0,true,268480121600,268480121664⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨795413444484,0,false,-355977169984,-355977169920⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1404673163368,0,true,269312778624,269312778688⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨794350092184,0,false,-357448040768,-357448040704⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592239321,0,true,80608576,80608640⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431016231,0,false,-80614528,-80614464⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099673397652,0,true,161757952,161758016⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099349857900,0,false,-161781824,-161781760⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511603974,0,false,-23808,-23744⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621866,0,false,-5952,-5888⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1403762009314,0,true,268599339008,268599339072⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨795261246238,0,false,-356187576000,-356187575936⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1404749501653,0,true,269372531008,269372531072⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨794273753899,0,false,-357553710656,-357553710592⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1014773861211,0,false,-88181179648,-88181179584⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1015321254226,0,false,-87588236992,-87588236928⟩
    { al := (283497/1024000), au := (142173/512000), zl := (999/1000), zu := (1999/2000),
      A := ⟨304402585878,305314192688⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨268718548224,268718548288⟩ : DyadicInterval 40),(⟨-356398030656,-356398030592⟩ : DyadicInterval 40),(⟨719430568731,719430588061⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨269432264896,269432264960⟩ : DyadicInterval 40),(⟨-357659363712,-357659363648⟩ : DyadicInterval 40),(⟨719171016832,719171036162⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨268480121600,268480121664⟩ : DyadicInterval 40),(⟨-355977169984,-355977169920⟩ : DyadicInterval 40),(⟨719517055681,719517075011⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨269312778624,269312778688⟩ : DyadicInterval 40),(⟨-357448040768,-357448040704⟩ : DyadicInterval 40),(⟨719214538312,719214557642⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨80611545,161769876⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80608576,80608640⟩ : DyadicInterval 40),(⟨-80614528,-80614464⟩ : DyadicInterval 40),(⟨762123380617,762123399947⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161757952,161758016⟩ : DyadicInterval 40),(⟨-161781824,-161781760⟩ : DyadicInterval 40),(⟨762123371686,762123391016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-23808,-5888⟩ : DyadicInterval 40),(⟨762123386560,762123414784⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨304250381538,305237873877⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨268599339008,268599339072⟩ : DyadicInterval 40),(⟨-356187576000,-356187575936⟩ : DyadicInterval 40),(⟨719473824478,719473843807⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨269372531008,269372531072⟩ : DyadicInterval 40),(⟨-357553710656,-357553710592⟩ : DyadicInterval 40),(⟨719192777669,719192796999⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-88181179648,-87588236928⟩ : DyadicInterval 40),(⟨805917502080,806213992704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨268718548224,269432264960⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-357659363712,-356398030592⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e270_ok : ecellOkT e270 = true := by decide +kernel
theorem e270_pos {a z : ℝ} (ha1 : ((283497/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((142173/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e270 e270_ok ha1 ha2 hz1 hz2 hz

-- box ['283497/1024000', '142173/512000', '1999/2000', '1']  interval_lower 357921603/1099511627776
noncomputable def e271 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1403914213654,0,true,268718548224,268718548288⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨795109041898,0,false,-356398030656,-356398030592⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1404825820464,0,true,269432264896,269432264960⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨794197435088,0,false,-357659363712,-357659363648⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1403762012361,0,true,268599341376,268599341440⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨795261243191,0,false,-356187580160,-356187580096⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592515292,0,true,80884480,80884544⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430740260,0,false,-80890496,-80890432⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621825,0,false,-5952,-5888⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1403838106733,0,true,268658941504,268658941568⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨795185148819,0,false,-356292791744,-356292791680⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1404825829115,0,true,269432271680,269432271744⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨794197426437,0,false,-357659375680,-357659375616⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1014731477039,0,false,-88227104000,-88227103936⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1015279134500,0,false,-87633850176,-87633850112⟩
    { al := (283497/1024000), au := (142173/512000), zl := (1999/2000), zu := 1,
      A := ⟨304402585878,305314192688⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨268718548224,268718548288⟩ : DyadicInterval 40),(⟨-356398030656,-356398030592⟩ : DyadicInterval 40),(⟨719430568731,719430588061⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨269432264896,269432264960⟩ : DyadicInterval 40),(⟨-357659363712,-357659363648⟩ : DyadicInterval 40),(⟨719171016832,719171036162⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨268599341376,268599341440⟩ : DyadicInterval 40),(⟨-356187580160,-356187580096⟩ : DyadicInterval 40),(⟨719473823605,719473842934⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨269432264896,269432264960⟩ : DyadicInterval 40),(⟨-357659363712,-357659363648⟩ : DyadicInterval 40),(⟨719171016832,719171036162⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,80887516⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80884480,80884544⟩ : DyadicInterval 40),(⟨-80890496,-80890432⟩ : DyadicInterval 40),(⟨762123380609,762123399938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5952,0⟩ : DyadicInterval 40),(⟨762123383616,762123405856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨304326478957,305314201339⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨268658941504,268658941568⟩ : DyadicInterval 40),(⟨-356292791744,-356292791680⟩ : DyadicInterval 40),(⟨719452200818,719452220148⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨269432271680,269432271744⟩ : DyadicInterval 40),(⟨-357659375680,-357659375616⟩ : DyadicInterval 40),(⟨719171014353,719171033683⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-88227104000,-87633850112⟩ : DyadicInterval 40),(⟨805940308672,806236954880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨268718548224,269432264960⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-357659363712,-356398030592⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e271_ok : ecellOkT e271 = true := by decide +kernel
theorem e271_pos {a z : ℝ} (ha1 : ((283497/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((142173/512000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e271 e271_ok ha1 ha2 hz1 hz2 hz

-- box ['508941/512000', '1018731/1024000', '999/1000', '1999/2000']  interval_lower 391274281432145/274877906944
noncomputable def e272 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2192454103072,0,true,758833891648,758833909632⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨6569152480,7,false,-5629759761088,-5629759626176⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2193365709882,0,true,759290965760,759290983872⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨5657545670,7,false,-5794020921088,-5794020786176⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2191361160596,0,true,758285646400,758285664128⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨7662094956,7,false,-5460544246912,-5460544112000⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨2192818782842,0,true,759016762688,759016780672⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨6204472710,7,false,-5692557695808,-5692557560896⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1108209558157,0,true,8663707264,8663707328⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1090813697395,0,false,-8732516416,-8732516352⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1119838609227,0,true,20141370240,20141370304⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1079184646325,0,false,-20517225152,-20517225088⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099135837139,0,false,-375854912,-375854848⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442820871,0,false,-68809088,-68809024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨2191911266285,0,true,758561626304,758561644160⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨7111989267,7,false,-5542461656768,-5542461521856⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨2193093323362,0,true,759154412736,759154430784⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨5929932190,7,false,-5742319018048,-5742318883136⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨11827882821,6,false,-4983164586176,-4983164470528⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨14177975937,6,false,-4783900011200,-4783899895552⟩
    { al := (508941/512000), au := (1018731/1024000), zl := (999/1000), zu := (1999/2000),
      A := ⟨1092942475296,1093854082106⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨758833891648,758833909632⟩ : DyadicInterval 40),(⟨-5629759761088,-5629759626176⟩ : DyadicInterval 40),(⟨22374149402,22374187000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759290965760,759290983872⟩ : DyadicInterval 40),(⟨-5794020921088,-5794020786176⟩ : DyadicInterval 40),(⟨19692458197,19692495874⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨758285646400,758285664128⟩ : DyadicInterval 40),(⟨-5460544246912,-5460544112000⟩ : DyadicInterval 40),(⟨25506096181,25506133583⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759016762688,759016780672⟩ : DyadicInterval 40),(⟨-5692557695808,-5692557560896⟩ : DyadicInterval 40),(⟨21309510456,21309548035⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨8697930381,20326981451⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨8663707264,8663707328⟩ : DyadicInterval 40),(⟨-8732516416,-8732516352⟩ : DyadicInterval 40),(⟨762088979786,762088999115⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨20141370240,20141370304⟩ : DyadicInterval 40),(⟨-20517225152,-20517225088⟩ : DyadicInterval 40),(⟨761935477549,761935496879⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-375854912,-68809024⟩ : DyadicInterval 40),(⟨762157788128,762311330336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨1092399638509,1093581695586⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨758561626304,758561644160⟩ : DyadicInterval 40),(⟨-5542461656768,-5542461521856⟩ : DyadicInterval 40),(⟨23940245692,23940283192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759154412736,759154430784⟩ : DyadicInterval 40),(⟨-5742319018048,-5742318883136⟩ : DyadicInterval 40),(⟨20500962004,20500999632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4983164586176,-4783899895552⟩ : DyadicInterval 40),(⟨3154073331392,3253705695968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨758833891648,759290983872⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-5794020921088,-5629759626176⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e272_ok : ecellOkT e272 = true := by decide +kernel
theorem e272_pos {a z : ℝ} (ha1 : ((508941/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1018731/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e272 e272_ok ha1 ha2 hz1 hz2 hz

-- box ['508941/512000', '1018731/1024000', '1999/2000', '1']  interval_lower 453147536552287/1099511627776
noncomputable def e273 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2192454103072,0,true,758833891648,758833909632⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨6569152480,7,false,-5629759761088,-5629759626176⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2193365709882,0,true,759290965760,759290983872⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨5657545670,7,false,-5794020921088,-5794020786176⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2191907631834,0,true,758559803200,758559821056⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨7115623718,7,false,-5541899915136,-5541899780224⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1110094309729,0,true,10532077760,10532077824⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1088928945823,0,false,-10633939712,-10633939648⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099409770592,0,false,-101861952,-101861888⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨2192181794376,0,true,758697320896,758697338752⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨6841461176,7,false,-5585101441216,-5585101306304⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨2193365724142,0,true,759290972928,759290991040⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨5657531410,7,false,-5794023692480,-5794023557568⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨11285952021,6,false,-5034732700416,-5034732584768⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨13640352915,6,false,-4826404101120,-4826403985472⟩
    { al := (508941/512000), au := (1018731/1024000), zl := (1999/2000), zu := 1,
      A := ⟨1092942475296,1093854082106⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨758833891648,758833909632⟩ : DyadicInterval 40),(⟨-5629759761088,-5629759626176⟩ : DyadicInterval 40),(⟨22374149402,22374187000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759290965760,759290983872⟩ : DyadicInterval 40),(⟨-5794020921088,-5794020786176⟩ : DyadicInterval 40),(⟨19692458197,19692495874⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨758559803200,758559821056⟩ : DyadicInterval 40),(⟨-5541899915136,-5541899780224⟩ : DyadicInterval 40),(⟨23950659267,23950696767⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759290965760,759290983872⟩ : DyadicInterval 40),(⟨-5794020921088,-5794020786176⟩ : DyadicInterval 40),(⟨19692458197,19692495874⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10582681953⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10532077760,10532077824⟩ : DyadicInterval 40),(⟨-10633939712,-10633939648⟩ : DyadicInterval 40),(⟨762072454199,762072473528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-101861952,0⟩ : DyadicInterval 40),(⟨762123383616,762174333856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨1092670166600,1093854096366⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨758697320896,758697338752⟩ : DyadicInterval 40),(⟨-5585101441216,-5585101306304⟩ : DyadicInterval 40),(⟨23162467400,23162504885⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759290972928,759290991040⟩ : DyadicInterval 40),(⟨-5794023692480,-5794023557568⟩ : DyadicInterval 40),(⟨19692415681,19692453359⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5034732700416,-4826403985472⟩ : DyadicInterval 40),(⟨3175325376352,3279489753088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨758833891648,759290983872⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-5794020921088,-5629759626176⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e273_ok : ecellOkT e273 = true := by decide +kernel
theorem e273_pos {a z : ℝ} (ha1 : ((508941/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1018731/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e273 e273_ok ha1 ha2 hz1 hz2 hz

-- box ['1018731/1024000', '50979/51200', '999/1000', '1999/2000']  interval_lower 855045360020591/1099511627776
noncomputable def e274 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2193365709881,0,true,759290965760,759290983872⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨5657545671,7,false,-5794020920896,-5794020785984⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2194277316690,0,true,759747849920,759747868160⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨4745938862,7,false,-5987206099712,-5987205963200⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2192271855798,0,true,758742491200,758742509120⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨6751399754,7,false,-5599671593920,-5599671459008⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨2193729933847,0,true,759473532288,759473550464⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨5293321705,7,false,-5867187043520,-5867186908544⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1109296887340,0,true,9741973504,9741973568⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1089726368212,0,false,-9829062336,-9829062272⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1122981606268,0,true,23222994048,23222994112⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1076041649284,0,false,-23724094208,-23724094144⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099010641814,0,false,-501100160,-501100096⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099424542472,0,false,-87088768,-87088704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨2192822865821,0,true,759018809920,759018827968⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨6200389731,7,false,-5693281489920,-5693281355008⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨2194004863474,0,true,759611320192,759611338432⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨5018392078,7,false,-5925831025984,-5925830890752⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨10013879205,6,false,-5166219686720,-5166219570752⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨12365814091,6,false,-4934262660736,-4934262545088⟩
    { al := (1018731/1024000), au := (50979/51200), zl := (999/1000), zu := (1999/2000),
      A := ⟨1093854082105,1094765688914⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759290965760,759290983872⟩ : DyadicInterval 40),(⟨-5794020920896,-5794020785984⟩ : DyadicInterval 40),(⟨19692458199,19692495877⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759747849920,759747868160⟩ : DyadicInterval 40),(⟨-5987206099712,-5987205963200⟩ : DyadicInterval 40),(⟨16936812298,16936850059⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨758742491200,758742509120⟩ : DyadicInterval 40),(⟨-5599671593920,-5599671459008⟩ : DyadicInterval 40),(⟨22902357222,22902394767⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759473532288,759473550464⟩ : DyadicInterval 40),(⟨-5867187043520,-5867186908544⟩ : DyadicInterval 40),(⟨18601026732,18601064455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨9785259564,23469978492⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨9741973504,9741973568⟩ : DyadicInterval 40),(⟨-9829062336,-9829062272⟩ : DyadicInterval 40),(⟨762079840364,762079859693⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23222994048,23222994112⟩ : DyadicInterval 40),(⟨-23724094208,-23724094144⟩ : DyadicInterval 40),(⟨761872871558,761872890887⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-501100160,-87088704⟩ : DyadicInterval 40),(⟨762166927968,762373952960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨1093311238045,1094493235698⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759018809920,759018827968⟩ : DyadicInterval 40),(⟨-5693281489920,-5693281355008⟩ : DyadicInterval 40),(⟨21297530958,21297568601⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨759611320192,759611338432⟩ : DyadicInterval 40),(⟨-5925831025984,-5925830890752⟩ : DyadicInterval 40),(⟨17768896259,17768934031⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5166219686720,-4934262545088⟩ : DyadicInterval 40),(⟨3229254656160,3345233246240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨759290965760,759747868160⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-5987206099712,-5794020785984⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e274_ok : ecellOkT e274 = true := by decide +kernel
theorem e274_pos {a z : ℝ} (ha1 : ((1018731/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((50979/51200 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e274 e274_ok ha1 ha2 hz1 hz2 hz

-- box ['222369/1024000', '445587/2048000', '999/1000', '1999/2000']  interval_lower 49433/34359738368
noncomputable def e275 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1338278523437,0,true,216073823360,216073823424⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨860744732115,0,false,-269186178752,-269186178688⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1338734326842,0,true,216448241536,216448241600⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨860288928710,0,false,-269768574336,-269768574272⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1338039756541,0,true,215877638208,215877638272⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨860983499011,0,false,-268881221248,-268881221184⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1338614715493,0,true,216349999552,216349999616⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨860408540059,0,false,-269615712960,-269615712896⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099573436492,0,true,61806976,61807040⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099449819060,0,false,-61810496,-61810432⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099635501120,0,true,123866304,123866368⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099387754432,0,false,-123880384,-123880320⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511613820,0,false,-14016,-13952⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624302,0,false,-3520,-3456⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1338159136051,0,true,215975731904,215975731968⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨860864119501,0,false,-269033684416,-269033684352⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1338674530240,0,true,216399129088,216399129152⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨860348725312,0,false,-269692152576,-269692152512⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1047489536813,0,false,-53293023424,-53293023360⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1047713509624,0,false,-53057952448,-53057952384⟩
    { al := (222369/1024000), au := (445587/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨238766895661,239222699066⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216073823360,216073823424⟩ : DyadicInterval 40),(⟨-269186178752,-269186178688⟩ : DyadicInterval 40),(⟨735990703137,735990722467⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216448241536,216448241600⟩ : DyadicInterval 40),(⟨-269768574336,-269768574272⟩ : DyadicInterval 40),(⟨735890021549,735890040879⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215877638208,215877638272⟩ : DyadicInterval 40),(⟨-268881221248,-268881221184⟩ : DyadicInterval 40),(⟨736043364781,736043384110⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216349999552,216349999616⟩ : DyadicInterval 40),(⟨-269615712960,-269615712896⟩ : DyadicInterval 40),(⟨735916461461,735916480791⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨61808716,123873344⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨61806976,61807040⟩ : DyadicInterval 40),(⟨-61810496,-61810432⟩ : DyadicInterval 40),(⟨762123381837,762123401166⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨123866304,123866368⟩ : DyadicInterval 40),(⟨-123880384,-123880320⟩ : DyadicInterval 40),(⟨762123376635,762123395965⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-14016,-3456⟩ : DyadicInterval 40),(⟨762123385344,762123409888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨238647508275,239162902464⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨215975731904,215975731968⟩ : DyadicInterval 40),(⟨-269033684416,-269033684352⟩ : DyadicInterval 40),(⟨736017041649,736017060978⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216399129088,216399129152⟩ : DyadicInterval 40),(⟨-269692152576,-269692152512⟩ : DyadicInterval 40),(⟨735903241206,735903260536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-53293023424,-53057952384⟩ : DyadicInterval 40),(⟨788652359808,788769914592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨216073823360,216448241600⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-269768574336,-269186178688⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e275_ok : ecellOkT e275 = true := by decide +kernel
theorem e275_pos {a z : ℝ} (ha1 : ((222369/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((445587/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e275 e275_ok ha1 ha2 hz1 hz2 hz

-- box ['445587/2048000', '111609/512000', '999/1000', '1999/2000']  interval_lower 6087819/549755813888
noncomputable def e276 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1338734326841,0,true,216448241536,216448241600⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨860288928711,0,false,-269768574336,-269768574272⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1339190130246,0,true,216822532288,216822532352⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨859833125306,0,false,-270351278464,-270351278400⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1338495104141,0,true,216251748736,216251748800⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨860528151411,0,false,-269462872832,-269462872768⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1339070290995,0,true,216724136576,216724136640⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨859952964557,0,false,-270198044736,-270198044672⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099573562948,0,true,61933376,61933440⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099449692604,0,false,-61936960,-61936896⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099635754149,0,true,124119360,124119424⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099387501403,0,false,-124133440,-124133376⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511613763,0,false,-14016,-13952⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624288,0,false,-3520,-3456⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1338614711548,0,true,216349996288,216349996352⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨860408544004,0,false,-269615707904,-269615707840⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1339130219699,0,true,216773342976,216773343040⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨859893035853,0,false,-270274670528,-270274670464⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1047291107187,0,false,-53501327552,-53501327488⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1047515556771,0,false,-53265711552,-53265711488⟩
    { al := (445587/2048000), au := (111609/512000), zl := (999/1000), zu := (1999/2000),
      A := ⟨239222699065,239678502470⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216448241536,216448241600⟩ : DyadicInterval 40),(⟨-269768574336,-269768574272⟩ : DyadicInterval 40),(⟨735890021550,735890040879⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216822532288,216822532352⟩ : DyadicInterval 40),(⟨-270351278464,-270351278400⟩ : DyadicInterval 40),(⟨735789141557,735789160886⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216251748736,216251748800⟩ : DyadicInterval 40),(⟨-269462872832,-269462872768⟩ : DyadicInterval 40),(⟨735942887748,735942907078⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216724136576,216724136640⟩ : DyadicInterval 40),(⟨-270198044736,-270198044672⟩ : DyadicInterval 40),(⟨735815684033,735815703362⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨61935172,124126373⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨61933376,61933440⟩ : DyadicInterval 40),(⟨-61936960,-61936896⟩ : DyadicInterval 40),(⟨762123381855,762123401184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨124119360,124119424⟩ : DyadicInterval 40),(⟨-124133440,-124133376⟩ : DyadicInterval 40),(⟨762123376578,762123395908⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-14016,-3456⟩ : DyadicInterval 40),(⟨762123385344,762123409888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨239103083772,239618591923⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216349996288,216349996352⟩ : DyadicInterval 40),(⟨-269615707904,-269615707840⟩ : DyadicInterval 40),(⟨735916462342,735916481671⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216773342976,216773343040⟩ : DyadicInterval 40),(⟨-270274670528,-270274670464⟩ : DyadicInterval 40),(⟨735802412500,735802431830⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-53501327552,-53265711488⟩ : DyadicInterval 40),(⟨788756239360,788874066656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨216448241536,216822532352⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-270351278464,-269768574272⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e276_ok : ecellOkT e276 = true := by decide +kernel
theorem e276_pos {a z : ℝ} (ha1 : ((445587/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((111609/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e276 e276_ok ha1 ha2 hz1 hz2 hz

-- box ['445587/2048000', '111609/512000', '1999/2000', '1']  interval_lower 9402299/1099511627776
noncomputable def e277 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1338734326841,0,true,216448241536,216448241600⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨860288928711,0,false,-269768574336,-269768574272⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1339190130246,0,true,216822532288,216822532352⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨859833125306,0,false,-270351278464,-270351278400⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1338614715491,0,true,216349999552,216349999616⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨860408540061,0,false,-269615712960,-269615712896⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099573692210,0,true,62062656,62062720⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099449563342,0,false,-62066240,-62066176⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624272,0,false,-3520,-3456⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1338674515671,0,true,216399117120,216399117184⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨860348739881,0,false,-269692133952,-269692133888⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1339190138807,0,true,216822539328,216822539392⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨859833116745,0,false,-270351289408,-270351289344⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1047264987359,0,false,-53528750080,-53528750016⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1047489543152,0,false,-53293016768,-53293016704⟩
    { al := (445587/2048000), au := (111609/512000), zl := (1999/2000), zu := 1,
      A := ⟨239222699065,239678502470⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216448241536,216448241600⟩ : DyadicInterval 40),(⟨-269768574336,-269768574272⟩ : DyadicInterval 40),(⟨735890021550,735890040879⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216822532288,216822532352⟩ : DyadicInterval 40),(⟨-270351278464,-270351278400⟩ : DyadicInterval 40),(⟨735789141557,735789160886⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216349999552,216349999616⟩ : DyadicInterval 40),(⟨-269615712960,-269615712896⟩ : DyadicInterval 40),(⟨735916461462,735916480791⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216822532288,216822532352⟩ : DyadicInterval 40),(⟨-270351278464,-270351278400⟩ : DyadicInterval 40),(⟨735789141557,735789160886⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,62064434⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨62062656,62062720⟩ : DyadicInterval 40),(⟨-62066240,-62066176⟩ : DyadicInterval 40),(⟨762123381840,762123401169⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3520,0⟩ : DyadicInterval 40),(⟨762123383616,762123404640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨239162887895,239678511031⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216399117120,216399117184⟩ : DyadicInterval 40),(⟨-269692133952,-269692133888⟩ : DyadicInterval 40),(⟨735903244426,735903263755⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216822539328,216822539392⟩ : DyadicInterval 40),(⟨-270351289408,-270351289344⟩ : DyadicInterval 40),(⟨735789139652,735789158981⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-53528750080,-53293016704⟩ : DyadicInterval 40),(⟨788769891968,788887777920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨216448241536,216822532352⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-270351278464,-269768574272⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e277_ok : ecellOkT e277 = true := by decide +kernel
theorem e277_pos {a z : ℝ} (ha1 : ((445587/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((111609/512000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e277 e277_ok ha1 ha2 hz1 hz2 hz

-- box ['111609/512000', '89457/409600', '999/1000', '1999/2000']  interval_lower 22860001/1099511627776
noncomputable def e278 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1339190130245,0,true,216822532288,216822532352⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨859833125307,0,false,-270351278464,-270351278400⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1339645933650,0,true,217196695616,217196695680⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨859377321902,0,false,-270934291648,-270934291584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1338950451742,0,true,216625732096,216625732160⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨860072803810,0,false,-270044832320,-270044832256⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1339525866498,0,true,217098146368,217098146432⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨859497389054,0,false,-270780685056,-270780684992⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099573689456,0,true,62059904,62059968⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099449566096,0,false,-62063488,-62063424⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099636007280,0,true,124372416,124372480⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099387248272,0,false,-124386560,-124386496⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511613705,0,false,-14080,-14016⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624273,0,false,-3520,-3456⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1339070287060,0,true,216724133376,216724133440⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨859952968492,0,false,-270198039680,-270198039616⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1339585909155,0,true,217147429568,217147429632⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨859437346397,0,false,-270857497280,-270857497216⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1047092299845,0,false,-53710067712,-53710067648⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1047317226382,0,false,-53473906304,-53473906240⟩
    { al := (111609/512000), au := (89457/409600), zl := (999/1000), zu := (1999/2000),
      A := ⟨239678502469,240134305874⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216822532288,216822532352⟩ : DyadicInterval 40),(⟨-270351278464,-270351278400⟩ : DyadicInterval 40),(⟨735789141557,735789160886⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨217196695616,217196695680⟩ : DyadicInterval 40),(⟨-270934291648,-270934291584⟩ : DyadicInterval 40),(⟨735688063247,735688082577⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216625732096,216625732160⟩ : DyadicInterval 40),(⟨-270044832320,-270044832256⟩ : DyadicInterval 40),(⟨735842212757,735842232086⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨217098146368,217098146432⟩ : DyadicInterval 40),(⟨-270780685056,-270780684992⟩ : DyadicInterval 40),(⟨735714708395,735714727725⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨62061680,124379504⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨62059904,62059968⟩ : DyadicInterval 40),(⟨-62063488,-62063424⟩ : DyadicInterval 40),(⟨762123381840,762123401170⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨124372416,124372480⟩ : DyadicInterval 40),(⟨-124386560,-124386496⟩ : DyadicInterval 40),(⟨762123376553,762123395883⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-14080,-3456⟩ : DyadicInterval 40),(⟨762123385344,762123409920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨239558659284,240074281379⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216724133376,216724133440⟩ : DyadicInterval 40),(⟨-270198039680,-270198039616⟩ : DyadicInterval 40),(⟨735815684875,735815704204⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨217147429568,217147429632⟩ : DyadicInterval 40),(⟨-270857497280,-270857497216⟩ : DyadicInterval 40),(⟨735701385513,735701404842⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-53710067712,-53473906240⟩ : DyadicInterval 40),(⟨788860336736,788978436736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨216822532288,217196695680⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-270934291648,-270351278400⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e278_ok : ecellOkT e278 = true := by decide +kernel
theorem e278_pos {a z : ℝ} (ha1 : ((111609/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((89457/409600 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e278 e278_ok ha1 ha2 hz1 hz2 hz

-- box ['89457/409600', '224067/1024000', '999/1000', '1999/2000']  interval_lower 16817269/549755813888
noncomputable def e279 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1339645933649,0,true,217196695616,217196695680⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨859377321903,0,false,-270934291648,-270934291584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1340101737055,0,true,217570731712,217570731776⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨858921518497,0,false,-271517614080,-271517614016⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1339405799343,0,true,216999588224,216999588288⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨859617456209,0,false,-270627099968,-270627099904⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1339981442001,0,true,217472028928,217472028992⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨859041813551,0,false,-271363634304,-271363634240⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099573816016,0,true,62186432,62186496⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099449439536,0,false,-62190016,-62189952⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099636260515,0,true,124625664,124625728⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099386995037,0,false,-124639808,-124639744⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511613648,0,false,-14144,-14080⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624259,0,false,-3520,-3456⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1339525862557,0,true,217098143104,217098143168⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨859497392995,0,false,-270780680000,-270780679936⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1340041598614,0,true,217521388928,217521388992⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨858981656938,0,false,-271440633152,-271440633088⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1046893114783,0,false,-53919244224,-53919244160⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1047118518470,0,false,-53682536896,-53682536832⟩
    { al := (89457/409600), au := (224067/1024000), zl := (999/1000), zu := (1999/2000),
      A := ⟨240134305873,240590109279⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨217196695616,217196695680⟩ : DyadicInterval 40),(⟨-270934291648,-270934291584⟩ : DyadicInterval 40),(⟨735688063248,735688082577⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨217570731712,217570731776⟩ : DyadicInterval 40),(⟨-271517614080,-271517614016⟩ : DyadicInterval 40),(⟨735586786465,735586805795⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216999588224,216999588288⟩ : DyadicInterval 40),(⟨-270627099968,-270627099904⟩ : DyadicInterval 40),(⟨735741339832,735741359162⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨217472028928,217472028992⟩ : DyadicInterval 40),(⟨-271363634304,-271363634240⟩ : DyadicInterval 40),(⟨735613534587,735613553916⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨62188240,124632739⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨62186432,62186496⟩ : DyadicInterval 40),(⟨-62190016,-62189952⟩ : DyadicInterval 40),(⟨762123381826,762123401155⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨124625664,124625728⟩ : DyadicInterval 40),(⟨-124639808,-124639744⟩ : DyadicInterval 40),(⟨762123376496,762123395825⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-14144,-3456⟩ : DyadicInterval 40),(⟨762123385344,762123409952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨240014234781,240529970838⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨217098143104,217098143168⟩ : DyadicInterval 40),(⟨-270780680000,-270780679936⟩ : DyadicInterval 40),(⟨735714709281,735714728611⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨217521388928,217521388992⟩ : DyadicInterval 40),(⟨-271440633152,-271440633088⟩ : DyadicInterval 40),(⟨735600160216,735600179545⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-53919244224,-53682536832⟩ : DyadicInterval 40),(⟨788964652032,789083024992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨217196695616,217570731776⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-271517614080,-270934291584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e279_ok : ecellOkT e279 = true := by decide +kernel
theorem e279_pos {a z : ℝ} (ha1 : ((89457/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((224067/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e279 e279_ok ha1 ha2 hz1 hz2 hz

-- box ['111609/512000', '89457/409600', '1999/2000', '1']  interval_lower 20067853/1099511627776
noncomputable def e280 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1339190130245,0,true,216822532288,216822532352⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨859833125307,0,false,-270351278464,-270351278400⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1339645933650,0,true,217196695616,217196695680⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨859377321902,0,false,-270934291648,-270934291584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1339070290993,0,true,216724136576,216724136640⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨859952964559,0,false,-270198044736,-270198044672⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099573818783,0,true,62189248,62189312⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099449436769,0,false,-62192768,-62192704⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624258,0,false,-3520,-3456⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1339130205120,0,true,216773331008,216773331072⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨859893050432,0,false,-270274651904,-270274651840⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1339645942204,0,true,217196702656,217196702720⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨859377313348,0,false,-270934302592,-270934302528⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1047066080581,0,false,-53737599872,-53737599808⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1047291113543,0,false,-53501320832,-53501320768⟩
    { al := (111609/512000), au := (89457/409600), zl := (1999/2000), zu := 1,
      A := ⟨239678502469,240134305874⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216822532288,216822532352⟩ : DyadicInterval 40),(⟨-270351278464,-270351278400⟩ : DyadicInterval 40),(⟨735789141557,735789160886⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨217196695616,217196695680⟩ : DyadicInterval 40),(⟨-270934291648,-270934291584⟩ : DyadicInterval 40),(⟨735688063247,735688082577⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216724136576,216724136640⟩ : DyadicInterval 40),(⟨-270198044736,-270198044672⟩ : DyadicInterval 40),(⟨735815684033,735815703362⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨217196695616,217196695680⟩ : DyadicInterval 40),(⟨-270934291648,-270934291584⟩ : DyadicInterval 40),(⟨735688063247,735688082577⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,62191007⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨62189248,62189312⟩ : DyadicInterval 40),(⟨-62192768,-62192704⟩ : DyadicInterval 40),(⟨762123381794,762123401123⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3520,0⟩ : DyadicInterval 40),(⟨762123383616,762123404640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨239618577344,240134314428⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨216773331008,216773331072⟩ : DyadicInterval 40),(⟨-270274651904,-270274651840⟩ : DyadicInterval 40),(⟨735802415735,735802435064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨217196702656,217196702720⟩ : DyadicInterval 40),(⟨-270934302592,-270934302528⟩ : DyadicInterval 40),(⟨735688061337,735688080666⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-53737599872,-53501320768⟩ : DyadicInterval 40),(⟨788874044000,788992202816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨216822532288,217196695680⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-270934291648,-270351278400⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e280_ok : ecellOkT e280 = true := by decide +kernel
theorem e280_pos {a z : ℝ} (ha1 : ((111609/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((89457/409600 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e280 e280_ok ha1 ha2 hz1 hz2 hz

-- box ['89457/409600', '224067/1024000', '1999/2000', '1']  interval_lower 30823939/1099511627776
noncomputable def e281 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1339645933649,0,true,217196695616,217196695680⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨859377321903,0,false,-270934291648,-270934291584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1340101737055,0,true,217570731712,217570731776⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨858921518497,0,false,-271517614080,-271517614016⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1339525866496,0,true,217098146368,217098146432⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨859497389056,0,false,-270780685056,-270780684992⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099573945407,0,true,62315840,62315904⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099449310145,0,false,-62319424,-62319360⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624243,0,false,-3584,-3520⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1339585894566,0,true,217147417600,217147417664⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨859437360986,0,false,-270857478656,-270857478592⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1340101745617,0,true,217570738752,217570738816⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨858921509935,0,false,-271517625088,-271517625024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1046866795888,0,false,-53946886272,-53946886208⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1047092306217,0,false,-53710060992,-53710060928⟩
    { al := (89457/409600), au := (224067/1024000), zl := (1999/2000), zu := 1,
      A := ⟨240134305873,240590109279⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨217196695616,217196695680⟩ : DyadicInterval 40),(⟨-270934291648,-270934291584⟩ : DyadicInterval 40),(⟨735688063248,735688082577⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨217570731712,217570731776⟩ : DyadicInterval 40),(⟨-271517614080,-271517614016⟩ : DyadicInterval 40),(⟨735586786465,735586805795⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨217098146368,217098146432⟩ : DyadicInterval 40),(⟨-270780685056,-270780684992⟩ : DyadicInterval 40),(⟨735714708395,735714727725⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨217570731712,217570731776⟩ : DyadicInterval 40),(⟨-271517614080,-271517614016⟩ : DyadicInterval 40),(⟨735586786465,735586805795⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,62317631⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨62315840,62315904⟩ : DyadicInterval 40),(⟨-62319424,-62319360⟩ : DyadicInterval 40),(⟨762123381811,762123401141⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3584,0⟩ : DyadicInterval 40),(⟨762123383616,762123404672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨240074266790,240590117841⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨217147417600,217147417664⟩ : DyadicInterval 40),(⟨-270857478656,-270857478592⟩ : DyadicInterval 40),(⟨735701388762,735701408092⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨217570738752,217570738816⟩ : DyadicInterval 40),(⟨-271517625088,-271517625024⟩ : DyadicInterval 40),(⟨735586784571,735586803900⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-53946886272,-53710060928⟩ : DyadicInterval 40),(⟨788978414080,789096846016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨217196695616,217570731776⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-271517614080,-270934291584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e281_ok : ecellOkT e281 = true := by decide +kernel
theorem e281_pos {a z : ℝ} (ha1 : ((89457/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((224067/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e281 e281_ok ha1 ha2 hz1 hz2 hz

-- box ['224067/1024000', '448983/2048000', '999/1000', '1999/2000']  interval_lower 44500371/1099511627776
noncomputable def e282 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1340101737054,0,true,217570731712,217570731776⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨858921518498,0,false,-271517614080,-271517614016⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1340557540459,0,true,217944640576,217944640640⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨858465715093,0,false,-272101246208,-272101246144⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1339861146944,0,true,217373317312,217373317376⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨859162108608,0,false,-271209676096,-271209676032⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1340437017503,0,true,217845784448,217845784512⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨858586238049,0,false,-271946892800,-271946892736⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099573942626,0,true,62313024,62313088⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099449312926,0,false,-62316672,-62316608⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099636513853,0,true,124878976,124879040⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099386741699,0,false,-124893184,-124893120⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511613591,0,false,-14208,-14144⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624245,0,false,-3584,-3520⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1339981438069,0,true,217472025728,217472025792⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨859041817483,0,false,-271363629312,-271363629248⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1340497288070,0,true,217895221056,217895221120⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨858525967482,0,false,-272024078464,-272024078400⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1046693552004,0,false,-54128857344,-54128857280⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1046919433022,0,false,-53891603520,-53891603456⟩
    { al := (224067/1024000), au := (448983/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨240590109278,241045912683⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨217570731712,217570731776⟩ : DyadicInterval 40),(⟨-271517614080,-271517614016⟩ : DyadicInterval 40),(⟨735586786466,735586805795⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨217944640576,217944640640⟩ : DyadicInterval 40),(⟨-272101246208,-272101246144⟩ : DyadicInterval 40),(⟨735485311273,735485330603⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨217373317312,217373317376⟩ : DyadicInterval 40),(⟨-271209676096,-271209676032⟩ : DyadicInterval 40),(⟨735640268872,735640288201⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨217845784448,217845784512⟩ : DyadicInterval 40),(⟨-271946892800,-271946892736⟩ : DyadicInterval 40),(⟨735512162503,735512181833⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨62314850,124886077⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨62313024,62313088⟩ : DyadicInterval 40),(⟨-62316672,-62316608⟩ : DyadicInterval 40),(⟨762123381844,762123401173⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨124878976,124879040⟩ : DyadicInterval 40),(⟨-124893184,-124893120⟩ : DyadicInterval 40),(⟨762123376470,762123395800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-14208,-3520⟩ : DyadicInterval 40),(⟨762123385376,762123409984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨240469810293,240985660294⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨217472025728,217472025792⟩ : DyadicInterval 40),(⟨-271363629312,-271363629248⟩ : DyadicInterval 40),(⟨735613535461,735613554791⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨217895221056,217895221120⟩ : DyadicInterval 40),(⟨-272024078464,-272024078400⟩ : DyadicInterval 40),(⟨735498736622,735498755952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-54128857344,-53891603456⟩ : DyadicInterval 40),(⟨789069185344,789187831552⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨217570731712,217944640640⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-272101246208,-271517614016⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e282_ok : ecellOkT e282 = true := by decide +kernel
theorem e282_pos {a z : ℝ} (ha1 : ((224067/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((448983/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e282 e282_ok ha1 ha2 hz1 hz2 hz

-- box ['448983/2048000', '56229/256000', '999/1000', '1999/2000']  interval_lower 55457949/1099511627776
noncomputable def e283 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1340557540458,0,true,217944640576,217944640640⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨858465715094,0,false,-272101246208,-272101246144⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1341013343863,0,true,218318422336,218318422400⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨858009911689,0,false,-272685188288,-272685188224⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1340316494545,0,true,217746919424,217746919488⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨858706761007,0,false,-271792561088,-271792561024⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1340892593006,0,true,218219412928,218219412992⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨858130662546,0,false,-272530460864,-272530460800⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099574069288,0,true,62439680,62439744⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099449186264,0,false,-62443328,-62443264⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099636767295,0,true,125132352,125132416⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099386488257,0,false,-125146688,-125146624⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511613533,0,false,-14272,-14208⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624230,0,false,-3584,-3520⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1340437013572,0,true,217845781248,217845781312⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨858586241980,0,false,-271946887808,-271946887744⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1340952977525,0,true,218268926208,218268926272⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨858070278027,0,false,-272607833472,-272607833408⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1046493611507,0,false,-54338907264,-54338907200⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1046719970049,0,false,-54101106496,-54101106432⟩
    { al := (448983/2048000), au := (56229/256000), zl := (999/1000), zu := (1999/2000),
      A := ⟨241045912682,241501716087⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨217944640576,217944640640⟩ : DyadicInterval 40),(⟨-272101246208,-272101246144⟩ : DyadicInterval 40),(⟨735485311273,735485330603⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨218318422336,218318422400⟩ : DyadicInterval 40),(⟨-272685188288,-272685188224⟩ : DyadicInterval 40),(⟨735383637578,735383656908⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨217746919424,217746919488⟩ : DyadicInterval 40),(⟨-271792561088,-271792561024⟩ : DyadicInterval 40),(⟨735538999873,735539019203⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨218219412928,218219412992⟩ : DyadicInterval 40),(⟨-272530460864,-272530460800⟩ : DyadicInterval 40),(⟨735410592155,735410611485⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨62441512,125139519⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨62439680,62439744⟩ : DyadicInterval 40),(⟨-62443328,-62443264⟩ : DyadicInterval 40),(⟨762123381829,762123401159⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨125132352,125132416⟩ : DyadicInterval 40),(⟨-125146688,-125146624⟩ : DyadicInterval 40),(⟨762123376477,762123395806⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-14272,-3520⟩ : DyadicInterval 40),(⟨762123385376,762123410016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨240925385796,241441349749⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨217845781248,217845781312⟩ : DyadicInterval 40),(⟨-271946887808,-271946887744⟩ : DyadicInterval 40),(⟨735512163380,735512182710⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨218268926208,218268926272⟩ : DyadicInterval 40),(⟨-272607833472,-272607833408⟩ : DyadicInterval 40),(⟨735397114562,735397133892⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-54338907264,-54101106432⟩ : DyadicInterval 40),(⟨789173936832,789292856512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨217944640576,218318422400⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-272685188288,-272101246144⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e283_ok : ecellOkT e283 = true := by decide +kernel
theorem e283_pos {a z : ℝ} (ha1 : ((448983/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((56229/256000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e283 e283_ok ha1 ha2 hz1 hz2 hz

-- box ['224067/1024000', '448983/2048000', '1999/2000', '1']  interval_lower 20835597/549755813888
noncomputable def e284 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1340101737054,0,true,217570731712,217570731776⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨858921518498,0,false,-271517614080,-271517614016⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1340557540459,0,true,217944640576,217944640640⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨858465715093,0,false,-272101246208,-272101246144⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1339981441999,0,true,217472028928,217472028992⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨859041813553,0,false,-271363634304,-271363634240⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099574072084,0,true,62442496,62442560⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099449183468,0,false,-62446144,-62446080⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624229,0,false,-3584,-3520⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1340041584014,0,true,217521376896,217521376960⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨858981671538,0,false,-271440614464,-271440614400⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1340557549016,0,true,217944647616,217944647680⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨858465706536,0,false,-272101257152,-272101257088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1046667133294,0,false,-54156609536,-54156609472⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1046893121172,0,false,-53919237504,-53919237440⟩
    { al := (224067/1024000), au := (448983/2048000), zl := (1999/2000), zu := 1,
      A := ⟨240590109278,241045912683⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨217570731712,217570731776⟩ : DyadicInterval 40),(⟨-271517614080,-271517614016⟩ : DyadicInterval 40),(⟨735586786466,735586805795⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨217944640576,217944640640⟩ : DyadicInterval 40),(⟨-272101246208,-272101246144⟩ : DyadicInterval 40),(⟨735485311273,735485330603⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨217472028928,217472028992⟩ : DyadicInterval 40),(⟨-271363634304,-271363634240⟩ : DyadicInterval 40),(⟨735613534587,735613553917⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨217944640576,217944640640⟩ : DyadicInterval 40),(⟨-272101246208,-272101246144⟩ : DyadicInterval 40),(⟨735485311273,735485330603⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,62444308⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨62442496,62442560⟩ : DyadicInterval 40),(⟨-62446144,-62446080⟩ : DyadicInterval 40),(⟨762123381829,762123401158⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3584,0⟩ : DyadicInterval 40),(⟨762123383616,762123404672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨240529956238,241045921240⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨217521376896,217521376960⟩ : DyadicInterval 40),(⟨-271440614464,-271440614400⟩ : DyadicInterval 40),(⟨735600163495,735600182824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨217944647616,217944647680⟩ : DyadicInterval 40),(⟨-272101257152,-272101257088⟩ : DyadicInterval 40),(⟨735485309347,735485328676⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-54156609536,-53919237440⟩ : DyadicInterval 40),(⟨789083002336,789201707648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨217570731712,217944640640⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-272101246208,-271517614016⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e284_ok : ecellOkT e284 = true := by decide +kernel
theorem e284_pos {a z : ℝ} (ha1 : ((224067/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((448983/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e284 e284_ok ha1 ha2 hz1 hz2 hz

-- box ['448983/2048000', '56229/256000', '1999/2000', '1']  interval_lower 26304967/549755813888
noncomputable def e285 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1340557540458,0,true,217944640576,217944640640⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨858465715094,0,false,-272101246208,-272101246144⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1341013343863,0,true,218318422336,218318422400⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨858009911689,0,false,-272685188288,-272685188224⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1340437017501,0,true,217845784448,217845784512⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨858586238051,0,false,-271946892800,-271946892736⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099574198812,0,true,62569216,62569280⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099449056740,0,false,-62572864,-62572800⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624215,0,false,-3584,-3520⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1340497273460,0,true,217895209088,217895209152⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨858525982092,0,false,-272024059712,-272024059648⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1341013352417,0,true,218318429376,218318429440⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨858009903135,0,false,-272685199232,-272685199168⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1046467092792,0,false,-54366769792,-54366769728⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1046693558409,0,false,-54128850624,-54128850560⟩
    { al := (448983/2048000), au := (56229/256000), zl := (1999/2000), zu := 1,
      A := ⟨241045912682,241501716087⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨217944640576,217944640640⟩ : DyadicInterval 40),(⟨-272101246208,-272101246144⟩ : DyadicInterval 40),(⟨735485311273,735485330603⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨218318422336,218318422400⟩ : DyadicInterval 40),(⟨-272685188288,-272685188224⟩ : DyadicInterval 40),(⟨735383637578,735383656908⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨217845784448,217845784512⟩ : DyadicInterval 40),(⟨-271946892800,-271946892736⟩ : DyadicInterval 40),(⟨735512162504,735512181834⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨218318422336,218318422400⟩ : DyadicInterval 40),(⟨-272685188288,-272685188224⟩ : DyadicInterval 40),(⟨735383637578,735383656908⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,62571036⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨62569216,62569280⟩ : DyadicInterval 40),(⟨-62572864,-62572800⟩ : DyadicInterval 40),(⟨762123381815,762123401144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3584,0⟩ : DyadicInterval 40),(⟨762123383616,762123404672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨240985645684,241501724641⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨217895209088,217895209152⟩ : DyadicInterval 40),(⟨-272024059712,-272024059648⟩ : DyadicInterval 40),(⟨735498739852,735498759181⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨218318429376,218318429440⟩ : DyadicInterval 40),(⟨-272685199232,-272685199168⟩ : DyadicInterval 40),(⟨735383635645,735383654975⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-54366769792,-54128850560⟩ : DyadicInterval 40),(⟨789187808896,789306787776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨217944640576,218318422400⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-272685188288,-272101246144⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e285_ok : ecellOkT e285 = true := by decide +kernel
theorem e285_pos {a z : ℝ} (ha1 : ((448983/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((56229/256000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e285 e285_ok ha1 ha2 hz1 hz2 hz

-- box ['56229/256000', '450681/2048000', '999/1000', '1999/2000']  interval_lower 66507419/1099511627776
noncomputable def e286 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1341013343862,0,true,218318422336,218318422400⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨858009911690,0,false,-272685188288,-272685188224⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1341469147268,0,true,218692077120,218692077184⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨857554108284,0,false,-273269440640,-273269440576⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1340771842145,0,true,218120394624,218120394688⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨858251413407,0,false,-272375755264,-272375755200⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1341348168509,0,true,218592914496,218592914560⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨857675087043,0,false,-273114338816,-273114338752⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099574196002,0,true,62566400,62566464⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099449059550,0,false,-62570048,-62569984⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099637020841,0,true,125385856,125385920⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099386234711,0,false,-125400256,-125400192⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511613475,0,false,-14336,-14272⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624216,0,false,-3584,-3520⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1340892589075,0,true,218219409728,218219409792⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨858130666477,0,false,-272530455808,-272530455744⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1341408666986,0,true,218642504384,218642504448⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨857614588566,0,false,-273191898624,-273191898560⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1046293293289,0,false,-54549394240,-54549394176⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1046520129546,0,false,-54311046080,-54311046016⟩
    { al := (56229/256000), au := (450681/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨241501716086,241957519492⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨218318422336,218318422400⟩ : DyadicInterval 40),(⟨-272685188288,-272685188224⟩ : DyadicInterval 40),(⟨735383637578,735383656908⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨218692077120,218692077184⟩ : DyadicInterval 40),(⟨-273269440640,-273269440576⟩ : DyadicInterval 40),(⟨735281765315,735281784644⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨218120394624,218120394688⟩ : DyadicInterval 40),(⟨-272375755264,-272375755200⟩ : DyadicInterval 40),(⟨735437532809,735437552138⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨218592914496,218592914560⟩ : DyadicInterval 40),(⟨-273114338816,-273114338752⟩ : DyadicInterval 40),(⟨735308823477,735308842806⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨62568226,125393065⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨62566400,62566464⟩ : DyadicInterval 40),(⟨-62570048,-62569984⟩ : DyadicInterval 40),(⟨762123381815,762123401144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨125385856,125385920⟩ : DyadicInterval 40),(⟨-125400256,-125400192⟩ : DyadicInterval 40),(⟨762123376451,762123395780⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-14336,-3520⟩ : DyadicInterval 40),(⟨762123385376,762123410048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨241380961299,241897039210⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨218219409728,218219409792⟩ : DyadicInterval 40),(⟨-272530455808,-272530455744⟩ : DyadicInterval 40),(⟨735410593011,735410612340⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨218642504384,218642504448⟩ : DyadicInterval 40),(⟨-273191898624,-273191898560⟩ : DyadicInterval 40),(⟨735295294096,735295313426⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-54549394240,-54311046016⟩ : DyadicInterval 40),(⟨789278906624,789398100000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨218318422336,218692077184⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-273269440640,-272685188224⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e286_ok : ecellOkT e286 = true := by decide +kernel
theorem e286_pos {a z : ℝ} (ha1 : ((56229/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((450681/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e286 e286_ok ha1 ha2 hz1 hz2 hz

-- box ['450681/2048000', '45153/204800', '999/1000', '1999/2000']  interval_lower 77649131/1099511627776
noncomputable def e287 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1341469147267,0,true,218692077120,218692077184⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨857554108285,0,false,-273269440640,-273269440576⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1341924950672,0,true,219065604928,219065604992⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨857098304880,0,false,-273854003584,-273854003520⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1341227189747,0,true,218493742976,218493743040⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨857796065805,0,false,-272959258944,-272959258880⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1341803744011,0,true,218966289216,218966289280⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨857219511541,0,false,-273698526976,-273698526912⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099574322768,0,true,62693184,62693248⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448932784,0,false,-62696832,-62696768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099637274490,0,true,125639488,125639552⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099385981062,0,false,-125653952,-125653888⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511613417,0,false,-14400,-14336⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624202,0,false,-3584,-3520⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1341348164582,0,true,218592911296,218592911360⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨857675090970,0,false,-273114333824,-273114333760⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1341864356444,0,true,219015955648,219015955712⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨857158899108,0,false,-273776274240,-273776274176⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1046092597354,0,false,-54760318528,-54760318464⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1046319911512,0,false,-54521422464,-54521422400⟩
    { al := (450681/2048000), au := (45153/204800), zl := (999/1000), zu := (1999/2000),
      A := ⟨241957519491,242413322896⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨218692077120,218692077184⟩ : DyadicInterval 40),(⟨-273269440640,-273269440576⟩ : DyadicInterval 40),(⟨735281765315,735281784644⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨219065604928,219065604992⟩ : DyadicInterval 40),(⟨-273854003584,-273854003520⟩ : DyadicInterval 40),(⟨735179694493,735179713822⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨218493742976,218493743040⟩ : DyadicInterval 40),(⟨-272959258944,-272959258880⟩ : DyadicInterval 40),(⟨735335867652,735335886981⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨218966289216,218966289280⟩ : DyadicInterval 40),(⟨-273698526976,-273698526912⟩ : DyadicInterval 40),(⟨735206856439,735206875769⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨62694992,125646714⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨62693184,62693248⟩ : DyadicInterval 40),(⟨-62696832,-62696768⟩ : DyadicInterval 40),(⟨762123381800,762123401130⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨125639488,125639552⟩ : DyadicInterval 40),(⟨-125653952,-125653888⟩ : DyadicInterval 40),(⟨762123376425,762123395754⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-14400,-3520⟩ : DyadicInterval 40),(⟨762123385376,762123410080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨241836536806,242352728668⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨218592911296,218592911360⟩ : DyadicInterval 40),(⟨-273114333824,-273114333760⟩ : DyadicInterval 40),(⟨735308824360,735308843689⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨219015955648,219015955712⟩ : DyadicInterval 40),(⟨-273776274240,-273776274176⟩ : DyadicInterval 40),(⟨735193275196,735193294526⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-54760318528,-54521422400⟩ : DyadicInterval 40),(⟨789384094816,789503562144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨218692077120,219065604992⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-273854003584,-273269440576⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e287_ok : ecellOkT e287 = true := by decide +kernel
theorem e287_pos {a z : ℝ} (ha1 : ((450681/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((45153/204800 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e287 e287_ok ha1 ha2 hz1 hz2 hz

-- box ['56229/256000', '450681/2048000', '1999/2000', '1']  interval_lower 63640123/1099511627776
noncomputable def e288 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1341013343862,0,true,218318422336,218318422400⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨858009911690,0,false,-272685188288,-272685188224⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1341469147268,0,true,218692077120,218692077184⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨857554108284,0,false,-273269440640,-273269440576⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1340892593003,0,true,218219412928,218219412992⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨858130662549,0,false,-272530460864,-272530460800⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099574325590,0,true,62696000,62696064⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448929962,0,false,-62699648,-62699584⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624200,0,false,-3584,-3520⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1340952962903,0,true,218268914240,218268914304⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨858070292649,0,false,-272607814784,-272607814720⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1341469155830,0,true,218692084096,218692084160⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨857554099722,0,false,-273269451584,-273269451520⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1046266674377,0,false,-54577367424,-54577367360⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1046493617930,0,false,-54338900480,-54338900416⟩
    { al := (56229/256000), au := (450681/2048000), zl := (1999/2000), zu := 1,
      A := ⟨241501716086,241957519492⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨218318422336,218318422400⟩ : DyadicInterval 40),(⟨-272685188288,-272685188224⟩ : DyadicInterval 40),(⟨735383637578,735383656908⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨218692077120,218692077184⟩ : DyadicInterval 40),(⟨-273269440640,-273269440576⟩ : DyadicInterval 40),(⟨735281765315,735281784644⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨218219412928,218219412992⟩ : DyadicInterval 40),(⟨-272530460864,-272530460800⟩ : DyadicInterval 40),(⟨735410592156,735410611486⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨218692077120,218692077184⟩ : DyadicInterval 40),(⟨-273269440640,-273269440576⟩ : DyadicInterval 40),(⟨735281765315,735281784644⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,62697814⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨62696000,62696064⟩ : DyadicInterval 40),(⟨-62699648,-62699584⟩ : DyadicInterval 40),(⟨762123381800,762123401129⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3584,0⟩ : DyadicInterval 40),(⟨762123383616,762123404672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨241441335127,241957528054⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨218268914240,218268914304⟩ : DyadicInterval 40),(⟨-272607814784,-272607814720⟩ : DyadicInterval 40),(⟨735397117832,735397137162⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨218692084096,218692084160⟩ : DyadicInterval 40),(⟨-273269451584,-273269451520⟩ : DyadicInterval 40),(⟨735281763412,735281782741⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-54577367424,-54338900416⟩ : DyadicInterval 40),(⟨789292833824,789412086592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨218318422336,218692077184⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-273269440640,-272685188224⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e288_ok : ecellOkT e288 = true := by decide +kernel
theorem e288_pos {a z : ℝ} (ha1 : ((56229/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((450681/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e288 e288_ok ha1 ha2 hz1 hz2 hz

-- box ['450681/2048000', '45153/204800', '1999/2000', '1']  interval_lower 74762843/1099511627776
noncomputable def e289 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1341469147267,0,true,218692077120,218692077184⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨857554108285,0,false,-273269440640,-273269440576⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1341924950672,0,true,219065604928,219065604992⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨857098304880,0,false,-273854003584,-273854003520⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1341348168507,0,true,218592914496,218592914560⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨857675087045,0,false,-273114338816,-273114338752⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099574452422,0,true,62822848,62822912⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448803130,0,false,-62826496,-62826432⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624186,0,false,-3648,-3584⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1341408652355,0,true,218642492416,218642492480⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨857614603197,0,false,-273191879872,-273191879808⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1341924959239,0,true,219065611904,219065611968⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨857098296313,0,false,-273854014592,-273854014528⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1046065878057,0,false,-54788402624,-54788402560⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1046293299728,0,false,-54549387456,-54549387392⟩
    { al := (450681/2048000), au := (45153/204800), zl := (1999/2000), zu := 1,
      A := ⟨241957519491,242413322896⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨218692077120,218692077184⟩ : DyadicInterval 40),(⟨-273269440640,-273269440576⟩ : DyadicInterval 40),(⟨735281765315,735281784644⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨219065604928,219065604992⟩ : DyadicInterval 40),(⟨-273854003584,-273854003520⟩ : DyadicInterval 40),(⟨735179694493,735179713822⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨218592914496,218592914560⟩ : DyadicInterval 40),(⟨-273114338816,-273114338752⟩ : DyadicInterval 40),(⟨735308823477,735308842807⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨219065604928,219065604992⟩ : DyadicInterval 40),(⟨-273854003584,-273854003520⟩ : DyadicInterval 40),(⟨735179694493,735179713822⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,62824646⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨62822848,62822912⟩ : DyadicInterval 40),(⟨-62826496,-62826432⟩ : DyadicInterval 40),(⟨762123381786,762123401115⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3648,0⟩ : DyadicInterval 40),(⟨762123383616,762123404704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨241897024579,242413331463⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨218642492416,218642492480⟩ : DyadicInterval 40),(⟨-273191879872,-273191879808⟩ : DyadicInterval 40),(⟨735295297356,735295316685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨219065611904,219065611968⟩ : DyadicInterval 40),(⟨-273854014592,-273854014528⟩ : DyadicInterval 40),(⟨735179692606,735179711935⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-54788402624,-54549387392⟩ : DyadicInterval 40),(⟨789398077312,789517604192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨218692077120,219065604992⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-273854003584,-273269440576⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e289_ok : ecellOkT e289 = true := by decide +kernel
theorem e289_pos {a z : ℝ} (ha1 : ((450681/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((45153/204800 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e289 e289_ok ha1 ha2 hz1 hz2 hz

-- box ['45153/204800', '452379/2048000', '999/1000', '1999/2000']  interval_lower 11110471/137438953472
noncomputable def e290 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1341924950671,0,true,219065604864,219065604928⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨857098304881,0,false,-273854003584,-273854003520⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1342380754076,0,true,219439005824,219439005888⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨856642501476,0,false,-274438877504,-274438877440⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1341682537348,0,true,218866964608,218866964672⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨857340718204,0,false,-273543072384,-273543072320⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1342259319514,0,true,219339537216,219339537280⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨856763936038,0,false,-274283025728,-274283025664⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099574449586,0,true,62819968,62820032⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448805966,0,false,-62823616,-62823552⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099637528245,0,true,125893248,125893312⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099385727307,0,false,-125907712,-125907648⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511613359,0,false,-14464,-14400⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624187,0,false,-3648,-3584⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1341803740085,0,true,218966286016,218966286080⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨857219515467,0,false,-273698521984,-273698521920⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1342320045897,0,true,219389280128,219389280192⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨856703209655,0,false,-274360960512,-274360960448⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1045891523703,0,false,-54971680384,-54971680320⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1046119315950,0,false,-54732235904,-54732235840⟩
    { al := (45153/204800), au := (452379/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨242413322895,242869126300⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨219065604864,219065604928⟩ : DyadicInterval 40),(⟨-273854003584,-273854003520⟩ : DyadicInterval 40),(⟨735179694532,735179713861⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨219439005824,219439005888⟩ : DyadicInterval 40),(⟨-274438877504,-274438877440⟩ : DyadicInterval 40),(⟨735077425108,735077444438⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨218866964608,218866964672⟩ : DyadicInterval 40),(⟨-273543072384,-273543072320⟩ : DyadicInterval 40),(⟨735234004310,735234023639⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨219339537216,219339537280⟩ : DyadicInterval 40),(⟨-274283025728,-274283025664⟩ : DyadicInterval 40),(⟨735104691000,735104710329⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨62821810,125900469⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨62819968,62820032⟩ : DyadicInterval 40),(⟨-62823616,-62823552⟩ : DyadicInterval 40),(⟨762123381786,762123401115⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨125893248,125893312⟩ : DyadicInterval 40),(⟨-125907712,-125907648⟩ : DyadicInterval 40),(⟨762123376367,762123395696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-14464,-3584⟩ : DyadicInterval 40),(⟨762123385408,762123410112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨242292112309,242808418121⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨218966286016,218966286080⟩ : DyadicInterval 40),(⟨-273698521984,-273698521920⟩ : DyadicInterval 40),(⟨735206857325,735206876655⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨219389280128,219389280192⟩ : DyadicInterval 40),(⟨-274360960512,-274360960448⟩ : DyadicInterval 40),(⟨735091057747,735091077076⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-54971680384,-54732235840⟩ : DyadicInterval 40),(⟨789489501536,789609243072⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨219065604864,219439005888⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-274438877504,-273854003520⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e290_ok : ecellOkT e290 = true := by decide +kernel
theorem e290_pos {a z : ℝ} (ha1 : ((45153/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((452379/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e290 e290_ok ha1 ha2 hz1 hz2 hz

-- box ['452379/2048000', '113307/512000', '999/1000', '1999/2000']  interval_lower 100211885/1099511627776
noncomputable def e291 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1342380754075,0,true,219439005824,219439005888⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨856642501477,0,false,-274438877504,-274438877440⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1342836557480,0,true,219812280000,219812280064⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨856186698072,0,false,-275024062720,-275024062656⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1342137884948,0,true,219240059584,219240059648⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨856885370604,0,false,-274127196032,-274127195968⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1342714895016,0,true,219712658560,219712658624⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨856308360536,0,false,-274867835328,-274867835264⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099574576456,0,true,62946816,62946880⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448679096,0,false,-62950528,-62950464⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099637782103,0,true,126147072,126147136⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099385473449,0,false,-126161600,-126161536⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511613301,0,false,-14528,-14464⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624173,0,false,-3648,-3584⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1342259315588,0,true,219339534016,219339534080⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨856763939964,0,false,-274283020672,-274283020608⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1342775735355,0,true,219762477888,219762477952⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨856247520197,0,false,-274945957952,-274945957888⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1045690072331,0,false,-55183480064,-55183480000⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1045918342858,0,false,-54943486656,-54943486592⟩
    { al := (452379/2048000), au := (113307/512000), zl := (999/1000), zu := (1999/2000),
      A := ⟨242869126299,243324929704⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨219439005824,219439005888⟩ : DyadicInterval 40),(⟨-274438877504,-274438877440⟩ : DyadicInterval 40),(⟨735077425108,735077444438⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨219812280000,219812280064⟩ : DyadicInterval 40),(⟨-275024062720,-275024062656⟩ : DyadicInterval 40),(⟨734974957055,734974976385⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨219240059584,219240059648⟩ : DyadicInterval 40),(⟨-274127196032,-274127195968⟩ : DyadicInterval 40),(⟨735131942805,735131962135⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨219712658560,219712658624⟩ : DyadicInterval 40),(⟨-274867835328,-274867835264⟩ : DyadicInterval 40),(⟨735002327106,735002346435⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨62948680,126154327⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨62946816,62946880⟩ : DyadicInterval 40),(⟨-62950528,-62950464⟩ : DyadicInterval 40),(⟨762123381803,762123401133⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨126147072,126147136⟩ : DyadicInterval 40),(⟨-126161600,-126161536⟩ : DyadicInterval 40),(⟨762123376341,762123395670⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-14528,-3584⟩ : DyadicInterval 40),(⟨762123385408,762123410144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨242747687812,243264107579⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨219339534016,219339534080⟩ : DyadicInterval 40),(⟨-274283020672,-274283020608⟩ : DyadicInterval 40),(⟨735104691865,735104711194⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨219762477888,219762477952⟩ : DyadicInterval 40),(⟨-274945957952,-274945957888⟩ : DyadicInterval 40),(⟨734988641791,734988661120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-55183480064,-54943486592⟩ : DyadicInterval 40),(⟨789595126912,789715142912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨219439005824,219812280064⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-275024062720,-274438877440⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e291_ok : ecellOkT e291 = true := by decide +kernel
theorem e291_pos {a z : ℝ} (ha1 : ((452379/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((113307/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e291 e291_ok ha1 ha2 hz1 hz2 hz

-- box ['45153/204800', '452379/2048000', '1999/2000', '1']  interval_lower 85978417/1099511627776
noncomputable def e292 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1341924950671,0,true,219065604864,219065604928⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨857098304881,0,false,-273854003584,-273854003520⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1342380754076,0,true,219439005824,219439005888⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨856642501476,0,false,-274438877504,-274438877440⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1341803744009,0,true,218966289216,218966289280⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨857219511543,0,false,-273698526976,-273698526912⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099574579306,0,true,62949696,62949760⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448676246,0,false,-62953344,-62953280⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624171,0,false,-3648,-3584⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1341864341797,0,true,219015943680,219015943744⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨857158913755,0,false,-273776255424,-273776255360⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1342380762635,0,true,219439012864,219439012928⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨856642492917,0,false,-274438888512,-274438888448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1045864703835,0,false,-54999875584,-54999875520⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1046092603812,0,false,-54760311744,-54760311680⟩
    { al := (45153/204800), au := (452379/2048000), zl := (1999/2000), zu := 1,
      A := ⟨242413322895,242869126300⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨219065604864,219065604928⟩ : DyadicInterval 40),(⟨-273854003584,-273854003520⟩ : DyadicInterval 40),(⟨735179694532,735179713861⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨219439005824,219439005888⟩ : DyadicInterval 40),(⟨-274438877504,-274438877440⟩ : DyadicInterval 40),(⟨735077425108,735077444438⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨218966289216,218966289280⟩ : DyadicInterval 40),(⟨-273698526976,-273698526912⟩ : DyadicInterval 40),(⟨735206856439,735206875769⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨219439005824,219439005888⟩ : DyadicInterval 40),(⟨-274438877504,-274438877440⟩ : DyadicInterval 40),(⟨735077425108,735077444438⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,62951530⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨62949696,62949760⟩ : DyadicInterval 40),(⟨-62953344,-62953280⟩ : DyadicInterval 40),(⟨762123381771,762123401100⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3648,0⟩ : DyadicInterval 40),(⟨762123383616,762123404704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨242352714021,242869134859⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨219015943680,219015943744⟩ : DyadicInterval 40),(⟨-273776255424,-273776255360⟩ : DyadicInterval 40),(⟨735193278447,735193297777⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨219439012864,219439012928⟩ : DyadicInterval 40),(⟨-274438888512,-274438888448⟩ : DyadicInterval 40),(⟨735077423177,735077442506⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-54999875584,-54760311680⟩ : DyadicInterval 40),(⟨789503539456,789623340672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨219065604864,219439005888⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-274438877504,-273854003520⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e292_ok : ecellOkT e292 = true := by decide +kernel
theorem e292_pos {a z : ℝ} (ha1 : ((45153/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((452379/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e292 e292_ok ha1 ha2 hz1 hz2 hz

-- box ['452379/2048000', '113307/512000', '1999/2000', '1']  interval_lower 97287145/1099511627776
noncomputable def e293 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1342380754075,0,true,219439005824,219439005888⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨856642501477,0,false,-274438877504,-274438877440⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1342836557480,0,true,219812280000,219812280064⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨856186698072,0,false,-275024062720,-275024062656⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1342259319511,0,true,219339537216,219339537280⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨856763936041,0,false,-274283025728,-274283025664⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099574706243,0,true,63076608,63076672⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448549309,0,false,-63080320,-63080256⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624157,0,false,-3648,-3584⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1342320031245,0,true,219389268096,219389268160⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨856703224307,0,false,-274360941760,-274360941696⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1342836566037,0,true,219812287040,219812287104⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨856186689515,0,false,-275024073728,-275024073664⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1045663151703,0,false,-55211786624,-55211786560⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1045891530175,0,false,-54971673600,-54971673536⟩
    { al := (452379/2048000), au := (113307/512000), zl := (1999/2000), zu := 1,
      A := ⟨242869126299,243324929704⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨219439005824,219439005888⟩ : DyadicInterval 40),(⟨-274438877504,-274438877440⟩ : DyadicInterval 40),(⟨735077425108,735077444438⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨219812280000,219812280064⟩ : DyadicInterval 40),(⟨-275024062720,-275024062656⟩ : DyadicInterval 40),(⟨734974957055,734974976385⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨219339537216,219339537280⟩ : DyadicInterval 40),(⟨-274283025728,-274283025664⟩ : DyadicInterval 40),(⟨735104691001,735104710330⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨219812280000,219812280064⟩ : DyadicInterval 40),(⟨-275024062720,-275024062656⟩ : DyadicInterval 40),(⟨734974957055,734974976385⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,63078467⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63076608,63076672⟩ : DyadicInterval 40),(⟨-63080320,-63080256⟩ : DyadicInterval 40),(⟨762123381789,762123401118⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3648,0⟩ : DyadicInterval 40),(⟨762123383616,762123404704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨242808403469,243324938261⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨219389268096,219389268160⟩ : DyadicInterval 40),(⟨-274360941760,-274360941696⟩ : DyadicInterval 40),(⟨735091061075,735091080405⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨219812287040,219812287104⟩ : DyadicInterval 40),(⟨-275024073728,-275024073664⟩ : DyadicInterval 40),(⟨734974955116,734974974446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-55211786624,-54971673536⟩ : DyadicInterval 40),(⟨789609220384,789729296192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨219439005824,219812280064⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-275024062720,-274438877440⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e293_ok : ecellOkT e293 = true := by decide +kernel
theorem e293_pos {a z : ℝ} (ha1 : ((452379/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((113307/512000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e293 e293_ok ha1 ha2 hz1 hz2 hz

-- box ['113307/512000', '454077/2048000', '999/1000', '1999/2000']  interval_lower 55816785/549755813888
noncomputable def e294 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1342836557479,0,true,219812280000,219812280064⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨856186698073,0,false,-275024062720,-275024062656⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1343292360885,0,true,220185427520,220185427584⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨855730894667,0,false,-275609559552,-275609559488⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1342593232549,0,true,219613028032,219613028096⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨856430023003,0,false,-274711630144,-274711630080⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1343170470519,0,true,220085653312,220085653376⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨855852785033,0,false,-275452956160,-275452956096⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099574703378,0,true,63073792,63073856⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448552174,0,false,-63077440,-63077376⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099638036067,0,true,126401024,126401088⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099385219485,0,false,-126415616,-126415552⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511613243,0,false,-14592,-14528⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624158,0,false,-3648,-3584⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1342714891095,0,true,219712655360,219712655424⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨856308364457,0,false,-274867830336,-274867830272⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1343231424814,0,true,220135548992,220135549056⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨855791830738,0,false,-275531266752,-275531266688⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1045488243240,0,false,-55395717760,-55395717696⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1045716992236,0,false,-55155174912,-55155174848⟩
    { al := (113307/512000), au := (454077/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨243324929703,243780733109⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨219812280000,219812280064⟩ : DyadicInterval 40),(⟨-275024062720,-275024062656⟩ : DyadicInterval 40),(⟨734974957055,734974976385⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨220185427520,220185427584⟩ : DyadicInterval 40),(⟨-275609559552,-275609559488⟩ : DyadicInterval 40),(⟨734872290303,734872309633⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨219613028032,219613028096⟩ : DyadicInterval 40),(⟨-274711630144,-274711630080⟩ : DyadicInterval 40),(⟨735029683045,735029702374⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨220085653312,220085653376⟩ : DyadicInterval 40),(⟨-275452956160,-275452956096⟩ : DyadicInterval 40),(⟨734899764753,734899784082⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨63075602,126408291⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63073792,63073856⟩ : DyadicInterval 40),(⟨-63077440,-63077376⟩ : DyadicInterval 40),(⟨762123381757,762123401086⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨126401024,126401088⟩ : DyadicInterval 40),(⟨-126415616,-126415552⟩ : DyadicInterval 40),(⟨762123376314,762123395644⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-14592,-3584⟩ : DyadicInterval 40),(⟨762123385408,762123410176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨243203263319,243719797038⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨219712655360,219712655424⟩ : DyadicInterval 40),(⟨-274867830336,-274867830272⟩ : DyadicInterval 40),(⟨735002327998,735002347328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨220135548992,220135549056⟩ : DyadicInterval 40),(⟨-275531266752,-275531266688⟩ : DyadicInterval 40),(⟨734886027250,734886046580⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-55395717760,-55155174848⟩ : DyadicInterval 40),(⟨789700971040,789821261760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨219812280000,220185427584⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-275609559552,-275024062656⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e294_ok : ecellOkT e294 = true := by decide +kernel
theorem e294_pos {a z : ℝ} (ha1 : ((113307/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((454077/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e294 e294_ok ha1 ha2 hz1 hz2 hz

-- box ['454077/2048000', '227463/1024000', '999/1000', '1999/2000']  interval_lower 123149665/1099511627776
noncomputable def e295 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1343292360884,0,true,220185427520,220185427584⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨855730894668,0,false,-275609559552,-275609559488⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1343748164289,0,true,220558448448,220558448512⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨855275091263,0,false,-276195368320,-276195368256⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1343048580150,0,true,219985870016,219985870080⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨855974675402,0,false,-275296375104,-275296375040⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1343626046021,0,true,220458521536,220458521600⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨855397209531,0,false,-276038388544,-276038388480⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099574830354,0,true,63200704,63200768⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448425198,0,false,-63204416,-63204352⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099638290136,0,true,126655040,126655104⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099384965416,0,false,-126669696,-126669632⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511613184,0,false,-14656,-14592⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624143,0,false,-3648,-3584⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1343170466603,0,true,220085650112,220085650176⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨855852788949,0,false,-275452951168,-275452951104⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1343687114269,0,true,220508493568,220508493632⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨855336141283,0,false,-276116887360,-276116887296⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1045286036433,0,false,-55608393728,-55608393664⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1045515264083,0,false,-55367300992,-55367300928⟩
    { al := (454077/2048000), au := (227463/1024000), zl := (999/1000), zu := (1999/2000),
      A := ⟨243780733108,244236536513⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨220185427520,220185427584⟩ : DyadicInterval 40),(⟨-275609559552,-275609559488⟩ : DyadicInterval 40),(⟨734872290304,734872309633⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨220558448448,220558448512⟩ : DyadicInterval 40),(⟨-276195368320,-276195368256⟩ : DyadicInterval 40),(⟨734769424823,734769444153⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨219985870016,219985870080⟩ : DyadicInterval 40),(⟨-275296375104,-275296375040⟩ : DyadicInterval 40),(⟨734927225026,734927244355⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨220458521536,220458521600⟩ : DyadicInterval 40),(⟨-276038388544,-276038388480⟩ : DyadicInterval 40),(⟨734797003911,734797023241⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨63202578,126662360⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63200704,63200768⟩ : DyadicInterval 40),(⟨-63204416,-63204352⟩ : DyadicInterval 40),(⟨762123381774,762123401104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨126655040,126655104⟩ : DyadicInterval 40),(⟨-126669696,-126669632⟩ : DyadicInterval 40),(⟨762123376288,762123395617⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-14656,-3584⟩ : DyadicInterval 40),(⟨762123385408,762123410208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨243658838827,244175486493⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨220085650112,220085650176⟩ : DyadicInterval 40),(⟨-275452951168,-275452951104⟩ : DyadicInterval 40),(⟨734899765647,734899784976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨220508493568,220508493632⟩ : DyadicInterval 40),(⟨-276116887360,-276116887296⟩ : DyadicInterval 40),(⟨734783214108,734783233438⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-55608393728,-55367300928⟩ : DyadicInterval 40),(⟨789807034080,789927599744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨220185427520,220558448512⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-276195368320,-275609559488⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e295_ok : ecellOkT e295 = true := by decide +kernel
theorem e295_pos {a z : ℝ} (ha1 : ((454077/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((227463/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e295 e295_ok ha1 ha2 hz1 hz2 hz

-- box ['113307/512000', '454077/2048000', '1999/2000', '1']  interval_lower 108689507/1099511627776
noncomputable def e296 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1342836557479,0,true,219812280000,219812280064⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨856186698073,0,false,-275024062720,-275024062656⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1343292360885,0,true,220185427520,220185427584⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨855730894667,0,false,-275609559552,-275609559488⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1342714895014,0,true,219712658560,219712658624⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨856308360538,0,false,-274867835328,-274867835264⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099574833233,0,true,63203584,63203648⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448422319,0,false,-63207296,-63207232⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624142,0,false,-3648,-3584⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1342775720693,0,true,219762465856,219762465920⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨856247534859,0,false,-274945939136,-274945939072⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1343292369445,0,true,220185434560,220185434624⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨855730886107,0,false,-275609570560,-275609570496⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1045461221661,0,false,-55424135936,-55424135872⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1045690078820,0,false,-55183473216,-55183473152⟩
    { al := (113307/512000), au := (454077/2048000), zl := (1999/2000), zu := 1,
      A := ⟨243324929703,243780733109⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨219812280000,219812280064⟩ : DyadicInterval 40),(⟨-275024062720,-275024062656⟩ : DyadicInterval 40),(⟨734974957055,734974976385⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨220185427520,220185427584⟩ : DyadicInterval 40),(⟨-275609559552,-275609559488⟩ : DyadicInterval 40),(⟨734872290303,734872309633⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨219712658560,219712658624⟩ : DyadicInterval 40),(⟨-274867835328,-274867835264⟩ : DyadicInterval 40),(⟨735002327106,735002346436⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨220185427520,220185427584⟩ : DyadicInterval 40),(⟨-275609559552,-275609559488⟩ : DyadicInterval 40),(⟨734872290303,734872309633⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,63205457⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63203584,63203648⟩ : DyadicInterval 40),(⟨-63207296,-63207232⟩ : DyadicInterval 40),(⟨762123381774,762123401103⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3648,0⟩ : DyadicInterval 40),(⟨762123383616,762123404704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨243264092917,243780741669⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨219762465856,219762465920⟩ : DyadicInterval 40),(⟨-274945939136,-274945939072⟩ : DyadicInterval 40),(⟨734988645110,734988664439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨220185434560,220185434624⟩ : DyadicInterval 40),(⟨-275609570560,-275609570496⟩ : DyadicInterval 40),(⟨734872288356,734872307686⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-55424135936,-55183473152⟩ : DyadicInterval 40),(⟨789715120192,789835470848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨219812280000,220185427584⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-275609559552,-275024062656⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e296_ok : ecellOkT e296 = true := by decide +kernel
theorem e296_pos {a z : ℝ} (ha1 : ((113307/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((454077/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e296 e296_ok ha1 ha2 hz1 hz2 hz

-- box ['454077/2048000', '227463/1024000', '1999/2000', '1']  interval_lower 120185977/1099511627776
noncomputable def e297 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1343292360884,0,true,220185427520,220185427584⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨855730894668,0,false,-275609559552,-275609559488⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1343748164289,0,true,220558448448,220558448512⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨855275091263,0,false,-276195368320,-276195368256⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1343170470517,0,true,220085653312,220085653376⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨855852785035,0,false,-275452956160,-275452956096⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099574960274,0,true,63330624,63330688⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448295278,0,false,-63334336,-63334272⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624128,0,false,-3712,-3648⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1343231410142,0,true,220135537024,220135537088⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨855791845410,0,false,-275531247936,-275531247872⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1343748172854,0,true,220558455424,220558455488⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨855275082698,0,false,-276195379328,-276195379264⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1045258913712,0,false,-55636923840,-55636923776⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1045488249746,0,false,-55395710912,-55395710848⟩
    { al := (454077/2048000), au := (227463/1024000), zl := (1999/2000), zu := 1,
      A := ⟨243780733108,244236536513⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨220185427520,220185427584⟩ : DyadicInterval 40),(⟨-275609559552,-275609559488⟩ : DyadicInterval 40),(⟨734872290304,734872309633⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨220558448448,220558448512⟩ : DyadicInterval 40),(⟨-276195368320,-276195368256⟩ : DyadicInterval 40),(⟨734769424823,734769444153⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨220085653312,220085653376⟩ : DyadicInterval 40),(⟨-275452956160,-275452956096⟩ : DyadicInterval 40),(⟨734899764753,734899784082⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨220558448448,220558448512⟩ : DyadicInterval 40),(⟨-276195368320,-276195368256⟩ : DyadicInterval 40),(⟨734769424823,734769444153⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,63332498⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63330624,63330688⟩ : DyadicInterval 40),(⟨-63334336,-63334272⟩ : DyadicInterval 40),(⟨762123381759,762123401089⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3712,0⟩ : DyadicInterval 40),(⟨762123383616,762123404736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨243719782366,244236545078⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨220135537024,220135537088⟩ : DyadicInterval 40),(⟨-275531247936,-275531247872⟩ : DyadicInterval 40),(⟨734886030545,734886049875⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨220558455424,220558455488⟩ : DyadicInterval 40),(⟨-276195379328,-276195379264⟩ : DyadicInterval 40),(⟨734769422907,734769442236⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-55636923840,-55395710848⟩ : DyadicInterval 40),(⟨789821239040,789941864800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨220185427520,220558448512⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-276195368320,-275609559488⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e297_ok : ecellOkT e297 = true := by decide +kernel
theorem e297_pos {a z : ℝ} (ha1 : ((454077/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((227463/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e297 e297_ok ha1 ha2 hz1 hz2 hz

-- box ['227463/1024000', '18231/81920', '999/1000', '1999/2000']  interval_lower 134760499/1099511627776
noncomputable def e298 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1343748164288,0,true,220558448448,220558448512⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨855275091264,0,false,-276195368320,-276195368256⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1344203967693,0,true,220931342848,220931342912⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨854819287859,0,false,-276781489344,-276781489280⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1343503927751,0,true,220358585600,220358585664⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨855519327801,0,false,-275881431232,-275881431168⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1344081621524,0,true,220831263424,220831263488⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨854941634028,0,false,-276624132800,-276624132736⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099574957381,0,true,63327744,63327808⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448298171,0,false,-63331456,-63331392⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099638544310,0,true,126909184,126909248⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099384711242,0,false,-126923904,-126923840⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511613126,0,false,-14656,-14592⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624129,0,false,-3648,-3584⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1343626042107,0,true,220458518336,220458518400⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨855397213445,0,false,-276038383552,-276038383488⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1344142803732,0,true,220881311744,220881311808⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨854880451820,0,false,-276702819968,-276702819904⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1045083451904,0,false,-55821508224,-55821508160⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1045313158403,0,false,-55579865152,-55579865088⟩
    { al := (227463/1024000), au := (18231/81920), zl := (999/1000), zu := (1999/2000),
      A := ⟨244236536512,244692339917⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨220558448448,220558448512⟩ : DyadicInterval 40),(⟨-276195368320,-276195368256⟩ : DyadicInterval 40),(⟨734769424823,734769444153⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨220931342848,220931342912⟩ : DyadicInterval 40),(⟨-276781489344,-276781489280⟩ : DyadicInterval 40),(⟨734666360585,734666379915⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨220358585600,220358585664⟩ : DyadicInterval 40),(⟨-275881431232,-275881431168⟩ : DyadicInterval 40),(⟨734824568718,734824588048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨220831263424,220831263488⟩ : DyadicInterval 40),(⟨-276624132800,-276624132736⟩ : DyadicInterval 40),(⟨734694044472,734694063802⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨63329605,126916534⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63327744,63327808⟩ : DyadicInterval 40),(⟨-63331456,-63331392⟩ : DyadicInterval 40),(⟨762123381760,762123401089⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨126909184,126909248⟩ : DyadicInterval 40),(⟨-126923904,-126923840⟩ : DyadicInterval 40),(⟨762123376261,762123395591⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-14656,-3584⟩ : DyadicInterval 40),(⟨762123385408,762123410208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨244114414331,244631175956⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨220458518336,220458518400⟩ : DyadicInterval 40),(⟨-276038383552,-276038383488⟩ : DyadicInterval 40),(⟨734797004808,734797024138⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨220881311744,220881311808⟩ : DyadicInterval 40),(⟨-276702819968,-276702819904⟩ : DyadicInterval 40),(⟨734680202242,734680221572⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-55821508224,-55579865088⟩ : DyadicInterval 40),(⟨789913316160,790034156992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨220558448448,220931342912⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-276781489344,-276195368256⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e298_ok : ecellOkT e298 = true := by decide +kernel
theorem e298_pos {a z : ℝ} (ha1 : ((227463/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((18231/81920 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e298 e298_ok ha1 ha2 hz1 hz2 hz

-- box ['18231/81920', '28539/128000', '999/1000', '1999/2000']  interval_lower 146466401/1099511627776
noncomputable def e299 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1344203967692,0,true,220931342848,220931342912⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨854819287860,0,false,-276781489344,-276781489280⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1344659771098,0,true,221304110784,221304110848⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨854363484454,0,false,-277367923008,-277367922944⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1343959275352,0,true,220731174848,220731174912⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨855063980200,0,false,-276466798784,-276466798720⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1344537197027,0,true,221203878976,221203879040⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨854486058525,0,false,-277210189248,-277210189184⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575084460,0,true,63454848,63454912⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448171092,0,false,-63458560,-63458496⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099638798590,0,true,127163456,127163520⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099384456962,0,false,-127178176,-127178112⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511613067,0,false,-14720,-14656⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624114,0,false,-3712,-3648⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1344081617613,0,true,220831260224,220831260288⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨854941637939,0,false,-276624127744,-276624127680⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1344598493188,0,true,221254003456,221254003520⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨854424762364,0,false,-277289065024,-277289064960⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1044880489659,0,false,-56035061568,-56035061504⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1045110675192,0,false,-55792867520,-55792867456⟩
    { al := (18231/81920), au := (28539/128000), zl := (999/1000), zu := (1999/2000),
      A := ⟨244692339916,245148143322⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨220931342848,220931342912⟩ : DyadicInterval 40),(⟨-276781489344,-276781489280⟩ : DyadicInterval 40),(⟨734666360586,734666379915⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨221304110784,221304110848⟩ : DyadicInterval 40),(⟨-277367923008,-277367922944⟩ : DyadicInterval 40),(⟨734563097583,734563116913⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨220731174848,220731174912⟩ : DyadicInterval 40),(⟨-276466798784,-276466798720⟩ : DyadicInterval 40),(⟨734721714068,734721733397⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨221203878976,221203879040⟩ : DyadicInterval 40),(⟨-277210189248,-277210189184⟩ : DyadicInterval 40),(⟨734590886447,734590905776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨63456684,127170814⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63454848,63454912⟩ : DyadicInterval 40),(⟨-63458560,-63458496⟩ : DyadicInterval 40),(⟨762123381745,762123401074⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨127163456,127163520⟩ : DyadicInterval 40),(⟨-127178176,-127178112⟩ : DyadicInterval 40),(⟨762123376203,762123395532⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-14720,-3648⟩ : DyadicInterval 40),(⟨762123385440,762123410240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨244569989837,245086865412⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨220831260224,220831260288⟩ : DyadicInterval 40),(⟨-276624127744,-276624127680⟩ : DyadicInterval 40),(⟨734694045348,734694064677⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨221254003456,221254003520⟩ : DyadicInterval 40),(⟨-277289065024,-277289064960⟩ : DyadicInterval 40),(⟨734576991753,734577011083⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-56035061568,-55792867456⟩ : DyadicInterval 40),(⟨790019817344,790140933664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨220931342848,221304110848⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-277367923008,-276781489280⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e299_ok : ecellOkT e299 = true := by decide +kernel
theorem e299_pos {a z : ℝ} (ha1 : ((18231/81920 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((28539/128000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e299 e299_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B004

end


