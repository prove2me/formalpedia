-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B036
-- name    : CK_CKLaneC2R_EpCells_B036
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:19:22.067503+00:00
-- url     : https://prove2.me/theorems/c8f4bde6-05bf-488b-99a7-1a91a85c5783
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B036` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B036` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B036` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B036 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B036.lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheckT

-- ===== source module CKLaneC2R.EpCells.B036 =====
section

namespace CKLaneC2R.EpCells.B036

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['323331/2048000', '1294173/8192000', '3999/4000', '7999/8000']  interval_lower 95905665/549755813888
noncomputable def e2160 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273098636623,0,true,161174873664,161174873728⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925924618929,0,false,-188927498816,-188927498752⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273212587475,0,true,161273282944,161273283008⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925810668077,0,false,-189062820864,-189062820800⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273055239870,0,true,161137393472,161137393536⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925968015682,0,false,-188875967488,-188875967424⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273190874856,0,true,161254532352,161254532416⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925832380696,0,false,-189037034816,-189037034752⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522676140,0,true,11048256,11048320⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500579412,0,false,-11048448,-11048384⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533740367,0,true,22112320,22112384⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489515185,0,false,-22112832,-22112768⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627331,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627665,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273076933729,0,true,161156129792,161156129856⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925946321823,0,false,-188901727488,-188901727424⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273201735543,0,true,161263911488,161263911552⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925821520009,0,false,-189049932928,-189049932864⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072073761023,0,false,-27786021440,-27786021376⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072113176801,0,false,-27745597632,-27745597568⟩
    { al := (323331/2048000), au := (1294173/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨173587008847,173700959699⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161174873664,161174873728⟩ : DyadicInterval 40),(⟨-188927498816,-188927498752⟩ : DyadicInterval 40),(⟨748363233677,748363253007⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161273282944,161273283008⟩ : DyadicInterval 40),(⟨-189062820864,-189062820800⟩ : DyadicInterval 40),(⟨748345085710,748345105039⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161137393472,161137393536⟩ : DyadicInterval 40),(⟨-188875967488,-188875967424⟩ : DyadicInterval 40),(⟨748370141880,748370161210⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161254532352,161254532416⟩ : DyadicInterval 40),(⟨-189037034816,-189037034752⟩ : DyadicInterval 40),(⟨748348544627,748348563956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11048364,22112591⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11048256,11048320⟩ : DyadicInterval 40),(⟨-11048448,-11048384⟩ : DyadicInterval 40),(⟨762123383536,762123402865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22112320,22112384⟩ : DyadicInterval 40),(⟨-22112832,-22112768⟩ : DyadicInterval 40),(⟨762123383363,762123402692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173565305953,173690107767⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161156129792,161156129856⟩ : DyadicInterval 40),(⟨-188901727488,-188901727424⟩ : DyadicInterval 40),(⟨748366688738,748366708067⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161263911488,161263911552⟩ : DyadicInterval 40),(⟨-189049932928,-189049932864⟩ : DyadicInterval 40),(⟨748346814500,748346833829⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27786021440,-27745597568⟩ : DyadicInterval 40),(⟨775996182400,776016413600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161174873664,161273283008⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189062820864,-188927498752⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2160_ok : ecellOkT e2160 = true := by decide +kernel
theorem e2160_pos {a z : ℝ} (ha1 : ((323331/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1294173/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2160 e2160_ok ha1 ha2 hz1 hz2 hz

-- box ['1294173/8192000', '647511/4096000', '3999/4000', '7999/8000']  interval_lower 192944539/1099511627776
noncomputable def e2161 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273212587474,0,true,161273282944,161273283008⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925810668078,0,false,-189062820864,-189062820800⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273326538327,0,true,161371683392,161371683456⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925696717225,0,false,-189198159552,-189198159488⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273169162234,0,true,161235781440,161235781504⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925854093318,0,false,-189011249344,-189011249280⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273304811464,0,true,161352922176,161352922240⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925718444088,0,false,-189172353408,-189172353344⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522683660,0,true,11055808,11055872⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500571892,0,false,-11056000,-11055936⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533755411,0,true,22127360,22127424⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489500141,0,false,-22127872,-22127808⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627330,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627665,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273190870333,0,true,161254528448,161254528512⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925832385219,0,false,-189037029440,-189037029376⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273315679274,0,true,161362306624,161362306688⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925707576278,0,false,-189185261568,-189185261504⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072037749779,0,false,-27822954944,-27822954880⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072077193676,0,false,-27782500928,-27782500864⟩
    { al := (1294173/8192000), au := (647511/4096000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨173700959698,173814910551⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161273282944,161273283008⟩ : DyadicInterval 40),(⟨-189062820864,-189062820800⟩ : DyadicInterval 40),(⟨748345085710,748345105039⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161371683392,161371683456⟩ : DyadicInterval 40),(⟨-189198159552,-189198159488⟩ : DyadicInterval 40),(⟨748326925638,748326944968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161235781440,161235781504⟩ : DyadicInterval 40),(⟨-189011249344,-189011249280⟩ : DyadicInterval 40),(⟨748352003093,748352022422⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161352922176,161352922240⟩ : DyadicInterval 40),(⟨-189172353408,-189172353344⟩ : DyadicInterval 40),(⟨748330389133,748330408463⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11055884,22127635⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11055808,11055872⟩ : DyadicInterval 40),(⟨-11056000,-11055936⟩ : DyadicInterval 40),(⟨762123383536,762123402865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22127360,22127424⟩ : DyadicInterval 40),(⟨-22127872,-22127808⟩ : DyadicInterval 40),(⟨762123383362,762123402691⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173679242557,173804051498⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161254528448,161254528512⟩ : DyadicInterval 40),(⟨-189037029440,-189037029376⟩ : DyadicInterval 40),(⟨748348545344,748348564674⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161362306624,161362306688⟩ : DyadicInterval 40),(⟨-189185261568,-189185261504⟩ : DyadicInterval 40),(⟨748328656716,748328676046⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27822954944,-27782500864⟩ : DyadicInterval 40),(⟨776014634048,776034880352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161273282944,161371683456⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189198159552,-189062820800⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2161_ok : ecellOkT e2161 = true := by decide +kernel
theorem e2161_pos {a z : ℝ} (ha1 : ((1294173/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((647511/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2161 e2161_ok ha1 ha2 hz1 hz2 hz

-- box ['323331/2048000', '1294173/8192000', '7999/8000', '1']  interval_lower 191648477/1099511627776
noncomputable def e2162 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273098636623,0,true,161174873664,161174873728⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925924618929,0,false,-188927498816,-188927498752⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273212587475,0,true,161273282944,161273283008⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925810668077,0,false,-189062820864,-189062820800⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273076938246,0,true,161156133696,161156133760⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925946317306,0,false,-188901732864,-188901732800⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522684227,0,true,11056384,11056448⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500571325,0,false,-11056512,-11056448⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627664,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1273087782875,0,true,161165499776,161165499840⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨925935472677,0,false,-188914610368,-188914610304⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1273212591840,0,true,161273286720,161273286784⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨925810663712,0,false,-189062826048,-189062825984⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1072070330972,0,false,-27789539264,-27789539200⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1072109751473,0,false,-27749110528,-27749110464⟩
    { al := (323331/2048000), au := (1294173/8192000), zl := (7999/8000), zu := 1,
      A := ⟨173587008847,173700959699⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161174873664,161174873728⟩ : DyadicInterval 40),(⟨-188927498816,-188927498752⟩ : DyadicInterval 40),(⟨748363233677,748363253007⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161273282944,161273283008⟩ : DyadicInterval 40),(⟨-189062820864,-189062820800⟩ : DyadicInterval 40),(⟨748345085710,748345105039⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161156133696,161156133760⟩ : DyadicInterval 40),(⟨-188901732864,-188901732800⟩ : DyadicInterval 40),(⟨748366688023,748366707352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161273282944,161273283008⟩ : DyadicInterval 40),(⟨-189062820864,-189062820800⟩ : DyadicInterval 40),(⟨748345085710,748345105039⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11056451⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11056384,11056448⟩ : DyadicInterval 40),(⟨-11056512,-11056448⟩ : DyadicInterval 40),(⟨762123383504,762123402833⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨173576155099,173700964064⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161165499776,161165499840⟩ : DyadicInterval 40),(⟨-188914610368,-188914610304⟩ : DyadicInterval 40),(⟨748364961641,748364980971⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161273286720,161273286784⟩ : DyadicInterval 40),(⟨-189062826048,-189062825984⟩ : DyadicInterval 40),(⟨748345085011,748345104340⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27789539264,-27749110464⟩ : DyadicInterval 40),(⟨775997938848,776018172512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨161174873664,161273283008⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189062820864,-188927498752⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2162_ok : ecellOkT e2162 = true := by decide +kernel
theorem e2162_pos {a z : ℝ} (ha1 : ((323331/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1294173/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2162 e2162_ok ha1 ha2 hz1 hz2 hz

-- box ['1294173/8192000', '647511/4096000', '7999/8000', '1']  interval_lower 192781557/1099511627776
noncomputable def e2163 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273212587474,0,true,161273282944,161273283008⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925810668078,0,false,-189062820864,-189062820800⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273326538327,0,true,161371683392,161371683456⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925696717225,0,false,-189198159552,-189198159488⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273190874853,0,true,161254532352,161254532416⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925832380699,0,false,-189037034816,-189037034752⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522691748,0,true,11063872,11063936⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500563804,0,false,-11064064,-11064000⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627664,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1273201726604,0,true,161263903744,161263903808⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨925821528948,0,false,-189049922304,-189049922240⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1273326542693,0,true,161371687168,161371687232⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨925696712859,0,false,-189198164736,-189198164672⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1072034315227,0,false,-27826477568,-27826477504⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1072073763848,0,false,-27786018560,-27786018496⟩
    { al := (1294173/8192000), au := (647511/4096000), zl := (7999/8000), zu := 1,
      A := ⟨173700959698,173814910551⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161273282944,161273283008⟩ : DyadicInterval 40),(⟨-189062820864,-189062820800⟩ : DyadicInterval 40),(⟨748345085710,748345105039⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161371683392,161371683456⟩ : DyadicInterval 40),(⟨-189198159552,-189198159488⟩ : DyadicInterval 40),(⟨748326925638,748326944968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161254532352,161254532416⟩ : DyadicInterval 40),(⟨-189037034816,-189037034752⟩ : DyadicInterval 40),(⟨748348544627,748348563957⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161371683392,161371683456⟩ : DyadicInterval 40),(⟨-189198159552,-189198159488⟩ : DyadicInterval 40),(⟨748326925638,748326944968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11063972⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11063872,11063936⟩ : DyadicInterval 40),(⟨-11064064,-11064000⟩ : DyadicInterval 40),(⟨762123383536,762123402865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨173690098828,173814914917⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161263903744,161263903808⟩ : DyadicInterval 40),(⟨-189049922304,-189049922240⟩ : DyadicInterval 40),(⟨748346815935,748346835264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161371687168,161371687232⟩ : DyadicInterval 40),(⟨-189198164736,-189198164672⟩ : DyadicInterval 40),(⟨748326924938,748326944267⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27826477568,-27786018496⟩ : DyadicInterval 40),(⟨776016392864,776036641664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨161273282944,161371683456⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189198159552,-189062820800⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2163_ok : ecellOkT e2163 = true := by decide +kernel
theorem e2163_pos {a z : ℝ} (ha1 : ((1294173/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((647511/4096000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2163 e2163_ok ha1 ha2 hz1 hz2 hz

-- box ['647511/4096000', '1295871/8192000', '3999/4000', '7999/8000']  interval_lower 194080577/1099511627776
noncomputable def e2164 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273326538326,0,true,161371683392,161371683456⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925696717226,0,false,-189198159552,-189198159488⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273440489178,0,true,161470075008,161470075072⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925582766374,0,false,-189333514880,-189333514816⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273283084598,0,true,161334160640,161334160704⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925740170954,0,false,-189146547840,-189146547776⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273418748071,0,true,161451303168,161451303232⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925604507481,0,false,-189307688640,-189307688576⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522691181,0,true,11063296,11063360⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500564371,0,false,-11063488,-11063424⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533770455,0,true,22142400,22142464⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489485097,0,false,-22142912,-22142848⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627330,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627665,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273304806940,0,true,161352918272,161352918336⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925718448612,0,false,-189172348032,-189172347968⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273429623002,0,true,161460692928,161460692992⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925593632550,0,false,-189320606848,-189320606784⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072001714920,0,false,-27859913920,-27859913856⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072041186936,0,false,-27819429696,-27819429632⟩
    { al := (647511/4096000), au := (1295871/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨173814910550,173928861402⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161371683392,161371683456⟩ : DyadicInterval 40),(⟨-189198159552,-189198159488⟩ : DyadicInterval 40),(⟨748326925638,748326944968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161470075008,161470075072⟩ : DyadicInterval 40),(⟨-189333514880,-189333514816⟩ : DyadicInterval 40),(⟨748308753461,748308772790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161334160640,161334160704⟩ : DyadicInterval 40),(⟨-189146547840,-189146547776⟩ : DyadicInterval 40),(⟨748333852176,748333871505⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161451303168,161451303232⟩ : DyadicInterval 40),(⟨-189307688640,-189307688576⟩ : DyadicInterval 40),(⟨748312221540,748312240870⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11063405,22142679⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11063296,11063360⟩ : DyadicInterval 40),(⟨-11063488,-11063424⟩ : DyadicInterval 40),(⟨762123383536,762123402865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22142400,22142464⟩ : DyadicInterval 40),(⟨-22142912,-22142848⟩ : DyadicInterval 40),(⟨762123383362,762123402691⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173793179164,173917995226⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161352918272,161352918336⟩ : DyadicInterval 40),(⟨-189172348032,-189172347968⟩ : DyadicInterval 40),(⟨748330389852,748330409181⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161460692928,161460692992⟩ : DyadicInterval 40),(⟨-189320606848,-189320606784⟩ : DyadicInterval 40),(⟨748310486830,748310506160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27859913920,-27819429632⟩ : DyadicInterval 40),(⟨776033098432,776053359840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161371683392,161470075072⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189333514880,-189198159488⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2164_ok : ecellOkT e2164 = true := by decide +kernel
theorem e2164_pos {a z : ℝ} (ha1 : ((647511/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1295871/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2164 e2164_ok ha1 ha2 hz1 hz2 hz

-- box ['1295871/8192000', '16209/102400', '3999/4000', '7999/8000']  interval_lower 195219315/1099511627776
noncomputable def e2165 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273440489177,0,true,161470075008,161470075072⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925582766375,0,false,-189333514880,-189333514816⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273554440029,0,true,161568457856,161568457920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925468815523,0,false,-189468886912,-189468886848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273397006961,0,true,161432531008,161432531072⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925626248591,0,false,-189281862976,-189281862912⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273532684678,0,true,161549675392,161549675456⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925490570874,0,false,-189443040512,-189443040448⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522698703,0,true,11070848,11070912⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500556849,0,false,-11071040,-11070976⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533785500,0,true,22157440,22157504⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489470052,0,false,-22157952,-22157888⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627329,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627665,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273418743543,0,true,161451299264,161451299328⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925604512009,0,false,-189307683264,-189307683200⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273543566734,0,true,161559070464,161559070528⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925479688818,0,false,-189455968832,-189455968768⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071965656444,0,false,-27896898368,-27896898304⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072005156585,0,false,-27856383936,-27856383872⟩
    { al := (1295871/8192000), au := (16209/102400), zl := (3999/4000), zu := (7999/8000),
      A := ⟨173928861401,174042812253⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161470075008,161470075072⟩ : DyadicInterval 40),(⟨-189333514880,-189333514816⟩ : DyadicInterval 40),(⟨748308753461,748308772790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161568457856,161568457920⟩ : DyadicInterval 40),(⟨-189468886912,-189468886848⟩ : DyadicInterval 40),(⟨748290569166,748290588496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161432531008,161432531072⟩ : DyadicInterval 40),(⟨-189281862976,-189281862912⟩ : DyadicInterval 40),(⟨748315689166,748315708495⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161549675392,161549675456⟩ : DyadicInterval 40),(⟨-189443040512,-189443040448⟩ : DyadicInterval 40),(⟨748294041809,748294061139⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11070927,22157724⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11070848,11070912⟩ : DyadicInterval 40),(⟨-11071040,-11070976⟩ : DyadicInterval 40),(⟨762123383536,762123402865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22157440,22157504⟩ : DyadicInterval 40),(⟨-22157952,-22157888⟩ : DyadicInterval 40),(⟨762123383361,762123402690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173907115767,174031938958⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161451299264,161451299328⟩ : DyadicInterval 40),(⟨-189307683264,-189307683200⟩ : DyadicInterval 40),(⟨748312222260,748312241590⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161559070464,161559070528⟩ : DyadicInterval 40),(⟨-189455968832,-189455968768⟩ : DyadicInterval 40),(⟨748292304830,748292324159⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27896898368,-27856383872⟩ : DyadicInterval 40),(⟨776051575552,776071852064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161470075008,161568457920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189468886912,-189333514816⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2165_ok : ecellOkT e2165 = true := by decide +kernel
theorem e2165_pos {a z : ℝ} (ha1 : ((1295871/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((16209/102400 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2165 e2165_ok ha1 ha2 hz1 hz2 hz

-- box ['647511/4096000', '1295871/8192000', '7999/8000', '1']  interval_lower 193917119/1099511627776
noncomputable def e2166 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273326538326,0,true,161371683392,161371683456⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925696717226,0,false,-189198159552,-189198159488⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273440489178,0,true,161470075008,161470075072⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925582766374,0,false,-189333514880,-189333514816⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273304811462,0,true,161352922176,161352922240⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925718444090,0,false,-189172353408,-189172353344⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522699270,0,true,11071424,11071488⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500556282,0,false,-11071552,-11071488⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627664,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1273315670333,0,true,161362298880,161362298944⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨925707585219,0,false,-189185250944,-189185250880⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1273440493543,0,true,161470078784,161470078848⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨925582762009,0,false,-189333520064,-189333520000⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1071998275863,0,false,-27863441216,-27863441152⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1072037752607,0,false,-27822952064,-27822952000⟩
    { al := (647511/4096000), au := (1295871/8192000), zl := (7999/8000), zu := 1,
      A := ⟨173814910550,173928861402⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161371683392,161371683456⟩ : DyadicInterval 40),(⟨-189198159552,-189198159488⟩ : DyadicInterval 40),(⟨748326925638,748326944968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161470075008,161470075072⟩ : DyadicInterval 40),(⟨-189333514880,-189333514816⟩ : DyadicInterval 40),(⟨748308753461,748308772790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161352922176,161352922240⟩ : DyadicInterval 40),(⟨-189172353408,-189172353344⟩ : DyadicInterval 40),(⟨748330389133,748330408463⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161470075008,161470075072⟩ : DyadicInterval 40),(⟨-189333514880,-189333514816⟩ : DyadicInterval 40),(⟨748308753461,748308772790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11071494⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11071424,11071488⟩ : DyadicInterval 40),(⟨-11071552,-11071488⟩ : DyadicInterval 40),(⟨762123383504,762123402833⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨173804042557,173928865767⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161362298880,161362298944⟩ : DyadicInterval 40),(⟨-189185250944,-189185250880⟩ : DyadicInterval 40),(⟨748328658153,748328677482⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161470078784,161470078848⟩ : DyadicInterval 40),(⟨-189333520064,-189333520000⟩ : DyadicInterval 40),(⟨748308752760,748308772089⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27863441216,-27822952000⟩ : DyadicInterval 40),(⟨776034859616,776055123488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨161371683392,161470075072⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189333514880,-189198159488⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2166_ok : ecellOkT e2166 = true := by decide +kernel
theorem e2166_pos {a z : ℝ} (ha1 : ((647511/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1295871/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2166 e2166_ok ha1 ha2 hz1 hz2 hz

-- box ['1295871/8192000', '16209/102400', '7999/8000', '1']  interval_lower 97527819/549755813888
noncomputable def e2167 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273440489177,0,true,161470075008,161470075072⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925582766375,0,false,-189333514880,-189333514816⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273554440029,0,true,161568457856,161568457920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925468815523,0,false,-189468886912,-189468886848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273418748069,0,true,161451303168,161451303232⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925604507483,0,false,-189307688640,-189307688576⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522706792,0,true,11078912,11078976⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500548760,0,false,-11079104,-11079040⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627664,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1273429614059,0,true,161460685184,161460685248⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨925593641493,0,false,-189320596224,-189320596160⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1273554444395,0,true,161568461632,161568461696⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨925468811157,0,false,-189468892096,-189468892032⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1071962212879,0,false,-27900430400,-27900430336⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1072001717750,0,false,-27859911040,-27859910976⟩
    { al := (1295871/8192000), au := (16209/102400), zl := (7999/8000), zu := 1,
      A := ⟨173928861401,174042812253⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161470075008,161470075072⟩ : DyadicInterval 40),(⟨-189333514880,-189333514816⟩ : DyadicInterval 40),(⟨748308753461,748308772790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161568457856,161568457920⟩ : DyadicInterval 40),(⟨-189468886912,-189468886848⟩ : DyadicInterval 40),(⟨748290569166,748290588496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161451303168,161451303232⟩ : DyadicInterval 40),(⟨-189307688640,-189307688576⟩ : DyadicInterval 40),(⟨748312221541,748312240870⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161568457856,161568457920⟩ : DyadicInterval 40),(⟨-189468886912,-189468886848⟩ : DyadicInterval 40),(⟨748290569166,748290588496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11079016⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11078912,11078976⟩ : DyadicInterval 40),(⟨-11079104,-11079040⟩ : DyadicInterval 40),(⟨762123383536,762123402865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨173917986283,174042816619⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161460685184,161460685248⟩ : DyadicInterval 40),(⟨-189320596224,-189320596160⟩ : DyadicInterval 40),(⟨748310488270,748310507599⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161568461632,161568461696⟩ : DyadicInterval 40),(⟨-189468892096,-189468892032⟩ : DyadicInterval 40),(⟨748290568464,748290587794⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27900430400,-27859910976⟩ : DyadicInterval 40),(⟨776053339104,776073618080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨161470075008,161568457920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189468886912,-189333514816⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2167_ok : ecellOkT e2167 = true := by decide +kernel
theorem e2167_pos {a z : ℝ} (ha1 : ((1295871/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((16209/102400 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2167 e2167_ok ha1 ha2 hz1 hz2 hz

-- box ['16209/102400', '1297569/8192000', '999/1000', '7993/8000']  interval_lower 197345755/1099511627776
noncomputable def e2168 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273554440028,0,true,161568457856,161568457920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925468815524,0,false,-189468886912,-189468886848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273668390880,0,true,161666831872,161666831936⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925354864672,0,false,-189604275584,-189604275520⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273380397215,0,true,161418189312,161418189376⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925642858337,0,false,-189262133184,-189262133120⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273516003713,0,true,161535273728,161535273792⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925507251839,0,false,-189423223232,-189423223168⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589177392,0,true,77546880,77546944⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434078160,0,false,-77552384,-77552320⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099600316850,0,true,88685440,88685504⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099422938702,0,false,-88692672,-88692608⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620622,0,false,-7168,-7104⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622307,0,false,-5504,-5440⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273467414837,0,true,161493322880,161493322944⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925555840715,0,false,-189365500672,-189365500608⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273592202271,0,true,161601059072,161601059136⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925431053281,0,false,-189513751552,-189513751488⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071950258117,0,false,-27912692480,-27912692416⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071989757987,0,false,-27872177792,-27872177728⟩
    { al := (16209/102400), au := (1297569/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨174042812252,174156763104⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161568457856,161568457920⟩ : DyadicInterval 40),(⟨-189468886912,-189468886848⟩ : DyadicInterval 40),(⟨748290569166,748290588496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161666831872,161666831936⟩ : DyadicInterval 40),(⟨-189604275584,-189604275520⟩ : DyadicInterval 40),(⟨748272372763,748272392093⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161418189312,161418189376⟩ : DyadicInterval 40),(⟨-189262133184,-189262133120⟩ : DyadicInterval 40),(⟨748318338056,748318357385⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161535273728,161535273792⟩ : DyadicInterval 40),(⟨-189423223232,-189423223168⟩ : DyadicInterval 40),(⟨748296704178,748296723507⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨77549616,88689074⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77546880,77546944⟩ : DyadicInterval 40),(⟨-77552384,-77552320⟩ : DyadicInterval 40),(⟨762123380834,762123400163⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨88685440,88685504⟩ : DyadicInterval 40),(⟨-88692672,-88692608⟩ : DyadicInterval 40),(⟨762123380013,762123399343⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7168,-5440⟩ : DyadicInterval 40),(⟨762123386336,762123406464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173955787061,174080574495⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161493322880,161493322944⟩ : DyadicInterval 40),(⟨-189365500672,-189365500608⟩ : DyadicInterval 40),(⟨748304457741,748304477070⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161601059072,161601059136⟩ : DyadicInterval 40),(⟨-189513751552,-189513751488⟩ : DyadicInterval 40),(⟨748284540362,748284559692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27912692480,-27872177728⟩ : DyadicInterval 40),(⟨776059472480,776079749120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161568457856,161666831936⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189604275584,-189468886848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2168_ok : ecellOkT e2168 = true := by decide +kernel
theorem e2168_pos {a z : ℝ} (ha1 : ((16209/102400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1297569/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2168 e2168_ok ha1 ha2 hz1 hz2 hz

-- box ['1297569/8192000', '649209/4096000', '999/1000', '7993/8000']  interval_lower 99246209/549755813888
noncomputable def e2169 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273668390879,0,true,161666831872,161666831936⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925354864673,0,false,-189604275584,-189604275520⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273782341731,0,true,161765197120,161765197184⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925240913821,0,false,-189739680896,-189739680832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273494234115,0,true,161516478400,161516478464⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925529021437,0,false,-189397361024,-189397360960⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273629854857,0,true,161633564608,161633564672⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925393400695,0,false,-189558487808,-189558487744⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589230051,0,true,77599488,77599552⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434025501,0,false,-77605056,-77604992⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099600377037,0,true,88745664,88745728⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099422878515,0,false,-88752896,-88752832⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620612,0,false,-7168,-7104⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622299,0,false,-5504,-5440⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273581308711,0,true,161591654400,161591654464⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925441946841,0,false,-189500808896,-189500808832⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273706103271,0,true,161699387136,161699387200⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925317152281,0,false,-189649086528,-189649086464⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071914179484,0,false,-27949699392,-27949699328⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071953707464,0,false,-27909154496,-27909154432⟩
    { al := (1297569/8192000), au := (649209/4096000), zl := (999/1000), zu := (7993/8000),
      A := ⟨174156763103,174270713955⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161666831872,161666831936⟩ : DyadicInterval 40),(⟨-189604275584,-189604275520⟩ : DyadicInterval 40),(⟨748272372764,748272392093⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161765197120,161765197184⟩ : DyadicInterval 40),(⟨-189739680896,-189739680832⟩ : DyadicInterval 40),(⟨748254164215,748254183544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161516478400,161516478464⟩ : DyadicInterval 40),(⟨-189397361024,-189397360960⟩ : DyadicInterval 40),(⟨748300178331,748300197661⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161633564608,161633564672⟩ : DyadicInterval 40),(⟨-189558487808,-189558487744⟩ : DyadicInterval 40),(⟨748278527799,748278547129⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨77602275,88749261⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77599488,77599552⟩ : DyadicInterval 40),(⟨-77605056,-77604992⟩ : DyadicInterval 40),(⟨762123380858,762123400188⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨88745664,88745728⟩ : DyadicInterval 40),(⟨-88752896,-88752832⟩ : DyadicInterval 40),(⟨762123380004,762123399333⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7168,-5440⟩ : DyadicInterval 40),(⟨762123386336,762123406464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174069680935,174194475495⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161591654400,161591654464⟩ : DyadicInterval 40),(⟨-189500808896,-189500808832⟩ : DyadicInterval 40),(⟨748286279693,748286299022⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161699387136,161699387200⟩ : DyadicInterval 40),(⟨-189649086528,-189649086464⟩ : DyadicInterval 40),(⟨748266347918,748266367247⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27949699392,-27909154432⟩ : DyadicInterval 40),(⟨776077960832,776098252576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161666831872,161765197184⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189739680896,-189604275520⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2169_ok : ecellOkT e2169 = true := by decide +kernel
theorem e2169_pos {a z : ℝ} (ha1 : ((1297569/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((649209/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2169 e2169_ok ha1 ha2 hz1 hz2 hz

-- box ['16209/102400', '1297569/8192000', '7993/8000', '3997/4000']  interval_lower 197181729/1099511627776
noncomputable def e2170 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273554440028,0,true,161568457856,161568457920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925468815524,0,false,-189468886912,-189468886848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273668390880,0,true,161666831872,161666831936⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925354864672,0,false,-189604275584,-189604275520⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273402152567,0,true,161436974016,161436974080⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925621102985,0,false,-189287975232,-189287975168⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273537773308,0,true,161554068672,161554068736⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925485482244,0,false,-189449086016,-189449085952⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578098993,0,true,66469184,66469248⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445156559,0,false,-66473280,-66473216⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589230928,0,true,77600384,77600448⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434024624,0,false,-77605952,-77605888⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622298,0,false,-5504,-5440⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623758,0,false,-4032,-3968⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273478292330,0,true,161502714432,161502714496⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925544963222,0,false,-189378422656,-189378422592⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273603086905,0,true,161610455872,161610455936⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925420168647,0,false,-189526683776,-189526683712⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071946811382,0,false,-27916227840,-27916227776⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071986315982,0,false,-27875708160,-27875708096⟩
    { al := (16209/102400), au := (1297569/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨174042812252,174156763104⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161568457856,161568457920⟩ : DyadicInterval 40),(⟨-189468886912,-189468886848⟩ : DyadicInterval 40),(⟨748290569166,748290588496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161666831872,161666831936⟩ : DyadicInterval 40),(⟨-189604275584,-189604275520⟩ : DyadicInterval 40),(⟨748272372763,748272392093⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161436974016,161436974080⟩ : DyadicInterval 40),(⟨-189287975232,-189287975168⟩ : DyadicInterval 40),(⟨748314868465,748314887794⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161554068672,161554068736⟩ : DyadicInterval 40),(⟨-189449086016,-189449085952⟩ : DyadicInterval 40),(⟨748293229606,748293248936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨66471217,77603152⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66469184,66469248⟩ : DyadicInterval 40),(⟨-66473280,-66473216⟩ : DyadicInterval 40),(⟨762123381581,762123400910⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77600384,77600448⟩ : DyadicInterval 40),(⟨-77605952,-77605888⟩ : DyadicInterval 40),(⟨762123380858,762123400187⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5504,-3968⟩ : DyadicInterval 40),(⟨762123385600,762123405632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173966664554,174091459129⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161502714432,161502714496⟩ : DyadicInterval 40),(⟨-189378422656,-189378422592⟩ : DyadicInterval 40),(⟨748302722186,748302741515⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161610455872,161610455936⟩ : DyadicInterval 40),(⟨-189526683776,-189526683712⟩ : DyadicInterval 40),(⟨748282802405,748282821734⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27916227840,-27875708096⟩ : DyadicInterval 40),(⟨776061237664,776081516800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161568457856,161666831936⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189604275584,-189468886848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2170_ok : ecellOkT e2170 = true := by decide +kernel
theorem e2170_pos {a z : ℝ} (ha1 : ((16209/102400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1297569/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2170 e2170_ok ha1 ha2 hz1 hz2 hz

-- box ['1297569/8192000', '649209/4096000', '7993/8000', '3997/4000']  interval_lower 99163971/549755813888
noncomputable def e2171 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273668390879,0,true,161666831872,161666831936⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925354864673,0,false,-189604275584,-189604275520⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273782341731,0,true,161765197120,161765197184⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925240913821,0,false,-189739680896,-189739680832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273516003711,0,true,161535273664,161535273728⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925507251841,0,false,-189423223232,-189423223168⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273651638696,0,true,161652370240,161652370304⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925371616856,0,false,-189584370688,-189584370624⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578144130,0,true,66514304,66514368⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445111422,0,false,-66518400,-66518336⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589283593,0,true,77653056,77653120⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433971959,0,false,-77658560,-77658496⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622291,0,false,-5504,-5440⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623753,0,false,-4032,-3968⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273592193320,0,true,161601051328,161601051392⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925431062232,0,false,-189513740928,-189513740864⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273716995032,0,true,161708789248,161708789312⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925306260520,0,false,-189662028800,-189662028736⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071910728236,0,false,-27953239488,-27953239424⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071950260953,0,false,-27912689600,-27912689536⟩
    { al := (1297569/8192000), au := (649209/4096000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨174156763103,174270713955⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161666831872,161666831936⟩ : DyadicInterval 40),(⟨-189604275584,-189604275520⟩ : DyadicInterval 40),(⟨748272372764,748272392093⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161765197120,161765197184⟩ : DyadicInterval 40),(⟨-189739680896,-189739680832⟩ : DyadicInterval 40),(⟨748254164215,748254183544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161535273664,161535273728⟩ : DyadicInterval 40),(⟨-189423223232,-189423223168⟩ : DyadicInterval 40),(⟨748296704216,748296723545⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161652370240,161652370304⟩ : DyadicInterval 40),(⟨-189584370688,-189584370624⟩ : DyadicInterval 40),(⟨748275048594,748275067924⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨66516354,77655817⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66514304,66514368⟩ : DyadicInterval 40),(⟨-66518400,-66518336⟩ : DyadicInterval 40),(⟨762123381575,762123400905⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77653056,77653120⟩ : DyadicInterval 40),(⟨-77658560,-77658496⟩ : DyadicInterval 40),(⟨762123380819,762123400148⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5504,-3968⟩ : DyadicInterval 40),(⟨762123385600,762123405632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174080565544,174205367256⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161601051328,161601051392⟩ : DyadicInterval 40),(⟨-189513740928,-189513740864⟩ : DyadicInterval 40),(⟨748284541805,748284561135⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161708789248,161708789312⟩ : DyadicInterval 40),(⟨-189662028800,-189662028736⟩ : DyadicInterval 40),(⟨748264607659,748264626989⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27953239488,-27912689536⟩ : DyadicInterval 40),(⟨776079728384,776100022624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161666831872,161765197184⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189739680896,-189604275520⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2171_ok : ecellOkT e2171 = true := by decide +kernel
theorem e2171_pos {a z : ℝ} (ha1 : ((1297569/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((649209/4096000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2171 e2171_ok ha1 ha2 hz1 hz2 hz

-- box ['649209/4096000', '1299267/8192000', '999/1000', '7993/8000']  interval_lower 199641853/1099511627776
noncomputable def e2172 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273782341730,0,true,161765197120,161765197184⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925240913822,0,false,-189739680896,-189739680832⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273896292582,0,true,161863553536,161863553600⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925126962970,0,false,-189875102912,-189875102848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273608071016,0,true,161614758720,161614758784⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925415184536,0,false,-189532605504,-189532605440⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273743706001,0,true,161731846784,161731846848⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925279549551,0,false,-189693769024,-189693768960⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589282715,0,true,77652160,77652224⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433972837,0,false,-77657728,-77657664⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099600437228,0,true,88805824,88805888⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099422818324,0,false,-88813056,-88812992⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620602,0,false,-7232,-7168⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622292,0,false,-5504,-5440⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273695202591,0,true,161689977216,161689977280⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925328052961,0,false,-189636133824,-189636133760⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273820004273,0,true,161797706432,161797706496⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925203251279,0,false,-189784438144,-189784438080⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071878077252,0,false,-27986731712,-27986731648⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071917633344,0,false,-27946156608,-27946156544⟩
    { al := (649209/4096000), au := (1299267/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨174270713954,174384664806⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161765197120,161765197184⟩ : DyadicInterval 40),(⟨-189739680896,-189739680832⟩ : DyadicInterval 40),(⟨748254164215,748254183544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161863553536,161863553600⟩ : DyadicInterval 40),(⟨-189875102912,-189875102848⟩ : DyadicInterval 40),(⟨748235943582,748235962911⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161614758720,161614758784⟩ : DyadicInterval 40),(⟨-189532605504,-189532605440⟩ : DyadicInterval 40),(⟨748282006510,748282025840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161731846784,161731846848⟩ : DyadicInterval 40),(⟨-189693769024,-189693768960⟩ : DyadicInterval 40),(⟨748260339280,748260358609⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨77654939,88809452⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77652160,77652224⟩ : DyadicInterval 40),(⟨-77657728,-77657664⟩ : DyadicInterval 40),(⟨762123380851,762123400180⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨88805824,88805888⟩ : DyadicInterval 40),(⟨-88813056,-88812992⟩ : DyadicInterval 40),(⟨762123379994,762123399324⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7232,-5440⟩ : DyadicInterval 40),(⟨762123386336,762123406496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174183574815,174308376497⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161689977216,161689977280⟩ : DyadicInterval 40),(⟨-189636133824,-189636133760⟩ : DyadicInterval 40),(⟨748268089512,748268108841⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161797706432,161797706496⟩ : DyadicInterval 40),(⟨-189784438144,-189784438080⟩ : DyadicInterval 40),(⟨748248143347,748248162676⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27986731712,-27946156544⟩ : DyadicInterval 40),(⟨776096461888,776116768736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161765197120,161863553600⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189875102912,-189739680832⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2172_ok : ecellOkT e2172 = true := by decide +kernel
theorem e2172_pos {a z : ℝ} (ha1 : ((649209/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1299267/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2172 e2172_ok ha1 ha2 hz1 hz2 hz

-- box ['1299267/8192000', '325029/2048000', '999/1000', '7993/8000']  interval_lower 25099269/137438953472
noncomputable def e2173 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273896292581,0,true,161863553536,161863553600⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925126962971,0,false,-189875102912,-189875102848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274010243433,0,true,161961901184,161961901248⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925013012119,0,false,-190010541632,-190010541568⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273721907916,0,true,161713030208,161713030272⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925301347636,0,false,-189667866624,-189667866560⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273857557145,0,true,161830120128,161830120192⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925165698407,0,false,-189829066880,-189829066816⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589335381,0,true,77704832,77704896⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433920171,0,false,-77710400,-77710336⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099600497424,0,true,88866048,88866112⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099422758128,0,false,-88873280,-88873216⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620592,0,false,-7232,-7168⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622285,0,false,-5504,-5440⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273809096463,0,true,161788291200,161788291264⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925214159089,0,false,-189771475392,-189771475328⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273933905273,0,true,161896016896,161896016960⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925089350279,0,false,-189919806464,-189919806400⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071841951422,0,false,-28023789504,-28023789440⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071881535631,0,false,-27983184192,-27983184128⟩
    { al := (1299267/8192000), au := (325029/2048000), zl := (999/1000), zu := (7993/8000),
      A := ⟨174384664805,174498615657⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161863553536,161863553600⟩ : DyadicInterval 40),(⟨-189875102912,-189875102848⟩ : DyadicInterval 40),(⟨748235943582,748235962912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161961901184,161961901248⟩ : DyadicInterval 40),(⟨-190010541632,-190010541568⟩ : DyadicInterval 40),(⟨748217710827,748217730157⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161713030208,161713030272⟩ : DyadicInterval 40),(⟨-189667866624,-189667866560⟩ : DyadicInterval 40),(⟨748263822628,748263841958⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161830120128,161830120192⟩ : DyadicInterval 40),(⟨-189829066880,-189829066816⟩ : DyadicInterval 40),(⟨748242138692,748242158022⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨77707605,88869648⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77704832,77704896⟩ : DyadicInterval 40),(⟨-77710400,-77710336⟩ : DyadicInterval 40),(⟨762123380843,762123400173⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨88866048,88866112⟩ : DyadicInterval 40),(⟨-88873280,-88873216⟩ : DyadicInterval 40),(⟨762123379984,762123399314⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7232,-5440⟩ : DyadicInterval 40),(⟨762123386336,762123406496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174297468687,174422277497⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161788291200,161788291264⟩ : DyadicInterval 40),(⟨-189771475392,-189771475328⟩ : DyadicInterval 40),(⟨748249887248,748249906577⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161896016896,161896016960⟩ : DyadicInterval 40),(⟨-189919806464,-189919806400⟩ : DyadicInterval 40),(⟨748229926714,748229946043⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28023789504,-27983184128⟩ : DyadicInterval 40),(⟨776114975680,776135297632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161863553536,161961901248⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190010541632,-189875102848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2173_ok : ecellOkT e2173 = true := by decide +kernel
theorem e2173_pos {a z : ℝ} (ha1 : ((1299267/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((325029/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2173 e2173_ok ha1 ha2 hz1 hz2 hz

-- box ['649209/4096000', '1299267/8192000', '7993/8000', '3997/4000']  interval_lower 199476985/1099511627776
noncomputable def e2174 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273782341730,0,true,161765197120,161765197184⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925240913822,0,false,-189739680896,-189739680832⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273896292582,0,true,161863553536,161863553600⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925126962970,0,false,-189875102912,-189875102848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273629854855,0,true,161633564608,161633564672⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925393400697,0,false,-189558487808,-189558487744⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273765504084,0,true,161750662976,161750663040⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925257751468,0,false,-189719672064,-189719672000⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578189270,0,true,66559424,66559488⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445066282,0,false,-66563520,-66563456⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589336259,0,true,77705728,77705792⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433919293,0,false,-77711232,-77711168⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622283,0,false,-5504,-5440⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623747,0,false,-4032,-3968⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273706094320,0,true,161699379392,161699379456⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925317161232,0,false,-189649075904,-189649075840⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273830903149,0,true,161807113856,161807113920⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925192352403,0,false,-189797390464,-189797390400⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071874621491,0,false,-27990276608,-27990276544⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071914182322,0,false,-27949696448,-27949696384⟩
    { al := (649209/4096000), au := (1299267/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨174270713954,174384664806⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161765197120,161765197184⟩ : DyadicInterval 40),(⟨-189739680896,-189739680832⟩ : DyadicInterval 40),(⟨748254164215,748254183544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161863553536,161863553600⟩ : DyadicInterval 40),(⟨-189875102912,-189875102848⟩ : DyadicInterval 40),(⟨748235943582,748235962911⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161633564608,161633564672⟩ : DyadicInterval 40),(⟨-189558487808,-189558487744⟩ : DyadicInterval 40),(⟨748278527800,748278547129⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161750662976,161750663040⟩ : DyadicInterval 40),(⟨-189719672064,-189719672000⟩ : DyadicInterval 40),(⟨748256855536,748256874866⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨66561494,77708483⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66559424,66559488⟩ : DyadicInterval 40),(⟨-66563520,-66563456⟩ : DyadicInterval 40),(⟨762123381570,762123400899⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77705728,77705792⟩ : DyadicInterval 40),(⟨-77711232,-77711168⟩ : DyadicInterval 40),(⟨762123380811,762123400141⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5504,-3968⟩ : DyadicInterval 40),(⟨762123385600,762123405632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174194466544,174319275373⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161699379392,161699379456⟩ : DyadicInterval 40),(⟨-189649075904,-189649075840⟩ : DyadicInterval 40),(⟨748266349363,748266368692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161807113856,161807113920⟩ : DyadicInterval 40),(⟨-189797390464,-189797390400⟩ : DyadicInterval 40),(⟨748246400787,748246420116⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27990276608,-27949696384⟩ : DyadicInterval 40),(⟨776098231808,776118541184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161765197120,161863553600⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189875102912,-189739680832⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2174_ok : ecellOkT e2174 = true := by decide +kernel
theorem e2174_pos {a z : ℝ} (ha1 : ((649209/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1299267/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2174 e2174_ok ha1 ha2 hz1 hz2 hz

-- box ['1299267/8192000', '325029/2048000', '7993/8000', '3997/4000']  interval_lower 50157311/274877906944
noncomputable def e2175 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273896292581,0,true,161863553536,161863553600⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925126962971,0,false,-189875102912,-189875102848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274010243433,0,true,161961901184,161961901248⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925013012119,0,false,-190010541632,-190010541568⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273743705999,0,true,161731846720,161731846784⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925279549553,0,false,-189693769024,-189693768960⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273879369472,0,true,161848946944,161848947008⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925143886080,0,false,-189854990016,-189854989952⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578234414,0,true,66604608,66604672⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445021138,0,false,-66608704,-66608640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589388932,0,true,77758400,77758464⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433866620,0,false,-77763968,-77763904⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622276,0,false,-5504,-5440⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623742,0,false,-4096,-4032⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273819995316,0,true,161797698688,161797698752⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925203260236,0,false,-189784427520,-189784427456⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273944811273,0,true,161905429632,161905429696⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925078444279,0,false,-189932768832,-189932768768⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071838491143,0,false,-28027339136,-28027339072⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071878080093,0,false,-27986728832,-27986728768⟩
    { al := (1299267/8192000), au := (325029/2048000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨174384664805,174498615657⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161863553536,161863553600⟩ : DyadicInterval 40),(⟨-189875102912,-189875102848⟩ : DyadicInterval 40),(⟨748235943582,748235962912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161961901184,161961901248⟩ : DyadicInterval 40),(⟨-190010541632,-190010541568⟩ : DyadicInterval 40),(⟨748217710827,748217730157⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161731846720,161731846784⟩ : DyadicInterval 40),(⟨-189693769024,-189693768960⟩ : DyadicInterval 40),(⟨748260339317,748260358647⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161848946944,161848947008⟩ : DyadicInterval 40),(⟨-189854990016,-189854989952⟩ : DyadicInterval 40),(⟨748238650341,748238669670⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨66606638,77761156⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66604608,66604672⟩ : DyadicInterval 40),(⟨-66608704,-66608640⟩ : DyadicInterval 40),(⟨762123381564,762123400894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77758400,77758464⟩ : DyadicInterval 40),(⟨-77763968,-77763904⟩ : DyadicInterval 40),(⟨762123380836,762123400165⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5504,-4032⟩ : DyadicInterval 40),(⟨762123385632,762123405632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174308367540,174433183497⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161797698688,161797698752⟩ : DyadicInterval 40),(⟨-189784427520,-189784427456⟩ : DyadicInterval 40),(⟨748248144795,748248164125⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161905429632,161905429696⟩ : DyadicInterval 40),(⟨-189932768832,-189932768768⟩ : DyadicInterval 40),(⟨748228181847,748228201176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28027339136,-27986728768⟩ : DyadicInterval 40),(⟨776116748000,776137072448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161863553536,161961901248⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190010541632,-189875102848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2175_ok : ecellOkT e2175 = true := by decide +kernel
theorem e2175_pos {a z : ℝ} (ha1 : ((1299267/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((325029/2048000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2175 e2175_ok ha1 ha2 hz1 hz2 hz

-- box ['16209/102400', '1297569/8192000', '3997/4000', '1599/1600']  interval_lower 24627229/137438953472
noncomputable def e2176 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273554440028,0,true,161568457856,161568457920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925468815524,0,false,-189468886912,-189468886848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273668390880,0,true,161666831872,161666831936⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925354864672,0,false,-189604275584,-189604275520⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273423907918,0,true,161455758336,161455758400⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925599347634,0,false,-189313817984,-189313817920⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273559542904,0,true,161572863360,161572863424⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925463712648,0,false,-189474949440,-189474949376⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567020542,0,true,55391360,55391424⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456235010,0,false,-55394176,-55394112⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578144955,0,true,66515136,66515200⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445110597,0,false,-66519232,-66519168⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623751,0,false,-4032,-3968⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624986,0,false,-2816,-2752⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273489169839,0,true,161512105984,161512106048⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925534085713,0,false,-189391344768,-189391344704⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273613971567,0,true,161619852672,161619852736⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925409283985,0,false,-189539616128,-189539616064⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071943364423,0,false,-27919763456,-27919763392⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071982873757,0,false,-27879238784,-27879238720⟩
    { al := (16209/102400), au := (1297569/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨174042812252,174156763104⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161568457856,161568457920⟩ : DyadicInterval 40),(⟨-189468886912,-189468886848⟩ : DyadicInterval 40),(⟨748290569166,748290588496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161666831872,161666831936⟩ : DyadicInterval 40),(⟨-189604275584,-189604275520⟩ : DyadicInterval 40),(⟨748272372763,748272392093⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161455758336,161455758400⟩ : DyadicInterval 40),(⟨-189313817984,-189313817920⟩ : DyadicInterval 40),(⟨748311398510,748311417839⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161572863360,161572863424⟩ : DyadicInterval 40),(⟨-189474949440,-189474949376⟩ : DyadicInterval 40),(⟨748289754568,748289773897⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55392766,66517179⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55391360,55391424⟩ : DyadicInterval 40),(⟨-55394176,-55394112⟩ : DyadicInterval 40),(⟨762123382169,762123401498⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66515136,66515200⟩ : DyadicInterval 40),(⟨-66519232,-66519168⟩ : DyadicInterval 40),(⟨762123381575,762123400905⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4032,-2752⟩ : DyadicInterval 40),(⟨762123384992,762123404896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173977542063,174102343791⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161512105984,161512106048⟩ : DyadicInterval 40),(⟨-189391344768,-189391344704⟩ : DyadicInterval 40),(⟨748300986462,748301005791⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161619852672,161619852736⟩ : DyadicInterval 40),(⟨-189539616128,-189539616064⟩ : DyadicInterval 40),(⟨748281064276,748281083605⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27919763456,-27879238720⟩ : DyadicInterval 40),(⟨776063002976,776083284608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161568457856,161666831936⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189604275584,-189468886848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2176_ok : ecellOkT e2176 = true := by decide +kernel
theorem e2176_pos {a z : ℝ} (ha1 : ((16209/102400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1297569/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2176 e2176_ok ha1 ha2 hz1 hz2 hz

-- box ['1297569/8192000', '649209/4096000', '3997/4000', '1599/1600']  interval_lower 99081807/549755813888
noncomputable def e2177 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273668390879,0,true,161666831872,161666831936⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925354864673,0,false,-189604275584,-189604275520⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273782341731,0,true,161765197120,161765197184⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925240913821,0,false,-189739680896,-189739680832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273537773306,0,true,161554068672,161554068736⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925485482246,0,false,-189449086016,-189449085952⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273673422535,0,true,161671175488,161671175552⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925349833017,0,false,-189610254208,-189610254144⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567058157,0,true,55428928,55428992⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456197395,0,false,-55431808,-55431744⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578190096,0,true,66560256,66560320⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445065456,0,false,-66564352,-66564288⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623746,0,false,-4032,-3968⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624982,0,false,-2816,-2752⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273603077957,0,true,161610448128,161610448192⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925420177595,0,false,-189526673152,-189526673088⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273727886812,0,true,161718191360,161718191424⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925295368740,0,false,-189674971200,-189674971136⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071907276766,0,false,-27956779840,-27956779776⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071946814217,0,false,-27916224960,-27916224896⟩
    { al := (1297569/8192000), au := (649209/4096000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨174156763103,174270713955⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161666831872,161666831936⟩ : DyadicInterval 40),(⟨-189604275584,-189604275520⟩ : DyadicInterval 40),(⟨748272372764,748272392093⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161765197120,161765197184⟩ : DyadicInterval 40),(⟨-189739680896,-189739680832⟩ : DyadicInterval 40),(⟨748254164215,748254183544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161554068672,161554068736⟩ : DyadicInterval 40),(⟨-189449086016,-189449085952⟩ : DyadicInterval 40),(⟨748293229606,748293248936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161671175488,161671175552⟩ : DyadicInterval 40),(⟨-189610254208,-189610254144⟩ : DyadicInterval 40),(⟨748271568996,748271588325⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55430381,66562320⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55428928,55428992⟩ : DyadicInterval 40),(⟨-55431808,-55431744⟩ : DyadicInterval 40),(⟨762123382197,762123401526⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66560256,66560320⟩ : DyadicInterval 40),(⟨-66564352,-66564288⟩ : DyadicInterval 40),(⟨762123381570,762123400899⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4032,-2752⟩ : DyadicInterval 40),(⟨762123384992,762123404896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174091450181,174216259036⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161610448128,161610448192⟩ : DyadicInterval 40),(⟨-189526673152,-189526673088⟩ : DyadicInterval 40),(⟨748282803848,748282823177⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161718191360,161718191424⟩ : DyadicInterval 40),(⟨-189674971200,-189674971136⟩ : DyadicInterval 40),(⟨748262867231,748262886560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27956779840,-27916224896⟩ : DyadicInterval 40),(⟨776081496064,776101792800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161666831872,161765197184⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189739680896,-189604275520⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2177_ok : ecellOkT e2177 = true := by decide +kernel
theorem e2177_pos {a z : ℝ} (ha1 : ((1297569/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((649209/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2177 e2177_ok ha1 ha2 hz1 hz2 hz

-- box ['16209/102400', '1297569/8192000', '1599/1600', '1999/2000']  interval_lower 196853735/1099511627776
noncomputable def e2178 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273554440028,0,true,161568457856,161568457920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925468815524,0,false,-189468886912,-189468886848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273668390880,0,true,161666831872,161666831936⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925354864672,0,false,-189604275584,-189604275520⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273445663270,0,true,161474542400,161474542464⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925577592282,0,false,-189339661248,-189339661184⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273581312499,0,true,161591657728,161591657792⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925441943053,0,false,-189500813440,-189500813376⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555942040,0,true,44313344,44313408⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467313512,0,false,-44315200,-44315136⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567058931,0,true,55429696,55429760⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456196621,0,false,-55432576,-55432512⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624981,0,false,-2816,-2752⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625990,0,false,-1792,-1728⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273500047381,0,true,161521497472,161521497536⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925523208171,0,false,-189404267072,-189404267008⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273624856256,0,true,161629249344,161629249408⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925398399296,0,false,-189552548672,-189552548608⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071939917240,0,false,-27923299328,-27923299264⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071979431307,0,false,-27882769600,-27882769536⟩
    { al := (16209/102400), au := (1297569/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨174042812252,174156763104⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161568457856,161568457920⟩ : DyadicInterval 40),(⟨-189468886912,-189468886848⟩ : DyadicInterval 40),(⟨748290569166,748290588496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161666831872,161666831936⟩ : DyadicInterval 40),(⟨-189604275584,-189604275520⟩ : DyadicInterval 40),(⟨748272372763,748272392093⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161474542400,161474542464⟩ : DyadicInterval 40),(⟨-189339661248,-189339661184⟩ : DyadicInterval 40),(⟨748307928035,748307947364⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161591657728,161591657792⟩ : DyadicInterval 40),(⟨-189500813440,-189500813376⟩ : DyadicInterval 40),(⟨748286279072,748286298402⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨44314264,55431155⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44313344,44313408⟩ : DyadicInterval 40),(⟨-44315200,-44315136⟩ : DyadicInterval 40),(⟨762123382693,762123402023⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55429696,55429760⟩ : DyadicInterval 40),(⟨-55432576,-55432512⟩ : DyadicInterval 40),(⟨762123382197,762123401526⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2816,-1728⟩ : DyadicInterval 40),(⟨762123384480,762123404288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173988419605,174113228480⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161521497472,161521497536⟩ : DyadicInterval 40),(⟨-189404267072,-189404267008⟩ : DyadicInterval 40),(⟨748299250630,748299269960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161629249344,161629249408⟩ : DyadicInterval 40),(⟨-189552548672,-189552548608⟩ : DyadicInterval 40),(⟨748279326076,748279345406⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27923299328,-27882769536⟩ : DyadicInterval 40),(⟨776064768384,776085052544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161568457856,161666831936⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189604275584,-189468886848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2178_ok : ecellOkT e2178 = true := by decide +kernel
theorem e2178_pos {a z : ℝ} (ha1 : ((16209/102400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1297569/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2178 e2178_ok ha1 ha2 hz1 hz2 hz

-- box ['1297569/8192000', '649209/4096000', '1599/1600', '1999/2000']  interval_lower 197999279/1099511627776
noncomputable def e2179 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273668390879,0,true,161666831872,161666831936⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925354864673,0,false,-189604275584,-189604275520⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273782341731,0,true,161765197120,161765197184⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925240913821,0,false,-189739680896,-189739680832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273559542901,0,true,161572863360,161572863424⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925463712651,0,false,-189474949440,-189474949376⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273695206375,0,true,161689980480,161689980544⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925328049177,0,false,-189636138368,-189636138304⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555972132,0,true,44343424,44343488⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467283420,0,false,-44345280,-44345216⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567096548,0,true,55467328,55467392⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456159004,0,false,-55470208,-55470144⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624977,0,false,-2816,-2752⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625988,0,false,-1792,-1728⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273613962619,0,true,161619844928,161619844992⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925409292933,0,false,-189539605504,-189539605440⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273738778620,0,true,161727593344,161727593408⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925284476932,0,false,-189687913856,-189687913792⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071903825071,0,false,-27960320448,-27960320384⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071943367258,0,false,-27919760576,-27919760512⟩
    { al := (1297569/8192000), au := (649209/4096000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨174156763103,174270713955⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161666831872,161666831936⟩ : DyadicInterval 40),(⟨-189604275584,-189604275520⟩ : DyadicInterval 40),(⟨748272372764,748272392093⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161765197120,161765197184⟩ : DyadicInterval 40),(⟨-189739680896,-189739680832⟩ : DyadicInterval 40),(⟨748254164215,748254183544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161572863360,161572863424⟩ : DyadicInterval 40),(⟨-189474949440,-189474949376⟩ : DyadicInterval 40),(⟨748289754568,748289773897⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161689980480,161689980544⟩ : DyadicInterval 40),(⟨-189636138368,-189636138304⟩ : DyadicInterval 40),(⟨748268088929,748268108259⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨44344356,55468772⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44343424,44343488⟩ : DyadicInterval 40),(⟨-44345280,-44345216⟩ : DyadicInterval 40),(⟨762123382691,762123402020⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55467328,55467392⟩ : DyadicInterval 40),(⟨-55470208,-55470144⟩ : DyadicInterval 40),(⟨762123382193,762123401522⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2816,-1728⟩ : DyadicInterval 40),(⟨762123384480,762123404288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174102334843,174227150844⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161619844928,161619844992⟩ : DyadicInterval 40),(⟨-189539605504,-189539605440⟩ : DyadicInterval 40),(⟨748281065719,748281085048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161727593344,161727593408⟩ : DyadicInterval 40),(⟨-189687913856,-189687913792⟩ : DyadicInterval 40),(⟨748261126758,748261146087⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27960320448,-27919760512⟩ : DyadicInterval 40),(⟨776083263872,776103563104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161666831872,161765197184⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189739680896,-189604275520⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2179_ok : ecellOkT e2179 = true := by decide +kernel
theorem e2179_pos {a z : ℝ} (ha1 : ((1297569/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((649209/4096000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2179 e2179_ok ha1 ha2 hz1 hz2 hz

-- box ['649209/4096000', '1299267/8192000', '3997/4000', '1599/1600']  interval_lower 199312443/1099511627776
noncomputable def e2180 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273782341730,0,true,161765197120,161765197184⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925240913822,0,false,-189739680896,-189739680832⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273896292582,0,true,161863553536,161863553600⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925126962970,0,false,-189875102912,-189875102848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273651638694,0,true,161652370240,161652370304⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925371616858,0,false,-189584370688,-189584370624⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273787302167,0,true,161769478848,161769478912⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925235953385,0,false,-189745575680,-189745575616⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567095774,0,true,55466560,55466624⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456159778,0,false,-55469440,-55469376⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578235240,0,true,66605440,66605504⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445020312,0,false,-66609536,-66609472⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623740,0,false,-4096,-4032⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624978,0,false,-2816,-2752⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273716986082,0,true,161708781568,161708781632⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925306269470,0,false,-189662018176,-189662018112⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273841802053,0,true,161816521216,161816521280⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925181453499,0,false,-189810342976,-189810342912⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071871165505,0,false,-27993821696,-27993821632⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071910731073,0,false,-27953236608,-27953236544⟩
    { al := (649209/4096000), au := (1299267/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨174270713954,174384664806⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161765197120,161765197184⟩ : DyadicInterval 40),(⟨-189739680896,-189739680832⟩ : DyadicInterval 40),(⟨748254164215,748254183544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161863553536,161863553600⟩ : DyadicInterval 40),(⟨-189875102912,-189875102848⟩ : DyadicInterval 40),(⟨748235943582,748235962911⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161652370240,161652370304⟩ : DyadicInterval 40),(⟨-189584370688,-189584370624⟩ : DyadicInterval 40),(⟨748275048595,748275067924⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161769478848,161769478912⟩ : DyadicInterval 40),(⟨-189745575680,-189745575616⟩ : DyadicInterval 40),(⟨748253371334,748253390664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55467998,66607464⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55466560,55466624⟩ : DyadicInterval 40),(⟨-55469440,-55469376⟩ : DyadicInterval 40),(⟨762123382193,762123401522⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66605440,66605504⟩ : DyadicInterval 40),(⟨-66609536,-66609472⟩ : DyadicInterval 40),(⟨762123381564,762123400894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4096,-2752⟩ : DyadicInterval 40),(⟨762123384992,762123404928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174205358306,174330174277⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161708781568,161708781632⟩ : DyadicInterval 40),(⟨-189662018176,-189662018112⟩ : DyadicInterval 40),(⟨748264609067,748264628397⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161816521216,161816521280⟩ : DyadicInterval 40),(⟨-189810342976,-189810342912⟩ : DyadicInterval 40),(⟨748244658118,748244677448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27993821696,-27953236544⟩ : DyadicInterval 40),(⟨776100001888,776120313728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161765197120,161863553600⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189875102912,-189739680832⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2180_ok : ecellOkT e2180 = true := by decide +kernel
theorem e2180_pos {a z : ℝ} (ha1 : ((649209/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1299267/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2180 e2180_ok ha1 ha2 hz1 hz2 hz

-- box ['1299267/8192000', '325029/2048000', '3997/4000', '1599/1600']  interval_lower 200463829/1099511627776
noncomputable def e2181 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273896292581,0,true,161863553536,161863553600⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925126962971,0,false,-189875102912,-189875102848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274010243433,0,true,161961901184,161961901248⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925013012119,0,false,-190010541632,-190010541568⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273765504082,0,true,161750662976,161750663040⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925257751470,0,false,-189719672064,-189719672000⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273901181799,0,true,161867773440,161867773504⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925122073753,0,false,-189880913792,-189880913728⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567133393,0,true,55504192,55504256⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456122159,0,false,-55507072,-55507008⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578280387,0,true,66650560,66650624⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444975165,0,false,-66654656,-66654592⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623735,0,false,-4096,-4032⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624974,0,false,-2816,-2752⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273830894196,0,true,161807106112,161807106176⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925192361356,0,false,-189797379840,-189797379776⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273955717296,0,true,161914842368,161914842432⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925067538256,0,false,-189945731392,-189945731328⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071835030639,0,false,-28030888960,-28030888896⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071874624331,0,false,-27990273664,-27990273600⟩
    { al := (1299267/8192000), au := (325029/2048000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨174384664805,174498615657⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161863553536,161863553600⟩ : DyadicInterval 40),(⟨-189875102912,-189875102848⟩ : DyadicInterval 40),(⟨748235943582,748235962912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161961901184,161961901248⟩ : DyadicInterval 40),(⟨-190010541632,-190010541568⟩ : DyadicInterval 40),(⟨748217710827,748217730157⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161750662976,161750663040⟩ : DyadicInterval 40),(⟨-189719672064,-189719672000⟩ : DyadicInterval 40),(⟨748256855537,748256874866⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161867773440,161867773504⟩ : DyadicInterval 40),(⟨-189880913792,-189880913728⟩ : DyadicInterval 40),(⟨748235161555,748235180885⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55505617,66652611⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55504192,55504256⟩ : DyadicInterval 40),(⟨-55507072,-55507008⟩ : DyadicInterval 40),(⟨762123382189,762123401519⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66650560,66650624⟩ : DyadicInterval 40),(⟨-66654656,-66654592⟩ : DyadicInterval 40),(⟨762123381559,762123400888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4096,-2752⟩ : DyadicInterval 40),(⟨762123384992,762123404928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174319266420,174444089520⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161807106112,161807106176⟩ : DyadicInterval 40),(⟨-189797379840,-189797379776⟩ : DyadicInterval 40),(⟨748246402234,748246421564⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161914842368,161914842432⟩ : DyadicInterval 40),(⟨-189945731392,-189945731328⟩ : DyadicInterval 40),(⟨748226436836,748226456165⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28030888960,-27990273600⟩ : DyadicInterval 40),(⟨776118520416,776138847360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161863553536,161961901248⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190010541632,-189875102848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2181_ok : ecellOkT e2181 = true := by decide +kernel
theorem e2181_pos {a z : ℝ} (ha1 : ((1299267/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((325029/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2181 e2181_ok ha1 ha2 hz1 hz2 hz

-- box ['649209/4096000', '1299267/8192000', '1599/1600', '1999/2000']  interval_lower 199147639/1099511627776
noncomputable def e2182 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273782341730,0,true,161765197120,161765197184⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925240913822,0,false,-189739680896,-189739680832⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273896292582,0,true,161863553536,161863553600⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925126962970,0,false,-189875102912,-189875102848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273673422533,0,true,161671175488,161671175552⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925349833019,0,false,-189610254208,-189610254144⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273809100250,0,true,161788294464,161788294528⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925214155302,0,false,-189771479872,-189771479808⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556002226,0,true,44373504,44373568⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467253326,0,false,-44375360,-44375296⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567134168,0,true,55504960,55505024⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456121384,0,false,-55507840,-55507776⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624973,0,false,-2816,-2752⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625986,0,false,-1792,-1728⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273727877861,0,true,161718183616,161718183680⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925295377691,0,false,-189674960576,-189674960512⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273852700987,0,true,161825928576,161825928640⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925170554565,0,false,-189823295616,-189823295552⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071867709293,0,false,-27997367040,-27997366976⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071907279603,0,false,-27956776960,-27956776896⟩
    { al := (649209/4096000), au := (1299267/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨174270713954,174384664806⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161765197120,161765197184⟩ : DyadicInterval 40),(⟨-189739680896,-189739680832⟩ : DyadicInterval 40),(⟨748254164215,748254183544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161863553536,161863553600⟩ : DyadicInterval 40),(⟨-189875102912,-189875102848⟩ : DyadicInterval 40),(⟨748235943582,748235962911⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161671175488,161671175552⟩ : DyadicInterval 40),(⟨-189610254208,-189610254144⟩ : DyadicInterval 40),(⟨748271568996,748271588325⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161788294464,161788294528⟩ : DyadicInterval 40),(⟨-189771479872,-189771479808⟩ : DyadicInterval 40),(⟨748249886636,748249905966⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨44374450,55506392⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44373504,44373568⟩ : DyadicInterval 40),(⟨-44375360,-44375296⟩ : DyadicInterval 40),(⟨762123382689,762123402018⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55504960,55505024⟩ : DyadicInterval 40),(⟨-55507840,-55507776⟩ : DyadicInterval 40),(⟨762123382189,762123401518⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2816,-1728⟩ : DyadicInterval 40),(⟨762123384480,762123404288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174216250085,174341073211⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161718183616,161718183680⟩ : DyadicInterval 40),(⟨-189674960576,-189674960512⟩ : DyadicInterval 40),(⟨748262868676,748262888006⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161825928576,161825928640⟩ : DyadicInterval 40),(⟨-189823295616,-189823295552⟩ : DyadicInterval 40),(⟨748242915278,748242934607⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27997367040,-27956776896⟩ : DyadicInterval 40),(⟨776101772064,776122086400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161765197120,161863553600⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189875102912,-189739680832⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2182_ok : ecellOkT e2182 = true := by decide +kernel
theorem e2182_pos {a z : ℝ} (ha1 : ((649209/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1299267/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2182 e2182_ok ha1 ha2 hz1 hz2 hz

-- box ['1299267/8192000', '325029/2048000', '1599/1600', '1999/2000']  interval_lower 200298885/1099511627776
noncomputable def e2183 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273896292581,0,true,161863553536,161863553600⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925126962971,0,false,-189875102912,-189875102848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274010243433,0,true,161961901184,161961901248⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925013012119,0,false,-190010541632,-190010541568⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273787302165,0,true,161769478848,161769478912⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925235953387,0,false,-189745575680,-189745575616⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273922994126,0,true,161886599616,161886599680⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925100261426,0,false,-189906838144,-189906838080⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556032322,0,true,44403648,44403712⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467223230,0,false,-44405504,-44405440⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567171791,0,true,55542592,55542656⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456083761,0,false,-55545472,-55545408⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624970,0,false,-2816,-2752⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625983,0,false,-1856,-1792⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273841793100,0,true,161816513536,161816513600⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925181462452,0,false,-189810332288,-189810332224⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273966623348,0,true,161924254976,161924255040⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925056632204,0,false,-189958694080,-189958694016⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071831569911,0,false,-28034439104,-28034439040⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071871168345,0,false,-27993818752,-27993818688⟩
    { al := (1299267/8192000), au := (325029/2048000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨174384664805,174498615657⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161863553536,161863553600⟩ : DyadicInterval 40),(⟨-189875102912,-189875102848⟩ : DyadicInterval 40),(⟨748235943582,748235962912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161961901184,161961901248⟩ : DyadicInterval 40),(⟨-190010541632,-190010541568⟩ : DyadicInterval 40),(⟨748217710827,748217730157⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161769478848,161769478912⟩ : DyadicInterval 40),(⟨-189745575680,-189745575616⟩ : DyadicInterval 40),(⟨748253371334,748253390664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161886599616,161886599680⟩ : DyadicInterval 40),(⟨-189906838144,-189906838080⟩ : DyadicInterval 40),(⟨748231672311,748231691640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨44404546,55544015⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44403648,44403712⟩ : DyadicInterval 40),(⟨-44405504,-44405440⟩ : DyadicInterval 40),(⟨762123382686,762123402015⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55542592,55542656⟩ : DyadicInterval 40),(⟨-55545472,-55545408⟩ : DyadicInterval 40),(⟨762123382186,762123401515⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2816,-1792⟩ : DyadicInterval 40),(⟨762123384512,762123404288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174330165324,174454995572⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161816513536,161816513600⟩ : DyadicInterval 40),(⟨-189810332288,-189810332224⟩ : DyadicInterval 40),(⟨748244659502,748244678832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161924254976,161924255040⟩ : DyadicInterval 40),(⟨-189958694080,-189958694016⟩ : DyadicInterval 40),(⟨748224691726,748224711055⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28034439104,-27993818688⟩ : DyadicInterval 40),(⟨776120292960,776140622432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161863553536,161961901248⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190010541632,-189875102848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2183_ok : ecellOkT e2183 = true := by decide +kernel
theorem e2183_pos {a z : ℝ} (ha1 : ((1299267/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((325029/2048000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2183 e2183_ok ha1 ha2 hz1 hz2 hz

-- box ['325029/2048000', '260193/1638400', '999/1000', '7993/8000']  interval_lower 201949441/1099511627776
noncomputable def e2184 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274010243432,0,true,161961901184,161961901248⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925013012120,0,false,-190010541632,-190010541568⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274124194284,0,true,162060240000,162060240064⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924899061268,0,false,-190145997056,-190145996992⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273835744816,0,true,161811292928,161811292992⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925187510736,0,false,-189803144384,-189803144320⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273971408289,0,true,161928384704,161928384768⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925051847263,0,false,-189964381440,-189964381376⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589388053,0,true,77757504,77757568⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433867499,0,false,-77763072,-77763008⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099600557625,0,true,88926208,88926272⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099422697927,0,false,-88933504,-88933440⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620583,0,false,-7232,-7168⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622277,0,false,-5504,-5440⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273922990337,0,true,161886596352,161886596416⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925100265215,0,false,-189906833600,-189906833536⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274047806269,0,true,161994318592,161994318656⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924975449283,0,false,-190055191424,-190055191360⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071805801995,0,false,-28060872768,-28060872704⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071845414321,0,false,-28020237248,-28020237184⟩
    { al := (325029/2048000), au := (260193/1638400), zl := (999/1000), zu := (7993/8000),
      A := ⟨174498615656,174612566508⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161961901184,161961901248⟩ : DyadicInterval 40),(⟨-190010541632,-190010541568⟩ : DyadicInterval 40),(⟨748217710827,748217730157⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162060240000,162060240064⟩ : DyadicInterval 40),(⟨-190145997056,-190145996992⟩ : DyadicInterval 40),(⟨748199465986,748199485316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161811292928,161811292992⟩ : DyadicInterval 40),(⟨-189803144384,-189803144320⟩ : DyadicInterval 40),(⟨748245626648,748245645978⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161928384704,161928384768⟩ : DyadicInterval 40),(⟨-189964381440,-189964381376⟩ : DyadicInterval 40),(⟨748223926026,748223945355⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨77760277,88929849⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77757504,77757568⟩ : DyadicInterval 40),(⟨-77763072,-77763008⟩ : DyadicInterval 40),(⟨762123380836,762123400165⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨88926208,88926272⟩ : DyadicInterval 40),(⟨-88933504,-88933440⟩ : DyadicInterval 40),(⟨762123380006,762123399336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7232,-5440⟩ : DyadicInterval 40),(⟨762123386336,762123406496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174411362561,174536178493⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161886596352,161886596416⟩ : DyadicInterval 40),(⟨-189906833600,-189906833536⟩ : DyadicInterval 40),(⟨748231672896,748231692226⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161994318592,161994318656⟩ : DyadicInterval 40),(⟨-190055191424,-190055191360⟩ : DyadicInterval 40),(⟨748211697953,748211717282⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28060872768,-28020237184⟩ : DyadicInterval 40),(⟨776133502208,776153839264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161961901184,162060240064⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190145997056,-190010541568⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2184_ok : ecellOkT e2184 = true := by decide +kernel
theorem e2184_pos {a z : ℝ} (ha1 : ((325029/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((260193/1638400 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2184 e2184_ok ha1 ha2 hz1 hz2 hz

-- box ['260193/1638400', '650907/4096000', '999/1000', '7993/8000']  interval_lower 203107171/1099511627776
noncomputable def e2185 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274124194283,0,true,162060240000,162060240064⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924899061269,0,false,-190145997056,-190145996992⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274238145135,0,true,162158570048,162158570112⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924785110417,0,false,-190281469120,-190281469056⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273949581716,0,true,161909546880,161909546944⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925073673836,0,false,-189938438784,-189938438720⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274085259433,0,true,162026640448,162026640512⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924937996119,0,false,-190099712640,-190099712576⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589440726,0,true,77810176,77810240⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433814826,0,false,-77815744,-77815680⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099600617828,0,true,88986432,88986496⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099422637724,0,false,-88993664,-88993600⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620573,0,false,-7232,-7168⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622270,0,false,-5568,-5504⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274036884209,0,true,161984892736,161984892800⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924986371343,0,false,-190042208512,-190042208448⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274161707265,0,true,162092611520,162092611584⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924861548287,0,false,-190190593024,-190190592960⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071769628969,0,false,-28097981504,-28097981440⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071809269417,0,false,-28057315712,-28057315648⟩
    { al := (260193/1638400), au := (650907/4096000), zl := (999/1000), zu := (7993/8000),
      A := ⟨174612566507,174726517359⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162060240000,162060240064⟩ : DyadicInterval 40),(⟨-190145997056,-190145996992⟩ : DyadicInterval 40),(⟨748199465986,748199485316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162158570048,162158570112⟩ : DyadicInterval 40),(⟨-190281469120,-190281469056⟩ : DyadicInterval 40),(⟨748181208993,748181228323⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161909546880,161909546944⟩ : DyadicInterval 40),(⟨-189938438784,-189938438720⟩ : DyadicInterval 40),(⟨748227418569,748227437898⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162026640448,162026640512⟩ : DyadicInterval 40),(⟨-190099712640,-190099712576⟩ : DyadicInterval 40),(⟨748205701289,748205720619⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨77812950,88990052⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77810176,77810240⟩ : DyadicInterval 40),(⟨-77815744,-77815680⟩ : DyadicInterval 40),(⟨762123380828,762123400158⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨88986432,88986496⟩ : DyadicInterval 40),(⟨-88993664,-88993600⟩ : DyadicInterval 40),(⟨762123379965,762123399294⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7232,-5504⟩ : DyadicInterval 40),(⟨762123386368,762123406496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174525256433,174650079489⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161984892736,161984892800⟩ : DyadicInterval 40),(⟨-190042208512,-190042208448⟩ : DyadicInterval 40),(⟨748213446446,748213465776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162092611520,162092611584⟩ : DyadicInterval 40),(⟨-190190593024,-190190592960⟩ : DyadicInterval 40),(⟨748193457063,748193476393⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28097981504,-28057315648⟩ : DyadicInterval 40),(⟨776152041440,776172393632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162060240000,162158570112⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190281469120,-190145996992⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2185_ok : ecellOkT e2185 = true := by decide +kernel
theorem e2185_pos {a z : ℝ} (ha1 : ((260193/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((650907/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2185 e2185_ok ha1 ha2 hz1 hz2 hz

-- box ['325029/2048000', '260193/1638400', '7993/8000', '3997/4000']  interval_lower 201783785/1099511627776
noncomputable def e2186 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274010243432,0,true,161961901184,161961901248⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925013012120,0,false,-190010541632,-190010541568⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274124194284,0,true,162060240000,162060240064⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924899061268,0,false,-190145997056,-190145996992⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273857557143,0,true,161830120128,161830120192⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925165698409,0,false,-189829066880,-189829066816⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273993234860,0,true,161947222144,161947222208⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925030020692,0,false,-189990324672,-189990324608⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578279560,0,true,66649728,66649792⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444975992,0,false,-66653824,-66653760⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589441607,0,true,77811072,77811136⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433813945,0,false,-77816640,-77816576⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622269,0,false,-5568,-5504⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623736,0,false,-4096,-4032⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273933896317,0,true,161896009152,161896009216⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925089359235,0,false,-189919795840,-189919795776⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274058719392,0,true,162003736640,162003736704⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924964536160,0,false,-190068163840,-190068163776⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071802337194,0,false,-28064427136,-28064427072⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071841954265,0,false,-28023786624,-28023786560⟩
    { al := (325029/2048000), au := (260193/1638400), zl := (7993/8000), zu := (3997/4000),
      A := ⟨174498615656,174612566508⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161961901184,161961901248⟩ : DyadicInterval 40),(⟨-190010541632,-190010541568⟩ : DyadicInterval 40),(⟨748217710827,748217730157⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162060240000,162060240064⟩ : DyadicInterval 40),(⟨-190145997056,-190145996992⟩ : DyadicInterval 40),(⟨748199465986,748199485316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161830120128,161830120192⟩ : DyadicInterval 40),(⟨-189829066880,-189829066816⟩ : DyadicInterval 40),(⟨748242138693,748242158022⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161947222144,161947222208⟩ : DyadicInterval 40),(⟨-189990324672,-189990324608⟩ : DyadicInterval 40),(⟨748220433059,748220452388⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨66651784,77813831⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66649728,66649792⟩ : DyadicInterval 40),(⟨-66653824,-66653760⟩ : DyadicInterval 40),(⟨762123381559,762123400888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77811072,77811136⟩ : DyadicInterval 40),(⟨-77816640,-77816576⟩ : DyadicInterval 40),(⟨762123380828,762123400158⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5568,-4032⟩ : DyadicInterval 40),(⟨762123385632,762123405664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174422268541,174547091616⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161896009152,161896009216⟩ : DyadicInterval 40),(⟨-189919795840,-189919795776⟩ : DyadicInterval 40),(⟨748229928163,748229947493⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162003736640,162003736704⟩ : DyadicInterval 40),(⟨-190068163840,-190068163776⟩ : DyadicInterval 40),(⟨748209950777,748209970107⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28064427136,-28023786560⟩ : DyadicInterval 40),(⟨776135276896,776155616448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161961901184,162060240064⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190145997056,-190010541568⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2186_ok : ecellOkT e2186 = true := by decide +kernel
theorem e2186_pos {a z : ℝ} (ha1 : ((325029/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((260193/1638400 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2186 e2186_ok ha1 ha2 hz1 hz2 hz

-- box ['260193/1638400', '650907/4096000', '7993/8000', '3997/4000']  interval_lower 25367663/137438953472
noncomputable def e2187 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274124194283,0,true,162060240000,162060240064⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924899061269,0,false,-190145997056,-190145996992⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274238145135,0,true,162158570048,162158570112⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924785110417,0,false,-190281469120,-190281469056⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273971408287,0,true,161928384640,161928384704⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925051847265,0,false,-189964381440,-189964381376⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274107100248,0,true,162045488512,162045488576⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924916155304,0,false,-190125675968,-190125675904⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578324710,0,true,66694848,66694912⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444930842,0,false,-66699008,-66698944⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589494286,0,true,77863744,77863808⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433761266,0,false,-77869312,-77869248⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622261,0,false,-5568,-5504⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623731,0,false,-4096,-4032⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274047797306,0,true,161994310848,161994310912⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924975458246,0,false,-190055180736,-190055180672⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274172627513,0,true,162102034880,162102034944⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924850628039,0,false,-190203575552,-190203575488⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071766159644,0,false,-28101540608,-28101540544⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071805804841,0,false,-28060869824,-28060869760⟩
    { al := (260193/1638400), au := (650907/4096000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨174612566507,174726517359⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162060240000,162060240064⟩ : DyadicInterval 40),(⟨-190145997056,-190145996992⟩ : DyadicInterval 40),(⟨748199465986,748199485316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162158570048,162158570112⟩ : DyadicInterval 40),(⟨-190281469120,-190281469056⟩ : DyadicInterval 40),(⟨748181208993,748181228323⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161928384640,161928384704⟩ : DyadicInterval 40),(⟨-189964381440,-189964381376⟩ : DyadicInterval 40),(⟨748223926063,748223945393⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162045488512,162045488576⟩ : DyadicInterval 40),(⟨-190125675968,-190125675904⟩ : DyadicInterval 40),(⟨748202203701,748202223030⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨66696934,77866510⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66694848,66694912⟩ : DyadicInterval 40),(⟨-66699008,-66698944⟩ : DyadicInterval 40),(⟨762123381586,762123400915⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77863744,77863808⟩ : DyadicInterval 40),(⟨-77869312,-77869248⟩ : DyadicInterval 40),(⟨762123380821,762123400150⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5568,-4032⟩ : DyadicInterval 40),(⟨762123385632,762123405664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174536169530,174660999737⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161994310848,161994310912⟩ : DyadicInterval 40),(⟨-190055180736,-190055180672⟩ : DyadicInterval 40),(⟨748211699379,748211718708⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162102034880,162102034944⟩ : DyadicInterval 40),(⟨-190203575552,-190203575488⟩ : DyadicInterval 40),(⟨748191707601,748191726930⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28101540608,-28060869760⟩ : DyadicInterval 40),(⟨776153818496,776174173184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162060240000,162158570112⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190281469120,-190145996992⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2187_ok : ecellOkT e2187 = true := by decide +kernel
theorem e2187_pos {a z : ℝ} (ha1 : ((260193/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((650907/4096000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2187 e2187_ok ha1 ha2 hz1 hz2 hz

-- box ['650907/4096000', '1302663/8192000', '999/1000', '7993/8000']  interval_lower 102134085/549755813888
noncomputable def e2188 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274238145134,0,true,162158570048,162158570112⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924785110418,0,false,-190281469120,-190281469056⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274352095986,0,true,162256891264,162256891328⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924671159566,0,false,-190416957888,-190416957824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274063418616,0,true,162007792064,162007792128⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924959836936,0,false,-190073749824,-190073749760⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274199110577,0,true,162124887488,162124887552⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924824144975,0,false,-190235060480,-190235060416⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589493406,0,true,77862848,77862912⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433762146,0,false,-77868416,-77868352⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099600678037,0,true,89046592,89046656⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099422577515,0,false,-89053888,-89053824⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620563,0,false,-7232,-7168⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622262,0,false,-5568,-5504⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274150778087,0,true,162083180352,162083180416⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924872477465,0,false,-190177600064,-190177600000⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274275608265,0,true,162190895680,162190895744⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924747647287,0,false,-190326011328,-190326011264⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071733432343,0,false,-28135115648,-28135115584⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071773100915,0,false,-28094419648,-28094419584⟩
    { al := (650907/4096000), au := (1302663/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨174726517358,174840468210⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162158570048,162158570112⟩ : DyadicInterval 40),(⟨-190281469120,-190281469056⟩ : DyadicInterval 40),(⟨748181208994,748181228323⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162256891264,162256891328⟩ : DyadicInterval 40),(⟨-190416957888,-190416957824⟩ : DyadicInterval 40),(⟨748162939913,748162959242⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162007792064,162007792128⟩ : DyadicInterval 40),(⟨-190073749824,-190073749760⟩ : DyadicInterval 40),(⟨748209198388,748209217717⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162124887488,162124887552⟩ : DyadicInterval 40),(⟨-190235060480,-190235060416⟩ : DyadicInterval 40),(⟨748187464407,748187483736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨77865630,89050261⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77862848,77862912⟩ : DyadicInterval 40),(⟨-77868416,-77868352⟩ : DyadicInterval 40),(⟨762123380821,762123400150⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨89046592,89046656⟩ : DyadicInterval 40),(⟨-89053888,-89053824⟩ : DyadicInterval 40),(⟨762123379987,762123399317⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7232,-5504⟩ : DyadicInterval 40),(⟨762123386368,762123406496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174639150311,174763980489⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162083180352,162083180416⟩ : DyadicInterval 40),(⟨-190177600064,-190177600000⟩ : DyadicInterval 40),(⟨748195207870,748195227199⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162190895680,162190895744⟩ : DyadicInterval 40),(⟨-190326011328,-190326011264⟩ : DyadicInterval 40),(⟨748175204069,748175223398⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28135115648,-28094419584⟩ : DyadicInterval 40),(⟨776170593408,776190960704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162158570048,162256891328⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190416957888,-190281469056⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2188_ok : ecellOkT e2188 = true := by decide +kernel
theorem e2188_pos {a z : ℝ} (ha1 : ((650907/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1302663/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2188 e2188_ok ha1 ha2 hz1 hz2 hz

-- box ['1302663/8192000', '162939/1024000', '999/1000', '7993/8000']  interval_lower 205431781/1099511627776
noncomputable def e2189 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274352095985,0,true,162256891264,162256891328⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924671159567,0,false,-190416957888,-190416957824⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274466046837,0,true,162355203712,162355203776⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924557208715,0,false,-190552463360,-190552463296⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274177255516,0,true,162106028480,162106028544⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924846000036,0,false,-190209077568,-190209077504⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274312961721,0,true,162223125696,162223125760⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924710293831,0,false,-190370424960,-190370424896⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589546087,0,true,77915520,77915584⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433709465,0,false,-77921088,-77921024⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099600738250,0,true,89106816,89106880⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099422517302,0,false,-89114112,-89114048⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620553,0,false,-7232,-7168⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622255,0,false,-5568,-5504⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274264671959,0,true,162181459200,162181459264⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924758583593,0,false,-190313008320,-190313008256⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274389509263,0,true,162289171008,162289171072⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924633746289,0,false,-190461446336,-190461446272⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071697212120,0,false,-28172275328,-28172275264⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071736908820,0,false,-28131549056,-28131548992⟩
    { al := (1302663/8192000), au := (162939/1024000), zl := (999/1000), zu := (7993/8000),
      A := ⟨174840468209,174954419061⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162256891264,162256891328⟩ : DyadicInterval 40),(⟨-190416957888,-190416957824⟩ : DyadicInterval 40),(⟨748162939913,748162959242⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162355203712,162355203776⟩ : DyadicInterval 40),(⟨-190552463360,-190552463296⟩ : DyadicInterval 40),(⟨748144658705,748144678034⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162106028480,162106028544⟩ : DyadicInterval 40),(⟨-190209077568,-190209077504⟩ : DyadicInterval 40),(⟨748190966131,748190985461⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162223125696,162223125760⟩ : DyadicInterval 40),(⟨-190370424960,-190370424896⟩ : DyadicInterval 40),(⟨748169215451,748169234781⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨77918311,89110474⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77915520,77915584⟩ : DyadicInterval 40),(⟨-77921088,-77921024⟩ : DyadicInterval 40),(⟨762123380814,762123400143⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨89106816,89106880⟩ : DyadicInterval 40),(⟨-89114112,-89114048⟩ : DyadicInterval 40),(⟨762123379977,762123399307⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7232,-5504⟩ : DyadicInterval 40),(⟨762123386368,762123406496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174753044183,174877881487⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162181459200,162181459264⟩ : DyadicInterval 40),(⟨-190313008320,-190313008256⟩ : DyadicInterval 40),(⟨748176957194,748176976523⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162289171008,162289171072⟩ : DyadicInterval 40),(⟨-190461446336,-190461446272⟩ : DyadicInterval 40),(⟨748156939007,748156958337⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28172275328,-28131548992⟩ : DyadicInterval 40),(⟨776189158112,776209540544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162256891264,162355203776⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190552463360,-190416957824⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2189_ok : ecellOkT e2189 = true := by decide +kernel
theorem e2189_pos {a z : ℝ} (ha1 : ((1302663/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((162939/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2189 e2189_ok ha1 ha2 hz1 hz2 hz

-- box ['650907/4096000', '1302663/8192000', '7993/8000', '3997/4000']  interval_lower 204101791/1099511627776
noncomputable def e2190 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274238145134,0,true,162158570048,162158570112⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924785110418,0,false,-190281469120,-190281469056⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274352095986,0,true,162256891264,162256891328⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924671159566,0,false,-190416957888,-190416957824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274085259431,0,true,162026640448,162026640512⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924937996121,0,false,-190099712640,-190099712576⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274220965635,0,true,162143746112,162143746176⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924802289917,0,false,-190261043968,-190261043904⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578369863,0,true,66740032,66740096⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444885689,0,false,-66744128,-66744064⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589546969,0,true,77916416,77916480⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433708583,0,false,-77921984,-77921920⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622254,0,false,-5568,-5504⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623725,0,false,-4096,-4032⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274161698304,0,true,162092603776,162092603840⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924861557248,0,false,-190190582400,-190190582336⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274286535629,0,true,162200324288,162200324352⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924736719923,0,false,-190339003904,-190339003840⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071729958493,0,false,-28138679552,-28138679488⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071769631817,0,false,-28097978560,-28097978496⟩
    { al := (650907/4096000), au := (1302663/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨174726517358,174840468210⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162158570048,162158570112⟩ : DyadicInterval 40),(⟨-190281469120,-190281469056⟩ : DyadicInterval 40),(⟨748181208994,748181228323⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162256891264,162256891328⟩ : DyadicInterval 40),(⟨-190416957888,-190416957824⟩ : DyadicInterval 40),(⟨748162939913,748162959242⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162026640448,162026640512⟩ : DyadicInterval 40),(⟨-190099712640,-190099712576⟩ : DyadicInterval 40),(⟨748205701289,748205720619⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162143746112,162143746176⟩ : DyadicInterval 40),(⟨-190261043968,-190261043904⟩ : DyadicInterval 40),(⟨748183962255,748183981585⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨66742087,77919193⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66740032,66740096⟩ : DyadicInterval 40),(⟨-66744128,-66744064⟩ : DyadicInterval 40),(⟨762123381548,762123400877⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77916416,77916480⟩ : DyadicInterval 40),(⟨-77921984,-77921920⟩ : DyadicInterval 40),(⟨762123380813,762123400143⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5568,-4032⟩ : DyadicInterval 40),(⟨762123385632,762123405664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174650070528,174774907853⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162092603776,162092603840⟩ : DyadicInterval 40),(⟨-190190582400,-190190582336⟩ : DyadicInterval 40),(⟨748193458518,748193477847⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162200324288,162200324352⟩ : DyadicInterval 40),(⟨-190339003904,-190339003840⟩ : DyadicInterval 40),(⟨748173452329,748173471659⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28138679552,-28097978496⟩ : DyadicInterval 40),(⟨776172372864,776192742656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162158570048,162256891328⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190416957888,-190281469056⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2190_ok : ecellOkT e2190 = true := by decide +kernel
theorem e2190_pos {a z : ℝ} (ha1 : ((650907/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1302663/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2190 e2190_ok ha1 ha2 hz1 hz2 hz

-- box ['1302663/8192000', '162939/1024000', '7993/8000', '3997/4000']  interval_lower 205265201/1099511627776
noncomputable def e2191 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274352095985,0,true,162256891264,162256891328⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924671159567,0,false,-190416957888,-190416957824⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274466046837,0,true,162355203712,162355203776⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924557208715,0,false,-190552463360,-190552463296⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274199110575,0,true,162124887488,162124887552⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924824144977,0,false,-190235060480,-190235060416⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274334831023,0,true,162241994944,162241995008⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924688424529,0,false,-190396428608,-190396428544⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578415019,0,true,66785152,66785216⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444840533,0,false,-66789312,-66789248⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589599656,0,true,77969088,77969152⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433655896,0,false,-77974656,-77974592⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622246,0,false,-5568,-5504⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623720,0,false,-4096,-4032⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274275599301,0,true,162190887936,162190888000⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924747656251,0,false,-190326000704,-190326000640⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274400443749,0,true,162298604992,162298605056⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924622811803,0,false,-190474448960,-190474448896⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071693733740,0,false,-28175843968,-28175843904⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071733435194,0,false,-28135112768,-28135112704⟩
    { al := (1302663/8192000), au := (162939/1024000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨174840468209,174954419061⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162256891264,162256891328⟩ : DyadicInterval 40),(⟨-190416957888,-190416957824⟩ : DyadicInterval 40),(⟨748162939913,748162959242⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162355203712,162355203776⟩ : DyadicInterval 40),(⟨-190552463360,-190552463296⟩ : DyadicInterval 40),(⟨748144658705,748144678034⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162124887488,162124887552⟩ : DyadicInterval 40),(⟨-190235060480,-190235060416⟩ : DyadicInterval 40),(⟨748187464407,748187483736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162241994944,162241995008⟩ : DyadicInterval 40),(⟨-190396428608,-190396428544⟩ : DyadicInterval 40),(⟨748165708693,748165728023⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨66787243,77971880⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66785152,66785216⟩ : DyadicInterval 40),(⟨-66789312,-66789248⟩ : DyadicInterval 40),(⟨762123381575,762123400904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77969088,77969152⟩ : DyadicInterval 40),(⟨-77974656,-77974592⟩ : DyadicInterval 40),(⟨762123380806,762123400135⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5568,-4032⟩ : DyadicInterval 40),(⟨762123385632,762123405664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174763971525,174888815973⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162190887936,162190888000⟩ : DyadicInterval 40),(⟨-190326000704,-190326000640⟩ : DyadicInterval 40),(⟨748175205525,748175224855⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162298604992,162298605056⟩ : DyadicInterval 40),(⟨-190474448960,-190474448896⟩ : DyadicInterval 40),(⟨748155184911,748155204241⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28175843968,-28135112704⟩ : DyadicInterval 40),(⟨776190939968,776211324864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162256891264,162355203776⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190552463360,-190416957824⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2191_ok : ecellOkT e2191 = true := by decide +kernel
theorem e2191_pos {a z : ℝ} (ha1 : ((1302663/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((162939/1024000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2191 e2191_ok ha1 ha2 hz1 hz2 hz

-- box ['325029/2048000', '260193/1638400', '3997/4000', '1599/1600']  interval_lower 201618359/1099511627776
noncomputable def e2192 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274010243432,0,true,161961901184,161961901248⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925013012120,0,false,-190010541632,-190010541568⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274124194284,0,true,162060240000,162060240064⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924899061268,0,false,-190145997056,-190145996992⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273879369470,0,true,161848946944,161848947008⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925143886082,0,false,-189854990016,-189854989952⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274015061430,0,true,161966059264,161966059328⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925008194122,0,false,-190016268544,-190016268480⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567171016,0,true,55541824,55541888⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456084536,0,false,-55544704,-55544640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578325538,0,true,66695680,66695744⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444930014,0,false,-66699840,-66699776⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623730,0,false,-4096,-4032⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624971,0,false,-2816,-2752⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273944802317,0,true,161905421952,161905422016⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925078453235,0,false,-189932758208,-189932758144⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274069632539,0,true,162013154688,162013154752⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924953623013,0,false,-190081136448,-190081136384⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071798872169,0,false,-28067981760,-28067981696⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071838493985,0,false,-28027336192,-28027336128⟩
    { al := (325029/2048000), au := (260193/1638400), zl := (3997/4000), zu := (1599/1600),
      A := ⟨174498615656,174612566508⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161961901184,161961901248⟩ : DyadicInterval 40),(⟨-190010541632,-190010541568⟩ : DyadicInterval 40),(⟨748217710827,748217730157⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162060240000,162060240064⟩ : DyadicInterval 40),(⟨-190145997056,-190145996992⟩ : DyadicInterval 40),(⟨748199465986,748199485316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161848946944,161848947008⟩ : DyadicInterval 40),(⟨-189854990016,-189854989952⟩ : DyadicInterval 40),(⟨748238650341,748238669670⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161966059264,161966059328⟩ : DyadicInterval 40),(⟨-190016268544,-190016268480⟩ : DyadicInterval 40),(⟨748216939658,748216958987⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55543240,66697762⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55541824,55541888⟩ : DyadicInterval 40),(⟨-55544704,-55544640⟩ : DyadicInterval 40),(⟨762123382186,762123401515⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66695680,66695744⟩ : DyadicInterval 40),(⟨-66699840,-66699776⟩ : DyadicInterval 40),(⟨762123381585,762123400915⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4096,-2752⟩ : DyadicInterval 40),(⟨762123384992,762123404928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174433174541,174558004763⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161905421952,161905422016⟩ : DyadicInterval 40),(⟨-189932758208,-189932758144⟩ : DyadicInterval 40),(⟨748228183260,748228202590⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162013154688,162013154752⟩ : DyadicInterval 40),(⟨-190081136448,-190081136384⟩ : DyadicInterval 40),(⟨748208203455,748208222785⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28067981760,-28027336128⟩ : DyadicInterval 40),(⟨776137051680,776157393760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161961901184,162060240064⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190145997056,-190010541568⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2192_ok : ecellOkT e2192 = true := by decide +kernel
theorem e2192_pos {a z : ℝ} (ha1 : ((325029/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((260193/1638400 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2192 e2192_ok ha1 ha2 hz1 hz2 hz

-- box ['260193/1638400', '650907/4096000', '3997/4000', '1599/1600']  interval_lower 202775581/1099511627776
noncomputable def e2193 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274124194283,0,true,162060240000,162060240064⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924899061269,0,false,-190145997056,-190145996992⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274238145135,0,true,162158570048,162158570112⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924785110417,0,false,-190281469120,-190281469056⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273993234858,0,true,161947222144,161947222208⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925030020694,0,false,-189990324672,-189990324608⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274128941062,0,true,162064336256,162064336320⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924894314490,0,false,-190151640000,-190151639936⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567208642,0,true,55579456,55579520⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456046910,0,false,-55582272,-55582208⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578370692,0,true,66740864,66740928⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444884860,0,false,-66744960,-66744896⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623724,0,false,-4096,-4032⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624967,0,false,-2816,-2752⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274058710433,0,true,162003728960,162003729024⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924964545119,0,false,-190068153216,-190068153152⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274183547781,0,true,162111458176,162111458240⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924839707771,0,false,-190216558208,-190216558144⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071762690095,0,false,-28105099968,-28105099904⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071802340040,0,false,-28064424256,-28064424192⟩
    { al := (260193/1638400), au := (650907/4096000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨174612566507,174726517359⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162060240000,162060240064⟩ : DyadicInterval 40),(⟨-190145997056,-190145996992⟩ : DyadicInterval 40),(⟨748199465986,748199485316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162158570048,162158570112⟩ : DyadicInterval 40),(⟨-190281469120,-190281469056⟩ : DyadicInterval 40),(⟨748181208993,748181228323⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161947222144,161947222208⟩ : DyadicInterval 40),(⟨-189990324672,-189990324608⟩ : DyadicInterval 40),(⟨748220433059,748220452389⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162064336256,162064336320⟩ : DyadicInterval 40),(⟨-190151640000,-190151639936⟩ : DyadicInterval 40),(⟨748198705705,748198725034⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55580866,66742916⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55579456,55579520⟩ : DyadicInterval 40),(⟨-55582272,-55582208⟩ : DyadicInterval 40),(⟨762123382150,762123401479⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66740864,66740928⟩ : DyadicInterval 40),(⟨-66744960,-66744896⟩ : DyadicInterval 40),(⟨762123381548,762123400877⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4096,-2752⟩ : DyadicInterval 40),(⟨762123384992,762123404928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174547082657,174671920005⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162003728960,162003729024⟩ : DyadicInterval 40),(⟨-190068153216,-190068153152⟩ : DyadicInterval 40),(⟨748209952192,748209971522⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162111458176,162111458240⟩ : DyadicInterval 40),(⟨-190216558208,-190216558144⟩ : DyadicInterval 40),(⟨748189958004,748189977333⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28105099968,-28064424192⟩ : DyadicInterval 40),(⟨776155595712,776175952864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162060240000,162158570112⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190281469120,-190145996992⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2193_ok : ecellOkT e2193 = true := by decide +kernel
theorem e2193_pos {a z : ℝ} (ha1 : ((260193/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((650907/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2193 e2193_ok ha1 ha2 hz1 hz2 hz

-- box ['325029/2048000', '260193/1638400', '1599/1600', '1999/2000']  interval_lower 201452919/1099511627776
noncomputable def e2194 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274010243432,0,true,161961901184,161961901248⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925013012120,0,false,-190010541632,-190010541568⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274124194284,0,true,162060240000,162060240064⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924899061268,0,false,-190145997056,-190145996992⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273901181797,0,true,161867773440,161867773504⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925122073755,0,false,-189880913792,-189880913728⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274036888001,0,true,161984896000,161984896064⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924986367551,0,false,-190042213056,-190042212992⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556062420,0,true,44433728,44433792⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467193132,0,false,-44435584,-44435520⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567209417,0,true,55580224,55580288⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456046135,0,false,-55583104,-55583040⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624966,0,false,-2816,-2752⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625981,0,false,-1856,-1792⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273955708341,0,true,161914834624,161914834688⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925067547211,0,false,-189945720704,-189945720640⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274080545707,0,true,162022572608,162022572672⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924942709845,0,false,-190094109248,-190094109184⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071795406921,0,false,-28071536640,-28071536576⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071835033482,0,false,-28030886080,-28030886016⟩
    { al := (325029/2048000), au := (260193/1638400), zl := (1599/1600), zu := (1999/2000),
      A := ⟨174498615656,174612566508⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161961901184,161961901248⟩ : DyadicInterval 40),(⟨-190010541632,-190010541568⟩ : DyadicInterval 40),(⟨748217710827,748217730157⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162060240000,162060240064⟩ : DyadicInterval 40),(⟨-190145997056,-190145996992⟩ : DyadicInterval 40),(⟨748199465986,748199485316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161867773440,161867773504⟩ : DyadicInterval 40),(⟨-189880913792,-189880913728⟩ : DyadicInterval 40),(⟨748235161556,748235180885⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161984896000,161984896064⟩ : DyadicInterval 40),(⟨-190042213056,-190042212992⟩ : DyadicInterval 40),(⟨748213445860,748213465189⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨44434644,55581641⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44433728,44433792⟩ : DyadicInterval 40),(⟨-44435584,-44435520⟩ : DyadicInterval 40),(⟨762123382684,762123402013⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55580224,55580288⟩ : DyadicInterval 40),(⟨-55583104,-55583040⟩ : DyadicInterval 40),(⟨762123382182,762123401511⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2816,-1792⟩ : DyadicInterval 40),(⟨762123384512,762123404288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174444080565,174568917931⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161914834624,161914834688⟩ : DyadicInterval 40),(⟨-189945720704,-189945720640⟩ : DyadicInterval 40),(⟨748226438259,748226457588⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162022572608,162022572672⟩ : DyadicInterval 40),(⟨-190094109248,-190094109184⟩ : DyadicInterval 40),(⟨748206456063,748206475393⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28071536640,-28030886016⟩ : DyadicInterval 40),(⟨776138826624,776159171200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161961901184,162060240064⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190145997056,-190010541568⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2194_ok : ecellOkT e2194 = true := by decide +kernel
theorem e2194_pos {a z : ℝ} (ha1 : ((325029/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((260193/1638400 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2194 e2194_ok ha1 ha2 hz1 hz2 hz

-- box ['260193/1638400', '650907/4096000', '1599/1600', '1999/2000']  interval_lower 25326205/137438953472
noncomputable def e2195 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274124194283,0,true,162060240000,162060240064⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924899061269,0,false,-190145997056,-190145996992⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274238145135,0,true,162158570048,162158570112⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924785110417,0,false,-190281469120,-190281469056⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274015061428,0,true,161966059264,161966059328⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925008194124,0,false,-190016268544,-190016268480⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274150781877,0,true,162083183616,162083183680⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924872473675,0,false,-190177604608,-190177604544⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556092520,0,true,44463808,44463872⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467163032,0,false,-44465664,-44465600⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567247045,0,true,55617856,55617920⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456008507,0,false,-55620736,-55620672⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624962,0,false,-2816,-2752⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625978,0,false,-1856,-1792⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274069623580,0,true,162013146944,162013147008⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924953631972,0,false,-190081125824,-190081125760⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274194468073,0,true,162120881408,162120881472⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924828787479,0,false,-190229541056,-190229540992⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071759220322,0,false,-28108659584,-28108659520⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071798875015,0,false,-28067978816,-28067978752⟩
    { al := (260193/1638400), au := (650907/4096000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨174612566507,174726517359⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162060240000,162060240064⟩ : DyadicInterval 40),(⟨-190145997056,-190145996992⟩ : DyadicInterval 40),(⟨748199465986,748199485316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162158570048,162158570112⟩ : DyadicInterval 40),(⟨-190281469120,-190281469056⟩ : DyadicInterval 40),(⟨748181208993,748181228323⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161966059264,161966059328⟩ : DyadicInterval 40),(⟨-190016268544,-190016268480⟩ : DyadicInterval 40),(⟨748216939658,748216958988⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162083183616,162083183680⟩ : DyadicInterval 40),(⟨-190177604608,-190177604544⟩ : DyadicInterval 40),(⟨748195207283,748195226612⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨44464744,55619269⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44463808,44463872⟩ : DyadicInterval 40),(⟨-44465664,-44465600⟩ : DyadicInterval 40),(⟨762123382681,762123402010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55617856,55617920⟩ : DyadicInterval 40),(⟨-55620736,-55620672⟩ : DyadicInterval 40),(⟨762123382178,762123401507⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2816,-1792⟩ : DyadicInterval 40),(⟨762123384512,762123404288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174557995804,174682840297⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162013146944,162013147008⟩ : DyadicInterval 40),(⟨-190081125824,-190081125760⟩ : DyadicInterval 40),(⟨748208204908,748208224238⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162120881408,162120881472⟩ : DyadicInterval 40),(⟨-190229541056,-190229540992⟩ : DyadicInterval 40),(⟨748188208298,748188227628⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28108659584,-28067978752⟩ : DyadicInterval 40),(⟨776157372992,776177732672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162060240000,162158570112⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190281469120,-190145996992⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2195_ok : ecellOkT e2195 = true := by decide +kernel
theorem e2195_pos {a z : ℝ} (ha1 : ((260193/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((650907/4096000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2195 e2195_ok ha1 ha2 hz1 hz2 hz

-- box ['650907/4096000', '1302663/8192000', '3997/4000', '1599/1600']  interval_lower 50983929/274877906944
noncomputable def e2196 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274238145134,0,true,162158570048,162158570112⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924785110418,0,false,-190281469120,-190281469056⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274352095986,0,true,162256891264,162256891328⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924671159566,0,false,-190416957888,-190416957824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274107100245,0,true,162045488512,162045488576⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924916155307,0,false,-190125675968,-190125675904⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274242820694,0,true,162162604480,162162604544⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924780434858,0,false,-190287028096,-190287028032⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567246269,0,true,55617024,55617088⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456009283,0,false,-55619904,-55619840⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578415849,0,true,66785984,66786048⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444839703,0,false,-66790144,-66790080⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623719,0,false,-4096,-4032⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624963,0,false,-2816,-2752⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274172618551,0,true,162102027136,162102027200⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924850637001,0,false,-190203564864,-190203564800⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274297463023,0,true,162209752896,162209752960⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924725792529,0,false,-190351996672,-190351996608⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071726484416,0,false,-28142243712,-28142243648⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071766162492,0,false,-28101537728,-28101537664⟩
    { al := (650907/4096000), au := (1302663/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨174726517358,174840468210⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162158570048,162158570112⟩ : DyadicInterval 40),(⟨-190281469120,-190281469056⟩ : DyadicInterval 40),(⟨748181208994,748181228323⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162256891264,162256891328⟩ : DyadicInterval 40),(⟨-190416957888,-190416957824⟩ : DyadicInterval 40),(⟨748162939913,748162959242⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162045488512,162045488576⟩ : DyadicInterval 40),(⟨-190125675968,-190125675904⟩ : DyadicInterval 40),(⟨748202203702,748202223031⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162162604480,162162604544⟩ : DyadicInterval 40),(⟨-190287028096,-190287028032⟩ : DyadicInterval 40),(⟨748180459630,748180478960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55618493,66788073⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55617024,55617088⟩ : DyadicInterval 40),(⟨-55619904,-55619840⟩ : DyadicInterval 40),(⟨762123382178,762123401507⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66785984,66786048⟩ : DyadicInterval 40),(⟨-66790144,-66790080⟩ : DyadicInterval 40),(⟨762123381574,762123400904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4096,-2752⟩ : DyadicInterval 40),(⟨762123384992,762123404928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174660990775,174785835247⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162102027136,162102027200⟩ : DyadicInterval 40),(⟨-190203564864,-190203564800⟩ : DyadicInterval 40),(⟨748191709029,748191728358⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162209752896,162209752960⟩ : DyadicInterval 40),(⟨-190351996672,-190351996608⟩ : DyadicInterval 40),(⟨748171700442,748171719772⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28142243712,-28101537664⟩ : DyadicInterval 40),(⟨776174152448,776194524736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162158570048,162256891328⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190416957888,-190281469056⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2196_ok : ecellOkT e2196 = true := by decide +kernel
theorem e2196_pos {a z : ℝ} (ha1 : ((650907/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1302663/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2196 e2196_ok ha1 ha2 hz1 hz2 hz

-- box ['1302663/8192000', '162939/1024000', '3997/4000', '1599/1600']  interval_lower 205098663/1099511627776
noncomputable def e2197 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274352095985,0,true,162256891264,162256891328⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924671159567,0,false,-190416957888,-190416957824⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274466046837,0,true,162355203712,162355203776⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924557208715,0,false,-190552463360,-190552463296⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274220965633,0,true,162143746112,162143746176⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924802289919,0,false,-190261043968,-190261043904⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274356700326,0,true,162260863872,162260863936⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924666555226,0,false,-190422432896,-190422432832⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567283900,0,true,55654656,55654720⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455971652,0,false,-55657536,-55657472⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578461010,0,true,66831168,66831232⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444794542,0,false,-66835328,-66835264⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623713,0,false,-4096,-4032⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624959,0,false,-2880,-2816⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274286526665,0,true,162200316608,162200316672⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924736728887,0,false,-190338993216,-190338993152⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274411378260,0,true,162308038848,162308038912⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924611877292,0,false,-190487451776,-190487451712⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071690255135,0,false,-28179412864,-28179412800⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071729961344,0,false,-28138676608,-28138676544⟩
    { al := (1302663/8192000), au := (162939/1024000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨174840468209,174954419061⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162256891264,162256891328⟩ : DyadicInterval 40),(⟨-190416957888,-190416957824⟩ : DyadicInterval 40),(⟨748162939913,748162959242⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162355203712,162355203776⟩ : DyadicInterval 40),(⟨-190552463360,-190552463296⟩ : DyadicInterval 40),(⟨748144658705,748144678034⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162143746112,162143746176⟩ : DyadicInterval 40),(⟨-190261043968,-190261043904⟩ : DyadicInterval 40),(⟨748183962256,748183981585⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162260863872,162260863936⟩ : DyadicInterval 40),(⟨-190422432896,-190422432832⟩ : DyadicInterval 40),(⟨748162201497,748162220827⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55656124,66833234⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55654656,55654720⟩ : DyadicInterval 40),(⟨-55657536,-55657472⟩ : DyadicInterval 40),(⟨762123382174,762123401503⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66831168,66831232⟩ : DyadicInterval 40),(⟨-66835328,-66835264⟩ : DyadicInterval 40),(⟨762123381569,762123400898⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4096,-2816⟩ : DyadicInterval 40),(⟨762123385024,762123404928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174774898889,174899750484⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162200316608,162200316672⟩ : DyadicInterval 40),(⟨-190338993216,-190338993152⟩ : DyadicInterval 40),(⟨748173453722,748173473051⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162308038848,162308038912⟩ : DyadicInterval 40),(⟨-190487451776,-190487451712⟩ : DyadicInterval 40),(⟨748153430743,748153450073⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28179412864,-28138676544⟩ : DyadicInterval 40),(⟨776192721888,776213109312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162256891264,162355203776⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190552463360,-190416957824⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2197_ok : ecellOkT e2197 = true := by decide +kernel
theorem e2197_pos {a z : ℝ} (ha1 : ((1302663/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((162939/1024000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2197 e2197_ok ha1 ha2 hz1 hz2 hz

-- box ['650907/4096000', '1302663/8192000', '1599/1600', '1999/2000']  interval_lower 203769107/1099511627776
noncomputable def e2198 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274238145134,0,true,162158570048,162158570112⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924785110418,0,false,-190281469120,-190281469056⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274352095986,0,true,162256891264,162256891328⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924671159566,0,false,-190416957888,-190416957824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274128941060,0,true,162064336256,162064336320⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924894314492,0,false,-190151640000,-190151639936⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274264675753,0,true,162181462464,162181462528⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924758579799,0,false,-190313012800,-190313012736⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556122624,0,true,44493888,44493952⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467132928,0,false,-44495808,-44495744⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567284677,0,true,55655488,55655552⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455970875,0,false,-55658368,-55658304⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624958,0,false,-2880,-2816⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625976,0,false,-1856,-1792⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274183538820,0,true,162111450432,162111450496⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924839716732,0,false,-190216547584,-190216547520⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274308390439,0,true,162219181440,162219181504⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924714865113,0,false,-190364989568,-190364989504⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071723010115,0,false,-28145808064,-28145808000⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071762692943,0,false,-28105097088,-28105097024⟩
    { al := (650907/4096000), au := (1302663/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨174726517358,174840468210⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162158570048,162158570112⟩ : DyadicInterval 40),(⟨-190281469120,-190281469056⟩ : DyadicInterval 40),(⟨748181208994,748181228323⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162256891264,162256891328⟩ : DyadicInterval 40),(⟨-190416957888,-190416957824⟩ : DyadicInterval 40),(⟨748162939913,748162959242⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162064336256,162064336320⟩ : DyadicInterval 40),(⟨-190151640000,-190151639936⟩ : DyadicInterval 40),(⟨748198705705,748198725034⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162181462464,162181462528⟩ : DyadicInterval 40),(⟨-190313012800,-190313012736⟩ : DyadicInterval 40),(⟨748176956578,748176975908⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨44494848,55656901⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44493888,44493952⟩ : DyadicInterval 40),(⟨-44495808,-44495744⟩ : DyadicInterval 40),(⟨762123382711,762123402040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55655488,55655552⟩ : DyadicInterval 40),(⟨-55658368,-55658304⟩ : DyadicInterval 40),(⟨762123382174,762123401503⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2880,-1792⟩ : DyadicInterval 40),(⟨762123384512,762123404320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174671911044,174796762663⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162111450432,162111450496⟩ : DyadicInterval 40),(⟨-190216547584,-190216547520⟩ : DyadicInterval 40),(⟨748189959458,748189978788⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162219181440,162219181504⟩ : DyadicInterval 40),(⟨-190364989568,-190364989504⟩ : DyadicInterval 40),(⟨748169948420,748169967749⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28145808064,-28105097024⟩ : DyadicInterval 40),(⟨776175932128,776196306912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162158570048,162256891328⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190416957888,-190281469056⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2198_ok : ecellOkT e2198 = true := by decide +kernel
theorem e2198_pos {a z : ℝ} (ha1 : ((650907/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1302663/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2198 e2198_ok ha1 ha2 hz1 hz2 hz

-- box ['1302663/8192000', '162939/1024000', '1599/1600', '1999/2000']  interval_lower 25616465/137438953472
noncomputable def e2199 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274352095985,0,true,162256891264,162256891328⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924671159567,0,false,-190416957888,-190416957824⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274466046837,0,true,162355203712,162355203776⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924557208715,0,false,-190552463360,-190552463296⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274242820692,0,true,162162604480,162162604544⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924780434860,0,false,-190287028096,-190287028032⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274378569628,0,true,162279732544,162279732608⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924644685924,0,false,-190448437760,-190448437696⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556152728,0,true,44524032,44524096⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467102824,0,false,-44525888,-44525824⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567322311,0,true,55693120,55693184⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455933241,0,false,-55696000,-55695936⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624954,0,false,-2880,-2816⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625973,0,false,-1856,-1792⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274297454058,0,true,162209745216,162209745280⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924725801494,0,false,-190351985984,-190351985920⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274422312803,0,true,162317472704,162317472768⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924600942749,0,false,-190500454784,-190500454720⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071686776302,0,false,-28182982016,-28182981952⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071726487267,0,false,-28142240768,-28142240704⟩
    { al := (1302663/8192000), au := (162939/1024000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨174840468209,174954419061⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162256891264,162256891328⟩ : DyadicInterval 40),(⟨-190416957888,-190416957824⟩ : DyadicInterval 40),(⟨748162939913,748162959242⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162355203712,162355203776⟩ : DyadicInterval 40),(⟨-190552463360,-190552463296⟩ : DyadicInterval 40),(⟨748144658705,748144678034⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162162604480,162162604544⟩ : DyadicInterval 40),(⟨-190287028096,-190287028032⟩ : DyadicInterval 40),(⟨748180459630,748180478960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162279732544,162279732608⟩ : DyadicInterval 40),(⟨-190448437760,-190448437696⟩ : DyadicInterval 40),(⟨748158693799,748158713129⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨44524952,55694535⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44524032,44524096⟩ : DyadicInterval 40),(⟨-44525888,-44525824⟩ : DyadicInterval 40),(⟨762123382676,762123402005⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55693120,55693184⟩ : DyadicInterval 40),(⟨-55696000,-55695936⟩ : DyadicInterval 40),(⟨762123382170,762123401499⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2880,-1792⟩ : DyadicInterval 40),(⟨762123384512,762123404320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174785826282,174910685027⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162209745216,162209745280⟩ : DyadicInterval 40),(⟨-190351985984,-190351985920⟩ : DyadicInterval 40),(⟨748171701835,748171721165⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162317472704,162317472768⟩ : DyadicInterval 40),(⟨-190500454784,-190500454720⟩ : DyadicInterval 40),(⟨748151676428,748151695757⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28182982016,-28142240704⟩ : DyadicInterval 40),(⟨776194503968,776214893888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162256891264,162355203776⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190552463360,-190416957824⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2199_ok : ecellOkT e2199 = true := by decide +kernel
theorem e2199_pos {a z : ℝ} (ha1 : ((1302663/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((162939/1024000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2199 e2199_ok ha1 ha2 hz1 hz2 hz

-- box ['16209/102400', '1297569/8192000', '1999/2000', '7997/8000']  interval_lower 196689477/1099511627776
noncomputable def e2200 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273554440028,0,true,161568457856,161568457920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925468815524,0,false,-189468886912,-189468886848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273668390880,0,true,161666831872,161666831936⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925354864672,0,false,-189604275584,-189604275520⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273467418621,0,true,161493326144,161493326208⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925555836931,0,false,-189365505152,-189365505088⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273603082094,0,true,161610451712,161610451776⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925420173458,0,false,-189526678016,-189526677952⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544863487,0,true,33235200,33235264⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478392065,0,false,-33236224,-33236160⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555972854,0,true,44344128,44344192⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467282698,0,false,-44345984,-44345920⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625987,0,false,-1792,-1728⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626772,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273510924946,0,true,161530888832,161530888896⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925512330606,0,false,-189417189632,-189417189568⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273635740965,0,true,161638646016,161638646080⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925387514587,0,false,-189565481408,-189565481344⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071936469835,0,false,-27926835392,-27926835328⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071975988634,0,false,-27886300736,-27886300672⟩
    { al := (16209/102400), au := (1297569/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨174042812252,174156763104⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161568457856,161568457920⟩ : DyadicInterval 40),(⟨-189468886912,-189468886848⟩ : DyadicInterval 40),(⟨748290569166,748290588496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161666831872,161666831936⟩ : DyadicInterval 40),(⟨-189604275584,-189604275520⟩ : DyadicInterval 40),(⟨748272372763,748272392093⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161493326144,161493326208⟩ : DyadicInterval 40),(⟨-189365505152,-189365505088⟩ : DyadicInterval 40),(⟨748304457132,748304476462⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161610451712,161610451776⟩ : DyadicInterval 40),(⟨-189526678016,-189526677952⟩ : DyadicInterval 40),(⟨748282803158,748282822488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33235711,44345078⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33235200,33235264⟩ : DyadicInterval 40),(⟨-33236224,-33236160⟩ : DyadicInterval 40),(⟨762123383059,762123402388⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44344128,44344192⟩ : DyadicInterval 40),(⟨-44345984,-44345920⟩ : DyadicInterval 40),(⟨762123382691,762123402020⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1792,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173999297170,174124113189⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161530888832,161530888896⟩ : DyadicInterval 40),(⟨-189417189632,-189417189568⟩ : DyadicInterval 40),(⟨748297514755,748297534085⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161638646016,161638646080⟩ : DyadicInterval 40),(⟨-189565481408,-189565481344⟩ : DyadicInterval 40),(⟨748277587733,748277607063⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27926835392,-27886300672⟩ : DyadicInterval 40),(⟨776066533952,776086820576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161568457856,161666831936⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189604275584,-189468886848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2200_ok : ecellOkT e2200 = true := by decide +kernel
theorem e2200_pos {a z : ℝ} (ha1 : ((16209/102400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1297569/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2200 e2200_ok ha1 ha2 hz1 hz2 hz

-- box ['1297569/8192000', '649209/4096000', '1999/2000', '7997/8000']  interval_lower 197834791/1099511627776
noncomputable def e2201 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273668390879,0,true,161666831872,161666831936⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925354864673,0,false,-189604275584,-189604275520⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273782341731,0,true,161765197120,161765197184⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925240913821,0,false,-189739680896,-189739680832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273581312497,0,true,161591657728,161591657792⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925441943055,0,false,-189500813440,-189500813376⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273716990214,0,true,161708785088,161708785152⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925306265338,0,false,-189662023040,-189662022976⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544886056,0,true,33257728,33257792⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478369496,0,false,-33258816,-33258752⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556002948,0,true,44374272,44374336⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467252604,0,false,-44376128,-44376064⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625985,0,false,-1792,-1728⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626770,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273624847307,0,true,161629241664,161629241728⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925398408245,0,false,-189552538048,-189552537984⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273749670454,0,true,161736995328,161736995392⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925273585098,0,false,-189700856640,-189700856576⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071900373152,0,false,-27963861248,-27963861184⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071939920075,0,false,-27923296384,-27923296320⟩
    { al := (1297569/8192000), au := (649209/4096000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨174156763103,174270713955⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161666831872,161666831936⟩ : DyadicInterval 40),(⟨-189604275584,-189604275520⟩ : DyadicInterval 40),(⟨748272372764,748272392093⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161765197120,161765197184⟩ : DyadicInterval 40),(⟨-189739680896,-189739680832⟩ : DyadicInterval 40),(⟨748254164215,748254183544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161591657728,161591657792⟩ : DyadicInterval 40),(⟨-189500813440,-189500813376⟩ : DyadicInterval 40),(⟨748286279073,748286298403⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161708785088,161708785152⟩ : DyadicInterval 40),(⟨-189662023040,-189662022976⟩ : DyadicInterval 40),(⟨748264608415,748264627745⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33258280,44375172⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33257728,33257792⟩ : DyadicInterval 40),(⟨-33258816,-33258752⟩ : DyadicInterval 40),(⟨762123383089,762123402419⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44374272,44374336⟩ : DyadicInterval 40),(⟨-44376128,-44376064⟩ : DyadicInterval 40),(⟨762123382689,762123402018⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1792,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174113219531,174238042678⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161629241664,161629241728⟩ : DyadicInterval 40),(⟨-189552538048,-189552537984⟩ : DyadicInterval 40),(⟨748279327483,748279346812⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161736995328,161736995392⟩ : DyadicInterval 40),(⟨-189700856640,-189700856576⟩ : DyadicInterval 40),(⟨748259386114,748259405443⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27963861248,-27923296320⟩ : DyadicInterval 40),(⟨776085031776,776105333504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161666831872,161765197184⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189739680896,-189604275520⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2201_ok : ecellOkT e2201 = true := by decide +kernel
theorem e2201_pos {a z : ℝ} (ha1 : ((1297569/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((649209/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2201 e2201_ok ha1 ha2 hz1 hz2 hz

-- box ['16209/102400', '1297569/8192000', '7997/8000', '3999/4000']  interval_lower 98262557/549755813888
noncomputable def e2202 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273554440028,0,true,161568457856,161568457920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925468815524,0,false,-189468886912,-189468886848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273668390880,0,true,161666831872,161666831936⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925354864672,0,false,-189604275584,-189604275520⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273489173973,0,true,161512109568,161512109632⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925534081579,0,false,-189391349696,-189391349632⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273624851690,0,true,161629245440,161629245504⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925398403862,0,false,-189552543296,-189552543232⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533784882,0,true,22156864,22156928⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489470670,0,false,-22157376,-22157312⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544886727,0,true,33258432,33258496⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478368825,0,false,-33259456,-33259392⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626769,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627330,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273521802535,0,true,161540280192,161540280256⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925501453017,0,false,-189430112320,-189430112256⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273646625700,0,true,161648042624,161648042688⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925376629852,0,false,-189578414336,-189578414272⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071933022206,0,false,-27930371712,-27930371648⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071972545738,0,false,-27889832064,-27889832000⟩
    { al := (16209/102400), au := (1297569/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨174042812252,174156763104⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161568457856,161568457920⟩ : DyadicInterval 40),(⟨-189468886912,-189468886848⟩ : DyadicInterval 40),(⟨748290569166,748290588496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161666831872,161666831936⟩ : DyadicInterval 40),(⟨-189604275584,-189604275520⟩ : DyadicInterval 40),(⟨748272372763,748272392093⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161512109568,161512109632⟩ : DyadicInterval 40),(⟨-189391349696,-189391349632⟩ : DyadicInterval 40),(⟨748300985801,748301005131⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161629245440,161629245504⟩ : DyadicInterval 40),(⟨-189552543296,-189552543232⟩ : DyadicInterval 40),(⟨748279326804,748279346133⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22157106,33258951⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22156864,22156928⟩ : DyadicInterval 40),(⟨-22157376,-22157312⟩ : DyadicInterval 40),(⟨762123383361,762123402690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33258432,33258496⟩ : DyadicInterval 40),(⟨-33259456,-33259392⟩ : DyadicInterval 40),(⟨762123383057,762123402386⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174010174759,174134997924⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161540280192,161540280256⟩ : DyadicInterval 40),(⟨-189430112320,-189430112256⟩ : DyadicInterval 40),(⟨748295778710,748295798039⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161648042624,161648042688⟩ : DyadicInterval 40),(⟨-189578414336,-189578414272⟩ : DyadicInterval 40),(⟨748275849283,748275868612⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27930371712,-27889832000⟩ : DyadicInterval 40),(⟨776068299616,776088588736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161568457856,161666831936⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189604275584,-189468886848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2202_ok : ecellOkT e2202 = true := by decide +kernel
theorem e2202_pos {a z : ℝ} (ha1 : ((16209/102400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1297569/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2202 e2202_ok ha1 ha2 hz1 hz2 hz

-- box ['1297569/8192000', '649209/4096000', '7997/8000', '3999/4000']  interval_lower 24708745/137438953472
noncomputable def e2203 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273668390879,0,true,161666831872,161666831936⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925354864673,0,false,-189604275584,-189604275520⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273782341731,0,true,161765197120,161765197184⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925240913821,0,false,-189739680896,-189739680832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273603082092,0,true,161610451712,161610451776⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925420173460,0,false,-189526678016,-189526677952⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273738774053,0,true,161727589440,161727589504⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925284481499,0,false,-189687908416,-189687908352⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533799929,0,true,22171904,22171968⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489455623,0,false,-22172416,-22172352⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544909297,0,true,33280960,33281024⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478346255,0,false,-33282048,-33281984⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626768,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627329,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273635732017,0,true,161638638272,161638638336⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925387523535,0,false,-189565470784,-189565470720⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273760562311,0,true,161746397248,161746397312⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925262693241,0,false,-189713799616,-189713799552⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071896921010,0,false,-27967402368,-27967402304⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071936472670,0,false,-27926832448,-27926832384⟩
    { al := (1297569/8192000), au := (649209/4096000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨174156763103,174270713955⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161666831872,161666831936⟩ : DyadicInterval 40),(⟨-189604275584,-189604275520⟩ : DyadicInterval 40),(⟨748272372764,748272392093⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161765197120,161765197184⟩ : DyadicInterval 40),(⟨-189739680896,-189739680832⟩ : DyadicInterval 40),(⟨748254164215,748254183544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161610451712,161610451776⟩ : DyadicInterval 40),(⟨-189526678016,-189526677952⟩ : DyadicInterval 40),(⟨748282803158,748282822488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161727589440,161727589504⟩ : DyadicInterval 40),(⟨-189687908416,-189687908352⟩ : DyadicInterval 40),(⟨748261127461,748261146790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22172153,33281521⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22171904,22171968⟩ : DyadicInterval 40),(⟨-22172416,-22172352⟩ : DyadicInterval 40),(⟨762123383360,762123402689⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33280960,33281024⟩ : DyadicInterval 40),(⟨-33282048,-33281984⟩ : DyadicInterval 40),(⟨762123383088,762123402417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174124104241,174248934535⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161638638272,161638638336⟩ : DyadicInterval 40),(⟨-189565470784,-189565470720⟩ : DyadicInterval 40),(⟨748277589177,748277608506⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161746397248,161746397312⟩ : DyadicInterval 40),(⟨-189713799616,-189713799552⟩ : DyadicInterval 40),(⟨748257645362,748257664692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27967402368,-27926832384⟩ : DyadicInterval 40),(⟨776086799808,776107104064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161666831872,161765197184⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189739680896,-189604275520⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2203_ok : ecellOkT e2203 = true := by decide +kernel
theorem e2203_pos {a z : ℝ} (ha1 : ((1297569/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((649209/4096000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2203 e2203_ok ha1 ha2 hz1 hz2 hz

-- box ['649209/4096000', '1299267/8192000', '1999/2000', '7997/8000']  interval_lower 99491319/549755813888
noncomputable def e2204 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273782341730,0,true,161765197120,161765197184⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925240913822,0,false,-189739680896,-189739680832⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273896292582,0,true,161863553536,161863553600⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925126962970,0,false,-189875102912,-189875102848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273695206373,0,true,161689980480,161689980544⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925328049179,0,false,-189636138304,-189636138240⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273830898333,0,true,161807109696,161807109760⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925192357219,0,false,-189797384768,-189797384704⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544908626,0,true,33280320,33280384⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478346926,0,false,-33281408,-33281344⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556033045,0,true,44404352,44404416⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467222507,0,false,-44406208,-44406144⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625982,0,false,-1856,-1792⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626769,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273738769672,0,true,161727585664,161727585728⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925284485880,0,false,-189687903168,-189687903104⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273863599938,0,true,161835335872,161835335936⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925159655614,0,false,-189836248512,-189836248448⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071864252860,0,false,-28000912640,-28000912576⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071903827908,0,false,-27960317504,-27960317440⟩
    { al := (649209/4096000), au := (1299267/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨174270713954,174384664806⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161765197120,161765197184⟩ : DyadicInterval 40),(⟨-189739680896,-189739680832⟩ : DyadicInterval 40),(⟨748254164215,748254183544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161863553536,161863553600⟩ : DyadicInterval 40),(⟨-189875102912,-189875102848⟩ : DyadicInterval 40),(⟨748235943582,748235962911⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161689980480,161689980544⟩ : DyadicInterval 40),(⟨-189636138304,-189636138240⟩ : DyadicInterval 40),(⟨748268088903,748268108232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161807109696,161807109760⟩ : DyadicInterval 40),(⟨-189797384768,-189797384704⟩ : DyadicInterval 40),(⟨748246401570,748246420900⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33280850,44405269⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33280320,33280384⟩ : DyadicInterval 40),(⟨-33281408,-33281344⟩ : DyadicInterval 40),(⟨762123383088,762123402417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44404352,44404416⟩ : DyadicInterval 40),(⟨-44406208,-44406144⟩ : DyadicInterval 40),(⟨762123382686,762123402015⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1856,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174227141896,174351972162⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161727585664,161727585728⟩ : DyadicInterval 40),(⟨-189687903168,-189687903104⟩ : DyadicInterval 40),(⟨748261128139,748261147469⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161835335872,161835335936⟩ : DyadicInterval 40),(⟨-189836248512,-189836248448⟩ : DyadicInterval 40),(⟨748241172357,748241191687⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28000912640,-27960317440⟩ : DyadicInterval 40),(⟨776103542336,776123859200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161765197120,161863553600⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189875102912,-189739680832⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2204_ok : ecellOkT e2204 = true := by decide +kernel
theorem e2204_pos {a z : ℝ} (ha1 : ((649209/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1299267/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2204 e2204_ok ha1 ha2 hz1 hz2 hz

-- box ['1299267/8192000', '325029/2048000', '1999/2000', '7997/8000']  interval_lower 200133279/1099511627776
noncomputable def e2205 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273896292581,0,true,161863553536,161863553600⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925126962971,0,false,-189875102912,-189875102848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274010243433,0,true,161961901184,161961901248⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925013012119,0,false,-190010541632,-190010541568⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273809100248,0,true,161788294464,161788294528⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925214155304,0,false,-189771479872,-189771479808⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273944806453,0,true,161905425472,161905425536⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925078449099,0,false,-189932763072,-189932763008⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544931199,0,true,33302912,33302976⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478324353,0,false,-33303936,-33303872⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556063143,0,true,44434432,44434496⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467192409,0,false,-44436288,-44436224⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625980,0,false,-1856,-1792⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626768,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273852692033,0,true,161825920832,161825920896⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925170563519,0,false,-189823284992,-189823284928⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273977529425,0,true,161933667584,161933667648⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925045726127,0,false,-189971657024,-189971656960⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071828108957,0,false,-28037989440,-28037989376⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071867712134,0,false,-27997364096,-27997364032⟩
    { al := (1299267/8192000), au := (325029/2048000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨174384664805,174498615657⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161863553536,161863553600⟩ : DyadicInterval 40),(⟨-189875102912,-189875102848⟩ : DyadicInterval 40),(⟨748235943582,748235962912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161961901184,161961901248⟩ : DyadicInterval 40),(⟨-190010541632,-190010541568⟩ : DyadicInterval 40),(⟨748217710827,748217730157⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161788294464,161788294528⟩ : DyadicInterval 40),(⟨-189771479872,-189771479808⟩ : DyadicInterval 40),(⟨748249886636,748249905966⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161905425472,161905425536⟩ : DyadicInterval 40),(⟨-189932763072,-189932763008⟩ : DyadicInterval 40),(⟨748228182605,748228201935⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33303423,44435367⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33302912,33302976⟩ : DyadicInterval 40),(⟨-33303936,-33303872⟩ : DyadicInterval 40),(⟨762123383055,762123402384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44434432,44434496⟩ : DyadicInterval 40),(⟨-44436288,-44436224⟩ : DyadicInterval 40),(⟨762123382684,762123402013⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1856,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174341064257,174465901649⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161825920832,161825920896⟩ : DyadicInterval 40),(⟨-189823284992,-189823284928⟩ : DyadicInterval 40),(⟨748242916726,748242936055⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161933667584,161933667648⟩ : DyadicInterval 40),(⟨-189971657024,-189971656960⟩ : DyadicInterval 40),(⟨748222946497,748222965827⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28037989440,-27997364032⟩ : DyadicInterval 40),(⟨776122065632,776142397600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161863553536,161961901248⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190010541632,-189875102848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2205_ok : ecellOkT e2205 = true := by decide +kernel
theorem e2205_pos {a z : ℝ} (ha1 : ((1299267/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((325029/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2205 e2205_ok ha1 ha2 hz1 hz2 hz

-- box ['649209/4096000', '1299267/8192000', '7997/8000', '3999/4000']  interval_lower 198817631/1099511627776
noncomputable def e2206 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273782341730,0,true,161765197120,161765197184⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925240913822,0,false,-189739680896,-189739680832⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273896292582,0,true,161863553536,161863553600⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925126962970,0,false,-189875102912,-189875102848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273716990212,0,true,161708785088,161708785152⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925306265340,0,false,-189662023040,-189662022976⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273852696416,0,true,161825924608,161825924672⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925170559136,0,false,-189823290176,-189823290112⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533814976,0,true,22186944,22187008⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489440576,0,false,-22187456,-22187392⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544931869,0,true,33303552,33303616⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478323683,0,false,-33304640,-33304576⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626767,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627329,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273749661502,0,true,161736987584,161736987648⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925273594050,0,false,-189700846016,-189700845952⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273874498918,0,true,161844743040,161844743104⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925148756634,0,false,-189849201536,-189849201472⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071860796202,0,false,-28004458432,-28004458368⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071900375990,0,false,-27963858368,-27963858304⟩
    { al := (649209/4096000), au := (1299267/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨174270713954,174384664806⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161765197120,161765197184⟩ : DyadicInterval 40),(⟨-189739680896,-189739680832⟩ : DyadicInterval 40),(⟨748254164215,748254183544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161863553536,161863553600⟩ : DyadicInterval 40),(⟨-189875102912,-189875102848⟩ : DyadicInterval 40),(⟨748235943582,748235962911⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161708785088,161708785152⟩ : DyadicInterval 40),(⟨-189662023040,-189662022976⟩ : DyadicInterval 40),(⟨748264608415,748264627745⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161825924608,161825924672⟩ : DyadicInterval 40),(⟨-189823290176,-189823290112⟩ : DyadicInterval 40),(⟨748242916018,748242935348⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22187200,33304093⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22186944,22187008⟩ : DyadicInterval 40),(⟨-22187456,-22187392⟩ : DyadicInterval 40),(⟨762123383360,762123402689⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33303552,33303616⟩ : DyadicInterval 40),(⟨-33304640,-33304576⟩ : DyadicInterval 40),(⟨762123383087,762123402416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174238033726,174362871142⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161736987584,161736987648⟩ : DyadicInterval 40),(⟨-189700846016,-189700845952⟩ : DyadicInterval 40),(⟨748259387560,748259406889⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161844743040,161844743104⟩ : DyadicInterval 40),(⟨-189849201536,-189849201472⟩ : DyadicInterval 40),(⟨748239429338,748239448668⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28004458432,-27963858304⟩ : DyadicInterval 40),(⟨776105312768,776125632096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161765197120,161863553600⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189875102912,-189739680832⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2206_ok : ecellOkT e2206 = true := by decide +kernel
theorem e2206_pos {a z : ℝ} (ha1 : ((649209/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1299267/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2206 e2206_ok ha1 ha2 hz1 hz2 hz

-- box ['1299267/8192000', '325029/2048000', '7997/8000', '3999/4000']  interval_lower 199968179/1099511627776
noncomputable def e2207 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273896292581,0,true,161863553536,161863553600⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925126962971,0,false,-189875102912,-189875102848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274010243433,0,true,161961901184,161961901248⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925013012119,0,false,-190010541632,-190010541568⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273830898331,0,true,161807109696,161807109760⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925192357221,0,false,-189797384768,-189797384704⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273966618780,0,true,161924251008,161924251072⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925056636772,0,false,-189958688640,-189958688576⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533830024,0,true,22201984,22202048⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489425528,0,false,-22202496,-22202432⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544954444,0,true,33326144,33326208⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478301108,0,false,-33327232,-33327168⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626765,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627328,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273863590984,0,true,161835328128,161835328192⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925159664568,0,false,-189836237824,-189836237760⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273988435526,0,true,161943080064,161943080128⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925034820026,0,false,-189984620096,-189984620032⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071824647780,0,false,-28041540032,-28041539968⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071864255701,0,false,-28000909696,-28000909632⟩
    { al := (1299267/8192000), au := (325029/2048000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨174384664805,174498615657⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161863553536,161863553600⟩ : DyadicInterval 40),(⟨-189875102912,-189875102848⟩ : DyadicInterval 40),(⟨748235943582,748235962912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161961901184,161961901248⟩ : DyadicInterval 40),(⟨-190010541632,-190010541568⟩ : DyadicInterval 40),(⟨748217710827,748217730157⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161807109696,161807109760⟩ : DyadicInterval 40),(⟨-189797384768,-189797384704⟩ : DyadicInterval 40),(⟨748246401570,748246420900⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161924251008,161924251072⟩ : DyadicInterval 40),(⟨-189958688640,-189958688576⟩ : DyadicInterval 40),(⟨748224692467,748224711796⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22202248,33326668⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22201984,22202048⟩ : DyadicInterval 40),(⟨-22202496,-22202432⟩ : DyadicInterval 40),(⟨762123383359,762123402688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33326144,33326208⟩ : DyadicInterval 40),(⟨-33327232,-33327168⟩ : DyadicInterval 40),(⟨762123383085,762123402414⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174351963208,174476807750⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161835328128,161835328192⟩ : DyadicInterval 40),(⟨-189836237824,-189836237760⟩ : DyadicInterval 40),(⟨748241173779,748241193108⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161943080064,161943080128⟩ : DyadicInterval 40),(⟨-189984620096,-189984620032⟩ : DyadicInterval 40),(⟨748221201171,748221220501⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28041540032,-28000909632⟩ : DyadicInterval 40),(⟨776123838432,776144172896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161863553536,161961901248⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190010541632,-189875102848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2207_ok : ecellOkT e2207 = true := by decide +kernel
theorem e2207_pos {a z : ℝ} (ha1 : ((1299267/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((325029/2048000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2207 e2207_ok ha1 ha2 hz1 hz2 hz

-- box ['16209/102400', '1297569/8192000', '3999/4000', '7999/8000']  interval_lower 196360911/1099511627776
noncomputable def e2208 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273554440028,0,true,161568457856,161568457920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925468815524,0,false,-189468886912,-189468886848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273668390880,0,true,161666831872,161666831936⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925354864672,0,false,-189604275584,-189604275520⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273510929324,0,true,161530892608,161530892672⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925512326228,0,false,-189417194816,-189417194752⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273646621285,0,true,161648038784,161648038848⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925376634267,0,false,-189578409088,-189578409024⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522706226,0,true,11078336,11078400⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500549326,0,false,-11078528,-11078464⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533800546,0,true,22172544,22172608⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489455006,0,false,-22173056,-22172992⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627328,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627665,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273532680146,0,true,161549671488,161549671552⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925490575406,0,false,-189443035136,-189443035072⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273657510461,0,true,161657439168,161657439232⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925365745091,0,false,-189591347456,-189591347392⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071929574353,0,false,-27933908288,-27933908224⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071969102620,0,false,-27893363648,-27893363584⟩
    { al := (16209/102400), au := (1297569/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨174042812252,174156763104⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161568457856,161568457920⟩ : DyadicInterval 40),(⟨-189468886912,-189468886848⟩ : DyadicInterval 40),(⟨748290569166,748290588496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161666831872,161666831936⟩ : DyadicInterval 40),(⟨-189604275584,-189604275520⟩ : DyadicInterval 40),(⟨748272372763,748272392093⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161530892608,161530892672⟩ : DyadicInterval 40),(⟨-189417194816,-189417194752⟩ : DyadicInterval 40),(⟨748297514052,748297533381⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161648038784,161648038848⟩ : DyadicInterval 40),(⟨-189578409088,-189578409024⟩ : DyadicInterval 40),(⟨748275850004,748275869333⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11078450,22172770⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11078336,11078400⟩ : DyadicInterval 40),(⟨-11078528,-11078464⟩ : DyadicInterval 40),(⟨762123383536,762123402865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22172544,22172608⟩ : DyadicInterval 40),(⟨-22173056,-22172992⟩ : DyadicInterval 40),(⟨762123383360,762123402689⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174021052370,174145882685⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161549671488,161549671552⟩ : DyadicInterval 40),(⟨-189443035136,-189443035072⟩ : DyadicInterval 40),(⟨748294042531,748294061861⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161657439168,161657439232⟩ : DyadicInterval 40),(⟨-189591347456,-189591347392⟩ : DyadicInterval 40),(⟨748274110725,748274130055⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27933908288,-27893363584⟩ : DyadicInterval 40),(⟨776070065408,776090357024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161568457856,161666831936⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189604275584,-189468886848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2208_ok : ecellOkT e2208 = true := by decide +kernel
theorem e2208_pos {a z : ℝ} (ha1 : ((16209/102400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1297569/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2208 e2208_ok ha1 ha2 hz1 hz2 hz

-- box ['1297569/8192000', '649209/4096000', '3999/4000', '7999/8000']  interval_lower 197505293/1099511627776
noncomputable def e2209 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273668390879,0,true,161666831872,161666831936⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925354864673,0,false,-189604275584,-189604275520⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273782341731,0,true,161765197120,161765197184⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925240913821,0,false,-189739680896,-189739680832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273624851688,0,true,161629245440,161629245504⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925398403864,0,false,-189552543296,-189552543232⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273760557892,0,true,161746393408,161746393472⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925262697660,0,false,-189713794368,-189713794304⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522713749,0,true,11085888,11085952⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500541803,0,false,-11086080,-11086016⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533815594,0,true,22187584,22187648⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489439958,0,false,-22188096,-22188032⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627328,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627665,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273646616751,0,true,161648034880,161648034944⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925376638801,0,false,-189578403712,-189578403648⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273771454192,0,true,161755799104,161755799168⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925251801360,0,false,-189726742784,-189726742720⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071893468644,0,false,-27970943680,-27970943616⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071933025041,0,false,-27930368832,-27930368768⟩
    { al := (1297569/8192000), au := (649209/4096000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨174156763103,174270713955⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161666831872,161666831936⟩ : DyadicInterval 40),(⟨-189604275584,-189604275520⟩ : DyadicInterval 40),(⟨748272372764,748272392093⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161765197120,161765197184⟩ : DyadicInterval 40),(⟨-189739680896,-189739680832⟩ : DyadicInterval 40),(⟨748254164215,748254183544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161629245440,161629245504⟩ : DyadicInterval 40),(⟨-189552543296,-189552543232⟩ : DyadicInterval 40),(⟨748279326805,748279346134⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161746393408,161746393472⟩ : DyadicInterval 40),(⟨-189713794368,-189713794304⟩ : DyadicInterval 40),(⟨748257646085,748257665414⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11085973,22187818⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11085888,11085952⟩ : DyadicInterval 40),(⟨-11086080,-11086016⟩ : DyadicInterval 40),(⟨762123383536,762123402865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22187584,22187648⟩ : DyadicInterval 40),(⟨-22188096,-22188032⟩ : DyadicInterval 40),(⟨762123383360,762123402689⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174134988975,174259826416⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161648034880,161648034944⟩ : DyadicInterval 40),(⟨-189578403712,-189578403648⟩ : DyadicInterval 40),(⟨748275850727,748275870056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161755799104,161755799168⟩ : DyadicInterval 40),(⟨-189726742784,-189726742720⟩ : DyadicInterval 40),(⟨748255904504,748255923833⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27970943680,-27930368768⟩ : DyadicInterval 40),(⟨776088568000,776108874720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161666831872,161765197184⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189739680896,-189604275520⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2209_ok : ecellOkT e2209 = true := by decide +kernel
theorem e2209_pos {a z : ℝ} (ha1 : ((1297569/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((649209/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2209 e2209_ok ha1 ha2 hz1 hz2 hz

-- box ['16209/102400', '1297569/8192000', '7999/8000', '1']  interval_lower 98098447/549755813888
noncomputable def e2210 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273554440028,0,true,161568457856,161568457920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925468815524,0,false,-189468886912,-189468886848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273668390880,0,true,161666831872,161666831936⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925354864672,0,false,-189604275584,-189604275520⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273532684676,0,true,161549675392,161549675456⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925490570876,0,false,-189443040512,-189443040448⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522714316,0,true,11086464,11086528⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500541236,0,false,-11086656,-11086592⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627664,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1273543557787,0,true,161559062720,161559062784⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨925479697765,0,false,-189455958208,-189455958144⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1273668395245,0,true,161666835648,161666835712⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨925354860307,0,false,-189604280768,-189604280704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1071926126277,0,false,-27937445056,-27937444992⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1071965659277,0,false,-27896895488,-27896895424⟩
    { al := (16209/102400), au := (1297569/8192000), zl := (7999/8000), zu := 1,
      A := ⟨174042812252,174156763104⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161568457856,161568457920⟩ : DyadicInterval 40),(⟨-189468886912,-189468886848⟩ : DyadicInterval 40),(⟨748290569166,748290588496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161666831872,161666831936⟩ : DyadicInterval 40),(⟨-189604275584,-189604275520⟩ : DyadicInterval 40),(⟨748272372763,748272392093⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161549675392,161549675456⟩ : DyadicInterval 40),(⟨-189443040512,-189443040448⟩ : DyadicInterval 40),(⟨748294041810,748294061139⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161666831872,161666831936⟩ : DyadicInterval 40),(⟨-189604275584,-189604275520⟩ : DyadicInterval 40),(⟨748272372763,748272392093⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11086540⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11086464,11086528⟩ : DyadicInterval 40),(⟨-11086656,-11086592⟩ : DyadicInterval 40),(⟨762123383536,762123402865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨174031930011,174156767469⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161559062720,161559062784⟩ : DyadicInterval 40),(⟨-189455958208,-189455958144⟩ : DyadicInterval 40),(⟨748292306272,748292325601⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161666835648,161666835712⟩ : DyadicInterval 40),(⟨-189604280768,-189604280704⟩ : DyadicInterval 40),(⟨748272372061,748272391390⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27937445056,-27896895424⟩ : DyadicInterval 40),(⟨776071831328,776092125408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨161568457856,161666831936⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189604275584,-189468886848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2210_ok : ecellOkT e2210 = true := by decide +kernel
theorem e2210_pos {a z : ℝ} (ha1 : ((16209/102400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1297569/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2210 e2210_ok ha1 ha2 hz1 hz2 hz

-- box ['1297569/8192000', '649209/4096000', '7999/8000', '1']  interval_lower 197340705/1099511627776
noncomputable def e2211 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273668390879,0,true,161666831872,161666831936⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925354864673,0,false,-189604275584,-189604275520⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273782341731,0,true,161765197120,161765197184⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925240913821,0,false,-189739680896,-189739680832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273646621283,0,true,161648038784,161648038848⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925376634269,0,false,-189578409088,-189578409024⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522721839,0,true,11093952,11094016⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500533713,0,false,-11094144,-11094080⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627664,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1273657501512,0,true,161657431424,161657431488⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨925365754040,0,false,-189591336832,-189591336768⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1273782346102,0,true,161765200896,161765200960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨925240909450,0,false,-189739686080,-189739686016⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1071890016054,0,false,-27974485184,-27974485120⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1071929577189,0,false,-27933905344,-27933905280⟩
    { al := (1297569/8192000), au := (649209/4096000), zl := (7999/8000), zu := 1,
      A := ⟨174156763103,174270713955⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161666831872,161666831936⟩ : DyadicInterval 40),(⟨-189604275584,-189604275520⟩ : DyadicInterval 40),(⟨748272372764,748272392093⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161765197120,161765197184⟩ : DyadicInterval 40),(⟨-189739680896,-189739680832⟩ : DyadicInterval 40),(⟨748254164215,748254183544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161648038784,161648038848⟩ : DyadicInterval 40),(⟨-189578409088,-189578409024⟩ : DyadicInterval 40),(⟨748275850004,748275869334⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161765197120,161765197184⟩ : DyadicInterval 40),(⟨-189739680896,-189739680832⟩ : DyadicInterval 40),(⟨748254164215,748254183544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11094063⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11093952,11094016⟩ : DyadicInterval 40),(⟨-11094144,-11094080⟩ : DyadicInterval 40),(⟨762123383536,762123402865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨174145873736,174270718326⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161657431424,161657431488⟩ : DyadicInterval 40),(⟨-189591336832,-189591336768⟩ : DyadicInterval 40),(⟨748274112169,748274131499⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161765200896,161765200960⟩ : DyadicInterval 40),(⟨-189739686080,-189739686016⟩ : DyadicInterval 40),(⟨748254163510,748254182840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27974485184,-27933905280⟩ : DyadicInterval 40),(⟨776090336256,776110645472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨161666831872,161765197184⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189739680896,-189604275520⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2211_ok : ecellOkT e2211 = true := by decide +kernel
theorem e2211_pos {a z : ℝ} (ha1 : ((1297569/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((649209/4096000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2211 e2211_ok ha1 ha2 hz1 hz2 hz

-- box ['649209/4096000', '1299267/8192000', '3999/4000', '7999/8000']  interval_lower 198652431/1099511627776
noncomputable def e2212 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273782341730,0,true,161765197120,161765197184⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925240913822,0,false,-189739680896,-189739680832⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273896292582,0,true,161863553536,161863553600⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925126962970,0,false,-189875102912,-189875102848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273738774051,0,true,161727589440,161727589504⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925284481501,0,false,-189687908416,-189687908352⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273874494499,0,true,161844739264,161844739328⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925148761053,0,false,-189849196288,-189849196224⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522721273,0,true,11093440,11093504⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500534279,0,false,-11093568,-11093504⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533830643,0,true,22202624,22202688⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489424909,0,false,-22203136,-22203072⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627327,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627665,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273760553360,0,true,161746389504,161746389568⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925262702192,0,false,-189713788992,-189713788928⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273885397923,0,true,161854150208,161854150272⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925137857629,0,false,-189862154752,-189862154688⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071857339319,0,false,-28008004480,-28008004416⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071896923848,0,false,-27967399424,-27967399360⟩
    { al := (649209/4096000), au := (1299267/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨174270713954,174384664806⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161765197120,161765197184⟩ : DyadicInterval 40),(⟨-189739680896,-189739680832⟩ : DyadicInterval 40),(⟨748254164215,748254183544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161863553536,161863553600⟩ : DyadicInterval 40),(⟨-189875102912,-189875102848⟩ : DyadicInterval 40),(⟨748235943582,748235962911⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161727589440,161727589504⟩ : DyadicInterval 40),(⟨-189687908416,-189687908352⟩ : DyadicInterval 40),(⟨748261127461,748261146790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161844739264,161844739328⟩ : DyadicInterval 40),(⟨-189849196288,-189849196224⟩ : DyadicInterval 40),(⟨748239430024,748239449354⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11093497,22202867⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11093440,11093504⟩ : DyadicInterval 40),(⟨-11093568,-11093504⟩ : DyadicInterval 40),(⟨762123383504,762123402833⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22202624,22202688⟩ : DyadicInterval 40),(⟨-22203136,-22203072⟩ : DyadicInterval 40),(⟨762123383359,762123402688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174248925584,174373770147⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161746389504,161746389568⟩ : DyadicInterval 40),(⟨-189713788992,-189713788928⟩ : DyadicInterval 40),(⟨748257646808,748257666138⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161854150208,161854150272⟩ : DyadicInterval 40),(⟨-189862154752,-189862154688⟩ : DyadicInterval 40),(⟨748237686174,748237705504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28008004480,-27967399360⟩ : DyadicInterval 40),(⟨776107083296,776127405120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161765197120,161863553600⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189875102912,-189739680832⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2212_ok : ecellOkT e2212 = true := by decide +kernel
theorem e2212_pos {a z : ℝ} (ha1 : ((649209/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1299267/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2212 e2212_ok ha1 ha2 hz1 hz2 hz

-- box ['1299267/8192000', '325029/2048000', '3999/4000', '7999/8000']  interval_lower 199802389/1099511627776
noncomputable def e2213 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273896292581,0,true,161863553536,161863553600⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925126962971,0,false,-189875102912,-189875102848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274010243433,0,true,161961901184,161961901248⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925013012119,0,false,-190010541632,-190010541568⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273852696414,0,true,161825924608,161825924672⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925170559138,0,false,-189823290176,-189823290112⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273988431107,0,true,161943076288,161943076352⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925034824445,0,false,-189984614848,-189984614784⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522728797,0,true,11100928,11100992⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500526755,0,false,-11101120,-11101056⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533845691,0,true,22217664,22217728⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489409861,0,false,-22218176,-22218112⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627327,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627664,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273874489963,0,true,161844735296,161844735360⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925148765589,0,false,-189849190848,-189849190784⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273999341654,0,true,161952492544,161952492608⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925023913898,0,false,-189997583360,-189997583296⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071821186378,0,false,-28045090816,-28045090752⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071860799043,0,false,-28004455488,-28004455424⟩
    { al := (1299267/8192000), au := (325029/2048000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨174384664805,174498615657⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161863553536,161863553600⟩ : DyadicInterval 40),(⟨-189875102912,-189875102848⟩ : DyadicInterval 40),(⟨748235943582,748235962912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161961901184,161961901248⟩ : DyadicInterval 40),(⟨-190010541632,-190010541568⟩ : DyadicInterval 40),(⟨748217710827,748217730157⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161825924608,161825924672⟩ : DyadicInterval 40),(⟨-189823290176,-189823290112⟩ : DyadicInterval 40),(⟨748242916019,748242935348⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161943076288,161943076352⟩ : DyadicInterval 40),(⟨-189984614848,-189984614784⟩ : DyadicInterval 40),(⟨748221201858,748221221188⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11101021,22217915⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11100928,11100992⟩ : DyadicInterval 40),(⟨-11101120,-11101056⟩ : DyadicInterval 40),(⟨762123383535,762123402864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22217664,22217728⟩ : DyadicInterval 40),(⟨-22218176,-22218112⟩ : DyadicInterval 40),(⟨762123383359,762123402688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174362862187,174487713878⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161844735296,161844735360⟩ : DyadicInterval 40),(⟨-189849190848,-189849190784⟩ : DyadicInterval 40),(⟨748239430760,748239450089⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161952492544,161952492608⟩ : DyadicInterval 40),(⟨-189997583360,-189997583296⟩ : DyadicInterval 40),(⟨748219455700,748219475029⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28045090816,-28004455424⟩ : DyadicInterval 40),(⟨776125611328,776145948288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161863553536,161961901248⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190010541632,-189875102848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2213_ok : ecellOkT e2213 = true := by decide +kernel
theorem e2213_pos {a z : ℝ} (ha1 : ((1299267/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((325029/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2213 e2213_ok ha1 ha2 hz1 hz2 hz

-- box ['649209/4096000', '1299267/8192000', '7999/8000', '1']  interval_lower 198487683/1099511627776
noncomputable def e2214 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273782341730,0,true,161765197120,161765197184⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925240913822,0,false,-189739680896,-189739680832⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273896292582,0,true,161863553536,161863553600⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925126962970,0,false,-189875102912,-189875102848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273760557890,0,true,161746393408,161746393472⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925262697662,0,false,-189713794368,-189713794304⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522729363,0,true,11101504,11101568⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500526189,0,false,-11101696,-11101632⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627663,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1273771445240,0,true,161755791360,161755791424⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨925251810312,0,false,-189726732096,-189726732032⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1273896296953,0,true,161863557312,161863557376⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨925126958599,0,false,-189875108160,-189875108096⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1071853882213,0,false,-28011550784,-28011550720⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1071893471483,0,false,-27970940736,-27970940672⟩
    { al := (649209/4096000), au := (1299267/8192000), zl := (7999/8000), zu := 1,
      A := ⟨174270713954,174384664806⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161765197120,161765197184⟩ : DyadicInterval 40),(⟨-189739680896,-189739680832⟩ : DyadicInterval 40),(⟨748254164215,748254183544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161863553536,161863553600⟩ : DyadicInterval 40),(⟨-189875102912,-189875102848⟩ : DyadicInterval 40),(⟨748235943582,748235962911⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161746393408,161746393472⟩ : DyadicInterval 40),(⟨-189713794368,-189713794304⟩ : DyadicInterval 40),(⟨748257646085,748257665414⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161863553536,161863553600⟩ : DyadicInterval 40),(⟨-189875102912,-189875102848⟩ : DyadicInterval 40),(⟨748235943582,748235962911⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11101587⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11101504,11101568⟩ : DyadicInterval 40),(⟨-11101696,-11101632⟩ : DyadicInterval 40),(⟨762123383535,762123402864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨174259817464,174384669177⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161755791360,161755791424⟩ : DyadicInterval 40),(⟨-189726732096,-189726732032⟩ : DyadicInterval 40),(⟨748255905923,748255925253⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161863557312,161863557376⟩ : DyadicInterval 40),(⟨-189875108160,-189875108096⟩ : DyadicInterval 40),(⟨748235942903,748235962232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28011550784,-27970940672⟩ : DyadicInterval 40),(⟨776108853952,776129178272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨161765197120,161863553600⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189875102912,-189739680832⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2214_ok : ecellOkT e2214 = true := by decide +kernel
theorem e2214_pos {a z : ℝ} (ha1 : ((649209/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1299267/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2214 e2214_ok ha1 ha2 hz1 hz2 hz

-- box ['1299267/8192000', '325029/2048000', '7999/8000', '1']  interval_lower 199637171/1099511627776
noncomputable def e2215 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273896292581,0,true,161863553536,161863553600⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925126962971,0,false,-189875102912,-189875102848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274010243433,0,true,161961901184,161961901248⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925013012119,0,false,-190010541632,-190010541568⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273874494497,0,true,161844739264,161844739328⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925148761055,0,false,-189849196288,-189849196224⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522736889,0,true,11109056,11109120⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500518663,0,false,-11109184,-11109120⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627663,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1273885388969,0,true,161854142464,161854142528⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨925137866583,0,false,-189862144064,-189862144000⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1274010247805,0,true,161961904960,161961905024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨925013007747,0,false,-190010546816,-190010546752⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1071817724753,0,false,-28048641856,-28048641792⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1071857342161,0,false,-28008001600,-28008001536⟩
    { al := (1299267/8192000), au := (325029/2048000), zl := (7999/8000), zu := 1,
      A := ⟨174384664805,174498615657⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161863553536,161863553600⟩ : DyadicInterval 40),(⟨-189875102912,-189875102848⟩ : DyadicInterval 40),(⟨748235943582,748235962912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161961901184,161961901248⟩ : DyadicInterval 40),(⟨-190010541632,-190010541568⟩ : DyadicInterval 40),(⟨748217710827,748217730157⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161844739264,161844739328⟩ : DyadicInterval 40),(⟨-189849196288,-189849196224⟩ : DyadicInterval 40),(⟨748239430025,748239449354⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161961901184,161961901248⟩ : DyadicInterval 40),(⟨-190010541632,-190010541568⟩ : DyadicInterval 40),(⟨748217710827,748217730157⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11109113⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11109056,11109120⟩ : DyadicInterval 40),(⟨-11109184,-11109120⟩ : DyadicInterval 40),(⟨762123383503,762123402832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨174373761193,174498620029⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161854142464,161854142528⟩ : DyadicInterval 40),(⟨-189862144064,-189862144000⟩ : DyadicInterval 40),(⟨748237687596,748237706925⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161961904960,161961905024⟩ : DyadicInterval 40),(⟨-190010546816,-190010546752⟩ : DyadicInterval 40),(⟨748217710120,748217729449⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28048641856,-28008001536⟩ : DyadicInterval 40),(⟨776127384384,776147723808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨161863553536,161961901248⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190010541632,-189875102848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2215_ok : ecellOkT e2215 = true := by decide +kernel
theorem e2215_pos {a z : ℝ} (ha1 : ((1299267/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((325029/2048000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2215 e2215_ok ha1 ha2 hz1 hz2 hz

-- box ['325029/2048000', '260193/1638400', '1999/2000', '7997/8000']  interval_lower 50321721/274877906944
noncomputable def e2216 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274010243432,0,true,161961901184,161961901248⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925013012120,0,false,-190010541632,-190010541568⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274124194284,0,true,162060240000,162060240064⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924899061268,0,false,-190145997056,-190145996992⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273922994124,0,true,161886599616,161886599680⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925100261428,0,false,-189906838144,-189906838080⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274058714572,0,true,162003732480,162003732544⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924964540980,0,false,-190068158080,-190068158016⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544953773,0,true,33325440,33325504⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478301779,0,false,-33326528,-33326464⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556093244,0,true,44464512,44464576⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467162308,0,false,-44466368,-44466304⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625977,0,false,-1856,-1792⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626766,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273966614391,0,true,161924247232,161924247296⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925056641161,0,false,-189958683456,-189958683392⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274091458908,0,true,162031990464,162031990528⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924931796644,0,false,-190107082240,-190107082176⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071791941446,0,false,-28075091712,-28075091648⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071831572754,0,false,-28034436160,-28034436096⟩
    { al := (325029/2048000), au := (260193/1638400), zl := (1999/2000), zu := (7997/8000),
      A := ⟨174498615656,174612566508⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161961901184,161961901248⟩ : DyadicInterval 40),(⟨-190010541632,-190010541568⟩ : DyadicInterval 40),(⟨748217710827,748217730157⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162060240000,162060240064⟩ : DyadicInterval 40),(⟨-190145997056,-190145996992⟩ : DyadicInterval 40),(⟨748199465986,748199485316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161886599616,161886599680⟩ : DyadicInterval 40),(⟨-189906838144,-189906838080⟩ : DyadicInterval 40),(⟨748231672311,748231691640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162003732480,162003732544⟩ : DyadicInterval 40),(⟨-190068158080,-190068158016⟩ : DyadicInterval 40),(⟨748209951536,748209970865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33325997,44465468⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33325440,33325504⟩ : DyadicInterval 40),(⟨-33326528,-33326464⟩ : DyadicInterval 40),(⟨762123383085,762123402414⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44464512,44464576⟩ : DyadicInterval 40),(⟨-44466368,-44466304⟩ : DyadicInterval 40),(⟨762123382681,762123402010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1856,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174454986615,174579831132⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161924247232,161924247296⟩ : DyadicInterval 40),(⟨-189958683456,-189958683392⟩ : DyadicInterval 40),(⟨748224693176,748224712506⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162031990464,162031990528⟩ : DyadicInterval 40),(⟨-190107082240,-190107082176⟩ : DyadicInterval 40),(⟨748204708562,748204727891⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28075091712,-28034436096⟩ : DyadicInterval 40),(⟨776140601664,776160948736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161961901184,162060240064⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190145997056,-190010541568⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2216_ok : ecellOkT e2216 = true := by decide +kernel
theorem e2216_pos {a z : ℝ} (ha1 : ((325029/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((260193/1638400 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2216 e2216_ok ha1 ha2 hz1 hz2 hz

-- box ['260193/1638400', '650907/4096000', '1999/2000', '7997/8000']  interval_lower 101221717/549755813888
noncomputable def e2217 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274124194283,0,true,162060240000,162060240064⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924899061269,0,false,-190145997056,-190145996992⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274238145135,0,true,162158570048,162158570112⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924785110417,0,false,-190281469120,-190281469056⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274036887999,0,true,161984896000,161984896064⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924986367553,0,false,-190042212992,-190042212928⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274172622692,0,true,162102030720,162102030784⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924850632860,0,false,-190203569792,-190203569728⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544976348,0,true,33348032,33348096⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478279204,0,false,-33349120,-33349056⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556123347,0,true,44494656,44494720⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467132205,0,false,-44496512,-44496448⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625975,0,false,-1856,-1792⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626765,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274080536750,0,true,162022564864,162022564928⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924942718802,0,false,-190094098560,-190094098496⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274205388396,0,true,162130304640,162130304704⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924817867156,0,false,-190242524096,-190242524032⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071755750322,0,false,-28112219456,-28112219392⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071795409766,0,false,-28071533696,-28071533632⟩
    { al := (260193/1638400), au := (650907/4096000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨174612566507,174726517359⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162060240000,162060240064⟩ : DyadicInterval 40),(⟨-190145997056,-190145996992⟩ : DyadicInterval 40),(⟨748199465986,748199485316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162158570048,162158570112⟩ : DyadicInterval 40),(⟨-190281469120,-190281469056⟩ : DyadicInterval 40),(⟨748181208993,748181228323⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161984896000,161984896064⟩ : DyadicInterval 40),(⟨-190042212992,-190042212928⟩ : DyadicInterval 40),(⟨748213445833,748213465163⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162102030720,162102030784⟩ : DyadicInterval 40),(⟨-190203569792,-190203569728⟩ : DyadicInterval 40),(⟨748191708361,748191727691⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33348572,44495571⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33348032,33348096⟩ : DyadicInterval 40),(⟨-33349120,-33349056⟩ : DyadicInterval 40),(⟨762123383084,762123402413⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44494656,44494720⟩ : DyadicInterval 40),(⟨-44496512,-44496448⟩ : DyadicInterval 40),(⟨762123382679,762123402008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1856,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174568908974,174693760620⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162022564864,162022564928⟩ : DyadicInterval 40),(⟨-190094098560,-190094098496⟩ : DyadicInterval 40),(⟨748206457489,748206476818⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162130304640,162130304704⟩ : DyadicInterval 40),(⟨-190242524096,-190242524032⟩ : DyadicInterval 40),(⟨748186458446,748186477775⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28112219456,-28071533632⟩ : DyadicInterval 40),(⟨776159150432,776179512608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162060240000,162158570112⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190281469120,-190145996992⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2217_ok : ecellOkT e2217 = true := by decide +kernel
theorem e2217_pos {a z : ℝ} (ha1 : ((260193/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((650907/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2217 e2217_ok ha1 ha2 hz1 hz2 hz

-- box ['325029/2048000', '260193/1638400', '7997/8000', '3999/4000']  interval_lower 201121311/1099511627776
noncomputable def e2218 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274010243432,0,true,161961901184,161961901248⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925013012120,0,false,-190010541632,-190010541568⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274124194284,0,true,162060240000,162060240064⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924899061268,0,false,-190145997056,-190145996992⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273944806451,0,true,161905425472,161905425536⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925078449101,0,false,-189932763072,-189932763008⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274080541143,0,true,162022568640,162022568704⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924942714409,0,false,-190094103808,-190094103744⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533845073,0,true,22217024,22217088⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489410479,0,false,-22217536,-22217472⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544977019,0,true,33348736,33348800⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478278533,0,false,-33349760,-33349696⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626764,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627328,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273977520468,0,true,161933659840,161933659904⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925045735084,0,false,-189971646336,-189971646272⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274102372131,0,true,162041408320,162041408384⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924920883421,0,false,-190120055360,-190120055296⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071788475747,0,false,-28078647040,-28078646976⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071828111801,0,false,-28037986496,-28037986432⟩
    { al := (325029/2048000), au := (260193/1638400), zl := (7997/8000), zu := (3999/4000),
      A := ⟨174498615656,174612566508⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161961901184,161961901248⟩ : DyadicInterval 40),(⟨-190010541632,-190010541568⟩ : DyadicInterval 40),(⟨748217710827,748217730157⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162060240000,162060240064⟩ : DyadicInterval 40),(⟨-190145997056,-190145996992⟩ : DyadicInterval 40),(⟨748199465986,748199485316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161905425472,161905425536⟩ : DyadicInterval 40),(⟨-189932763072,-189932763008⟩ : DyadicInterval 40),(⟨748228182605,748228201935⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162022568640,162022568704⟩ : DyadicInterval 40),(⟨-190094103808,-190094103744⟩ : DyadicInterval 40),(⟨748206456805,748206476134⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22217297,33349243⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22217024,22217088⟩ : DyadicInterval 40),(⟨-22217536,-22217472⟩ : DyadicInterval 40),(⟨762123383359,762123402688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33348736,33348800⟩ : DyadicInterval 40),(⟨-33349760,-33349696⟩ : DyadicInterval 40),(⟨762123383052,762123402381⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174465892692,174590744355⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161933659840,161933659904⟩ : DyadicInterval 40),(⟨-189971646336,-189971646272⟩ : DyadicInterval 40),(⟨748222947921,748222967251⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162041408320,162041408384⟩ : DyadicInterval 40),(⟨-190120055360,-190120055296⟩ : DyadicInterval 40),(⟨748202960888,748202980217⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28078647040,-28037986432⟩ : DyadicInterval 40),(⟨776142376832,776162726400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161961901184,162060240064⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190145997056,-190010541568⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2218_ok : ecellOkT e2218 = true := by decide +kernel
theorem e2218_pos {a z : ℝ} (ha1 : ((325029/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((260193/1638400 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2218 e2218_ok ha1 ha2 hz1 hz2 hz

-- box ['260193/1638400', '650907/4096000', '7997/8000', '3999/4000']  interval_lower 202277273/1099511627776
noncomputable def e2219 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1274124194283,0,true,162060240000,162060240064⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨924899061269,0,false,-190145997056,-190145996992⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1274238145135,0,true,162158570048,162158570112⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨924785110417,0,false,-190281469120,-190281469056⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1274058714570,0,true,162003732480,162003732544⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨924964540982,0,false,-190068158080,-190068158016⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1274194463506,0,true,162120877504,162120877568⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨924828792046,0,false,-190229535616,-190229535552⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533860123,0,true,22232064,22232128⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489395429,0,false,-22232576,-22232512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544999597,0,true,33371264,33371328⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478255955,0,false,-33372352,-33372288⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626763,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627327,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1274091449948,0,true,162031982720,162031982784⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨924931805604,0,false,-190107071552,-190107071488⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1274216308743,0,true,162139727744,162139727808⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨924806946809,0,false,-190255507328,-190255507264⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071752280097,0,false,-28115779584,-28115779520⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071791944292,0,false,-28075088768,-28075088704⟩
    { al := (260193/1638400), au := (650907/4096000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨174612566507,174726517359⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162060240000,162060240064⟩ : DyadicInterval 40),(⟨-190145997056,-190145996992⟩ : DyadicInterval 40),(⟨748199465986,748199485316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162158570048,162158570112⟩ : DyadicInterval 40),(⟨-190281469120,-190281469056⟩ : DyadicInterval 40),(⟨748181208993,748181228323⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162003732480,162003732544⟩ : DyadicInterval 40),(⟨-190068158080,-190068158016⟩ : DyadicInterval 40),(⟨748209951536,748209970866⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162120877504,162120877568⟩ : DyadicInterval 40),(⟨-190229535616,-190229535552⟩ : DyadicInterval 40),(⟨748188209004,748188228334⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22232347,33371821⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22232064,22232128⟩ : DyadicInterval 40),(⟨-22232576,-22232512⟩ : DyadicInterval 40),(⟨762123383358,762123402687⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33371264,33371328⟩ : DyadicInterval 40),(⟨-33372352,-33372288⟩ : DyadicInterval 40),(⟨762123383083,762123402412⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨174579822172,174704680967⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162031982720,162031982784⟩ : DyadicInterval 40),(⟨-190107071552,-190107071488⟩ : DyadicInterval 40),(⟨748204709988,748204729317⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨162139727744,162139727808⟩ : DyadicInterval 40),(⟨-190255507328,-190255507264⟩ : DyadicInterval 40),(⟨748184708522,748184727852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28115779584,-28075088704⟩ : DyadicInterval 40),(⟨776160927968,776181292672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨162060240000,162158570112⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-190281469120,-190145996992⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2219_ok : ecellOkT e2219 = true := by decide +kernel
theorem e2219_pos {a z : ℝ} (ha1 : ((260193/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((650907/4096000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2219 e2219_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B036

end


