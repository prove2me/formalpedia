-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B046
-- name    : CK_CKLaneC2R_EpCells_B046
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:15:13.679659+00:00
-- url     : https://prove2.me/theorems/31233832-0b4e-4a75-9fb5-fa6b63c01213
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B046` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B046` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B046` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B046 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B046.lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheckT

-- ===== source module CKLaneC2R.EpCells.B046 =====
section

namespace CKLaneC2R.EpCells.B046

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['340311/2048000', '1362093/8192000', '999/1000', '7993/8000']  interval_lower 73199807/274877906944
noncomputable def e2760 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282214704709,0,true,169019911872,169019911936⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916808550843,0,false,-199806235648,-199806235584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282328655561,0,true,169117621504,169117621568⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916694599991,0,false,-199942903360,-199942903296⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282032001632,0,true,168863231040,168863231104⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916991253920,0,false,-199587145088,-199587145024⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282168690662,0,true,168980453696,168980453760⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916854564890,0,false,-199751053248,-199751053184⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593190573,0,true,81559744,81559808⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430064979,0,false,-81565824,-81565760⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099604903716,0,true,93271936,93272000⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099418351836,0,false,-93279936,-93279872⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619863,0,false,-7936,-7872⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621726,0,false,-6080,-6016⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282123349316,0,true,168941570944,168941571008⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916899906236,0,false,-199696680320,-199696680256⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282248682291,0,true,169049047616,169049047680⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916774573261,0,false,-199846985088,-199846985024⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069141024819,0,false,-30797937472,-30797937408⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069182670809,0,false,-30755109312,-30755109248⟩
    { al := (340311/2048000), au := (1362093/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨182703076933,182817027785⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169019911872,169019911936⟩ : DyadicInterval 40),(⟨-199806235648,-199806235584⟩ : DyadicInterval 40),(⟨746873089607,746873108937⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169117621504,169117621568⟩ : DyadicInterval 40),(⟨-199942903360,-199942903296⟩ : DyadicInterval 40),(⟨746853971409,746853990739⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168863231040,168863231104⟩ : DyadicInterval 40),(⟨-199587145088,-199587145024⟩ : DyadicInterval 40),(⟨746903717471,746903736801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168980453696,168980453760⟩ : DyadicInterval 40),(⟨-199751053248,-199751053184⟩ : DyadicInterval 40),(⟨746880806209,746880825538⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨81562797,93275940⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81559744,81559808⟩ : DyadicInterval 40),(⟨-81565824,-81565760⟩ : DyadicInterval 40),(⟨762123380541,762123399870⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨93271936,93272000⟩ : DyadicInterval 40),(⟨-93279936,-93279872⟩ : DyadicInterval 40),(⟨762123379638,762123398968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7936,-6016⟩ : DyadicInterval 40),(⟨762123386624,762123406848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182611721540,182737054515⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168941570944,168941571008⟩ : DyadicInterval 40),(⟨-199696680320,-199696680256⟩ : DyadicInterval 40),(⟨746888408100,746888427429⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169049047616,169049047680⟩ : DyadicInterval 40),(⟨-199846985088,-199846985024⟩ : DyadicInterval 40),(⟨746867390240,746867409570⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30797937472,-30755109248⟩ : DyadicInterval 40),(⟨777500938240,777522371616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169019911872,169117621568⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199942903360,-199806235584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2760_ok : ecellOkT e2760 = true := by decide +kernel
theorem e2760_pos {a z : ℝ} (ha1 : ((340311/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1362093/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2760 e2760_ok ha1 ha2 hz1 hz2 hz

-- box ['1362093/8192000', '681471/4096000', '999/1000', '7993/8000']  interval_lower 147085897/549755813888
noncomputable def e2761 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282328655560,0,true,169117621504,169117621568⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916694599992,0,false,-199942903296,-199942903232⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282442606412,0,true,169215322432,169215322496⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916580649140,0,false,-200079587968,-200079587904⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282145838532,0,true,168960856896,168960856960⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916877417020,0,false,-199723648832,-199723648768⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282282541806,0,true,169078081344,169078081408⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916740713746,0,false,-199887594496,-199887594432⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593243529,0,true,81612672,81612736⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430012023,0,false,-81618816,-81618752⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099604964244,0,true,93332480,93332544⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099418291308,0,false,-93340480,-93340416⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619852,0,false,-7936,-7872⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621718,0,false,-6080,-6016⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282237243194,0,true,169039238656,169039238720⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916786012358,0,false,-199833265984,-199833265920⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282362583289,0,true,169146711872,169146711936⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916660672263,0,false,-199983598016,-199983597952⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069103152697,0,false,-30836886144,-30836886080⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069144827020,0,false,-30794027264,-30794027200⟩
    { al := (1362093/8192000), au := (681471/4096000), zl := (999/1000), zu := (7993/8000),
      A := ⟨182817027784,182930978636⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169117621504,169117621568⟩ : DyadicInterval 40),(⟨-199942903296,-199942903232⟩ : DyadicInterval 40),(⟨746853971383,746853990713⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169215322432,169215322496⟩ : DyadicInterval 40),(⟨-200079587968,-200079587904⟩ : DyadicInterval 40),(⟨746834841040,746834860370⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168960856896,168960856960⟩ : DyadicInterval 40),(⟨-199723648832,-199723648768⟩ : DyadicInterval 40),(⟨746884637804,746884657133⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169078081344,169078081408⟩ : DyadicInterval 40),(⟨-199887594496,-199887594432⟩ : DyadicInterval 40),(⟨746861709634,746861728964⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨81615753,93336468⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81612672,81612736⟩ : DyadicInterval 40),(⟨-81618816,-81618752⟩ : DyadicInterval 40),(⟨762123380565,762123399894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨93332480,93332544⟩ : DyadicInterval 40),(⟨-93340480,-93340416⟩ : DyadicInterval 40),(⟨762123379628,762123398958⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7936,-6016⟩ : DyadicInterval 40),(⟨762123386624,762123406848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182725615418,182850955513⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169039238656,169039238720⟩ : DyadicInterval 40),(⟨-199833265984,-199833265920⟩ : DyadicInterval 40),(⟨746869309169,746869328499⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169146711872,169146711936⟩ : DyadicInterval 40),(⟨-199983598016,-199983597952⟩ : DyadicInterval 40),(⟨746848276793,746848296123⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30836886144,-30794027200⟩ : DyadicInterval 40),(⟨777520397216,777541845952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169117621504,169215322496⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200079587968,-199942903232⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2761_ok : ecellOkT e2761 = true := by decide +kernel
theorem e2761_pos {a z : ℝ} (ha1 : ((1362093/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((681471/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2761 e2761_ok ha1 ha2 hz1 hz2 hz

-- box ['340311/2048000', '1362093/8192000', '7993/8000', '3997/4000']  interval_lower 36575495/137438953472
noncomputable def e2762 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282214704709,0,true,169019911872,169019911936⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916808550843,0,false,-199806235648,-199806235584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282328655561,0,true,169117621504,169117621568⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916694599991,0,false,-199942903360,-199942903296⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282054839516,0,true,168882817344,168882817408⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916968416036,0,false,-199614529024,-199614528960⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282191542791,0,true,169000050112,169000050176⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916831712761,0,false,-199778458368,-199778458304⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581538886,0,true,69908864,69908928⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441716666,0,false,-69913344,-69913280⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593244465,0,true,81613632,81613696⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430011087,0,false,-81619776,-81619712⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621717,0,false,-6080,-6016⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623331,0,false,-4480,-4416⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282134768041,0,true,168951363264,168951363328⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916888487511,0,false,-199710373248,-199710373184⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282260108165,0,true,169058845120,169058845184⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916763147387,0,false,-199860688576,-199860688512⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069137226777,0,false,-30801843392,-30801843328⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069178877747,0,false,-30759009984,-30759009920⟩
    { al := (340311/2048000), au := (1362093/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨182703076933,182817027785⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169019911872,169019911936⟩ : DyadicInterval 40),(⟨-199806235648,-199806235584⟩ : DyadicInterval 40),(⟨746873089607,746873108937⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169117621504,169117621568⟩ : DyadicInterval 40),(⟨-199942903360,-199942903296⟩ : DyadicInterval 40),(⟨746853971409,746853990739⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168882817344,168882817408⟩ : DyadicInterval 40),(⟨-199614529024,-199614528960⟩ : DyadicInterval 40),(⟨746899890709,746899910039⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169000050112,169000050176⟩ : DyadicInterval 40),(⟨-199778458368,-199778458304⟩ : DyadicInterval 40),(⟨746876974155,746876993484⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨69911110,81616689⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69908864,69908928⟩ : DyadicInterval 40),(⟨-69913344,-69913280⟩ : DyadicInterval 40),(⟨762123381346,762123400675⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81613632,81613696⟩ : DyadicInterval 40),(⟨-81619776,-81619712⟩ : DyadicInterval 40),(⟨762123380565,762123399894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6080,-4416⟩ : DyadicInterval 40),(⟨762123385824,762123405920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182623140265,182748480389⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168951363264,168951363328⟩ : DyadicInterval 40),(⟨-199710373248,-199710373184⟩ : DyadicInterval 40),(⟨746886493811,746886513140⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169058845120,169058845184⟩ : DyadicInterval 40),(⟨-199860688576,-199860688512⟩ : DyadicInterval 40),(⟨746865473455,746865492785⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30801843392,-30759009920⟩ : DyadicInterval 40),(⟨777502888576,777524324576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169019911872,169117621568⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199942903360,-199806235584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2762_ok : ecellOkT e2762 = true := by decide +kernel
theorem e2762_pos {a z : ℝ} (ha1 : ((340311/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1362093/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2762 e2762_ok ha1 ha2 hz1 hz2 hz

-- box ['1362093/8192000', '681471/4096000', '7993/8000', '3997/4000']  interval_lower 36746993/137438953472
noncomputable def e2763 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282328655560,0,true,169117621504,169117621568⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916694599992,0,false,-199942903296,-199942903232⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282442606412,0,true,169215322432,169215322496⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916580649140,0,false,-200079587968,-200079587904⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282168690660,0,true,168980453696,168980453760⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916854564892,0,false,-199751053248,-199751053184⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282305408179,0,true,169097688256,169097688320⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916717847373,0,false,-199915020032,-199915019968⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581584279,0,true,69954240,69954304⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441671273,0,false,-69958784,-69958720⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593297428,0,true,81666560,81666624⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429958124,0,false,-81672704,-81672640⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621709,0,false,-6080,-6016⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623326,0,false,-4480,-4416⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282248669043,0,true,169049036224,169049036288⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916774586509,0,false,-199846969216,-199846969152⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282374016291,0,true,169156514624,169156514688⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916649239261,0,false,-199997311744,-199997311680⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069099349916,0,false,-30840797056,-30840796992⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069141029224,0,false,-30797932928,-30797932864⟩
    { al := (1362093/8192000), au := (681471/4096000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨182817027784,182930978636⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169117621504,169117621568⟩ : DyadicInterval 40),(⟨-199942903296,-199942903232⟩ : DyadicInterval 40),(⟨746853971383,746853990713⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169215322432,169215322496⟩ : DyadicInterval 40),(⟨-200079587968,-200079587904⟩ : DyadicInterval 40),(⟨746834841040,746834860370⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168980453696,168980453760⟩ : DyadicInterval 40),(⟨-199751053248,-199751053184⟩ : DyadicInterval 40),(⟨746880806209,746880825539⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169097688256,169097688320⟩ : DyadicInterval 40),(⟨-199915020032,-199915019968⟩ : DyadicInterval 40),(⟨746857872714,746857892043⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨69956503,81669652⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69954240,69954304⟩ : DyadicInterval 40),(⟨-69958784,-69958720⟩ : DyadicInterval 40),(⟨762123381372,762123400702⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81666560,81666624⟩ : DyadicInterval 40),(⟨-81672704,-81672640⟩ : DyadicInterval 40),(⟨762123380557,762123399886⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6080,-4416⟩ : DyadicInterval 40),(⟨762123385824,762123405920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182737041267,182862388515⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169049036224,169049036288⟩ : DyadicInterval 40),(⟨-199846969216,-199846969152⟩ : DyadicInterval 40),(⟨746867392489,746867411818⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169156514624,169156514688⟩ : DyadicInterval 40),(⟨-199997311744,-199997311680⟩ : DyadicInterval 40),(⟨746846357585,746846376914⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30840797056,-30797932864⟩ : DyadicInterval 40),(⟨777522350048,777543801408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169117621504,169215322496⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200079587968,-199942903232⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2763_ok : ecellOkT e2763 = true := by decide +kernel
theorem e2763_pos {a z : ℝ} (ha1 : ((1362093/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((681471/4096000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2763 e2763_ok ha1 ha2 hz1 hz2 hz

-- box ['681471/4096000', '1363791/8192000', '999/1000', '7993/8000']  interval_lower 295547497/1099511627776
noncomputable def e2764 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282442606411,0,true,169215322432,169215322496⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916580649141,0,false,-200079587968,-200079587904⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282556557263,0,true,169313014720,169313014784⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916466698289,0,false,-200216289600,-200216289536⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282259675432,0,true,169058474048,169058474112⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916763580120,0,false,-199860169536,-199860169472⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282396392950,0,true,169175700288,169175700352⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916626862602,0,false,-200024152640,-200024152576⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593296491,0,true,81665664,81665728⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429959061,0,false,-81671808,-81671744⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099605024776,0,true,93393024,93393088⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099418230776,0,false,-93401024,-93400960⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619842,0,false,-7936,-7872⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621710,0,false,-6080,-6016⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282351137066,0,true,169136897728,169136897792⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916672118486,0,false,-199969868672,-199969868608⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282476484290,0,true,169244367488,169244367552⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916546771262,0,false,-200120227968,-200120227904⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069065256975,0,false,-30875860416,-30875860352⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069106959638,0,false,-30832970880,-30832970816⟩
    { al := (681471/4096000), au := (1363791/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨182930978635,183044929487⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169215322432,169215322496⟩ : DyadicInterval 40),(⟨-200079587968,-200079587904⟩ : DyadicInterval 40),(⟨746834841041,746834860370⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169313014720,169313014784⟩ : DyadicInterval 40),(⟨-200216289600,-200216289536⟩ : DyadicInterval 40),(⟨746815698514,746815717843⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169058474048,169058474112⟩ : DyadicInterval 40),(⟨-199860169536,-199860169472⟩ : DyadicInterval 40),(⟨746865546041,746865565370⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169175700288,169175700352⟩ : DyadicInterval 40),(⟨-200024152640,-200024152576⟩ : DyadicInterval 40),(⟨746842600931,746842620260⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨81668715,93397000⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81665664,81665728⟩ : DyadicInterval 40),(⟨-81671808,-81671744⟩ : DyadicInterval 40),(⟨762123380557,762123399887⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨93393024,93393088⟩ : DyadicInterval 40),(⟨-93401024,-93400960⟩ : DyadicInterval 40),(⟨762123379618,762123398947⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7936,-6016⟩ : DyadicInterval 40),(⟨762123386624,762123406848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182839509290,182964856514⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169136897728,169136897792⟩ : DyadicInterval 40),(⟨-199969868672,-199969868608⟩ : DyadicInterval 40),(⟨746850198110,746850217439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169244367488,169244367552⟩ : DyadicInterval 40),(⟨-200120227968,-200120227904⟩ : DyadicInterval 40),(⟨746829151210,746829170540⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30875860416,-30832970816⟩ : DyadicInterval 40),(⟨777539869024,777561333088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169215322432,169313014784⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200216289600,-200079587904⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2764_ok : ecellOkT e2764 = true := by decide +kernel
theorem e2764_pos {a z : ℝ} (ha1 : ((681471/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1363791/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2764 e2764_ok ha1 ha2 hz1 hz2 hz

-- box ['1363791/8192000', '8529/51200', '999/1000', '7993/8000']  interval_lower 296926341/1099511627776
noncomputable def e2765 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282556557262,0,true,169313014720,169313014784⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916466698290,0,false,-200216289600,-200216289536⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282670508114,0,true,169410698304,169410698368⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916352747438,0,false,-200353008256,-200353008192⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282373512332,0,true,169156082560,169156082624⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916649743220,0,false,-199996707264,-199996707200⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282510244094,0,true,169273310592,169273310656⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916513011458,0,false,-200160727744,-200160727680⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593349457,0,true,81718592,81718656⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429906095,0,false,-81724736,-81724672⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099605085314,0,true,93453504,93453568⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099418170238,0,false,-93461568,-93461504⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619832,0,false,-8000,-7936⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621703,0,false,-6080,-6016⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282465030942,0,true,169234548096,169234548160⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916558224610,0,false,-200106488320,-200106488256⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282590385288,0,true,169342014464,169342014528⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916432870264,0,false,-200256874816,-200256874752⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069027337655,0,false,-30914860352,-30914860288⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069069068658,0,false,-30871940160,-30871940096⟩
    { al := (1363791/8192000), au := (8529/51200), zl := (999/1000), zu := (7993/8000),
      A := ⟨183044929486,183158880338⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169313014720,169313014784⟩ : DyadicInterval 40),(⟨-200216289600,-200216289536⟩ : DyadicInterval 40),(⟨746815698514,746815717844⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169410698304,169410698368⟩ : DyadicInterval 40),(⟨-200353008256,-200353008192⟩ : DyadicInterval 40),(⟨746796543867,746796563196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169156082560,169156082624⟩ : DyadicInterval 40),(⟨-199996707264,-199996707200⟩ : DyadicInterval 40),(⟨746846442172,746846461502⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169273310592,169273310656⟩ : DyadicInterval 40),(⟨-200160727744,-200160727680⟩ : DyadicInterval 40),(⟨746823480087,746823499416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨81721681,93457538⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81718592,81718656⟩ : DyadicInterval 40),(⟨-81724736,-81724672⟩ : DyadicInterval 40),(⟨762123380549,762123399879⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨93453504,93453568⟩ : DyadicInterval 40),(⟨-93461568,-93461504⟩ : DyadicInterval 40),(⟨762123379639,762123398969⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8000,-6016⟩ : DyadicInterval 40),(⟨762123386624,762123406880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182953403166,183078757512⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169234548096,169234548160⟩ : DyadicInterval 40),(⟨-200106488320,-200106488256⟩ : DyadicInterval 40),(⟨746831074928,746831094258⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169342014464,169342014528⟩ : DyadicInterval 40),(⟨-200256874816,-200256874752⟩ : DyadicInterval 40),(⟨746810013438,746810032768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30914860352,-30871940096⟩ : DyadicInterval 40),(⟨777559353664,777580833056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169313014720,169410698368⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200353008256,-200216289536⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2765_ok : ecellOkT e2765 = true := by decide +kernel
theorem e2765_pos {a z : ℝ} (ha1 : ((1363791/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((8529/51200 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2765 e2765_ok ha1 ha2 hz1 hz2 hz

-- box ['681471/4096000', '1363791/8192000', '7993/8000', '3997/4000']  interval_lower 73837827/274877906944
noncomputable def e2766 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282442606411,0,true,169215322432,169215322496⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916580649141,0,false,-200079587968,-200079587904⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282556557263,0,true,169313014720,169313014784⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916466698289,0,false,-200216289600,-200216289536⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282282541804,0,true,169078081344,169078081408⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916740713748,0,false,-199887594496,-199887594432⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282419273567,0,true,169195317696,169195317760⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916603981985,0,false,-200051598720,-200051598656⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581629674,0,true,69999616,69999680⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441625878,0,false,-70004160,-70004096⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593350394,0,true,81719552,81719616⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429905158,0,false,-81725696,-81725632⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621701,0,false,-6080,-6016⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623320,0,false,-4480,-4416⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282362570035,0,true,169146700544,169146700608⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916660685517,0,false,-199983582144,-199983582080⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282487924411,0,true,169254175488,169254175552⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916535331141,0,false,-200133951872,-200133951808⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069061449456,0,false,-30879776384,-30879776320⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069103157106,0,false,-30836881600,-30836881536⟩
    { al := (681471/4096000), au := (1363791/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨182930978635,183044929487⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169215322432,169215322496⟩ : DyadicInterval 40),(⟨-200079587968,-200079587904⟩ : DyadicInterval 40),(⟨746834841041,746834860370⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169313014720,169313014784⟩ : DyadicInterval 40),(⟨-200216289600,-200216289536⟩ : DyadicInterval 40),(⟨746815698514,746815717843⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169078081344,169078081408⟩ : DyadicInterval 40),(⟨-199887594496,-199887594432⟩ : DyadicInterval 40),(⟨746861709634,746861728964⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169195317696,169195317760⟩ : DyadicInterval 40),(⟨-200051598720,-200051598656⟩ : DyadicInterval 40),(⟨746838759191,746838778520⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨70001898,81722618⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69999616,69999680⟩ : DyadicInterval 40),(⟨-70004160,-70004096⟩ : DyadicInterval 40),(⟨762123381367,762123400696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81719552,81719616⟩ : DyadicInterval 40),(⟨-81725696,-81725632⟩ : DyadicInterval 40),(⟨762123380549,762123399879⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6080,-4416⟩ : DyadicInterval 40),(⟨762123385824,762123405920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182850942259,182976296635⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169146700544,169146700608⟩ : DyadicInterval 40),(⟨-199983582144,-199983582080⟩ : DyadicInterval 40),(⟨746848279008,746848298337⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169254175488,169254175552⟩ : DyadicInterval 40),(⟨-200133951872,-200133951808⟩ : DyadicInterval 40),(⟨746827229550,746827248880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30879776384,-30836881536⟩ : DyadicInterval 40),(⟨777541824384,777563291072⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169215322432,169313014784⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200216289600,-200079587904⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2766_ok : ecellOkT e2766 = true := by decide +kernel
theorem e2766_pos {a z : ℝ} (ha1 : ((681471/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1363791/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2766 e2766_ok ha1 ha2 hz1 hz2 hz

-- box ['1363791/8192000', '8529/51200', '7993/8000', '3997/4000']  interval_lower 296729631/1099511627776
noncomputable def e2767 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282556557262,0,true,169313014720,169313014784⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916466698290,0,false,-200216289600,-200216289536⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282670508114,0,true,169410698304,169410698368⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916352747438,0,false,-200353008256,-200353008192⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282396392948,0,true,169175700288,169175700352⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916626862604,0,false,-200024152640,-200024152576⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282533138954,0,true,169292938432,169292938496⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916490116598,0,false,-200188194368,-200188194304⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581675074,0,true,70045056,70045120⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441580478,0,false,-70049536,-70049472⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593403365,0,true,81772544,81772608⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429852187,0,false,-81778688,-81778624⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621693,0,false,-6144,-6080⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623314,0,false,-4480,-4416⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282476471033,0,true,169244356160,169244356224⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916546784519,0,false,-200120212032,-200120211968⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282601832527,0,true,169351827648,169351827712⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916421423025,0,false,-200270609024,-200270608960⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069023525395,0,false,-30918781312,-30918781248⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069065261388,0,false,-30875855872,-30875855808⟩
    { al := (1363791/8192000), au := (8529/51200), zl := (7993/8000), zu := (3997/4000),
      A := ⟨183044929486,183158880338⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169313014720,169313014784⟩ : DyadicInterval 40),(⟨-200216289600,-200216289536⟩ : DyadicInterval 40),(⟨746815698514,746815717844⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169410698304,169410698368⟩ : DyadicInterval 40),(⟨-200353008256,-200353008192⟩ : DyadicInterval 40),(⟨746796543867,746796563196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169175700288,169175700352⟩ : DyadicInterval 40),(⟨-200024152640,-200024152576⟩ : DyadicInterval 40),(⟨746842600931,746842620261⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169292938432,169292938496⟩ : DyadicInterval 40),(⟨-200188194368,-200188194304⟩ : DyadicInterval 40),(⟨746819633558,746819652887⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨70047298,81775589⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70045056,70045120⟩ : DyadicInterval 40),(⟨-70049536,-70049472⟩ : DyadicInterval 40),(⟨762123381329,762123400658⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81772544,81772608⟩ : DyadicInterval 40),(⟨-81778688,-81778624⟩ : DyadicInterval 40),(⟨762123380541,762123399871⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6144,-4416⟩ : DyadicInterval 40),(⟨762123385824,762123405952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182964843257,183090204751⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169244356160,169244356224⟩ : DyadicInterval 40),(⟨-200120212032,-200120211968⟩ : DyadicInterval 40),(⟨746829153402,746829172731⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169351827648,169351827712⟩ : DyadicInterval 40),(⟨-200270609024,-200270608960⟩ : DyadicInterval 40),(⟨746808089415,746808108744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30918781312,-30875855808⟩ : DyadicInterval 40),(⟨777561311520,777582793536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169313014720,169410698368⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200353008256,-200216289536⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2767_ok : ecellOkT e2767 = true := by decide +kernel
theorem e2767_pos {a z : ℝ} (ha1 : ((1363791/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((8529/51200 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2767 e2767_ok ha1 ha2 hz1 hz2 hz

-- box ['340311/2048000', '1362093/8192000', '3997/4000', '1599/1600']  interval_lower 73102041/274877906944
noncomputable def e2768 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282214704709,0,true,169019911872,169019911936⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916808550843,0,false,-199806235648,-199806235584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282328655561,0,true,169117621504,169117621568⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916694599991,0,false,-199942903360,-199942903296⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282077677401,0,true,168902403328,168902403392⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916945578151,0,false,-199641913600,-199641913536⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282214394919,0,true,169019646208,169019646272⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916808860633,0,false,-199805864128,-199805864064⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569887142,0,true,58257792,58257856⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453368410,0,false,-58260928,-58260864⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581585154,0,true,69955136,69955200⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441670398,0,false,-69959616,-69959552⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623324,0,false,-4480,-4416⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624690,0,false,-3136,-3072⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282146186800,0,true,168961155520,168961155584⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916877068752,0,false,-199724066496,-199724066432⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282271534072,0,true,169068642560,169068642624⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916751721480,0,false,-199874392192,-199874392128⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069133428486,0,false,-30805749632,-30805749568⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069175084436,0,false,-30762910912,-30762910848⟩
    { al := (340311/2048000), au := (1362093/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨182703076933,182817027785⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169019911872,169019911936⟩ : DyadicInterval 40),(⟨-199806235648,-199806235584⟩ : DyadicInterval 40),(⟨746873089607,746873108937⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169117621504,169117621568⟩ : DyadicInterval 40),(⟨-199942903360,-199942903296⟩ : DyadicInterval 40),(⟨746853971409,746853990739⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168902403328,168902403392⟩ : DyadicInterval 40),(⟨-199641913600,-199641913536⟩ : DyadicInterval 40),(⟨746896063425,746896082755⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169019646208,169019646272⟩ : DyadicInterval 40),(⟨-199805864128,-199805864064⟩ : DyadicInterval 40),(⟨746873141578,746873160907⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨58259366,69957378⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58257792,58257856⟩ : DyadicInterval 40),(⟨-58260928,-58260864⟩ : DyadicInterval 40),(⟨762123382032,762123401362⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69955136,69955200⟩ : DyadicInterval 40),(⟨-69959616,-69959552⟩ : DyadicInterval 40),(⟨762123381340,762123400670⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4480,-3072⟩ : DyadicInterval 40),(⟨762123385152,762123405120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182634559024,182759906296⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168961155520,168961155584⟩ : DyadicInterval 40),(⟨-199724066496,-199724066432⟩ : DyadicInterval 40),(⟨746884579444,746884598773⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169068642560,169068642624⟩ : DyadicInterval 40),(⟨-199874392192,-199874392128⟩ : DyadicInterval 40),(⟨746863556511,746863575841⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30805749632,-30762910848⟩ : DyadicInterval 40),(⟨777504839040,777526277696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169019911872,169117621568⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199942903360,-199806235584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2768_ok : ecellOkT e2768 = true := by decide +kernel
theorem e2768_pos {a z : ℝ} (ha1 : ((340311/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1362093/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2768 e2768_ok ha1 ha2 hz1 hz2 hz

-- box ['1362093/8192000', '681471/4096000', '3997/4000', '1599/1600']  interval_lower 146890047/549755813888
noncomputable def e2769 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282328655560,0,true,169117621504,169117621568⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916694599992,0,false,-199942903296,-199942903232⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282442606412,0,true,169215322432,169215322496⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916580649140,0,false,-200079587968,-200079587904⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282191542789,0,true,169000050112,169000050176⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916831712763,0,false,-199778458368,-199778458304⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282328274551,0,true,169117294848,169117294912⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916694981001,0,false,-199942446336,-199942446272⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569924969,0,true,58295616,58295680⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453330583,0,false,-58298752,-58298688⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581630552,0,true,70000512,70000576⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441625000,0,false,-70005056,-70004992⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623319,0,false,-4480,-4416⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624686,0,false,-3136,-3072⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282260094917,0,true,169058833728,169058833792⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916763160635,0,false,-199860672640,-199860672576⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282385449318,0,true,169166317312,169166317376⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916637806234,0,false,-200011025600,-200011025536⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069095546890,0,false,-30844708288,-30844708224⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069137231182,0,false,-30801838912,-30801838848⟩
    { al := (1362093/8192000), au := (681471/4096000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨182817027784,182930978636⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169117621504,169117621568⟩ : DyadicInterval 40),(⟨-199942903296,-199942903232⟩ : DyadicInterval 40),(⟨746853971383,746853990713⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169215322432,169215322496⟩ : DyadicInterval 40),(⟨-200079587968,-200079587904⟩ : DyadicInterval 40),(⟨746834841040,746834860370⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169000050112,169000050176⟩ : DyadicInterval 40),(⟨-199778458368,-199778458304⟩ : DyadicInterval 40),(⟨746876974155,746876993484⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169117294848,169117294912⟩ : DyadicInterval 40),(⟨-199942446336,-199942446272⟩ : DyadicInterval 40),(⟨746854035322,746854054651⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨58297193,70002776⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58295616,58295680⟩ : DyadicInterval 40),(⟨-58298752,-58298688⟩ : DyadicInterval 40),(⟨762123382028,762123401358⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70000512,70000576⟩ : DyadicInterval 40),(⟨-70005056,-70004992⟩ : DyadicInterval 40),(⟨762123381366,762123400696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4480,-3072⟩ : DyadicInterval 40),(⟨762123385152,762123405120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182748467141,182873821542⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169058833728,169058833792⟩ : DyadicInterval 40),(⟨-199860672640,-199860672576⟩ : DyadicInterval 40),(⟨746865475677,746865495006⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169166317312,169166317376⟩ : DyadicInterval 40),(⟨-200011025600,-200011025536⟩ : DyadicInterval 40),(⟨746844438219,746844457548⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30844708288,-30801838848⟩ : DyadicInterval 40),(⟨777524303040,777545757024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169117621504,169215322496⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200079587968,-199942903232⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2769_ok : ecellOkT e2769 = true := by decide +kernel
theorem e2769_pos {a z : ℝ} (ha1 : ((1362093/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((681471/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2769 e2769_ok ha1 ha2 hz1 hz2 hz

-- box ['340311/2048000', '1362093/8192000', '1599/1600', '1999/2000']  interval_lower 292212481/1099511627776
noncomputable def e2770 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282214704709,0,true,169019911872,169019911936⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916808550843,0,false,-199806235648,-199806235584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282328655561,0,true,169117621504,169117621568⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916694599991,0,false,-199942903360,-199942903296⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282100515285,0,true,168921988992,168921989056⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916922740267,0,false,-199669298944,-199669298880⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282237247048,0,true,169039241984,169039242048⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916786008504,0,false,-199833270592,-199833270528⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558235337,0,true,46606528,46606592⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465020215,0,false,-46608576,-46608512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569925785,0,true,58296448,58296512⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453329767,0,false,-58299584,-58299520⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624684,0,false,-3136,-3072⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625801,0,false,-1984,-1920⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282157605585,0,true,168970947712,168970947776⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916865649967,0,false,-199737759872,-199737759808⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282282960010,0,true,169078439936,169078440000⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916740295542,0,false,-199888096064,-199888096000⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069129629948,0,false,-30809656128,-30809656064⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069171290879,0,false,-30766812096,-30766812032⟩
    { al := (340311/2048000), au := (1362093/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨182703076933,182817027785⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169019911872,169019911936⟩ : DyadicInterval 40),(⟨-199806235648,-199806235584⟩ : DyadicInterval 40),(⟨746873089607,746873108937⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169117621504,169117621568⟩ : DyadicInterval 40),(⟨-199942903360,-199942903296⟩ : DyadicInterval 40),(⟨746853971409,746853990739⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168921988992,168921989056⟩ : DyadicInterval 40),(⟨-199669298944,-199669298880⟩ : DyadicInterval 40),(⟨746892235672,746892255002⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169039241984,169039242048⟩ : DyadicInterval 40),(⟨-199833270592,-199833270528⟩ : DyadicInterval 40),(⟨746869308503,746869327833⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨46607561,58298009⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46606528,46606592⟩ : DyadicInterval 40),(⟨-46608576,-46608512⟩ : DyadicInterval 40),(⟨762123382600,762123401929⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58296448,58296512⟩ : DyadicInterval 40),(⟨-58299584,-58299520⟩ : DyadicInterval 40),(⟨762123382028,762123401358⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3136,-1920⟩ : DyadicInterval 40),(⟨762123384576,762123404448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182645977809,182771332234⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168970947712,168970947776⟩ : DyadicInterval 40),(⟨-199737759872,-199737759808⟩ : DyadicInterval 40),(⟨746882664919,746882684248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169078439936,169078440000⟩ : DyadicInterval 40),(⟨-199888096064,-199888096000⟩ : DyadicInterval 40),(⟨746861639461,746861658791⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30809656128,-30766812032⟩ : DyadicInterval 40),(⟨777506789632,777528230944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169019911872,169117621568⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199942903360,-199806235584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2770_ok : ecellOkT e2770 = true := by decide +kernel
theorem e2770_pos {a z : ℝ} (ha1 : ((340311/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1362093/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2770 e2770_ok ha1 ha2 hz1 hz2 hz

-- box ['1362093/8192000', '681471/4096000', '1599/1600', '1999/2000']  interval_lower 73395937/274877906944
noncomputable def e2771 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282328655560,0,true,169117621504,169117621568⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916694599992,0,false,-199942903296,-199942903232⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282442606412,0,true,169215322432,169215322496⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916580649140,0,false,-200079587968,-200079587904⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282214394917,0,true,169019646208,169019646272⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916808860635,0,false,-199805864128,-199805864064⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282351140923,0,true,169136901056,169136901120⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916672114629,0,false,-199969873280,-199969873216⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558265598,0,true,46636800,46636864⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464989954,0,false,-46638848,-46638784⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569963614,0,true,58334272,58334336⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453291938,0,false,-58337408,-58337344⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624680,0,false,-3136,-3072⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625798,0,false,-1984,-1920⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282271520824,0,true,169068631168,169068631232⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916751734728,0,false,-199874376320,-199874376256⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282396882374,0,true,169176119936,169176120000⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916626373178,0,false,-200024739712,-200024739648⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069091743616,0,false,-30848619776,-30848619712⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069133432891,0,false,-30805745088,-30805745024⟩
    { al := (1362093/8192000), au := (681471/4096000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨182817027784,182930978636⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169117621504,169117621568⟩ : DyadicInterval 40),(⟨-199942903296,-199942903232⟩ : DyadicInterval 40),(⟨746853971383,746853990713⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169215322432,169215322496⟩ : DyadicInterval 40),(⟨-200079587968,-200079587904⟩ : DyadicInterval 40),(⟨746834841040,746834860370⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169019646208,169019646272⟩ : DyadicInterval 40),(⟨-199805864128,-199805864064⟩ : DyadicInterval 40),(⟨746873141578,746873160907⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169136901056,169136901120⟩ : DyadicInterval 40),(⟨-199969873280,-199969873216⟩ : DyadicInterval 40),(⟨746850197442,746850216772⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨46637822,58335838⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46636800,46636864⟩ : DyadicInterval 40),(⟨-46638848,-46638784⟩ : DyadicInterval 40),(⟨762123382597,762123401926⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58334272,58334336⟩ : DyadicInterval 40),(⟨-58337408,-58337344⟩ : DyadicInterval 40),(⟨762123382024,762123401354⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3136,-1920⟩ : DyadicInterval 40),(⟨762123384576,762123404448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182759893048,182885254598⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169068631168,169068631232⟩ : DyadicInterval 40),(⟨-199874376320,-199874376256⟩ : DyadicInterval 40),(⟨746863558760,746863578089⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169176119936,169176120000⟩ : DyadicInterval 40),(⟨-200024739712,-200024739648⟩ : DyadicInterval 40),(⟨746842518747,746842538076⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30848619776,-30805745024⟩ : DyadicInterval 40),(⟨777526256128,777547712768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169117621504,169215322496⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200079587968,-199942903232⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2771_ok : ecellOkT e2771 = true := by decide +kernel
theorem e2771_pos {a z : ℝ} (ha1 : ((1362093/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((681471/4096000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2771 e2771_ok ha1 ha2 hz1 hz2 hz

-- box ['681471/4096000', '1363791/8192000', '3997/4000', '1599/1600']  interval_lower 147577469/549755813888
noncomputable def e2772 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282442606411,0,true,169215322432,169215322496⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916580649141,0,false,-200079587968,-200079587904⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282556557263,0,true,169313014720,169313014784⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916466698289,0,false,-200216289600,-200216289536⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282305408176,0,true,169097688256,169097688320⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916717847376,0,false,-199915020032,-199915019968⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282442154183,0,true,169214934720,169214934784⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916581101369,0,false,-200079045504,-200079045440⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569962799,0,true,58333440,58333504⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453292753,0,false,-58336576,-58336512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581675951,0,true,70045888,70045952⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441579601,0,false,-70050432,-70050368⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623313,0,false,-4480,-4416⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624682,0,false,-3136,-3072⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282374003036,0,true,169156503296,169156503360⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916649252516,0,false,-199997295808,-199997295744⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282499364558,0,true,169263983360,169263983424⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916523890994,0,false,-200147676032,-200147675968⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069057641690,0,false,-30883692608,-30883692544⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069099354326,0,false,-30840792512,-30840792448⟩
    { al := (681471/4096000), au := (1363791/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨182930978635,183044929487⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169215322432,169215322496⟩ : DyadicInterval 40),(⟨-200079587968,-200079587904⟩ : DyadicInterval 40),(⟨746834841041,746834860370⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169313014720,169313014784⟩ : DyadicInterval 40),(⟨-200216289600,-200216289536⟩ : DyadicInterval 40),(⟨746815698514,746815717843⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169097688256,169097688320⟩ : DyadicInterval 40),(⟨-199915020032,-199915019968⟩ : DyadicInterval 40),(⟨746857872714,746857892044⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169214934720,169214934784⟩ : DyadicInterval 40),(⟨-200079045504,-200079045440⟩ : DyadicInterval 40),(⟨746834916988,746834936318⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨58335023,70048175⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58333440,58333504⟩ : DyadicInterval 40),(⟨-58336576,-58336512⟩ : DyadicInterval 40),(⟨762123382024,762123401354⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70045888,70045952⟩ : DyadicInterval 40),(⟨-70050432,-70050368⟩ : DyadicInterval 40),(⟨762123381361,762123400690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4480,-3072⟩ : DyadicInterval 40),(⟨762123385152,762123405120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182862375260,182987736782⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169156503296,169156503360⟩ : DyadicInterval 40),(⟨-199997295808,-199997295744⟩ : DyadicInterval 40),(⟨746846359773,746846379103⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169263983360,169263983424⟩ : DyadicInterval 40),(⟨-200147676032,-200147675968⟩ : DyadicInterval 40),(⟨746825307823,746825327153⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30883692608,-30840792448⟩ : DyadicInterval 40),(⟨777543779840,777565249184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169215322432,169313014784⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200216289600,-200079587904⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2772_ok : ecellOkT e2772 = true := by decide +kernel
theorem e2772_pos {a z : ℝ} (ha1 : ((681471/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1363791/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2772 e2772_ok ha1 ha2 hz1 hz2 hz

-- box ['1363791/8192000', '8529/51200', '3997/4000', '1599/1600']  interval_lower 296532819/1099511627776
noncomputable def e2773 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282556557262,0,true,169313014720,169313014784⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916466698290,0,false,-200216289600,-200216289536⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282670508114,0,true,169410698304,169410698368⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916352747438,0,false,-200353008256,-200353008192⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282419273564,0,true,169195317696,169195317760⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916603981988,0,false,-200051598720,-200051598656⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282556033814,0,true,169312565952,169312566016⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916467221738,0,false,-200215661632,-200215661568⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570000632,0,true,58371264,58371328⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453254920,0,false,-58374464,-58374400⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581721355,0,true,70091328,70091392⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441534197,0,false,-70095872,-70095808⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623307,0,false,-4480,-4416⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624677,0,false,-3136,-3072⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282487911155,0,true,169254164096,169254164160⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916535344397,0,false,-200133936000,-200133935936⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282613279799,0,true,169361640832,169361640896⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916409975753,0,false,-200284343360,-200284343296⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069019712887,0,false,-30922702528,-30922702464⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069061453869,0,false,-30879771840,-30879771776⟩
    { al := (1363791/8192000), au := (8529/51200), zl := (3997/4000), zu := (1599/1600),
      A := ⟨183044929486,183158880338⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169313014720,169313014784⟩ : DyadicInterval 40),(⟨-200216289600,-200216289536⟩ : DyadicInterval 40),(⟨746815698514,746815717844⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169410698304,169410698368⟩ : DyadicInterval 40),(⟨-200353008256,-200353008192⟩ : DyadicInterval 40),(⟨746796543867,746796563196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169195317696,169195317760⟩ : DyadicInterval 40),(⟨-200051598720,-200051598656⟩ : DyadicInterval 40),(⟨746838759191,746838778520⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169312565952,169312566016⟩ : DyadicInterval 40),(⟨-200215661632,-200215661568⟩ : DyadicInterval 40),(⟨746815786502,746815805831⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨58372856,70093579⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58371264,58371328⟩ : DyadicInterval 40),(⟨-58374464,-58374400⟩ : DyadicInterval 40),(⟨762123382052,762123401382⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70091328,70091392⟩ : DyadicInterval 40),(⟨-70095872,-70095808⟩ : DyadicInterval 40),(⟨762123381355,762123400684⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4480,-3072⟩ : DyadicInterval 40),(⟨762123385152,762123405120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182976283379,183101652023⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169254164096,169254164160⟩ : DyadicInterval 40),(⟨-200133936000,-200133935936⟩ : DyadicInterval 40),(⟨746827231806,746827251136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169361640832,169361640896⟩ : DyadicInterval 40),(⟨-200284343360,-200284343296⟩ : DyadicInterval 40),(⟨746806165194,746806184524⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30922702528,-30879771776⟩ : DyadicInterval 40),(⟨777563269504,777584754144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169313014720,169410698368⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200353008256,-200216289536⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2773_ok : ecellOkT e2773 = true := by decide +kernel
theorem e2773_pos {a z : ℝ} (ha1 : ((1363791/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((8529/51200 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2773 e2773_ok ha1 ha2 hz1 hz2 hz

-- box ['681471/4096000', '1363791/8192000', '1599/1600', '1999/2000']  interval_lower 147479039/549755813888
noncomputable def e2774 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282442606411,0,true,169215322432,169215322496⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916580649141,0,false,-200079587968,-200079587904⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282556557263,0,true,169313014720,169313014784⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916466698289,0,false,-200216289600,-200216289536⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282328274549,0,true,169117294784,169117294848⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916694981003,0,false,-199942446336,-199942446272⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282465034799,0,true,169234551424,169234551488⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916558220753,0,false,-200106492928,-200106492864⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558295862,0,true,46667072,46667136⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464959690,0,false,-46669120,-46669056⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570001449,0,true,58372096,58372160⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453254103,0,false,-58375232,-58375168⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624676,0,false,-3136,-3072⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625796,0,false,-1984,-1920⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282385436060,0,true,169166305920,169166305984⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916637819492,0,false,-200011009728,-200011009664⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282510804739,0,true,169273791232,169273791296⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916512450813,0,false,-200161400320,-200161400256⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069053833676,0,false,-30887609088,-30887609024⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069095551301,0,false,-30844703744,-30844703680⟩
    { al := (681471/4096000), au := (1363791/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨182930978635,183044929487⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169215322432,169215322496⟩ : DyadicInterval 40),(⟨-200079587968,-200079587904⟩ : DyadicInterval 40),(⟨746834841041,746834860370⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169313014720,169313014784⟩ : DyadicInterval 40),(⟨-200216289600,-200216289536⟩ : DyadicInterval 40),(⟨746815698514,746815717843⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169117294784,169117294848⟩ : DyadicInterval 40),(⟨-199942446336,-199942446272⟩ : DyadicInterval 40),(⟨746854035359,746854054689⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169234551424,169234551488⟩ : DyadicInterval 40),(⟨-200106492928,-200106492864⟩ : DyadicInterval 40),(⟨746831074260,746831093590⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨46668086,58373673⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46667072,46667136⟩ : DyadicInterval 40),(⟨-46669120,-46669056⟩ : DyadicInterval 40),(⟨762123382595,762123401924⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58372096,58372160⟩ : DyadicInterval 40),(⟨-58375232,-58375168⟩ : DyadicInterval 40),(⟨762123382020,762123401349⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3136,-1920⟩ : DyadicInterval 40),(⟨762123384576,762123404448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182873808284,182999176963⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169166305920,169166305984⟩ : DyadicInterval 40),(⟨-200011009728,-200011009664⟩ : DyadicInterval 40),(⟨746844440471,746844459801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169273791232,169273791296⟩ : DyadicInterval 40),(⟨-200161400320,-200161400256⟩ : DyadicInterval 40),(⟨746823385898,746823405228⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30887609088,-30844703680⟩ : DyadicInterval 40),(⟨777545735456,777567207424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169215322432,169313014784⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200216289600,-200079587904⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2774_ok : ecellOkT e2774 = true := by decide +kernel
theorem e2774_pos {a z : ℝ} (ha1 : ((681471/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1363791/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2774 e2774_ok ha1 ha2 hz1 hz2 hz

-- box ['1363791/8192000', '8529/51200', '1599/1600', '1999/2000']  interval_lower 296335901/1099511627776
noncomputable def e2775 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282556557262,0,true,169313014720,169313014784⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916466698290,0,false,-200216289600,-200216289536⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282670508114,0,true,169410698304,169410698368⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916352747438,0,false,-200353008256,-200353008192⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282442154180,0,true,169214934720,169214934784⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916581101372,0,false,-200079045504,-200079045440⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282578928674,0,true,169332193152,169332193216⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916444326878,0,false,-200243129536,-200243129472⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558326129,0,true,46697344,46697408⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464929423,0,false,-46699392,-46699328⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570039285,0,true,58409920,58409984⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453216267,0,false,-58413120,-58413056⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624672,0,false,-3136,-3072⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625793,0,false,-1984,-1920⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282499351302,0,true,169263972032,169263972096⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916523904250,0,false,-200147660096,-200147660032⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282624727103,0,true,169371453888,169371453952⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916398528449,0,false,-200298077952,-200298077888⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069015900129,0,false,-30926624064,-30926624000⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069057646104,0,false,-30883688064,-30883688000⟩
    { al := (1363791/8192000), au := (8529/51200), zl := (1599/1600), zu := (1999/2000),
      A := ⟨183044929486,183158880338⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169313014720,169313014784⟩ : DyadicInterval 40),(⟨-200216289600,-200216289536⟩ : DyadicInterval 40),(⟨746815698514,746815717844⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169410698304,169410698368⟩ : DyadicInterval 40),(⟨-200353008256,-200353008192⟩ : DyadicInterval 40),(⟨746796543867,746796563196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169214934720,169214934784⟩ : DyadicInterval 40),(⟨-200079045504,-200079045440⟩ : DyadicInterval 40),(⟨746834916989,746834936318⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169332193152,169332193216⟩ : DyadicInterval 40),(⟨-200243129536,-200243129472⟩ : DyadicInterval 40),(⟨746811938919,746811958248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨46698353,58411509⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46697344,46697408⟩ : DyadicInterval 40),(⟨-46699392,-46699328⟩ : DyadicInterval 40),(⟨762123382592,762123401921⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58409920,58409984⟩ : DyadicInterval 40),(⟨-58413120,-58413056⟩ : DyadicInterval 40),(⟨762123382048,762123401377⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3136,-1920⟩ : DyadicInterval 40),(⟨762123384576,762123404448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182987723526,183113099327⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169263972032,169263972096⟩ : DyadicInterval 40),(⟨-200147660096,-200147660032⟩ : DyadicInterval 40),(⟨746825310015,746825329344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169371453888,169371453952⟩ : DyadicInterval 40),(⟨-200298077952,-200298077888⟩ : DyadicInterval 40),(⟨746804240904,746804260234⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30926624064,-30883688000⟩ : DyadicInterval 40),(⟨777565227616,777586714912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169313014720,169410698368⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200353008256,-200216289536⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2775_ok : ecellOkT e2775 = true := by decide +kernel
theorem e2775_pos {a z : ℝ} (ha1 : ((1363791/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((8529/51200 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2775 e2775_ok ha1 ha2 hz1 hz2 hz

-- box ['169731/1024000', '1358697/8192000', '1999/2000', '7997/8000']  interval_lower 286565091/1099511627776
noncomputable def e2776 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281758901305,0,true,168628986496,168628986560⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917264354247,0,false,-199259734848,-199259734784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281872852157,0,true,168726730880,168726730944⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917150403395,0,false,-199396334592,-199396334528⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281667777668,0,true,168550816576,168550816640⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917355477884,0,false,-199150511680,-199150511616⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281804466698,0,true,168668072512,168668072576⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917218788854,0,false,-199314354816,-199314354752⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546492701,0,true,34864320,34864384⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476762851,0,false,-34865536,-34865472⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558145318,0,true,46516544,46516608⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465110234,0,false,-46518528,-46518464⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625807,0,false,-1984,-1920⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626671,0,false,-1152,-1088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281713334955,0,true,168589898368,168589898432⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917309920597,0,false,-199205116480,-199205116416⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281838668033,0,true,168697409472,168697409536⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917184587519,0,false,-199355354240,-199355354176⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069277159336,0,false,-30657944768,-30657944704⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069318711885,0,false,-30615218112,-30615218048⟩
    { al := (169731/1024000), au := (1358697/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨182247273529,182361224381⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168628986496,168628986560⟩ : DyadicInterval 40),(⟨-199259734848,-199259734784⟩ : DyadicInterval 40),(⟨746949441046,746949460376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168726730880,168726730944⟩ : DyadicInterval 40),(⟨-199396334592,-199396334528⟩ : DyadicInterval 40),(⟨746930371400,746930390730⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168550816576,168550816640⟩ : DyadicInterval 40),(⟨-199150511680,-199150511616⟩ : DyadicInterval 40),(⟨746964681792,746964701122⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168668072512,168668072576⟩ : DyadicInterval 40),(⟨-199314354816,-199314354752⟩ : DyadicInterval 40),(⟨746941817133,746941836462⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34864925,46517542⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34864320,34864384⟩ : DyadicInterval 40),(⟨-34865536,-34865472⟩ : DyadicInterval 40),(⟨762123383054,762123402383⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46516544,46516608⟩ : DyadicInterval 40),(⟨-46518528,-46518464⟩ : DyadicInterval 40),(⟨762123382575,762123401905⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1984,-1088⟩ : DyadicInterval 40),(⟨762123384160,762123403872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182201707179,182327040257⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168589898368,168589898432⟩ : DyadicInterval 40),(⟨-199205116480,-199205116416⟩ : DyadicInterval 40),(⟨746957063135,746957082465⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168697409472,168697409536⟩ : DyadicInterval 40),(⟨-199355354240,-199355354176⟩ : DyadicInterval 40),(⟨746936093364,746936112694⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30657944768,-30615218048⟩ : DyadicInterval 40),(⟨777430992640,777452375264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168628986496,168726730944⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199396334592,-199259734784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2776_ok : ecellOkT e2776 = true := by decide +kernel
theorem e2776_pos {a z : ℝ} (ha1 : ((169731/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1358697/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2776 e2776_ok ha1 ha2 hz1 hz2 hz

-- box ['1358697/8192000', '679773/4096000', '1999/2000', '7997/8000']  interval_lower 35990433/137438953472
noncomputable def e2777 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281872852156,0,true,168726730880,168726730944⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917150403396,0,false,-199396334592,-199396334528⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281986803008,0,true,168824466560,168824466624⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917036452544,0,false,-199532951296,-199532951232⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281781671543,0,true,168648518976,168648519040⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917241584009,0,false,-199287029568,-199287029504⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281918374818,0,true,168765776768,168765776832⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917104880734,0,false,-199450910080,-199450910016⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546515392,0,true,34887040,34887104⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476740160,0,false,-34888192,-34888128⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558175572,0,true,46546752,46546816⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465079980,0,false,-46548800,-46548736⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625805,0,false,-1984,-1920⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626670,0,false,-1152,-1088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281827257312,0,true,168687621760,168687621824⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917195998240,0,false,-199341675264,-199341675200⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281952597520,0,true,168795129408,168795129472⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917070658032,0,false,-199491940288,-199491940224⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069239362708,0,false,-30696810816,-30696810752⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069280943595,0,false,-30654053504,-30654053440⟩
    { al := (1358697/8192000), au := (679773/4096000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨182361224380,182475175232⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168726730880,168726730944⟩ : DyadicInterval 40),(⟨-199396334592,-199396334528⟩ : DyadicInterval 40),(⟨746930371400,746930390730⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168824466560,168824466624⟩ : DyadicInterval 40),(⟨-199532951296,-199532951232⟩ : DyadicInterval 40),(⟨746911289614,746911308944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168648518976,168648519040⟩ : DyadicInterval 40),(⟨-199287029568,-199287029504⟩ : DyadicInterval 40),(⟨746945631430,746945650759⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168765776768,168765776832⟩ : DyadicInterval 40),(⟨-199450910080,-199450910016⟩ : DyadicInterval 40),(⟨746922749773,746922769102⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34887616,46547796⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34887040,34887104⟩ : DyadicInterval 40),(⟨-34888192,-34888128⟩ : DyadicInterval 40),(⟨762123383020,762123402350⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46546752,46546816⟩ : DyadicInterval 40),(⟨-46548800,-46548736⟩ : DyadicInterval 40),(⟨762123382605,762123401934⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1984,-1088⟩ : DyadicInterval 40),(⟨762123384160,762123403872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182315629536,182440969744⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168687621760,168687621824⟩ : DyadicInterval 40),(⟨-199341675264,-199341675200⟩ : DyadicInterval 40),(⟨746938003122,746938022451⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168795129408,168795129472⟩ : DyadicInterval 40),(⟨-199491940288,-199491940224⟩ : DyadicInterval 40),(⟨746917018836,746917038165⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30696810816,-30654053440⟩ : DyadicInterval 40),(⟨777450410336,777471808288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168726730880,168824466624⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199532951296,-199396334528⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2777_ok : ecellOkT e2777 = true := by decide +kernel
theorem e2777_pos {a z : ℝ} (ha1 : ((1358697/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((679773/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2777 e2777_ok ha1 ha2 hz1 hz2 hz

-- box ['169731/1024000', '1358697/8192000', '7997/8000', '3999/4000']  interval_lower 143185437/549755813888
noncomputable def e2778 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281758901305,0,true,168628986496,168628986560⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917264354247,0,false,-199259734848,-199259734784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281872852157,0,true,168726730880,168726730944⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917150403395,0,false,-199396334592,-199396334528⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281690558577,0,true,168570359552,168570359616⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917332696975,0,false,-199177816512,-199177816448⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281827261852,0,true,168687625664,168687625728⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917195993700,0,false,-199341680768,-199341680704⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534871034,0,true,23243008,23243072⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488384518,0,false,-23243520,-23243456⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546516085,0,true,34887744,34887808⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476739467,0,false,-34888896,-34888832⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626668,0,false,-1152,-1088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627285,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281724725304,0,true,168599669440,168599669504⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917298530248,0,false,-199218769344,-199218769280⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281850065537,0,true,168707185792,168707185856⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917173190015,0,false,-199369017536,-199369017472⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069273379225,0,false,-30661831744,-30661831680⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069314936744,0,false,-30619099840,-30619099776⟩
    { al := (169731/1024000), au := (1358697/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨182247273529,182361224381⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168628986496,168628986560⟩ : DyadicInterval 40),(⟨-199259734848,-199259734784⟩ : DyadicInterval 40),(⟨746949441046,746949460376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168726730880,168726730944⟩ : DyadicInterval 40),(⟨-199396334592,-199396334528⟩ : DyadicInterval 40),(⟨746930371400,746930390730⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168570359552,168570359616⟩ : DyadicInterval 40),(⟨-199177816512,-199177816448⟩ : DyadicInterval 40),(⟨746960872372,746960891702⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168687625664,168687625728⟩ : DyadicInterval 40),(⟨-199341680768,-199341680704⟩ : DyadicInterval 40),(⟨746938002382,746938021711⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23243258,34888309⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23243008,23243072⟩ : DyadicInterval 40),(⟨-23243520,-23243456⟩ : DyadicInterval 40),(⟨762123383316,762123402645⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34887744,34887808⟩ : DyadicInterval 40),(⟨-34888896,-34888832⟩ : DyadicInterval 40),(⟨762123383020,762123402349⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1152,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182213097528,182338437761⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168599669440,168599669504⟩ : DyadicInterval 40),(⟨-199218769344,-199218769280⟩ : DyadicInterval 40),(⟨746955158023,746955177353⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168707185792,168707185856⟩ : DyadicInterval 40),(⟨-199369017536,-199369017472⟩ : DyadicInterval 40),(⟨746934185676,746934205006⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30661831744,-30619099776⟩ : DyadicInterval 40),(⟨777432933504,777454318752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168628986496,168726730944⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199396334592,-199259734784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2778_ok : ecellOkT e2778 = true := by decide +kernel
theorem e2778_pos {a z : ℝ} (ha1 : ((169731/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1358697/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2778 e2778_ok ha1 ha2 hz1 hz2 hz

-- box ['1358697/8192000', '679773/4096000', '7997/8000', '3999/4000']  interval_lower 287728899/1099511627776
noncomputable def e2779 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281872852156,0,true,168726730880,168726730944⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917150403396,0,false,-199396334592,-199396334528⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281986803008,0,true,168824466560,168824466624⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917036452544,0,false,-199532951296,-199532951232⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281804466696,0,true,168668072512,168668072576⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917218788856,0,false,-199314354816,-199314354752⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281941184215,0,true,168785340352,168785340416⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917082071337,0,false,-199478256512,-199478256448⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534886160,0,true,23258112,23258176⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488369392,0,false,-23258688,-23258624⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546538778,0,true,34910400,34910464⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476716774,0,false,-34911616,-34911552⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626667,0,false,-1152,-1088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627285,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281838654792,0,true,168697398080,168697398144⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917184600760,0,false,-199355338368,-199355338304⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281964002143,0,true,168804910976,168804911040⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917059253409,0,false,-199505613824,-199505613760⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069235577872,0,false,-30700702784,-30700702720⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069277163728,0,false,-30657940224,-30657940160⟩
    { al := (1358697/8192000), au := (679773/4096000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨182361224380,182475175232⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168726730880,168726730944⟩ : DyadicInterval 40),(⟨-199396334592,-199396334528⟩ : DyadicInterval 40),(⟨746930371400,746930390730⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168824466560,168824466624⟩ : DyadicInterval 40),(⟨-199532951296,-199532951232⟩ : DyadicInterval 40),(⟨746911289614,746911308944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168668072512,168668072576⟩ : DyadicInterval 40),(⟨-199314354816,-199314354752⟩ : DyadicInterval 40),(⟨746941817133,746941836463⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168785340352,168785340416⟩ : DyadicInterval 40),(⟨-199478256512,-199478256448⟩ : DyadicInterval 40),(⟨746918930240,746918949569⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23258384,34911002⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23258112,23258176⟩ : DyadicInterval 40),(⟨-23258688,-23258624⟩ : DyadicInterval 40),(⟨762123383348,762123402677⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34910400,34910464⟩ : DyadicInterval 40),(⟨-34911616,-34911552⟩ : DyadicInterval 40),(⟨762123383051,762123402380⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1152,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182327027016,182452374367⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168697398080,168697398144⟩ : DyadicInterval 40),(⟨-199355338368,-199355338304⟩ : DyadicInterval 40),(⟨746936095601,746936114930⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168804910976,168804911040⟩ : DyadicInterval 40),(⟨-199505613824,-199505613760⟩ : DyadicInterval 40),(⟨746915108738,746915128067⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30700702784,-30657940160⟩ : DyadicInterval 40),(⟨777452353696,777473754272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168726730880,168824466624⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199532951296,-199396334528⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2779_ok : ecellOkT e2779 = true := by decide +kernel
theorem e2779_pos {a z : ℝ} (ha1 : ((1358697/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((679773/4096000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2779 e2779_ok ha1 ha2 hz1 hz2 hz

-- box ['679773/4096000', '272079/1638400', '1999/2000', '7997/8000']  interval_lower 144642345/549755813888
noncomputable def e2780 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281986803007,0,true,168824466560,168824466624⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917036452545,0,false,-199532951296,-199532951232⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282100753859,0,true,168922193600,168922193664⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916922501693,0,false,-199669585024,-199669584960⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281895565419,0,true,168746212736,168746212800⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917127690133,0,false,-199423564416,-199423564352⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282032282937,0,true,168863472320,168863472384⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916990972615,0,false,-199587482368,-199587482304⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546538083,0,true,34909696,34909760⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476717469,0,false,-34910912,-34910848⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558205831,0,true,46577024,46577088⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465049721,0,false,-46579072,-46579008⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625802,0,false,-1984,-1920⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626668,0,false,-1152,-1088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281941179672,0,true,168785336448,168785336512⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917082075880,0,false,-199478251072,-199478251008⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282066527004,0,true,168892840704,168892840768⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916956728548,0,false,-199628543232,-199628543168⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069201542470,0,false,-30735702528,-30735702464⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069243151697,0,false,-30692914560,-30692914496⟩
    { al := (679773/4096000), au := (272079/1638400), zl := (1999/2000), zu := (7997/8000),
      A := ⟨182475175231,182589126083⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168824466560,168824466624⟩ : DyadicInterval 40),(⟨-199532951296,-199532951232⟩ : DyadicInterval 40),(⟨746911289614,746911308944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168922193600,168922193664⟩ : DyadicInterval 40),(⟨-199669585024,-199669584960⟩ : DyadicInterval 40),(⟨746892195677,746892215006⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168746212736,168746212800⟩ : DyadicInterval 40),(⟨-199423564416,-199423564352⟩ : DyadicInterval 40),(⟨746926568914,746926588244⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168863472320,168863472384⟩ : DyadicInterval 40),(⟨-199587482368,-199587482304⟩ : DyadicInterval 40),(⟨746903670317,746903689647⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34910307,46578055⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34909696,34909760⟩ : DyadicInterval 40),(⟨-34910912,-34910848⟩ : DyadicInterval 40),(⟨762123383051,762123402380⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46577024,46577088⟩ : DyadicInterval 40),(⟨-46579072,-46579008⟩ : DyadicInterval 40),(⟨762123382602,762123401931⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1984,-1088⟩ : DyadicInterval 40),(⟨762123384160,762123403872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182429551896,182554899228⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168785336448,168785336512⟩ : DyadicInterval 40),(⟨-199478251072,-199478251008⟩ : DyadicInterval 40),(⟨746918931007,746918950337⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168892840704,168892840768⟩ : DyadicInterval 40),(⟨-199628543232,-199628543168⟩ : DyadicInterval 40),(⟨746897932112,746897951442⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30735702528,-30692914496⟩ : DyadicInterval 40),(⟨777469840864,777491254144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168824466560,168922193664⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199669585024,-199532951232⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2780_ok : ecellOkT e2780 = true := by decide +kernel
theorem e2780_pos {a z : ℝ} (ha1 : ((679773/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((272079/1638400 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2780 e2780_ok ha1 ha2 hz1 hz2 hz

-- box ['272079/1638400', '340311/2048000', '1999/2000', '7997/8000']  interval_lower 72662327/274877906944
noncomputable def e2781 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282100753858,0,true,168922193600,168922193664⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916922501694,0,false,-199669585024,-199669584960⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282214704710,0,true,169019911872,169019911936⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916808550842,0,false,-199806235648,-199806235584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282009459294,0,true,168843897856,168843897920⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917013796258,0,false,-199560116160,-199560116096⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282146191057,0,true,168961159168,168961159232⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916877064495,0,false,-199724071552,-199724071488⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546560777,0,true,34932416,34932480⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476694775,0,false,-34933568,-34933504⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558236091,0,true,46607296,46607360⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465019461,0,false,-46609344,-46609280⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625800,0,false,-1984,-1920⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626667,0,false,-1152,-1088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282055102038,0,true,168883042496,168883042560⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916968153514,0,false,-199614843776,-199614843712⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282180456489,0,true,168990543296,168990543360⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916842799063,0,false,-199765163200,-199765163136⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069163698622,0,false,-30774619840,-30774619776⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069205336189,0,false,-30731801216,-30731801152⟩
    { al := (272079/1638400), au := (340311/2048000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨182589126082,182703076934⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168922193600,168922193664⟩ : DyadicInterval 40),(⟨-199669585024,-199669584960⟩ : DyadicInterval 40),(⟨746892195677,746892215007⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169019911872,169019911936⟩ : DyadicInterval 40),(⟨-199806235648,-199806235584⟩ : DyadicInterval 40),(⟨746873089607,746873108937⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168843897856,168843897920⟩ : DyadicInterval 40),(⟨-199560116160,-199560116096⟩ : DyadicInterval 40),(⟨746907494220,746907513549⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168961159168,168961159232⟩ : DyadicInterval 40),(⟨-199724071552,-199724071488⟩ : DyadicInterval 40),(⟨746884578711,746884598041⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34933001,46608315⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34932416,34932480⟩ : DyadicInterval 40),(⟨-34933568,-34933504⟩ : DyadicInterval 40),(⟨762123383018,762123402347⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46607296,46607360⟩ : DyadicInterval 40),(⟨-46609344,-46609280⟩ : DyadicInterval 40),(⟨762123382600,762123401929⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1984,-1088⟩ : DyadicInterval 40),(⟨762123384160,762123403872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182543474262,182668828713⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168883042496,168883042560⟩ : DyadicInterval 40),(⟨-199614843776,-199614843712⟩ : DyadicInterval 40),(⟨746899846700,746899866029⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168990543296,168990543360⟩ : DyadicInterval 40),(⟨-199765163200,-199765163136⟩ : DyadicInterval 40),(⟨746878833282,746878852612⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30774619840,-30731801152⟩ : DyadicInterval 40),(⟨777489284192,777510712800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168922193600,169019911936⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199806235648,-199669584960⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2781_ok : ecellOkT e2781 = true := by decide +kernel
theorem e2781_pos {a z : ℝ} (ha1 : ((272079/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((340311/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2781 e2781_ok ha1 ha2 hz1 hz2 hz

-- box ['679773/4096000', '272079/1638400', '7997/8000', '3999/4000']  interval_lower 144544857/549755813888
noncomputable def e2782 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281986803007,0,true,168824466560,168824466624⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917036452545,0,false,-199532951296,-199532951232⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282100753859,0,true,168922193600,168922193664⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916922501693,0,false,-199669585024,-199669584960⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281918374816,0,true,168765776768,168765776832⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917104880736,0,false,-199450910080,-199450910016⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282055106578,0,true,168883046400,168883046464⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916968148974,0,false,-199614849216,-199614849152⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534901288,0,true,23273216,23273280⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488354264,0,false,-23273792,-23273728⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546561471,0,true,34933120,34933184⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476694081,0,false,-34934272,-34934208⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626666,0,false,-1152,-1088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627284,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281952584276,0,true,168795118080,168795118144⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917070671276,0,false,-199491924416,-199491924352⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282077938753,0,true,168902627456,168902627520⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916945316799,0,false,-199642227008,-199642226944⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069197752904,0,false,-30739599488,-30739599424⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069239367104,0,false,-30696806272,-30696806208⟩
    { al := (679773/4096000), au := (272079/1638400), zl := (7997/8000), zu := (3999/4000),
      A := ⟨182475175231,182589126083⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168824466560,168824466624⟩ : DyadicInterval 40),(⟨-199532951296,-199532951232⟩ : DyadicInterval 40),(⟨746911289614,746911308944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168922193600,168922193664⟩ : DyadicInterval 40),(⟨-199669585024,-199669584960⟩ : DyadicInterval 40),(⟨746892195677,746892215006⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168765776768,168765776832⟩ : DyadicInterval 40),(⟨-199450910080,-199450910016⟩ : DyadicInterval 40),(⟨746922749773,746922769102⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168883046400,168883046464⟩ : DyadicInterval 40),(⟨-199614849216,-199614849152⟩ : DyadicInterval 40),(⟨746899845931,746899865261⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23273512,34933695⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23273216,23273280⟩ : DyadicInterval 40),(⟨-23273792,-23273728⟩ : DyadicInterval 40),(⟨762123383347,762123402676⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34933120,34933184⟩ : DyadicInterval 40),(⟨-34934272,-34934208⟩ : DyadicInterval 40),(⟨762123383018,762123402347⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1152,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182440956500,182566310977⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168795118080,168795118144⟩ : DyadicInterval 40),(⟨-199491924416,-199491924352⟩ : DyadicInterval 40),(⟨746917021038,746917040368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168902627456,168902627520⟩ : DyadicInterval 40),(⟨-199642227008,-199642226944⟩ : DyadicInterval 40),(⟨746896019637,746896038966⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30739599488,-30696806208⟩ : DyadicInterval 40),(⟨777471786720,777493202624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168824466560,168922193664⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199669585024,-199532951232⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2782_ok : ecellOkT e2782 = true := by decide +kernel
theorem e2782_pos {a z : ℝ} (ha1 : ((679773/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((272079/1638400 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2782 e2782_ok ha1 ha2 hz1 hz2 hz

-- box ['272079/1638400', '340311/2048000', '7997/8000', '3999/4000']  interval_lower 290454105/1099511627776
noncomputable def e2783 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282100753858,0,true,168922193600,168922193664⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916922501694,0,false,-199669585024,-199669584960⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282214704710,0,true,169019911872,169019911936⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916808550842,0,false,-199806235648,-199806235584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282032282935,0,true,168863472320,168863472384⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916990972617,0,false,-199587482368,-199587482304⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282169028941,0,true,168980743744,168980743808⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916854226611,0,false,-199751458944,-199751458880⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534916416,0,true,23288384,23288448⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488339136,0,false,-23288896,-23288832⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546584166,0,true,34955776,34955840⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476671386,0,false,-34956992,-34956928⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626664,0,false,-1152,-1088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627283,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282066513758,0,true,168892829376,168892829440⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916956741794,0,false,-199628527360,-199628527296⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282191875357,0,true,169000335296,169000335360⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916831380195,0,false,-199778857216,-199778857152⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069159904326,0,false,-30778521856,-30778521792⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069201546870,0,false,-30735697984,-30735697920⟩
    { al := (272079/1638400), au := (340311/2048000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨182589126082,182703076934⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168922193600,168922193664⟩ : DyadicInterval 40),(⟨-199669585024,-199669584960⟩ : DyadicInterval 40),(⟨746892195677,746892215007⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169019911872,169019911936⟩ : DyadicInterval 40),(⟨-199806235648,-199806235584⟩ : DyadicInterval 40),(⟨746873089607,746873108937⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168863472320,168863472384⟩ : DyadicInterval 40),(⟨-199587482368,-199587482304⟩ : DyadicInterval 40),(⟨746903670317,746903689647⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168980743744,168980743808⟩ : DyadicInterval 40),(⟨-199751458944,-199751458880⟩ : DyadicInterval 40),(⟨746880749520,746880768849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23288640,34956390⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23288384,23288448⟩ : DyadicInterval 40),(⟨-23288896,-23288832⟩ : DyadicInterval 40),(⟨762123383314,762123402643⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34955776,34955840⟩ : DyadicInterval 40),(⟨-34956992,-34956928⟩ : DyadicInterval 40),(⟨762123383048,762123402377⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1152,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182554885982,182680247581⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168892829376,168892829440⟩ : DyadicInterval 40),(⟨-199628527360,-199628527296⟩ : DyadicInterval 40),(⟨746897934318,746897953648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169000335296,169000335360⟩ : DyadicInterval 40),(⟨-199778857216,-199778857152⟩ : DyadicInterval 40),(⟨746876918390,746876937720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30778521856,-30735697920⟩ : DyadicInterval 40),(⟨777491232576,777512663808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168922193600,169019911936⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199806235648,-199669584960⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2783_ok : ecellOkT e2783 = true := by decide +kernel
theorem e2783_pos {a z : ℝ} (ha1 : ((272079/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((340311/2048000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2783 e2783_ok ha1 ha2 hz1 hz2 hz

-- box ['169731/1024000', '1358697/8192000', '3999/4000', '7999/8000']  interval_lower 286177033/1099511627776
noncomputable def e2784 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281758901305,0,true,168628986496,168628986560⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917264354247,0,false,-199259734848,-199259734784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281872852157,0,true,168726730880,168726730944⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917150403395,0,false,-199396334592,-199396334528⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281713339486,0,true,168589902208,168589902272⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917309916066,0,false,-199205121920,-199205121856⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281850057005,0,true,168707178432,168707178496⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917173198547,0,false,-199369007360,-199369007296⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523249305,0,true,11621440,11621504⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500006247,0,false,-11621632,-11621568⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534886795,0,true,23258752,23258816⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488368757,0,false,-23259328,-23259264⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627283,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627654,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281736115689,0,true,168609440512,168609440576⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917287139863,0,false,-199232422400,-199232422336⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281861463069,0,true,168716961984,168716962048⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917161792483,0,false,-199382681088,-199382681024⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069269598868,0,false,-30665719040,-30665718976⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069311161355,0,false,-30622981888,-30622981824⟩
    { al := (169731/1024000), au := (1358697/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨182247273529,182361224381⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168628986496,168628986560⟩ : DyadicInterval 40),(⟨-199259734848,-199259734784⟩ : DyadicInterval 40),(⟨746949441046,746949460376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168726730880,168726730944⟩ : DyadicInterval 40),(⟨-199396334592,-199396334528⟩ : DyadicInterval 40),(⟨746930371400,746930390730⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168589902208,168589902272⟩ : DyadicInterval 40),(⟨-199205121920,-199205121856⟩ : DyadicInterval 40),(⟨746957062408,746957081738⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168707178432,168707178496⟩ : DyadicInterval 40),(⟨-199369007360,-199369007296⟩ : DyadicInterval 40),(⟨746934187150,746934206480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11621529,23259019⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11621440,11621504⟩ : DyadicInterval 40),(⟨-11621632,-11621568⟩ : DyadicInterval 40),(⟨762123383525,762123402854⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23258752,23258816⟩ : DyadicInterval 40),(⟨-23259328,-23259264⟩ : DyadicInterval 40),(⟨762123383347,762123402676⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182224487913,182349835293⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168609440512,168609440576⟩ : DyadicInterval 40),(⟨-199232422400,-199232422336⟩ : DyadicInterval 40),(⟨746953252742,746953272072⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168716961984,168716962048⟩ : DyadicInterval 40),(⟨-199382681088,-199382681024⟩ : DyadicInterval 40),(⟨746932277922,746932297251⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30665719040,-30622981824⟩ : DyadicInterval 40),(⟨777434874528,777456262400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168628986496,168726730944⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199396334592,-199259734784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2784_ok : ecellOkT e2784 = true := by decide +kernel
theorem e2784_pos {a z : ℝ} (ha1 : ((169731/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1358697/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2784 e2784_ok ha1 ha2 hz1 hz2 hz

-- box ['1358697/8192000', '679773/4096000', '3999/4000', '7999/8000']  interval_lower 287534475/1099511627776
noncomputable def e2785 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281872852156,0,true,168726730880,168726730944⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917150403396,0,false,-199396334592,-199396334528⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281986803008,0,true,168824466560,168824466624⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917036452544,0,false,-199532951296,-199532951232⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281827261849,0,true,168687625664,168687625728⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917195993703,0,false,-199341680704,-199341680640⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281963993612,0,true,168804903616,168804903680⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917059261940,0,false,-199505603584,-199505603520⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523256869,0,true,11628992,11629056⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499998683,0,false,-11629184,-11629120⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534901922,0,true,23273856,23273920⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488353630,0,false,-23274432,-23274368⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627283,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627654,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281850052298,0,true,168707174400,168707174464⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917173203254,0,false,-199369001664,-199369001600⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281975406797,0,true,168814692416,168814692480⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917047848755,0,false,-199519287552,-199519287488⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069231792789,0,false,-30704595072,-30704595008⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069273383617,0,false,-30661827264,-30661827200⟩
    { al := (1358697/8192000), au := (679773/4096000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨182361224380,182475175232⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168726730880,168726730944⟩ : DyadicInterval 40),(⟨-199396334592,-199396334528⟩ : DyadicInterval 40),(⟨746930371400,746930390730⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168824466560,168824466624⟩ : DyadicInterval 40),(⟨-199532951296,-199532951232⟩ : DyadicInterval 40),(⟨746911289614,746911308944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168687625664,168687625728⟩ : DyadicInterval 40),(⟨-199341680704,-199341680640⟩ : DyadicInterval 40),(⟨746938002356,746938021686⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168804903616,168804903680⟩ : DyadicInterval 40),(⟨-199505603584,-199505603520⟩ : DyadicInterval 40),(⟨746915110187,746915129516⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11629093,23274146⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11628992,11629056⟩ : DyadicInterval 40),(⟨-11629184,-11629120⟩ : DyadicInterval 40),(⟨762123383525,762123402854⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23273856,23273920⟩ : DyadicInterval 40),(⟨-23274432,-23274368⟩ : DyadicInterval 40),(⟨762123383347,762123402676⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182338424522,182463779021⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168707174400,168707174464⟩ : DyadicInterval 40),(⟨-199369001664,-199369001600⟩ : DyadicInterval 40),(⟨746934187913,746934207242⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168814692416,168814692480⟩ : DyadicInterval 40),(⟨-199519287552,-199519287488⟩ : DyadicInterval 40),(⟨746913198546,746913217875⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30704595072,-30661827200⟩ : DyadicInterval 40),(⟨777454297216,777475700416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168726730880,168824466624⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199532951296,-199396334528⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2785_ok : ecellOkT e2785 = true := by decide +kernel
theorem e2785_pos {a z : ℝ} (ha1 : ((1358697/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((679773/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2785 e2785_ok ha1 ha2 hz1 hz2 hz

-- box ['169731/1024000', '1358697/8192000', '7999/8000', '1']  interval_lower 142991421/549755813888
noncomputable def e2786 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281758901305,0,true,168628986496,168628986560⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917264354247,0,false,-199259734848,-199259734784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281872852157,0,true,168726730880,168726730944⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917150403395,0,false,-199396334592,-199396334528⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281736120395,0,true,168609444544,168609444608⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917287135157,0,false,-199232428096,-199232428032⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523257443,0,true,11629568,11629632⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499998109,0,false,-11629760,-11629696⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627652,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1281747506100,0,true,168619211520,168619211584⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨917275749452,0,false,-199246075712,-199246075648⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1281872860632,0,true,168726738176,168726738240⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨917150394920,0,false,-199396344768,-199396344704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1069265818265,0,false,-30669606592,-30669606528⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1069307385721,0,false,-30626864128,-30626864064⟩
    { al := (169731/1024000), au := (1358697/8192000), zl := (7999/8000), zu := 1,
      A := ⟨182247273529,182361224381⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168628986496,168628986560⟩ : DyadicInterval 40),(⟨-199259734848,-199259734784⟩ : DyadicInterval 40),(⟨746949441046,746949460376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168726730880,168726730944⟩ : DyadicInterval 40),(⟨-199396334592,-199396334528⟩ : DyadicInterval 40),(⟨746930371400,746930390730⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168609444544,168609444608⟩ : DyadicInterval 40),(⟨-199232428096,-199232428032⟩ : DyadicInterval 40),(⟨746953251981,746953271310⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168726730880,168726730944⟩ : DyadicInterval 40),(⟨-199396334592,-199396334528⟩ : DyadicInterval 40),(⟨746930371400,746930390730⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11629667⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11629568,11629632⟩ : DyadicInterval 40),(⟨-11629760,-11629696⟩ : DyadicInterval 40),(⟨762123383524,762123402853⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨182235878324,182361232856⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168619211520,168619211584⟩ : DyadicInterval 40),(⟨-199246075712,-199246075648⟩ : DyadicInterval 40),(⟨746951347358,746951366688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168726738176,168726738240⟩ : DyadicInterval 40),(⟨-199396344768,-199396344704⟩ : DyadicInterval 40),(⟨746930369973,746930389302⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30669606592,-30626864064⟩ : DyadicInterval 40),(⟨777436815648,777458206176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨168628986496,168726730944⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199396334592,-199259734784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2786_ok : ecellOkT e2786 = true := by decide +kernel
theorem e2786_pos {a z : ℝ} (ha1 : ((169731/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1358697/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2786 e2786_ok ha1 ha2 hz1 hz2 hz

-- box ['1358697/8192000', '679773/4096000', '7999/8000', '1']  interval_lower 71834951/274877906944
noncomputable def e2787 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281872852156,0,true,168726730880,168726730944⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917150403396,0,false,-199396334592,-199396334528⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281986803008,0,true,168824466560,168824466624⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917036452544,0,false,-199532951296,-199532951232⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281850057002,0,true,168707178432,168707178496⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917173198550,0,false,-199369007360,-199369007296⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523265007,0,true,11637120,11637184⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499990545,0,false,-11637312,-11637248⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627652,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1281861449827,0,true,168716950656,168716950720⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨917161805725,0,false,-199382665216,-199382665152⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1281986811483,0,true,168824473856,168824473920⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨917036444069,0,false,-199532961472,-199532961408⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1069228007459,0,false,-30708487616,-30708487552⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1069269603261,0,false,-30665714496,-30665714432⟩
    { al := (1358697/8192000), au := (679773/4096000), zl := (7999/8000), zu := 1,
      A := ⟨182361224380,182475175232⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168726730880,168726730944⟩ : DyadicInterval 40),(⟨-199396334592,-199396334528⟩ : DyadicInterval 40),(⟨746930371400,746930390730⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168824466560,168824466624⟩ : DyadicInterval 40),(⟨-199532951296,-199532951232⟩ : DyadicInterval 40),(⟨746911289614,746911308944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168707178432,168707178496⟩ : DyadicInterval 40),(⟨-199369007360,-199369007296⟩ : DyadicInterval 40),(⟨746934187151,746934206480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168824466560,168824466624⟩ : DyadicInterval 40),(⟨-199532951296,-199532951232⟩ : DyadicInterval 40),(⟨746911289614,746911308944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11637231⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11637120,11637184⟩ : DyadicInterval 40),(⟨-11637312,-11637248⟩ : DyadicInterval 40),(⟨762123383524,762123402853⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨182349822051,182475183707⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168716950656,168716950720⟩ : DyadicInterval 40),(⟨-199382665216,-199382665152⟩ : DyadicInterval 40),(⟨746932280122,746932299452⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168824473856,168824473920⟩ : DyadicInterval 40),(⟨-199532961472,-199532961408⟩ : DyadicInterval 40),(⟨746911288185,746911307515⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30708487616,-30665714432⟩ : DyadicInterval 40),(⟨777456240832,777477646688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨168726730880,168824466624⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199532951296,-199396334528⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2787_ok : ecellOkT e2787 = true := by decide +kernel
theorem e2787_pos {a z : ℝ} (ha1 : ((1358697/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((679773/4096000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2787 e2787_ok ha1 ha2 hz1 hz2 hz

-- box ['679773/4096000', '272079/1638400', '3999/4000', '7999/8000']  interval_lower 144447317/549755813888
noncomputable def e2788 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281986803007,0,true,168824466560,168824466624⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917036452545,0,false,-199532951296,-199532951232⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282100753859,0,true,168922193600,168922193664⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916922501693,0,false,-199669585024,-199669584960⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281941184213,0,true,168785340352,168785340416⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917082071339,0,false,-199478256512,-199478256448⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282077930219,0,true,168902620160,168902620224⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916945325333,0,false,-199642216768,-199642216704⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523264433,0,true,11636544,11636608⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499991119,0,false,-11636736,-11636672⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534917051,0,true,23289024,23289088⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488338501,0,false,-23289536,-23289472⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627282,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627653,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281963988899,0,true,168804899584,168804899648⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917059266653,0,false,-199505597952,-199505597888⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282089350530,0,true,168912414208,168912414272⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916933905022,0,false,-199655910976,-199655910912⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069193963092,0,false,-30743496768,-30743496704⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069235582268,0,false,-30700698304,-30700698240⟩
    { al := (679773/4096000), au := (272079/1638400), zl := (3999/4000), zu := (7999/8000),
      A := ⟨182475175231,182589126083⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168824466560,168824466624⟩ : DyadicInterval 40),(⟨-199532951296,-199532951232⟩ : DyadicInterval 40),(⟨746911289614,746911308944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168922193600,168922193664⟩ : DyadicInterval 40),(⟨-199669585024,-199669584960⟩ : DyadicInterval 40),(⟨746892195677,746892215006⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168785340352,168785340416⟩ : DyadicInterval 40),(⟨-199478256512,-199478256448⟩ : DyadicInterval 40),(⟨746918930240,746918949569⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168902620160,168902620224⟩ : DyadicInterval 40),(⟨-199642216768,-199642216704⟩ : DyadicInterval 40),(⟨746896021051,746896040380⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11636657,23289275⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11636544,11636608⟩ : DyadicInterval 40),(⟨-11636736,-11636672⟩ : DyadicInterval 40),(⟨762123383524,762123402853⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23289024,23289088⟩ : DyadicInterval 40),(⟨-23289536,-23289472⟩ : DyadicInterval 40),(⟨762123383314,762123402643⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182452361123,182577722754⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168804899584,168804899648⟩ : DyadicInterval 40),(⟨-199505597952,-199505597888⟩ : DyadicInterval 40),(⟨746915110978,746915130308⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168912414208,168912414272⟩ : DyadicInterval 40),(⟨-199655910976,-199655910912⟩ : DyadicInterval 40),(⟨746894106993,746894126323⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30743496768,-30700698240⟩ : DyadicInterval 40),(⟨777473732736,777495151264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168824466560,168922193664⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199669585024,-199532951232⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2788_ok : ecellOkT e2788 = true := by decide +kernel
theorem e2788_pos {a z : ℝ} (ha1 : ((679773/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((272079/1638400 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2788 e2788_ok ha1 ha2 hz1 hz2 hz

-- box ['272079/1638400', '340311/2048000', '3999/4000', '7999/8000']  interval_lower 290258471/1099511627776
noncomputable def e2789 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282100753858,0,true,168922193600,168922193664⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916922501694,0,false,-199669585024,-199669584960⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282214704710,0,true,169019911872,169019911936⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916808550842,0,false,-199806235648,-199806235584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282055106576,0,true,168883046400,168883046464⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916968148976,0,false,-199614849216,-199614849152⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282191866826,0,true,169000328000,169000328064⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916831388726,0,false,-199778846976,-199778846912⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523271998,0,true,11644160,11644224⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499983554,0,false,-11644288,-11644224⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534932181,0,true,23304128,23304192⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488323371,0,false,-23304704,-23304640⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627282,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627653,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282077925506,0,true,168902616128,168902616192⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916945330046,0,false,-199642211136,-199642211072⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282203294258,0,true,169010127232,169010127296⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916819961294,0,false,-199792551424,-199792551360⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069156109781,0,false,-30782424128,-30782424064⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069197757305,0,false,-30739594944,-30739594880⟩
    { al := (272079/1638400), au := (340311/2048000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨182589126082,182703076934⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168922193600,168922193664⟩ : DyadicInterval 40),(⟨-199669585024,-199669584960⟩ : DyadicInterval 40),(⟨746892195677,746892215007⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169019911872,169019911936⟩ : DyadicInterval 40),(⟨-199806235648,-199806235584⟩ : DyadicInterval 40),(⟨746873089607,746873108937⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168883046400,168883046464⟩ : DyadicInterval 40),(⟨-199614849216,-199614849152⟩ : DyadicInterval 40),(⟨746899845931,746899865261⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169000328000,169000328064⟩ : DyadicInterval 40),(⟨-199778846976,-199778846912⟩ : DyadicInterval 40),(⟨746876919805,746876939135⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11644222,23304405⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11644160,11644224⟩ : DyadicInterval 40),(⟨-11644288,-11644224⟩ : DyadicInterval 40),(⟨762123383492,762123402821⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23304128,23304192⟩ : DyadicInterval 40),(⟨-23304704,-23304640⟩ : DyadicInterval 40),(⟨762123383346,762123402675⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182566297730,182691666482⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168902616128,168902616192⟩ : DyadicInterval 40),(⟨-199642211136,-199642211072⟩ : DyadicInterval 40),(⟨746896021843,746896041173⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169010127232,169010127296⟩ : DyadicInterval 40),(⟨-199792551424,-199792551360⟩ : DyadicInterval 40),(⟨746875003366,746875022696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30782424128,-30739594880⟩ : DyadicInterval 40),(⟨777493181056,777514614944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168922193600,169019911936⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199806235648,-199669584960⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2789_ok : ecellOkT e2789 = true := by decide +kernel
theorem e2789_pos {a z : ℝ} (ha1 : ((272079/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((340311/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2789 e2789_ok ha1 ha2 hz1 hz2 hz

-- box ['679773/4096000', '272079/1638400', '7999/8000', '1']  interval_lower 288699837/1099511627776
noncomputable def e2790 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281986803007,0,true,168824466560,168824466624⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917036452545,0,false,-199532951296,-199532951232⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282100753859,0,true,168922193600,168922193664⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916922501693,0,false,-199669585024,-199669584960⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281963993610,0,true,168804903616,168804903680⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917059261942,0,false,-199505603584,-199505603520⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523272572,0,true,11644672,11644736⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499982980,0,false,-11644864,-11644800⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627652,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1281975393553,0,true,168814681088,168814681152⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨917047861999,0,false,-199519271680,-199519271616⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1282100762336,0,true,168922200832,168922200896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨916922493216,0,false,-199669595200,-199669595136⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1069190173034,0,false,-30747394304,-30747394240⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1069231797186,0,false,-30704590528,-30704590464⟩
    { al := (679773/4096000), au := (272079/1638400), zl := (7999/8000), zu := 1,
      A := ⟨182475175231,182589126083⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168824466560,168824466624⟩ : DyadicInterval 40),(⟨-199532951296,-199532951232⟩ : DyadicInterval 40),(⟨746911289614,746911308944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168922193600,168922193664⟩ : DyadicInterval 40),(⟨-199669585024,-199669584960⟩ : DyadicInterval 40),(⟨746892195677,746892215006⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168804903616,168804903680⟩ : DyadicInterval 40),(⟨-199505603584,-199505603520⟩ : DyadicInterval 40),(⟨746915110187,746915129516⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168922193600,168922193664⟩ : DyadicInterval 40),(⟨-199669585024,-199669584960⟩ : DyadicInterval 40),(⟨746892195677,746892215006⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11644796⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11644672,11644736⟩ : DyadicInterval 40),(⟨-11644864,-11644800⟩ : DyadicInterval 40),(⟨762123383524,762123402853⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨182463765777,182589134560⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168814681088,168814681152⟩ : DyadicInterval 40),(⟨-199519271680,-199519271616⟩ : DyadicInterval 40),(⟨746913200749,746913220079⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168922200832,168922200896⟩ : DyadicInterval 40),(⟨-199669595200,-199669595136⟩ : DyadicInterval 40),(⟨746892194283,746892213612⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30747394304,-30704590464⟩ : DyadicInterval 40),(⟨777475678848,777497100032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨168824466560,168922193664⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199669585024,-199532951232⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2790_ok : ecellOkT e2790 = true := by decide +kernel
theorem e2790_pos {a z : ℝ} (ha1 : ((679773/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((272079/1638400 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2790 e2790_ok ha1 ha2 hz1 hz2 hz

-- box ['272079/1638400', '340311/2048000', '7999/8000', '1']  interval_lower 72515769/274877906944
noncomputable def e2791 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282100753858,0,true,168922193600,168922193664⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916922501694,0,false,-199669585024,-199669584960⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282214704710,0,true,169019911872,169019911936⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916808550842,0,false,-199806235648,-199806235584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282077930217,0,true,168902620160,168902620224⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916945325335,0,false,-199642216768,-199642216704⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523280137,0,true,11652288,11652352⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499975415,0,false,-11652480,-11652416⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627652,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1282089337283,0,true,168912402816,168912402880⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨916933918269,0,false,-199655895104,-199655895040⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1282214713187,0,true,169019919168,169019919232⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨916808542365,0,false,-199806245824,-199806245760⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1069152314990,0,false,-30786326656,-30786326592⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1069193967493,0,false,-30743492224,-30743492160⟩
    { al := (272079/1638400), au := (340311/2048000), zl := (7999/8000), zu := 1,
      A := ⟨182589126082,182703076934⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168922193600,168922193664⟩ : DyadicInterval 40),(⟨-199669585024,-199669584960⟩ : DyadicInterval 40),(⟨746892195677,746892215007⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169019911872,169019911936⟩ : DyadicInterval 40),(⟨-199806235648,-199806235584⟩ : DyadicInterval 40),(⟨746873089607,746873108937⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168902620160,168902620224⟩ : DyadicInterval 40),(⟨-199642216768,-199642216704⟩ : DyadicInterval 40),(⟨746896021051,746896040381⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169019911872,169019911936⟩ : DyadicInterval 40),(⟨-199806235648,-199806235584⟩ : DyadicInterval 40),(⟨746873089607,746873108937⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11652361⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11652288,11652352⟩ : DyadicInterval 40),(⟨-11652480,-11652416⟩ : DyadicInterval 40),(⟨762123383524,762123402853⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨182577709507,182703085411⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168912402816,168912402880⟩ : DyadicInterval 40),(⟨-199655895104,-199655895040⟩ : DyadicInterval 40),(⟨746894109237,746894128566⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169019919168,169019919232⟩ : DyadicInterval 40),(⟨-199806245824,-199806245760⟩ : DyadicInterval 40),(⟨746873088174,746873107503⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30786326656,-30743492160⟩ : DyadicInterval 40),(⟨777495129696,777516566208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨168922193600,169019911936⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199806235648,-199669584960⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2791_ok : ecellOkT e2791 = true := by decide +kernel
theorem e2791_pos {a z : ℝ} (ha1 : ((272079/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((340311/2048000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2791 e2791_ok ha1 ha2 hz1 hz2 hz

-- box ['340311/2048000', '1362093/8192000', '1999/2000', '7997/8000']  interval_lower 146008475/549755813888
noncomputable def e2792 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282214704709,0,true,169019911872,169019911936⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916808550843,0,false,-199806235648,-199806235584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282328655561,0,true,169117621504,169117621568⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916694599991,0,false,-199942903360,-199942903296⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282123353170,0,true,168941574272,168941574336⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916899902382,0,false,-199696684928,-199696684864⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282260099176,0,true,169058837376,169058837440⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916763156376,0,false,-199860677760,-199860677696⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546583471,0,true,34955136,34955200⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476672081,0,false,-34956288,-34956224⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558266353,0,true,46637568,46637632⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464989199,0,false,-46639616,-46639552⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625797,0,false,-1984,-1920⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626665,0,false,-1152,-1088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282169024398,0,true,168980739840,168980739904⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916854231154,0,false,-199751453504,-199751453440⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282294385971,0,true,169088237248,169088237312⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916728869581,0,false,-199901800128,-199901800064⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069125831164,0,false,-30813562880,-30813562816⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069167497075,0,false,-30770713600,-30770713536⟩
    { al := (340311/2048000), au := (1362093/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨182703076933,182817027785⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169019911872,169019911936⟩ : DyadicInterval 40),(⟨-199806235648,-199806235584⟩ : DyadicInterval 40),(⟨746873089607,746873108937⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169117621504,169117621568⟩ : DyadicInterval 40),(⟨-199942903360,-199942903296⟩ : DyadicInterval 40),(⟨746853971409,746853990739⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168941574272,168941574336⟩ : DyadicInterval 40),(⟨-199696684928,-199696684864⟩ : DyadicInterval 40),(⟨746888407434,746888426764⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169058837376,169058837440⟩ : DyadicInterval 40),(⟨-199860677760,-199860677696⟩ : DyadicInterval 40),(⟨746865474970,746865494299⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34955695,46638577⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34955136,34955200⟩ : DyadicInterval 40),(⟨-34956288,-34956224⟩ : DyadicInterval 40),(⟨762123383016,762123402345⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46637568,46637632⟩ : DyadicInterval 40),(⟨-46639616,-46639552⟩ : DyadicInterval 40),(⟨762123382597,762123401926⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1984,-1088⟩ : DyadicInterval 40),(⟨762123384160,762123403872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182657396622,182782758195⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168980739840,168980739904⟩ : DyadicInterval 40),(⟨-199751453504,-199751453440⟩ : DyadicInterval 40),(⟨746880750290,746880769619⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169088237248,169088237312⟩ : DyadicInterval 40),(⟨-199901800128,-199901800064⟩ : DyadicInterval 40),(⟨746859722281,746859741611⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30813562880,-30770713536⟩ : DyadicInterval 40),(⟨777508740384,777530184320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169019911872,169117621568⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199942903360,-199806235584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2792_ok : ecellOkT e2792 = true := by decide +kernel
theorem e2792_pos {a z : ℝ} (ha1 : ((340311/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1362093/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2792 e2792_ok ha1 ha2 hz1 hz2 hz

-- box ['1362093/8192000', '681471/4096000', '1999/2000', '7997/8000']  interval_lower 293387893/1099511627776
noncomputable def e2793 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282328655560,0,true,169117621504,169117621568⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916694599992,0,false,-199942903296,-199942903232⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282442606412,0,true,169215322432,169215322496⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916580649140,0,false,-200079587968,-200079587904⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282237247046,0,true,169039241984,169039242048⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916786008506,0,false,-199833270592,-199833270528⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282374007296,0,true,169156506944,169156507008⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916649248256,0,false,-199997300928,-199997300864⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546606168,0,true,34977792,34977856⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476649384,0,false,-34979008,-34978944⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558296618,0,true,46667840,46667904⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464958934,0,false,-46669888,-46669824⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625795,0,false,-1984,-1920⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626664,0,false,-1152,-1088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282282946762,0,true,169078428544,169078428608⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916740308790,0,false,-199888080128,-199888080064⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282408315460,0,true,169185922432,169185922496⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916614940092,0,false,-200038454016,-200038453952⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069087940094,0,false,-30852531520,-30852531456⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069129634353,0,false,-30809651584,-30809651520⟩
    { al := (1362093/8192000), au := (681471/4096000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨182817027784,182930978636⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169117621504,169117621568⟩ : DyadicInterval 40),(⟨-199942903296,-199942903232⟩ : DyadicInterval 40),(⟨746853971383,746853990713⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169215322432,169215322496⟩ : DyadicInterval 40),(⟨-200079587968,-200079587904⟩ : DyadicInterval 40),(⟨746834841040,746834860370⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169039241984,169039242048⟩ : DyadicInterval 40),(⟨-199833270592,-199833270528⟩ : DyadicInterval 40),(⟨746869308504,746869327833⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169156506944,169156507008⟩ : DyadicInterval 40),(⟨-199997300928,-199997300864⟩ : DyadicInterval 40),(⟨746846359065,746846378394⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34978392,46668842⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34977792,34977856⟩ : DyadicInterval 40),(⟨-34979008,-34978944⟩ : DyadicInterval 40),(⟨762123383047,762123402376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46667840,46667904⟩ : DyadicInterval 40),(⟨-46669888,-46669824⟩ : DyadicInterval 40),(⟨762123382595,762123401924⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1984,-1088⟩ : DyadicInterval 40),(⟨762123384160,762123403872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182771318986,182896687684⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169078428544,169078428608⟩ : DyadicInterval 40),(⟨-199888080128,-199888080064⟩ : DyadicInterval 40),(⟨746861641684,746861661013⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169185922432,169185922496⟩ : DyadicInterval 40),(⟨-200038454016,-200038453952⟩ : DyadicInterval 40),(⟨746840599180,746840618510⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30852531520,-30809651520⟩ : DyadicInterval 40),(⟨777528209376,777549668640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169117621504,169215322496⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200079587968,-199942903232⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2793_ok : ecellOkT e2793 = true := by decide +kernel
theorem e2793_pos {a z : ℝ} (ha1 : ((1362093/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((681471/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2793 e2793_ok ha1 ha2 hz1 hz2 hz

-- box ['340311/2048000', '1362093/8192000', '7997/8000', '3999/4000']  interval_lower 72955283/274877906944
noncomputable def e2794 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282214704709,0,true,169019911872,169019911936⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916808550843,0,false,-199806235648,-199806235584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282328655561,0,true,169117621504,169117621568⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916694599991,0,false,-199942903360,-199942903296⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282146191055,0,true,168961159168,168961159232⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916877064497,0,false,-199724071552,-199724071488⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282282951305,0,true,169078432448,169078432512⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916740304247,0,false,-199888085632,-199888085568⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534931547,0,true,23303488,23303552⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488324005,0,false,-23304064,-23304000⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546606863,0,true,34978496,34978560⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476648689,0,false,-34979648,-34979584⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626663,0,false,-1152,-1088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627283,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282180443240,0,true,168990531968,168990532032⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916842812312,0,false,-199765147264,-199765147200⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282305811963,0,true,169098034496,169098034560⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916717443589,0,false,-199915504384,-199915504320⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069122032133,0,false,-30817469888,-30817469824⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069163703025,0,false,-30774615296,-30774615232⟩
    { al := (340311/2048000), au := (1362093/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨182703076933,182817027785⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169019911872,169019911936⟩ : DyadicInterval 40),(⟨-199806235648,-199806235584⟩ : DyadicInterval 40),(⟨746873089607,746873108937⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169117621504,169117621568⟩ : DyadicInterval 40),(⟨-199942903360,-199942903296⟩ : DyadicInterval 40),(⟨746853971409,746853990739⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168961159168,168961159232⟩ : DyadicInterval 40),(⟨-199724071552,-199724071488⟩ : DyadicInterval 40),(⟨746884578712,746884598041⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169078432448,169078432512⟩ : DyadicInterval 40),(⟨-199888085632,-199888085568⟩ : DyadicInterval 40),(⟨746861640939,746861660269⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23303771,34979087⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23303488,23303552⟩ : DyadicInterval 40),(⟨-23304064,-23304000⟩ : DyadicInterval 40),(⟨762123383346,762123402675⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34978496,34978560⟩ : DyadicInterval 40),(⟨-34979648,-34979584⟩ : DyadicInterval 40),(⟨762123383015,762123402344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1152,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182668815464,182794184187⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168990531968,168990532032⟩ : DyadicInterval 40),(⟨-199765147264,-199765147200⟩ : DyadicInterval 40),(⟨746878835465,746878854794⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169098034496,169098034560⟩ : DyadicInterval 40),(⟨-199915504384,-199915504320⟩ : DyadicInterval 40),(⟨746857804969,746857824298⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30817469888,-30774615232⟩ : DyadicInterval 40),(⟨777510691232,777532137824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169019911872,169117621568⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199942903360,-199806235584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2794_ok : ecellOkT e2794 = true := by decide +kernel
theorem e2794_pos {a z : ℝ} (ha1 : ((340311/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1362093/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2794 e2794_ok ha1 ha2 hz1 hz2 hz

-- box ['1362093/8192000', '681471/4096000', '7997/8000', '3999/4000']  interval_lower 36648939/137438953472
noncomputable def e2795 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282328655560,0,true,169117621504,169117621568⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916694599992,0,false,-199942903296,-199942903232⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282442606412,0,true,169215322432,169215322496⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916580649140,0,false,-200079587968,-200079587904⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282260099174,0,true,169058837376,169058837440⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916763156378,0,false,-199860677760,-199860677696⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282396873668,0,true,169176112448,169176112512⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916626381884,0,false,-200024729280,-200024729216⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534946678,0,true,23318592,23318656⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488308874,0,false,-23319168,-23319104⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546629562,0,true,35001216,35001280⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476625990,0,false,-35002368,-35002304⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626661,0,false,-1152,-1088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627282,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282294372723,0,true,169088225856,169088225920⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916728882829,0,false,-199901784192,-199901784128⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282419748572,0,true,169195724928,169195724992⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916603506980,0,false,-200052168512,-200052168448⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069084136326,0,false,-30856443520,-30856443456⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069125835570,0,false,-30813558336,-30813558272⟩
    { al := (1362093/8192000), au := (681471/4096000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨182817027784,182930978636⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169117621504,169117621568⟩ : DyadicInterval 40),(⟨-199942903296,-199942903232⟩ : DyadicInterval 40),(⟨746853971383,746853990713⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169215322432,169215322496⟩ : DyadicInterval 40),(⟨-200079587968,-200079587904⟩ : DyadicInterval 40),(⟨746834841040,746834860370⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169058837376,169058837440⟩ : DyadicInterval 40),(⟨-199860677760,-199860677696⟩ : DyadicInterval 40),(⟨746865474970,746865494299⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169176112448,169176112512⟩ : DyadicInterval 40),(⟨-200024729280,-200024729216⟩ : DyadicInterval 40),(⟨746842520227,746842539556⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23318902,35001786⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23318592,23318656⟩ : DyadicInterval 40),(⟨-23319168,-23319104⟩ : DyadicInterval 40),(⟨762123383345,762123402674⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35001216,35001280⟩ : DyadicInterval 40),(⟨-35002368,-35002304⟩ : DyadicInterval 40),(⟨762123383013,762123402342⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1152,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182782744947,182908120796⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169088225856,169088225920⟩ : DyadicInterval 40),(⟨-199901784192,-199901784128⟩ : DyadicInterval 40),(⟨746859724503,746859743833⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169195724928,169195724992⟩ : DyadicInterval 40),(⟨-200052168512,-200052168448⟩ : DyadicInterval 40),(⟨746838679445,746838698774⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30856443520,-30813558272⟩ : DyadicInterval 40),(⟨777530162752,777551624640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169117621504,169215322496⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200079587968,-199942903232⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2795_ok : ecellOkT e2795 = true := by decide +kernel
theorem e2795_pos {a z : ℝ} (ha1 : ((1362093/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((681471/4096000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2795 e2795_ok ha1 ha2 hz1 hz2 hz

-- box ['681471/4096000', '1363791/8192000', '1999/2000', '7997/8000']  interval_lower 294761573/1099511627776
noncomputable def e2796 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282442606411,0,true,169215322432,169215322496⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916580649141,0,false,-200079587968,-200079587904⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282556557263,0,true,169313014720,169313014784⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916466698289,0,false,-200216289600,-200216289536⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282351140921,0,true,169136901056,169136901120⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916672114631,0,false,-199969873280,-199969873216⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282487915415,0,true,169254167744,169254167808⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916535340137,0,false,-200133941056,-200133940992⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546628867,0,true,35000512,35000576⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476626685,0,false,-35001664,-35001600⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558326886,0,true,46698112,46698176⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464928666,0,false,-46700160,-46700096⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625792,0,false,-2048,-1984⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626662,0,false,-1152,-1088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282396869120,0,true,169176108544,169176108608⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916626386432,0,false,-200024723840,-200024723776⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282522244945,0,true,169283599040,169283599104⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916501010607,0,false,-200175124928,-200175124864⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069050025415,0,false,-30891525824,-30891525760⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069091748026,0,false,-30848615232,-30848615168⟩
    { al := (681471/4096000), au := (1363791/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨182930978635,183044929487⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169215322432,169215322496⟩ : DyadicInterval 40),(⟨-200079587968,-200079587904⟩ : DyadicInterval 40),(⟨746834841041,746834860370⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169313014720,169313014784⟩ : DyadicInterval 40),(⟨-200216289600,-200216289536⟩ : DyadicInterval 40),(⟨746815698514,746815717843⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169136901056,169136901120⟩ : DyadicInterval 40),(⟨-199969873280,-199969873216⟩ : DyadicInterval 40),(⟨746850197443,746850216772⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169254167744,169254167808⟩ : DyadicInterval 40),(⟨-200133941056,-200133940992⟩ : DyadicInterval 40),(⟨746827231070,746827250400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨35001091,46699110⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35000512,35000576⟩ : DyadicInterval 40),(⟨-35001664,-35001600⟩ : DyadicInterval 40),(⟨762123383013,762123402342⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46698112,46698176⟩ : DyadicInterval 40),(⟨-46700160,-46700096⟩ : DyadicInterval 40),(⟨762123382592,762123401921⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2048,-1088⟩ : DyadicInterval 40),(⟨762123384160,762123403904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182885241344,183010617169⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169176108544,169176108608⟩ : DyadicInterval 40),(⟨-200024723840,-200024723776⟩ : DyadicInterval 40),(⟨746842521000,746842540329⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169283599040,169283599104⟩ : DyadicInterval 40),(⟨-200175124928,-200175124864⟩ : DyadicInterval 40),(⟨746821463895,746821483225⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30891525824,-30848615168⟩ : DyadicInterval 40),(⟨777547691200,777569165792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169215322432,169313014784⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200216289600,-200079587904⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2796_ok : ecellOkT e2796 = true := by decide +kernel
theorem e2796_pos {a z : ℝ} (ha1 : ((681471/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1363791/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2796 e2796_ok ha1 ha2 hz1 hz2 hz

-- box ['1363791/8192000', '8529/51200', '1999/2000', '7997/8000']  interval_lower 296138593/1099511627776
noncomputable def e2797 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282556557262,0,true,169313014720,169313014784⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916466698290,0,false,-200216289600,-200216289536⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282670508114,0,true,169410698304,169410698368⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916352747438,0,false,-200353008256,-200353008192⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282465034797,0,true,169234551424,169234551488⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916558220755,0,false,-200106492928,-200106492864⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282601823534,0,true,169351819968,169351820032⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916421432018,0,false,-200270598208,-200270598144⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546651567,0,true,35023232,35023296⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476603985,0,false,-35024384,-35024320⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558357155,0,true,46728384,46728448⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464898397,0,false,-46730432,-46730368⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625789,0,false,-2048,-1984⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626661,0,false,-1152,-1088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282510791482,0,true,169273779840,169273779904⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916512464070,0,false,-200161384448,-200161384384⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282636174431,0,true,169381266880,169381266944⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916387081121,0,false,-200311812800,-200311812736⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069012087125,0,false,-30930545856,-30930545792⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069053838090,0,false,-30887604544,-30887604480⟩
    { al := (1363791/8192000), au := (8529/51200), zl := (1999/2000), zu := (7997/8000),
      A := ⟨183044929486,183158880338⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169313014720,169313014784⟩ : DyadicInterval 40),(⟨-200216289600,-200216289536⟩ : DyadicInterval 40),(⟨746815698514,746815717844⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169410698304,169410698368⟩ : DyadicInterval 40),(⟨-200353008256,-200353008192⟩ : DyadicInterval 40),(⟨746796543867,746796563196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169234551424,169234551488⟩ : DyadicInterval 40),(⟨-200106492928,-200106492864⟩ : DyadicInterval 40),(⟨746831074261,746831093590⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169351819968,169351820032⟩ : DyadicInterval 40),(⟨-200270598208,-200270598144⟩ : DyadicInterval 40),(⟨746808090898,746808110228⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨35023791,46729379⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35023232,35023296⟩ : DyadicInterval 40),(⟨-35024384,-35024320⟩ : DyadicInterval 40),(⟨762123383012,762123402341⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46728384,46728448⟩ : DyadicInterval 40),(⟨-46730432,-46730368⟩ : DyadicInterval 40),(⟨762123382589,762123401919⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2048,-1088⟩ : DyadicInterval 40),(⟨762123384160,762123403904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182999163706,183124546655⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169273779840,169273779904⟩ : DyadicInterval 40),(⟨-200161384448,-200161384384⟩ : DyadicInterval 40),(⟨746823388154,746823407484⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169381266880,169381266944⟩ : DyadicInterval 40),(⟨-200311812800,-200311812736⟩ : DyadicInterval 40),(⟨746802316509,746802335839⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30930545856,-30887604480⟩ : DyadicInterval 40),(⟨777567185856,777588675808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169313014720,169410698368⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200353008256,-200216289536⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2797_ok : ecellOkT e2797 = true := by decide +kernel
theorem e2797_pos {a z : ℝ} (ha1 : ((1363791/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((8529/51200 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2797 e2797_ok ha1 ha2 hz1 hz2 hz

-- box ['681471/4096000', '1363791/8192000', '7997/8000', '3999/4000']  interval_lower 73641277/274877906944
noncomputable def e2798 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282442606411,0,true,169215322432,169215322496⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916580649141,0,false,-200079587968,-200079587904⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282556557263,0,true,169313014720,169313014784⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916466698289,0,false,-200216289600,-200216289536⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282374007293,0,true,169156506944,169156507008⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916649248259,0,false,-199997300928,-199997300864⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282510796031,0,true,169273783744,169273783808⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916512459521,0,false,-200161389888,-200161389824⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534961811,0,true,23333760,23333824⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488293741,0,false,-23334336,-23334272⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546652263,0,true,35023872,35023936⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476603289,0,false,-35025088,-35025024⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626660,0,false,-1152,-1088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627281,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282408302206,0,true,169185911104,169185911168⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916614953346,0,false,-200038438080,-200038438016⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282533685181,0,true,169293406720,169293406784⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916489570371,0,false,-200188849664,-200188849600⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069046216905,0,false,-30895442880,-30895442816⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069087944504,0,false,-30852526976,-30852526912⟩
    { al := (681471/4096000), au := (1363791/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨182930978635,183044929487⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169215322432,169215322496⟩ : DyadicInterval 40),(⟨-200079587968,-200079587904⟩ : DyadicInterval 40),(⟨746834841041,746834860370⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169313014720,169313014784⟩ : DyadicInterval 40),(⟨-200216289600,-200216289536⟩ : DyadicInterval 40),(⟨746815698514,746815717843⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169156506944,169156507008⟩ : DyadicInterval 40),(⟨-199997300928,-199997300864⟩ : DyadicInterval 40),(⟨746846359065,746846378395⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169273783744,169273783808⟩ : DyadicInterval 40),(⟨-200161389888,-200161389824⟩ : DyadicInterval 40),(⟨746823387380,746823406710⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23334035,35024487⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23333760,23333824⟩ : DyadicInterval 40),(⟨-23334336,-23334272⟩ : DyadicInterval 40),(⟨762123383344,762123402673⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35023872,35023936⟩ : DyadicInterval 40),(⟨-35025088,-35025024⟩ : DyadicInterval 40),(⟨762123383044,762123402373⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1152,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182896674430,183022057405⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169185911104,169185911168⟩ : DyadicInterval 40),(⟨-200038438080,-200038438016⟩ : DyadicInterval 40),(⟨746840601369,746840620698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169293406720,169293406784⟩ : DyadicInterval 40),(⟨-200188849664,-200188849600⟩ : DyadicInterval 40),(⟨746819541770,746819561100⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30895442880,-30852526912⟩ : DyadicInterval 40),(⟨777549647072,777571124320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169215322432,169313014784⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200216289600,-200079587904⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2798_ok : ecellOkT e2798 = true := by decide +kernel
theorem e2798_pos {a z : ℝ} (ha1 : ((681471/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1363791/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2798 e2798_ok ha1 ha2 hz1 hz2 hz

-- box ['1363791/8192000', '8529/51200', '7997/8000', '3999/4000']  interval_lower 147970791/549755813888
noncomputable def e2799 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282556557262,0,true,169313014720,169313014784⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916466698290,0,false,-200216289600,-200216289536⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282670508114,0,true,169410698304,169410698368⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916352747438,0,false,-200353008256,-200353008192⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282487915413,0,true,169254167744,169254167808⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916535340139,0,false,-200133941056,-200133940992⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282624718395,0,true,169371446400,169371446464⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916398537157,0,false,-200298067520,-200298067456⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534976945,0,true,23348864,23348928⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488278607,0,false,-23349440,-23349376⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546674965,0,true,35046592,35046656⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476580587,0,false,-35047808,-35047744⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626658,0,false,-1152,-1088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627281,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282522231688,0,true,169283587648,169283587712⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916501023864,0,false,-200175108992,-200175108928⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282647621788,0,true,169391079872,169391079936⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916375633764,0,false,-200325547776,-200325547712⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069008273872,0,false,-30934467904,-30934467840⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069050029829,0,false,-30891521280,-30891521216⟩
    { al := (1363791/8192000), au := (8529/51200), zl := (7997/8000), zu := (3999/4000),
      A := ⟨183044929486,183158880338⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169313014720,169313014784⟩ : DyadicInterval 40),(⟨-200216289600,-200216289536⟩ : DyadicInterval 40),(⟨746815698514,746815717844⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169410698304,169410698368⟩ : DyadicInterval 40),(⟨-200353008256,-200353008192⟩ : DyadicInterval 40),(⟨746796543867,746796563196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169254167744,169254167808⟩ : DyadicInterval 40),(⟨-200133941056,-200133940992⟩ : DyadicInterval 40),(⟨746827231070,746827250400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169371446400,169371446464⟩ : DyadicInterval 40),(⟨-200298067520,-200298067456⟩ : DyadicInterval 40),(⟨746804242388,746804261718⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23349169,35047189⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23348864,23348928⟩ : DyadicInterval 40),(⟨-23349440,-23349376⟩ : DyadicInterval 40),(⟨762123383344,762123402673⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35046592,35046656⟩ : DyadicInterval 40),(⟨-35047808,-35047744⟩ : DyadicInterval 40),(⟨762123383042,762123402371⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1152,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183010603912,183135994012⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169283587648,169283587712⟩ : DyadicInterval 40),(⟨-200175108992,-200175108928⟩ : DyadicInterval 40),(⟨746821466125,746821485454⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169391079872,169391079936⟩ : DyadicInterval 40),(⟨-200325547776,-200325547712⟩ : DyadicInterval 40),(⟨746800391917,746800411247⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30934467904,-30891521216⟩ : DyadicInterval 40),(⟨777569144224,777590636832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169313014720,169410698368⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200353008256,-200216289536⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2799_ok : ecellOkT e2799 = true := by decide +kernel
theorem e2799_pos {a z : ℝ} (ha1 : ((1363791/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((8529/51200 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2799 e2799_ok ha1 ha2 hz1 hz2 hz

-- box ['340311/2048000', '1362093/8192000', '3999/4000', '7999/8000']  interval_lower 291625357/1099511627776
noncomputable def e2800 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282214704709,0,true,169019911872,169019911936⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916808550843,0,false,-199806235648,-199806235584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282328655561,0,true,169117621504,169117621568⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916694599991,0,false,-199942903360,-199942903296⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282169028939,0,true,168980743744,168980743808⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916854226613,0,false,-199751458944,-199751458880⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282305803433,0,true,169098027136,169098027200⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916717452119,0,false,-199915494144,-199915494080⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523279563,0,true,11651712,11651776⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499975989,0,false,-11651904,-11651840⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534947313,0,true,23319232,23319296⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488308239,0,false,-23319808,-23319744⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627281,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627653,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282191862108,0,true,169000323968,169000324032⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916831393444,0,false,-199778841280,-199778841216⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282317237984,0,true,169107831680,169107831744⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916706017568,0,false,-199929208832,-199929208768⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069118232854,0,false,-30821377152,-30821377088⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069159908729,0,false,-30778517312,-30778517248⟩
    { al := (340311/2048000), au := (1362093/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨182703076933,182817027785⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169019911872,169019911936⟩ : DyadicInterval 40),(⟨-199806235648,-199806235584⟩ : DyadicInterval 40),(⟨746873089607,746873108937⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169117621504,169117621568⟩ : DyadicInterval 40),(⟨-199942903360,-199942903296⟩ : DyadicInterval 40),(⟨746853971409,746853990739⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168980743744,168980743808⟩ : DyadicInterval 40),(⟨-199751458944,-199751458880⟩ : DyadicInterval 40),(⟨746880749520,746880768849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169098027136,169098027200⟩ : DyadicInterval 40),(⟨-199915494144,-199915494080⟩ : DyadicInterval 40),(⟨746857806423,746857825752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11651787,23319537⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11651712,11651776⟩ : DyadicInterval 40),(⟨-11651904,-11651840⟩ : DyadicInterval 40),(⟨762123383524,762123402853⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23319232,23319296⟩ : DyadicInterval 40),(⟨-23319808,-23319744⟩ : DyadicInterval 40),(⟨762123383345,762123402674⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182680234332,182805610208⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169000323968,169000324032⟩ : DyadicInterval 40),(⟨-199778841280,-199778841216⟩ : DyadicInterval 40),(⟨746876920573,746876939902⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169107831680,169107831744⟩ : DyadicInterval 40),(⟨-199929208832,-199929208768⟩ : DyadicInterval 40),(⟨746855887524,746855906854⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30821377152,-30778517248⟩ : DyadicInterval 40),(⟨777512642240,777534091456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169019911872,169117621568⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199942903360,-199806235584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2800_ok : ecellOkT e2800 = true := by decide +kernel
theorem e2800_pos {a z : ℝ} (ha1 : ((340311/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1362093/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2800 e2800_ok ha1 ha2 hz1 hz2 hz

-- box ['1362093/8192000', '681471/4096000', '3999/4000', '7999/8000']  interval_lower 292995245/1099511627776
noncomputable def e2801 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282328655560,0,true,169117621504,169117621568⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916694599992,0,false,-199942903296,-199942903232⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282442606412,0,true,169215322432,169215322496⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916580649140,0,false,-200079587968,-200079587904⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282282951303,0,true,169078432448,169078432512⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916740304249,0,false,-199888085632,-199888085568⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282419740040,0,true,169195717632,169195717696⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916603515512,0,false,-200052158272,-200052158208⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523287128,0,true,11659264,11659328⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499968424,0,false,-11659456,-11659392⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534962446,0,true,23334400,23334464⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488293106,0,false,-23334976,-23334912⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627280,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627653,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282305798714,0,true,169098023104,169098023168⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916717456838,0,false,-199915488448,-199915488384⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282431181716,0,true,169205527360,169205527424⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916592073836,0,false,-200065883200,-200065883136⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069080332309,0,false,-30860355840,-30860355776⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069122036539,0,false,-30817465344,-30817465280⟩
    { al := (1362093/8192000), au := (681471/4096000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨182817027784,182930978636⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169117621504,169117621568⟩ : DyadicInterval 40),(⟨-199942903296,-199942903232⟩ : DyadicInterval 40),(⟨746853971383,746853990713⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169215322432,169215322496⟩ : DyadicInterval 40),(⟨-200079587968,-200079587904⟩ : DyadicInterval 40),(⟨746834841040,746834860370⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169078432448,169078432512⟩ : DyadicInterval 40),(⟨-199888085632,-199888085568⟩ : DyadicInterval 40),(⟨746861640939,746861660269⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169195717632,169195717696⟩ : DyadicInterval 40),(⟨-200052158272,-200052158208⟩ : DyadicInterval 40),(⟨746838680864,746838700193⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11659352,23334670⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11659264,11659328⟩ : DyadicInterval 40),(⟨-11659456,-11659392⟩ : DyadicInterval 40),(⟨762123383524,762123402853⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23334400,23334464⟩ : DyadicInterval 40),(⟨-23334976,-23334912⟩ : DyadicInterval 40),(⟨762123383344,762123402673⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182794170938,182919553940⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169098023104,169098023168⟩ : DyadicInterval 40),(⟨-199915488448,-199915488384⟩ : DyadicInterval 40),(⟨746857807191,746857826521⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169205527360,169205527424⟩ : DyadicInterval 40),(⟨-200065883200,-200065883136⟩ : DyadicInterval 40),(⟨746836759577,746836778906⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30860355840,-30817465280⟩ : DyadicInterval 40),(⟨777532116256,777553580800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169117621504,169215322496⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200079587968,-199942903232⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2801_ok : ecellOkT e2801 = true := by decide +kernel
theorem e2801_pos {a z : ℝ} (ha1 : ((1362093/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((681471/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2801 e2801_ok ha1 ha2 hz1 hz2 hz

-- box ['340311/2048000', '1362093/8192000', '7999/8000', '1']  interval_lower 145714717/549755813888
noncomputable def e2802 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282214704709,0,true,169019911872,169019911936⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916808550843,0,false,-199806235648,-199806235584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282328655561,0,true,169117621504,169117621568⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916694599991,0,false,-199942903360,-199942903296⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282191866824,0,true,169000328000,169000328064⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916831388728,0,false,-199778846976,-199778846912⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523287704,0,true,11659840,11659904⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499967848,0,false,-11660032,-11659968⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627652,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1282203281008,0,true,169010115904,169010115968⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨916819974544,0,false,-199792535552,-199792535488⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1282328664034,0,true,169117628800,169117628864⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨916694591518,0,false,-199942913472,-199942913408⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1069114433329,0,false,-30825284672,-30825284608⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1069156114185,0,false,-30782419584,-30782419520⟩
    { al := (340311/2048000), au := (1362093/8192000), zl := (7999/8000), zu := 1,
      A := ⟨182703076933,182817027785⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169019911872,169019911936⟩ : DyadicInterval 40),(⟨-199806235648,-199806235584⟩ : DyadicInterval 40),(⟨746873089607,746873108937⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169117621504,169117621568⟩ : DyadicInterval 40),(⟨-199942903360,-199942903296⟩ : DyadicInterval 40),(⟨746853971409,746853990739⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169000328000,169000328064⟩ : DyadicInterval 40),(⟨-199778846976,-199778846912⟩ : DyadicInterval 40),(⟨746876919806,746876939135⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169117621504,169117621568⟩ : DyadicInterval 40),(⟨-199942903360,-199942903296⟩ : DyadicInterval 40),(⟨746853971409,746853990739⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11659928⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11659840,11659904⟩ : DyadicInterval 40),(⟨-11660032,-11659968⟩ : DyadicInterval 40),(⟨762123383524,762123402853⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨182691653232,182817036258⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169010115904,169010115968⟩ : DyadicInterval 40),(⟨-199792535552,-199792535488⟩ : DyadicInterval 40),(⟨746875005576,746875024906⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169117628800,169117628864⟩ : DyadicInterval 40),(⟨-199942913472,-199942913408⟩ : DyadicInterval 40),(⟨746853969948,746853989278⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30825284672,-30782419520⟩ : DyadicInterval 40),(⟨777514593376,777536045216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨169019911872,169117621568⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199942903360,-199806235584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2802_ok : ecellOkT e2802 = true := by decide +kernel
theorem e2802_pos {a z : ℝ} (ha1 : ((340311/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1362093/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2802 e2802_ok ha1 ha2 hz1 hz2 hz

-- box ['1362093/8192000', '681471/4096000', '7999/8000', '1']  interval_lower 2287491/8589934592
noncomputable def e2803 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282328655560,0,true,169117621504,169117621568⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916694599992,0,false,-199942903296,-199942903232⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282442606412,0,true,169215322432,169215322496⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916580649140,0,false,-200079587968,-200079587904⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282305803431,0,true,169098027136,169098027200⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916717452121,0,false,-199915494144,-199915494080⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523295270,0,true,11667392,11667456⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499960282,0,false,-11667584,-11667520⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627652,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1282317224734,0,true,169107820288,169107820352⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨916706030818,0,false,-199929192960,-199929192896⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1282442614886,0,true,169215329728,169215329792⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨916580640666,0,false,-200079598144,-200079598080⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1069076528046,0,false,-30864268416,-30864268352⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1069118237261,0,false,-30821372608,-30821372544⟩
    { al := (1362093/8192000), au := (681471/4096000), zl := (7999/8000), zu := 1,
      A := ⟨182817027784,182930978636⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169117621504,169117621568⟩ : DyadicInterval 40),(⟨-199942903296,-199942903232⟩ : DyadicInterval 40),(⟨746853971383,746853990713⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169215322432,169215322496⟩ : DyadicInterval 40),(⟨-200079587968,-200079587904⟩ : DyadicInterval 40),(⟨746834841040,746834860370⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169098027136,169098027200⟩ : DyadicInterval 40),(⟨-199915494144,-199915494080⟩ : DyadicInterval 40),(⟨746857806423,746857825753⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169215322432,169215322496⟩ : DyadicInterval 40),(⟨-200079587968,-200079587904⟩ : DyadicInterval 40),(⟨746834841040,746834860370⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11667494⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11667392,11667456⟩ : DyadicInterval 40),(⟨-11667584,-11667520⟩ : DyadicInterval 40),(⟨762123383524,762123402853⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨182805596958,182930987110⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169107820288,169107820352⟩ : DyadicInterval 40),(⟨-199929192960,-199929192896⟩ : DyadicInterval 40),(⟨746855889774,746855909104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169215329728,169215329792⟩ : DyadicInterval 40),(⟨-200079598144,-200079598080⟩ : DyadicInterval 40),(⟨746834839604,746834858933⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30864268416,-30821372544⟩ : DyadicInterval 40),(⟨777534069888,777555537088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨169117621504,169215322496⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200079587968,-199942903232⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2803_ok : ecellOkT e2803 = true := by decide +kernel
theorem e2803_pos {a z : ℝ} (ha1 : ((1362093/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((681471/4096000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2803 e2803_ok ha1 ha2 hz1 hz2 hz

-- box ['681471/4096000', '1363791/8192000', '3999/4000', '7999/8000']  interval_lower 36796019/137438953472
noncomputable def e2804 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282442606411,0,true,169215322432,169215322496⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916580649141,0,false,-200079587968,-200079587904⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282556557263,0,true,169313014720,169313014784⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916466698289,0,false,-200216289600,-200216289536⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282396873666,0,true,169176112448,169176112512⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916626381886,0,false,-200024729280,-200024729216⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282533676647,0,true,169293399424,169293399488⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916489578905,0,false,-200188839424,-200188839360⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523294695,0,true,11666816,11666880⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499960857,0,false,-11667008,-11666944⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534977580,0,true,23349504,23349568⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488277972,0,false,-23350080,-23350016⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627280,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627653,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282419735317,0,true,169195713600,169195713664⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916603520235,0,false,-200052152640,-200052152576⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282545125446,0,true,169303214400,169303214464⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916478130106,0,false,-200202574592,-200202574528⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069042408148,0,false,-30899360192,-30899360128⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069084140737,0,false,-30856438976,-30856438912⟩
    { al := (681471/4096000), au := (1363791/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨182930978635,183044929487⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169215322432,169215322496⟩ : DyadicInterval 40),(⟨-200079587968,-200079587904⟩ : DyadicInterval 40),(⟨746834841041,746834860370⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169313014720,169313014784⟩ : DyadicInterval 40),(⟨-200216289600,-200216289536⟩ : DyadicInterval 40),(⟨746815698514,746815717843⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169176112448,169176112512⟩ : DyadicInterval 40),(⟨-200024729280,-200024729216⟩ : DyadicInterval 40),(⟨746842520227,746842539556⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169293399424,169293399488⟩ : DyadicInterval 40),(⟨-200188839424,-200188839360⟩ : DyadicInterval 40),(⟨746819543192,746819562521⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11666919,23349804⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11666816,11666880⟩ : DyadicInterval 40),(⟨-11667008,-11666944⟩ : DyadicInterval 40),(⟨762123383524,762123402853⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23349504,23349568⟩ : DyadicInterval 40),(⟨-23350080,-23350016⟩ : DyadicInterval 40),(⟨762123383344,762123402673⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182908107541,183033497670⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169195713600,169195713664⟩ : DyadicInterval 40),(⟨-200052152640,-200052152576⟩ : DyadicInterval 40),(⟨746838681661,746838700990⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169303214400,169303214464⟩ : DyadicInterval 40),(⟨-200202574592,-200202574528⟩ : DyadicInterval 40),(⟨746817619475,746817638805⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30899360192,-30856438912⟩ : DyadicInterval 40),(⟨777551603072,777573082976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169215322432,169313014784⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200216289600,-200079587904⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2804_ok : ecellOkT e2804 = true := by decide +kernel
theorem e2804_pos {a z : ℝ} (ha1 : ((681471/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1363791/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2804 e2804_ok ha1 ha2 hz1 hz2 hz

-- box ['1363791/8192000', '8529/51200', '3999/4000', '7999/8000']  interval_lower 73936121/274877906944
noncomputable def e2805 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282556557262,0,true,169313014720,169313014784⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916466698290,0,false,-200216289600,-200216289536⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282670508114,0,true,169410698304,169410698368⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916352747438,0,false,-200353008256,-200353008192⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282510796029,0,true,169273783744,169273783808⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916512459523,0,false,-200161389888,-200161389824⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282647613255,0,true,169391072512,169391072576⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916375642297,0,false,-200325537536,-200325537472⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523302262,0,true,11674368,11674432⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499953290,0,false,-11674560,-11674496⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534992715,0,true,23364672,23364736⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488262837,0,false,-23365248,-23365184⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627279,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627653,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282533671923,0,true,169293395392,169293395456⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916489583629,0,false,-200188833728,-200188833664⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282659069174,0,true,169400892736,169400892800⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916364186378,0,false,-200339283008,-200339282944⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069004460372,0,false,-30938390208,-30938390144⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069046221320,0,false,-30895438336,-30895438272⟩
    { al := (1363791/8192000), au := (8529/51200), zl := (3999/4000), zu := (7999/8000),
      A := ⟨183044929486,183158880338⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169313014720,169313014784⟩ : DyadicInterval 40),(⟨-200216289600,-200216289536⟩ : DyadicInterval 40),(⟨746815698514,746815717844⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169410698304,169410698368⟩ : DyadicInterval 40),(⟨-200353008256,-200353008192⟩ : DyadicInterval 40),(⟨746796543867,746796563196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169273783744,169273783808⟩ : DyadicInterval 40),(⟨-200161389888,-200161389824⟩ : DyadicInterval 40),(⟨746823387381,746823406710⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169391072512,169391072576⟩ : DyadicInterval 40),(⟨-200325537536,-200325537472⟩ : DyadicInterval 40),(⟨746800393378,746800412707⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11674486,23364939⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11674368,11674432⟩ : DyadicInterval 40),(⟨-11674560,-11674496⟩ : DyadicInterval 40),(⟨762123383524,762123402853⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23364672,23364736⟩ : DyadicInterval 40),(⟨-23365248,-23365184⟩ : DyadicInterval 40),(⟨762123383343,762123402672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183022044147,183147441398⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169293395392,169293395456⟩ : DyadicInterval 40),(⟨-200188833728,-200188833664⟩ : DyadicInterval 40),(⟨746819543963,746819563292⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169400892736,169400892800⟩ : DyadicInterval 40),(⟨-200339283008,-200339282944⟩ : DyadicInterval 40),(⟨746798467257,746798486586⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30938390208,-30895438272⟩ : DyadicInterval 40),(⟨777571102752,777592597984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169313014720,169410698368⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200353008256,-200216289536⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2805_ok : ecellOkT e2805 = true := by decide +kernel
theorem e2805_pos {a z : ℝ} (ha1 : ((1363791/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((8529/51200 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2805 e2805_ok ha1 ha2 hz1 hz2 hz

-- box ['681471/4096000', '1363791/8192000', '7999/8000', '1']  interval_lower 294171403/1099511627776
noncomputable def e2806 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282442606411,0,true,169215322432,169215322496⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916580649141,0,false,-200079587968,-200079587904⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282556557263,0,true,169313014720,169313014784⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916466698289,0,false,-200216289600,-200216289536⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282419740038,0,true,169195717632,169195717696⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916603515514,0,false,-200052158272,-200052158208⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523302837,0,true,11674944,11675008⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499952715,0,false,-11675136,-11675072⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627652,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1282431168461,0,true,169205515968,169205516032⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨916592087091,0,false,-200065867328,-200065867264⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1282556565741,0,true,169313021952,169313022016⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨916466689811,0,false,-200216299776,-200216299712⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1069038599143,0,false,-30903277760,-30903277696⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1069080336720,0,false,-30860351296,-30860351232⟩
    { al := (681471/4096000), au := (1363791/8192000), zl := (7999/8000), zu := 1,
      A := ⟨182930978635,183044929487⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169215322432,169215322496⟩ : DyadicInterval 40),(⟨-200079587968,-200079587904⟩ : DyadicInterval 40),(⟨746834841041,746834860370⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169313014720,169313014784⟩ : DyadicInterval 40),(⟨-200216289600,-200216289536⟩ : DyadicInterval 40),(⟨746815698514,746815717843⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169195717632,169195717696⟩ : DyadicInterval 40),(⟨-200052158272,-200052158208⟩ : DyadicInterval 40),(⟨746838680864,746838700194⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169313014720,169313014784⟩ : DyadicInterval 40),(⟨-200216289600,-200216289536⟩ : DyadicInterval 40),(⟨746815698514,746815717843⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11675061⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11674944,11675008⟩ : DyadicInterval 40),(⟨-11675136,-11675072⟩ : DyadicInterval 40),(⟨762123383524,762123402853⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨182919540685,183044937965⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169205515968,169205516032⟩ : DyadicInterval 40),(⟨-200065867328,-200065867264⟩ : DyadicInterval 40),(⟨746836761830,746836781160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169313021952,169313022016⟩ : DyadicInterval 40),(⟨-200216299776,-200216299712⟩ : DyadicInterval 40),(⟨746815697112,746815716441⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30903277760,-30860351232⟩ : DyadicInterval 40),(⟨777553559232,777575041760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨169215322432,169313014784⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200216289600,-200079587904⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2806_ok : ecellOkT e2806 = true := by decide +kernel
theorem e2806_pos {a z : ℝ} (ha1 : ((681471/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1363791/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2806 e2806_ok ha1 ha2 hz1 hz2 hz

-- box ['1363791/8192000', '8529/51200', '7999/8000', '1']  interval_lower 147773569/549755813888
noncomputable def e2807 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282556557262,0,true,169313014720,169313014784⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916466698290,0,false,-200216289600,-200216289536⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282670508114,0,true,169410698304,169410698368⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916352747438,0,false,-200353008256,-200353008192⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282533676645,0,true,169293399424,169293399488⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916489578907,0,false,-200188839424,-200188839360⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523310404,0,true,11682560,11682624⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499945148,0,false,-11682752,-11682688⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627651,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1282545112189,0,true,169303203008,169303203072⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨916478143363,0,false,-200202558720,-200202558656⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1282670516590,0,true,169410705536,169410705600⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨916352738962,0,false,-200353018432,-200353018368⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1069000646623,0,false,-30942312832,-30942312768⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1069042412563,0,false,-30899355648,-30899355584⟩
    { al := (1363791/8192000), au := (8529/51200), zl := (7999/8000), zu := 1,
      A := ⟨183044929486,183158880338⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169313014720,169313014784⟩ : DyadicInterval 40),(⟨-200216289600,-200216289536⟩ : DyadicInterval 40),(⟨746815698514,746815717844⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169410698304,169410698368⟩ : DyadicInterval 40),(⟨-200353008256,-200353008192⟩ : DyadicInterval 40),(⟨746796543867,746796563196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169293399424,169293399488⟩ : DyadicInterval 40),(⟨-200188839424,-200188839360⟩ : DyadicInterval 40),(⟨746819543192,746819562521⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169410698304,169410698368⟩ : DyadicInterval 40),(⟨-200353008256,-200353008192⟩ : DyadicInterval 40),(⟨746796543867,746796563196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11682628⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11682560,11682624⟩ : DyadicInterval 40),(⟨-11682752,-11682688⟩ : DyadicInterval 40),(⟨762123383523,762123402852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨183033484413,183158888814⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169303203008,169303203072⟩ : DyadicInterval 40),(⟨-200202558720,-200202558656⟩ : DyadicInterval 40),(⟨746817621732,746817641062⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169410705536,169410705600⟩ : DyadicInterval 40),(⟨-200353018432,-200353018368⟩ : DyadicInterval 40),(⟨746796542463,746796561793⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30942312832,-30899355584⟩ : DyadicInterval 40),(⟨777573061408,777594559296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨169313014720,169410698368⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200353008256,-200216289536⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2807_ok : ecellOkT e2807 = true := by decide +kernel
theorem e2807_pos {a z : ℝ} (ha1 : ((1363791/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((8529/51200 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2807 e2807_ok ha1 ha2 hz1 hz2 hz

-- box ['8529/51200', '1365489/8192000', '999/1000', '7993/8000']  interval_lower 149154291/549755813888
noncomputable def e2808 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282670508113,0,true,169410698304,169410698368⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916352747439,0,false,-200353008256,-200353008192⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282784458965,0,true,169508373184,169508373248⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916238796587,0,false,-200489743872,-200489743808⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282487349232,0,true,169253682368,169253682432⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916535906320,0,false,-200133261888,-200133261824⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282624095238,0,true,169370912256,169370912320⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916399160314,0,false,-200297319872,-200297319808⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593402426,0,true,81771584,81771648⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429853126,0,false,-81777728,-81777664⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099605145855,0,true,93514048,93514112⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099418109697,0,false,-93522112,-93522048⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619821,0,false,-8000,-7936⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621695,0,false,-6144,-6080⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282578924814,0,true,169332189824,169332189888⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916444330738,0,false,-200243124928,-200243124864⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282704286288,0,true,169439652736,169439652800⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916318969264,0,false,-200393538688,-200393538624⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068989394736,0,false,-30953885888,-30953885824⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069031154084,0,false,-30910935104,-30910935040⟩
    { al := (8529/51200), au := (1365489/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨183158880337,183272831189⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169410698304,169410698368⟩ : DyadicInterval 40),(⟨-200353008256,-200353008192⟩ : DyadicInterval 40),(⟨746796543867,746796563196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169508373184,169508373248⟩ : DyadicInterval 40),(⟨-200489743872,-200489743808⟩ : DyadicInterval 40),(⟨746777377070,746777396400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169253682368,169253682432⟩ : DyadicInterval 40),(⟨-200133261888,-200133261824⟩ : DyadicInterval 40),(⟨746827326180,746827345509⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169370912256,169370912320⟩ : DyadicInterval 40),(⟨-200297319872,-200297319808⟩ : DyadicInterval 40),(⟨746804347127,746804366457⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨81774650,93518079⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81771584,81771648⟩ : DyadicInterval 40),(⟨-81777728,-81777664⟩ : DyadicInterval 40),(⟨762123380541,762123399871⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨93514048,93514112⟩ : DyadicInterval 40),(⟨-93522112,-93522048⟩ : DyadicInterval 40),(⟨762123379629,762123398959⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8000,-6080⟩ : DyadicInterval 40),(⟨762123386656,762123406880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183067297038,183192658512⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169332189824,169332189888⟩ : DyadicInterval 40),(⟨-200243124928,-200243124864⟩ : DyadicInterval 40),(⟨746811939588,746811958917⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169439652736,169439652800⟩ : DyadicInterval 40),(⟨-200393538688,-200393538624⟩ : DyadicInterval 40),(⟨746790863566,746790882895⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30953885888,-30910935040⟩ : DyadicInterval 40),(⟨777578851136,777600345824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169410698304,169508373248⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200489743872,-200353008192⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2808_ok : ecellOkT e2808 = true := by decide +kernel
theorem e2808_pos {a z : ℝ} (ha1 : ((8529/51200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1365489/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2808 e2808_ok ha1 ha2 hz1 hz2 hz

-- box ['1365489/8192000', '683169/4096000', '999/1000', '7993/8000']  interval_lower 149846787/549755813888
noncomputable def e2809 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282784458964,0,true,169508373184,169508373248⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916238796588,0,false,-200489743872,-200489743808⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282898409817,0,true,169606039424,169606039488⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916124845735,0,false,-200626496512,-200626496448⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282601186132,0,true,169351273536,169351273600⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916422069420,0,false,-200269833472,-200269833408⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282737946383,0,true,169468505216,169468505280⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916285309169,0,false,-200433928896,-200433928832⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593455399,0,true,81824576,81824640⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429800153,0,false,-81830720,-81830656⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099605206402,0,true,93574592,93574656⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099418049150,0,false,-93582656,-93582592⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619811,0,false,-8000,-7936⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621687,0,false,-6144,-6080⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282692818688,0,true,169429822848,169429822912⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916330436864,0,false,-200379778560,-200379778496⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282818187289,0,true,169537282368,169537282432⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916205068263,0,false,-200530219520,-200530219456⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068951428218,0,false,-30992937152,-30992937088⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068993215914,0,false,-30949955648,-30949955584⟩
    { al := (1365489/8192000), au := (683169/4096000), zl := (999/1000), zu := (7993/8000),
      A := ⟨183272831188,183386782041⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169508373184,169508373248⟩ : DyadicInterval 40),(⟨-200489743872,-200489743808⟩ : DyadicInterval 40),(⟨746777377070,746777396400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169606039424,169606039488⟩ : DyadicInterval 40),(⟨-200626496512,-200626496448⟩ : DyadicInterval 40),(⟨746758198113,746758217442⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169351273536,169351273600⟩ : DyadicInterval 40),(⟨-200269833472,-200269833408⟩ : DyadicInterval 40),(⟨746808198051,746808217381⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169468505216,169468505280⟩ : DyadicInterval 40),(⟨-200433928896,-200433928832⟩ : DyadicInterval 40),(⟨746785202036,746785221365⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨81827623,93578626⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81824576,81824640⟩ : DyadicInterval 40),(⟨-81830720,-81830656⟩ : DyadicInterval 40),(⟨762123380534,762123399863⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨93574592,93574656⟩ : DyadicInterval 40),(⟨-93582656,-93582592⟩ : DyadicInterval 40),(⟨762123379619,762123398948⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8000,-6080⟩ : DyadicInterval 40),(⟨762123386656,762123406880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183181190912,183306559513⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169429822848,169429822912⟩ : DyadicInterval 40),(⟨-200379778560,-200379778496⟩ : DyadicInterval 40),(⟨746792792150,746792811480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169537282368,169537282432⟩ : DyadicInterval 40),(⟨-200530219520,-200530219456⟩ : DyadicInterval 40),(⟨746771701528,746771720858⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30992937152,-30949955584⟩ : DyadicInterval 40),(⟨777598361408,777619871456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169508373184,169606039488⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200626496512,-200489743808⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2809_ok : ecellOkT e2809 = true := by decide +kernel
theorem e2809_pos {a z : ℝ} (ha1 : ((1365489/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((683169/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2809 e2809_ok ha1 ha2 hz1 hz2 hz

-- box ['8529/51200', '1365489/8192000', '7993/8000', '3997/4000']  interval_lower 298111197/1099511627776
noncomputable def e2810 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282670508113,0,true,169410698304,169410698368⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916352747439,0,false,-200353008256,-200353008192⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282784458965,0,true,169508373184,169508373248⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916238796587,0,false,-200489743872,-200489743808⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282510244092,0,true,169273310592,169273310656⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916513011460,0,false,-200160727744,-200160727680⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282647004342,0,true,169390550528,169390550592⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916376251210,0,false,-200324806912,-200324806848⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581720477,0,true,70090432,70090496⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441535075,0,false,-70094976,-70094912⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593456339,0,true,81825472,81825536⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429799213,0,false,-81831616,-81831552⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621686,0,false,-6144,-6080⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623308,0,false,-4480,-4416⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282590372029,0,true,169342003072,169342003136⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916432883523,0,false,-200256858880,-200256858816⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282715740649,0,true,169449471168,169449471232⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916307514903,0,false,-200407283136,-200407283072⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068985577731,0,false,-30957811904,-30957811840⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069027342071,0,false,-30914855808,-30914855744⟩
    { al := (8529/51200), au := (1365489/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨183158880337,183272831189⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169410698304,169410698368⟩ : DyadicInterval 40),(⟨-200353008256,-200353008192⟩ : DyadicInterval 40),(⟨746796543867,746796563196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169508373184,169508373248⟩ : DyadicInterval 40),(⟨-200489743872,-200489743808⟩ : DyadicInterval 40),(⟨746777377070,746777396400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169273310592,169273310656⟩ : DyadicInterval 40),(⟨-200160727744,-200160727680⟩ : DyadicInterval 40),(⟨746823480087,746823499417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169390550528,169390550592⟩ : DyadicInterval 40),(⟨-200324806912,-200324806848⟩ : DyadicInterval 40),(⟨746800495750,746800515080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨70092701,81828563⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70090432,70090496⟩ : DyadicInterval 40),(⟨-70094976,-70094912⟩ : DyadicInterval 40),(⟨762123381355,762123400684⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81825472,81825536⟩ : DyadicInterval 40),(⟨-81831616,-81831552⟩ : DyadicInterval 40),(⟨762123380533,762123399863⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6144,-4416⟩ : DyadicInterval 40),(⟨762123385824,762123405952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183078744253,183204112873⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169342003072,169342003136⟩ : DyadicInterval 40),(⟨-200256858880,-200256858816⟩ : DyadicInterval 40),(⟨746810015670,746810034999⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169449471168,169449471232⟩ : DyadicInterval 40),(⟨-200407283136,-200407283072⟩ : DyadicInterval 40),(⟨746788937111,746788956440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30957811904,-30914855744⟩ : DyadicInterval 40),(⟨777580811488,777602308832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169410698304,169508373248⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200489743872,-200353008192⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2810_ok : ecellOkT e2810 = true := by decide +kernel
theorem e2810_pos {a z : ℝ} (ha1 : ((8529/51200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1365489/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2810 e2810_ok ha1 ha2 hz1 hz2 hz

-- box ['1365489/8192000', '683169/4096000', '7993/8000', '3997/4000']  interval_lower 74873939/274877906944
noncomputable def e2811 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282784458964,0,true,169508373184,169508373248⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916238796588,0,false,-200489743872,-200489743808⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282898409817,0,true,169606039424,169606039488⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916124845735,0,false,-200626496512,-200626496448⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282624095236,0,true,169370912192,169370912256⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916399160316,0,false,-200297319872,-200297319808⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282760869731,0,true,169488153984,169488154048⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916262385821,0,false,-200461436544,-200461436480⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581765883,0,true,70135808,70135872⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441489669,0,false,-70140352,-70140288⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593509317,0,true,81878464,81878528⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429746235,0,false,-81884608,-81884544⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621678,0,false,-6144,-6080⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623302,0,false,-4480,-4416⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282704273021,0,true,169439641344,169439641408⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916318982531,0,false,-200393522752,-200393522688⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282829648769,0,true,169547105984,169547106048⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916193606783,0,false,-200543974208,-200543974144⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068947606467,0,false,-30996868160,-30996868096⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068989399158,0,false,-30953881344,-30953881280⟩
    { al := (1365489/8192000), au := (683169/4096000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨183272831188,183386782041⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169508373184,169508373248⟩ : DyadicInterval 40),(⟨-200489743872,-200489743808⟩ : DyadicInterval 40),(⟨746777377070,746777396400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169606039424,169606039488⟩ : DyadicInterval 40),(⟨-200626496512,-200626496448⟩ : DyadicInterval 40),(⟨746758198113,746758217442⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169370912192,169370912256⟩ : DyadicInterval 40),(⟨-200297319872,-200297319808⟩ : DyadicInterval 40),(⟨746804347165,746804366495⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169488153984,169488154048⟩ : DyadicInterval 40),(⟨-200461436544,-200461436480⟩ : DyadicInterval 40),(⟨746781345847,746781365176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨70138107,81881541⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70135808,70135872⟩ : DyadicInterval 40),(⟨-70140352,-70140288⟩ : DyadicInterval 40),(⟨762123381349,762123400679⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81878464,81878528⟩ : DyadicInterval 40),(⟨-81884608,-81884544⟩ : DyadicInterval 40),(⟨762123380525,762123399855⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6144,-4416⟩ : DyadicInterval 40),(⟨762123385824,762123405952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183192645245,183318020993⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169439641344,169439641408⟩ : DyadicInterval 40),(⟨-200393522752,-200393522688⟩ : DyadicInterval 40),(⟨746790865802,746790885132⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169547105984,169547106048⟩ : DyadicInterval 40),(⟨-200543974208,-200543974144⟩ : DyadicInterval 40),(⟨746769772676,746769792006⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30996868160,-30953881280⟩ : DyadicInterval 40),(⟨777600324256,777621836960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169508373184,169606039488⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200626496512,-200489743808⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2811_ok : ecellOkT e2811 = true := by decide +kernel
theorem e2811_pos {a z : ℝ} (ha1 : ((1365489/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((683169/4096000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2811 e2811_ok ha1 ha2 hz1 hz2 hz

-- box ['683169/4096000', '1367187/8192000', '999/1000', '7993/8000']  interval_lower 301081927/1099511627776
noncomputable def e2812 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282898409816,0,true,169606039424,169606039488⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916124845736,0,false,-200626496512,-200626496448⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283012360668,0,true,169703696960,169703697024⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916010894884,0,false,-200763266176,-200763266112⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282715023033,0,true,169448856064,169448856128⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916308232519,0,false,-200406422016,-200406421952⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282851797527,0,true,169566089536,169566089600⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916171458025,0,false,-200570554944,-200570554880⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593508378,0,true,81877504,81877568⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429747174,0,false,-81883712,-81883648⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099605266952,0,true,93635136,93635200⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099417988600,0,false,-93643200,-93643136⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619801,0,false,-8000,-7936⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621679,0,false,-6144,-6080⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282806712566,0,true,169527447232,169527447296⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916216542986,0,false,-200516449152,-200516449088⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282932088287,0,true,169634903296,169634903360⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916091167265,0,false,-200666917376,-200666917312⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068913438103,0,false,-31032014080,-31032014016⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068955254147,0,false,-30989001856,-30989001792⟩
    { al := (683169/4096000), au := (1367187/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨183386782040,183500732892⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169606039424,169606039488⟩ : DyadicInterval 40),(⟨-200626496512,-200626496448⟩ : DyadicInterval 40),(⟨746758198113,746758217443⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169703696960,169703697024⟩ : DyadicInterval 40),(⟨-200763266176,-200763266112⟩ : DyadicInterval 40),(⟨746739007030,746739026360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169448856064,169448856128⟩ : DyadicInterval 40),(⟨-200406422016,-200406421952⟩ : DyadicInterval 40),(⟨746789057786,746789077115⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169566089536,169566089600⟩ : DyadicInterval 40),(⟨-200570554944,-200570554880⟩ : DyadicInterval 40),(⟨746766044825,746766064155⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨81880602,93639176⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81877504,81877568⟩ : DyadicInterval 40),(⟨-81883712,-81883648⟩ : DyadicInterval 40),(⟨762123380558,762123399887⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨93635136,93635200⟩ : DyadicInterval 40),(⟨-93643200,-93643136⟩ : DyadicInterval 40),(⟨762123379608,762123398938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8000,-6080⟩ : DyadicInterval 40),(⟨762123386656,762123406880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183295084790,183420460511⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169527447232,169527447296⟩ : DyadicInterval 40),(⟨-200516449152,-200516449088⟩ : DyadicInterval 40),(⟨746773632550,746773651879⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169634903296,169634903360⟩ : DyadicInterval 40),(⟨-200666917376,-200666917312⟩ : DyadicInterval 40),(⟨746752527388,746752546717⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31032014080,-30989001792⟩ : DyadicInterval 40),(⟨777617884512,777639409920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169606039424,169703697024⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200763266176,-200626496448⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2812_ok : ecellOkT e2812 = true := by decide +kernel
theorem e2812_pos {a z : ℝ} (ha1 : ((683169/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1367187/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2812 e2812_ok ha1 ha2 hz1 hz2 hz

-- box ['1367187/8192000', '342009/2048000', '999/1000', '7993/8000']  interval_lower 18904591/68719476736
noncomputable def e2813 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283012360667,0,true,169703696960,169703697024⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916010894885,0,false,-200763266176,-200763266112⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283126311519,0,true,169801345856,169801345920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915896944033,0,false,-200900052864,-200900052800⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282828859934,0,true,169546429888,169546429952⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916194395618,0,false,-200543027520,-200543027456⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282965648671,0,true,169663665152,169663665216⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916057606881,0,false,-200707198016,-200707197952⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593561359,0,true,81930496,81930560⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429694193,0,false,-81936640,-81936576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099605327508,0,true,93695680,93695744⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099417928044,0,false,-93703744,-93703680⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619790,0,false,-8000,-7936⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621671,0,false,-6144,-6080⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282920606439,0,true,169625062912,169625062976⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916102649113,0,false,-200653136704,-200653136640⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283045989280,0,true,169732515520,169732515584⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915977266272,0,false,-200803632192,-200803632128⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068875424391,0,false,-31071116608,-31071116544⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068917268786,0,false,-31028073728,-31028073664⟩
    { al := (1367187/8192000), au := (342009/2048000), zl := (999/1000), zu := (7993/8000),
      A := ⟨183500732891,183614683743⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169703696960,169703697024⟩ : DyadicInterval 40),(⟨-200763266176,-200763266112⟩ : DyadicInterval 40),(⟨746739007031,746739026360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169801345856,169801345920⟩ : DyadicInterval 40),(⟨-200900052864,-200900052800⟩ : DyadicInterval 40),(⟨746719803785,746719823114⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169546429888,169546429952⟩ : DyadicInterval 40),(⟨-200543027520,-200543027456⟩ : DyadicInterval 40),(⟨746769905420,746769924749⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169663665152,169663665216⟩ : DyadicInterval 40),(⟨-200707198016,-200707197952⟩ : DyadicInterval 40),(⟨746746875534,746746894864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨81933583,93699732⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81930496,81930560⟩ : DyadicInterval 40),(⟨-81936640,-81936576⟩ : DyadicInterval 40),(⟨762123380518,762123399847⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨93695680,93695744⟩ : DyadicInterval 40),(⟨-93703744,-93703680⟩ : DyadicInterval 40),(⟨762123379598,762123398928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8000,-6080⟩ : DyadicInterval 40),(⟨762123386656,762123406880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183408978663,183534361504⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169625062912,169625062976⟩ : DyadicInterval 40),(⟨-200653136704,-200653136640⟩ : DyadicInterval 40),(⟨746754460824,746754480153⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169732515520,169732515584⟩ : DyadicInterval 40),(⟨-200803632192,-200803632128⟩ : DyadicInterval 40),(⟨746733341117,746733360447⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31071116608,-31028073664⟩ : DyadicInterval 40),(⟨777637420448,777658961184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169703696960,169801345920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200900052864,-200763266112⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2813_ok : ecellOkT e2813 = true := by decide +kernel
theorem e2813_pos {a z : ℝ} (ha1 : ((1367187/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((342009/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2813 e2813_ok ha1 ha2 hz1 hz2 hz

-- box ['683169/4096000', '1367187/8192000', '7993/8000', '3997/4000']  interval_lower 150441829/549755813888
noncomputable def e2814 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282898409816,0,true,169606039424,169606039488⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916124845736,0,false,-200626496512,-200626496448⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283012360668,0,true,169703696960,169703697024⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916010894884,0,false,-200763266176,-200763266112⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282737946381,0,true,169468505216,169468505280⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916285309171,0,false,-200433928896,-200433928832⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282874735119,0,true,169585748800,169585748864⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916148520433,0,false,-200598083072,-200598083008⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581811294,0,true,70181248,70181312⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441444258,0,false,-70185792,-70185728⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593562299,0,true,81931456,81931520⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429693253,0,false,-81937600,-81937536⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621670,0,false,-6144,-6080⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623297,0,false,-4480,-4416⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282818174024,0,true,169537270976,169537271040⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916205081528,0,false,-200530203648,-200530203584⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282943556893,0,true,169644732160,169644732224⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916079698659,0,false,-200680682304,-200680682240⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068909611599,0,false,-31035950144,-31035950080⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068951432642,0,false,-30992932608,-30992932544⟩
    { al := (683169/4096000), au := (1367187/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨183386782040,183500732892⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169606039424,169606039488⟩ : DyadicInterval 40),(⟨-200626496512,-200626496448⟩ : DyadicInterval 40),(⟨746758198113,746758217443⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169703696960,169703697024⟩ : DyadicInterval 40),(⟨-200763266176,-200763266112⟩ : DyadicInterval 40),(⟨746739007030,746739026360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169468505216,169468505280⟩ : DyadicInterval 40),(⟨-200433928896,-200433928832⟩ : DyadicInterval 40),(⟨746785202036,746785221365⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169585748800,169585748864⟩ : DyadicInterval 40),(⟨-200598083072,-200598083008⟩ : DyadicInterval 40),(⟨746762183765,746762203094⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨70183518,81934523⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70181248,70181312⟩ : DyadicInterval 40),(⟨-70185792,-70185728⟩ : DyadicInterval 40),(⟨762123381343,762123400673⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81931456,81931520⟩ : DyadicInterval 40),(⟨-81937600,-81937536⟩ : DyadicInterval 40),(⟨762123380518,762123399847⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6144,-4416⟩ : DyadicInterval 40),(⟨762123385824,762123405952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183306546248,183431929117⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169537270976,169537271040⟩ : DyadicInterval 40),(⟨-200530203648,-200530203584⟩ : DyadicInterval 40),(⟨746771703793,746771723122⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169644732160,169644732224⟩ : DyadicInterval 40),(⟨-200680682304,-200680682240⟩ : DyadicInterval 40),(⟨746750596098,746750615427⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31035950144,-30992932544⟩ : DyadicInterval 40),(⟨777619849888,777641377952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169606039424,169703697024⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200763266176,-200626496448⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2814_ok : ecellOkT e2814 = true := by decide +kernel
theorem e2814_pos {a z : ℝ} (ha1 : ((683169/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1367187/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2814 e2814_ok ha1 ha2 hz1 hz2 hz

-- box ['1367187/8192000', '342009/2048000', '7993/8000', '3997/4000']  interval_lower 302274867/1099511627776
noncomputable def e2815 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283012360667,0,true,169703696960,169703697024⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916010894885,0,false,-200763266176,-200763266112⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283126311519,0,true,169801345856,169801345920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915896944033,0,false,-200900052864,-200900052800⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282851797525,0,true,169566089536,169566089600⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916171458027,0,false,-200570554944,-200570554880⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282988600507,0,true,169683334912,169683334976⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916034655045,0,false,-200734746624,-200734746560⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581856706,0,true,70226624,70226688⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441398846,0,false,-70231232,-70231168⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593615286,0,true,81984448,81984512⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429640266,0,false,-81990592,-81990528⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621662,0,false,-6144,-6080⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623291,0,false,-4544,-4480⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282932075019,0,true,169634891904,169634891968⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916091180533,0,false,-200666901440,-200666901376⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283057465012,0,true,169742349696,169742349760⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915965790540,0,false,-200817407424,-200817407360⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068871593131,0,false,-31075057728,-31075057664⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068913442530,0,false,-31032009536,-31032009472⟩
    { al := (1367187/8192000), au := (342009/2048000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨183500732891,183614683743⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169703696960,169703697024⟩ : DyadicInterval 40),(⟨-200763266176,-200763266112⟩ : DyadicInterval 40),(⟨746739007031,746739026360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169801345856,169801345920⟩ : DyadicInterval 40),(⟨-200900052864,-200900052800⟩ : DyadicInterval 40),(⟨746719803785,746719823114⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169566089536,169566089600⟩ : DyadicInterval 40),(⟨-200570554944,-200570554880⟩ : DyadicInterval 40),(⟨746766044826,746766064155⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169683334912,169683334976⟩ : DyadicInterval 40),(⟨-200734746624,-200734746560⟩ : DyadicInterval 40),(⟨746743009595,746743028925⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨70228930,81987510⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70226624,70226688⟩ : DyadicInterval 40),(⟨-70231232,-70231168⟩ : DyadicInterval 40),(⟨762123381370,762123400699⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81984448,81984512⟩ : DyadicInterval 40),(⟨-81990592,-81990528⟩ : DyadicInterval 40),(⟨762123380510,762123399839⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6144,-4480⟩ : DyadicInterval 40),(⟨762123385856,762123405952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183420447243,183545837236⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169634891904,169634891968⟩ : DyadicInterval 40),(⟨-200666901440,-200666901376⟩ : DyadicInterval 40),(⟨746752529629,746752548959⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169742349696,169742349760⟩ : DyadicInterval 40),(⟨-200817407424,-200817407360⟩ : DyadicInterval 40),(⟨746731407375,746731426704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31075057728,-31032009472⟩ : DyadicInterval 40),(⟨777639388352,777660931744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169703696960,169801345920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200900052864,-200763266112⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2815_ok : ecellOkT e2815 = true := by decide +kernel
theorem e2815_pos {a z : ℝ} (ha1 : ((1367187/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((342009/2048000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2815 e2815_ok ha1 ha2 hz1 hz2 hz

-- box ['8529/51200', '1365489/8192000', '3997/4000', '1599/1600']  interval_lower 148957017/549755813888
noncomputable def e2816 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282670508113,0,true,169410698304,169410698368⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916352747439,0,false,-200353008256,-200353008192⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282784458965,0,true,169508373184,169508373248⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916238796587,0,false,-200489743872,-200489743808⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282533138952,0,true,169292938432,169292938496⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916490116600,0,false,-200188194368,-200188194304⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282669913446,0,true,169410188544,169410188608⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916353342106,0,false,-200352294720,-200352294656⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570038468,0,true,58409088,58409152⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453217084,0,false,-58412288,-58412224⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581766762,0,true,70136704,70136768⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441488790,0,false,-70141248,-70141184⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623301,0,false,-4480,-4416⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624673,0,false,-3136,-3072⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282601819268,0,true,169351816320,169351816384⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916421436284,0,false,-200270593088,-200270593024⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282727195042,0,true,169459289536,169459289600⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916296060510,0,false,-200421027776,-200421027712⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068981760478,0,false,-30961738176,-30961738112⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069023529812,0,false,-30918776768,-30918776704⟩
    { al := (8529/51200), au := (1365489/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨183158880337,183272831189⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169410698304,169410698368⟩ : DyadicInterval 40),(⟨-200353008256,-200353008192⟩ : DyadicInterval 40),(⟨746796543867,746796563196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169508373184,169508373248⟩ : DyadicInterval 40),(⟨-200489743872,-200489743808⟩ : DyadicInterval 40),(⟨746777377070,746777396400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169292938432,169292938496⟩ : DyadicInterval 40),(⟨-200188194368,-200188194304⟩ : DyadicInterval 40),(⟨746819633558,746819652888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169410188544,169410188608⟩ : DyadicInterval 40),(⟨-200352294720,-200352294656⟩ : DyadicInterval 40),(⟨746796643861,746796663190⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨58410692,70138986⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58409088,58409152⟩ : DyadicInterval 40),(⟨-58412288,-58412224⟩ : DyadicInterval 40),(⟨762123382048,762123401378⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70136704,70136768⟩ : DyadicInterval 40),(⟨-70141248,-70141184⟩ : DyadicInterval 40),(⟨762123381349,762123400678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4480,-3072⟩ : DyadicInterval 40),(⟨762123385152,762123405120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183090191492,183215567266⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169351816320,169351816384⟩ : DyadicInterval 40),(⟨-200270593088,-200270593024⟩ : DyadicInterval 40),(⟨746808091610,746808110939⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169459289536,169459289600⟩ : DyadicInterval 40),(⟨-200421027776,-200421027712⟩ : DyadicInterval 40),(⟨746787010523,746787029852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30961738176,-30918776704⟩ : DyadicInterval 40),(⟨777582771968,777604271968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169410698304,169508373248⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200489743872,-200353008192⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2816_ok : ecellOkT e2816 = true := by decide +kernel
theorem e2816_pos {a z : ℝ} (ha1 : ((8529/51200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1365489/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2816 e2816_ok ha1 ha2 hz1 hz2 hz

-- box ['1365489/8192000', '683169/4096000', '3997/4000', '1599/1600']  interval_lower 149648989/549755813888
noncomputable def e2817 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282784458964,0,true,169508373184,169508373248⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916238796588,0,false,-200489743872,-200489743808⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282898409817,0,true,169606039424,169606039488⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916124845735,0,false,-200626496512,-200626496448⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282647004340,0,true,169390550528,169390550592⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916376251212,0,false,-200324806912,-200324806848⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282783793079,0,true,169507802432,169507802496⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916239462473,0,false,-200488944768,-200488944704⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570076306,0,true,58446976,58447040⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453179246,0,false,-58450112,-58450048⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581812172,0,true,70182144,70182208⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441443380,0,false,-70186688,-70186624⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623295,0,false,-4544,-4480⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624669,0,false,-3136,-3072⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282715727387,0,true,169449459776,169449459840⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916307528165,0,false,-200407267200,-200407267136⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282841110287,0,true,169556929600,169556929664⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916182145265,0,false,-200557729088,-200557729024⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068943784463,0,false,-31000799488,-31000799424⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068985582152,0,false,-30957807360,-30957807296⟩
    { al := (1365489/8192000), au := (683169/4096000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨183272831188,183386782041⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169508373184,169508373248⟩ : DyadicInterval 40),(⟨-200489743872,-200489743808⟩ : DyadicInterval 40),(⟨746777377070,746777396400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169606039424,169606039488⟩ : DyadicInterval 40),(⟨-200626496512,-200626496448⟩ : DyadicInterval 40),(⟨746758198113,746758217442⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169390550528,169390550592⟩ : DyadicInterval 40),(⟨-200324806912,-200324806848⟩ : DyadicInterval 40),(⟨746800495751,746800515080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169507802432,169507802496⟩ : DyadicInterval 40),(⟨-200488944768,-200488944704⟩ : DyadicInterval 40),(⟨746777489100,746777508430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨58448530,70184396⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58446976,58447040⟩ : DyadicInterval 40),(⟨-58450112,-58450048⟩ : DyadicInterval 40),(⟨762123382012,762123401342⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70182144,70182208⟩ : DyadicInterval 40),(⟨-70186688,-70186624⟩ : DyadicInterval 40),(⟨762123381343,762123400673⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4544,-3072⟩ : DyadicInterval 40),(⟨762123385152,762123405152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183204099611,183329482511⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169449459776,169449459840⟩ : DyadicInterval 40),(⟨-200407267200,-200407267136⟩ : DyadicInterval 40),(⟨746788939346,746788958676⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169556929600,169556929664⟩ : DyadicInterval 40),(⟨-200557729088,-200557729024⟩ : DyadicInterval 40),(⟨746767843652,746767862981⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31000799488,-30957807296⟩ : DyadicInterval 40),(⟨777602287264,777623802624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169508373184,169606039488⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200626496512,-200489743808⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2817_ok : ecellOkT e2817 = true := by decide +kernel
theorem e2817_pos {a z : ℝ} (ha1 : ((1365489/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((683169/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2817 e2817_ok ha1 ha2 hz1 hz2 hz

-- box ['8529/51200', '1365489/8192000', '1599/1600', '1999/2000']  interval_lower 297716499/1099511627776
noncomputable def e2818 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282670508113,0,true,169410698304,169410698368⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916352747439,0,false,-200353008256,-200353008192⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282784458965,0,true,169508373184,169508373248⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916238796587,0,false,-200489743872,-200489743808⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282556033812,0,true,169312565952,169312566016⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916467221740,0,false,-200215661632,-200215661568⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282692822550,0,true,169429826176,169429826240⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916330433002,0,false,-200379783168,-200379783104⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558356399,0,true,46727616,46727680⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464899153,0,false,-46729664,-46729600⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570077124,0,true,58447744,58447808⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453178428,0,false,-58450944,-58450880⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624668,0,false,-3136,-3072⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625791,0,false,-2048,-1984⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282613266539,0,true,169361629440,169361629504⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916409989013,0,false,-200284327488,-200284327424⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282738649465,0,true,169469107840,169469107904⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916284606087,0,false,-200434772608,-200434772544⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068977942975,0,false,-30965664704,-30965664640⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069019717304,0,false,-30922697984,-30922697920⟩
    { al := (8529/51200), au := (1365489/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨183158880337,183272831189⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169410698304,169410698368⟩ : DyadicInterval 40),(⟨-200353008256,-200353008192⟩ : DyadicInterval 40),(⟨746796543867,746796563196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169508373184,169508373248⟩ : DyadicInterval 40),(⟨-200489743872,-200489743808⟩ : DyadicInterval 40),(⟨746777377070,746777396400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169312565952,169312566016⟩ : DyadicInterval 40),(⟨-200215661632,-200215661568⟩ : DyadicInterval 40),(⟨746815786502,746815805832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169429826176,169429826240⟩ : DyadicInterval 40),(⟨-200379783168,-200379783104⟩ : DyadicInterval 40),(⟨746792791480,746792810809⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨46728623,58449348⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46727616,46727680⟩ : DyadicInterval 40),(⟨-46729664,-46729600⟩ : DyadicInterval 40),(⟨762123382590,762123401919⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58447744,58447808⟩ : DyadicInterval 40),(⟨-58450944,-58450880⟩ : DyadicInterval 40),(⟨762123382044,762123401373⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3136,-1984⟩ : DyadicInterval 40),(⟨762123384608,762123404448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183101638763,183227021689⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169361629440,169361629504⟩ : DyadicInterval 40),(⟨-200284327488,-200284327424⟩ : DyadicInterval 40),(⟨746806167453,746806186783⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169469107840,169469107904⟩ : DyadicInterval 40),(⟨-200434772608,-200434772544⟩ : DyadicInterval 40),(⟨746785083801,746785103130⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30965664704,-30922697920⟩ : DyadicInterval 40),(⟨777584732576,777606235232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169410698304,169508373248⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200489743872,-200353008192⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2818_ok : ecellOkT e2818 = true := by decide +kernel
theorem e2818_pos {a z : ℝ} (ha1 : ((8529/51200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1365489/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2818 e2818_ok ha1 ha2 hz1 hz2 hz

-- box ['1365489/8192000', '683169/4096000', '1599/1600', '1999/2000']  interval_lower 149550083/549755813888
noncomputable def e2819 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282784458964,0,true,169508373184,169508373248⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916238796588,0,false,-200489743872,-200489743808⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282898409817,0,true,169606039424,169606039488⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916124845735,0,false,-200626496512,-200626496448⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282669913444,0,true,169410188544,169410188608⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916353342108,0,false,-200352294720,-200352294656⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282806716427,0,true,169527450560,169527450624⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916216539125,0,false,-200516453760,-200516453696⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558386670,0,true,46757888,46757952⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464868882,0,false,-46759936,-46759872⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570114967,0,true,58485632,58485696⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453140585,0,false,-58488768,-58488704⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624664,0,false,-3136,-3072⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625788,0,false,-2048,-1984⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282727181780,0,true,169459278144,169459278208⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916296073772,0,false,-200421011840,-200421011776⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282852571831,0,true,169566753152,169566753216⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916170683721,0,false,-200571484224,-200571484160⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068939962213,0,false,-31004731008,-31004730944⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068981764898,0,false,-30961733632,-30961733568⟩
    { al := (1365489/8192000), au := (683169/4096000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨183272831188,183386782041⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169508373184,169508373248⟩ : DyadicInterval 40),(⟨-200489743872,-200489743808⟩ : DyadicInterval 40),(⟨746777377070,746777396400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169606039424,169606039488⟩ : DyadicInterval 40),(⟨-200626496512,-200626496448⟩ : DyadicInterval 40),(⟨746758198113,746758217442⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169410188544,169410188608⟩ : DyadicInterval 40),(⟨-200352294720,-200352294656⟩ : DyadicInterval 40),(⟨746796643861,746796663191⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169527450560,169527450624⟩ : DyadicInterval 40),(⟨-200516453760,-200516453696⟩ : DyadicInterval 40),(⟨746773631878,746773651208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨46758894,58487191⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46757888,46757952⟩ : DyadicInterval 40),(⟨-46759936,-46759872⟩ : DyadicInterval 40),(⟨762123382587,762123401916⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58485632,58485696⟩ : DyadicInterval 40),(⟨-58488768,-58488704⟩ : DyadicInterval 40),(⟨762123382008,762123401337⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3136,-1984⟩ : DyadicInterval 40),(⟨762123384608,762123404448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183215554004,183340944055⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169459278144,169459278208⟩ : DyadicInterval 40),(⟨-200421011840,-200421011776⟩ : DyadicInterval 40),(⟨746787012758,746787032087⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169566753152,169566753216⟩ : DyadicInterval 40),(⟨-200571484224,-200571484160⟩ : DyadicInterval 40),(⟨746765914522,746765933852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31004731008,-30961733568⟩ : DyadicInterval 40),(⟨777604250400,777625768384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169508373184,169606039488⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200626496512,-200489743808⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2819_ok : ecellOkT e2819 = true := by decide +kernel
theorem e2819_pos {a z : ℝ} (ha1 : ((1365489/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((683169/4096000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2819 e2819_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B046

end


