-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B005
-- name    : CK_CKLaneC2R_EpCells_B005
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:24:43.221513+00:00
-- url     : https://prove2.me/theorems/d51f9398-b14b-498c-9779-3d2218dfa479
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B005` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B005` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B005` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B005 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B005.lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheckT

-- ===== source module CKLaneC2R.EpCells.B005 =====
section

namespace CKLaneC2R.EpCells.B005

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['227463/1024000', '18231/81920', '1999/2000', '1']  interval_lower 131777033/1099511627776
noncomputable def e300 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1343748164288,0,true,220558448448,220558448512⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨855275091264,0,false,-276195368320,-276195368256⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1344203967693,0,true,220931342848,220931342912⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨854819287859,0,false,-276781489344,-276781489280⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1343626046019,0,true,220458521536,220458521600⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨855397209533,0,false,-276038388544,-276038388480⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575087367,0,true,63457728,63457792⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448168185,0,false,-63461440,-63461376⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624113,0,false,-3712,-3648⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1343687099586,0,true,220508481600,220508481664⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨855336155966,0,false,-276116868480,-276116868416⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1344203976261,0,true,220931349824,220931349888⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨854819279291,0,false,-276781500352,-276781500288⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1045056227856,0,false,-55850150464,-55850150400⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1045286042956,0,false,-55608386880,-55608386816⟩
    { al := (227463/1024000), au := (18231/81920), zl := (1999/2000), zu := 1,
      A := ⟨244236536512,244692339917⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨220558448448,220558448512⟩ : DyadicInterval 40),(⟨-276195368320,-276195368256⟩ : DyadicInterval 40),(⟨734769424823,734769444153⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨220931342848,220931342912⟩ : DyadicInterval 40),(⟨-276781489344,-276781489280⟩ : DyadicInterval 40),(⟨734666360585,734666379915⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨220458521536,220458521600⟩ : DyadicInterval 40),(⟨-276038388544,-276038388480⟩ : DyadicInterval 40),(⟨734797003912,734797023241⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨220931342848,220931342912⟩ : DyadicInterval 40),(⟨-276781489344,-276781489280⟩ : DyadicInterval 40),(⟨734666360585,734666379915⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,63459591⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63457728,63457792⟩ : DyadicInterval 40),(⟨-63461440,-63461376⟩ : DyadicInterval 40),(⟨762123381745,762123401074⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3712,0⟩ : DyadicInterval 40),(⟨762123383616,762123404736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨244175471810,244692348485⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨220508481600,220508481664⟩ : DyadicInterval 40),(⟨-276116868480,-276116868416⟩ : DyadicInterval 40),(⟨734783217393,734783236723⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨220931349824,220931349888⟩ : DyadicInterval 40),(⟨-276781500352,-276781500288⟩ : DyadicInterval 40),(⟨734666358661,734666377991⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-55850150464,-55608386816⟩ : DyadicInterval 40),(⟨789927577024,790048478112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨220558448448,220931342912⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-276781489344,-276195368256⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e300_ok : ecellOkT e300 = true := by decide +kernel
theorem e300_pos {a z : ℝ} (ha1 : ((227463/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((18231/81920 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e300 e300_ok ha1 ha2 hz1 hz2 hz

-- box ['18231/81920', '28539/128000', '1999/2000', '1']  interval_lower 143463173/1099511627776
noncomputable def e301 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1344203967692,0,true,220931342848,220931342912⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨854819287860,0,false,-276781489344,-276781489280⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1344659771098,0,true,221304110784,221304110848⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨854363484454,0,false,-277367923008,-277367922944⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1344081621522,0,true,220831263424,220831263488⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨854941634030,0,false,-276624132800,-276624132736⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575214515,0,true,63584896,63584960⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448041037,0,false,-63588608,-63588544⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624098,0,false,-3712,-3648⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1344142789039,0,true,220881299712,220881299776⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨854880466513,0,false,-276702801088,-276702801024⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1344659779659,0,true,221304117824,221304117888⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨854363475893,0,false,-277367934016,-277367933952⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1044853164096,0,false,-56063816192,-56063816128⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1045083458443,0,false,-55821501376,-55821501312⟩
    { al := (18231/81920), au := (28539/128000), zl := (1999/2000), zu := 1,
      A := ⟨244692339916,245148143322⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨220931342848,220931342912⟩ : DyadicInterval 40),(⟨-276781489344,-276781489280⟩ : DyadicInterval 40),(⟨734666360586,734666379915⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨221304110784,221304110848⟩ : DyadicInterval 40),(⟨-277367923008,-277367922944⟩ : DyadicInterval 40),(⟨734563097583,734563116913⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨220831263424,220831263488⟩ : DyadicInterval 40),(⟨-276624132800,-276624132736⟩ : DyadicInterval 40),(⟨734694044473,734694063802⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨221304110784,221304110848⟩ : DyadicInterval 40),(⟨-277367923008,-277367922944⟩ : DyadicInterval 40),(⟨734563097583,734563116913⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,63586739⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63584896,63584960⟩ : DyadicInterval 40),(⟨-63588608,-63588544⟩ : DyadicInterval 40),(⟨762123381730,762123401059⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3712,0⟩ : DyadicInterval 40),(⟨762123383616,762123404736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨244631161263,245148151883⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨220881299712,220881299776⟩ : DyadicInterval 40),(⟨-276702801088,-276702801024⟩ : DyadicInterval 40),(⟨734680205581,734680224911⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨221304117824,221304117888⟩ : DyadicInterval 40),(⟨-277367934016,-277367933952⟩ : DyadicInterval 40),(⟨734563095614,734563114944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-56063816192,-55821501312⟩ : DyadicInterval 40),(⟨790034134272,790155310976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨220931342848,221304110848⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-277367923008,-276781489280⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e301_ok : ecellOkT e301 = true := by decide +kernel
theorem e301_pos {a z : ℝ} (ha1 : ((18231/81920 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((28539/128000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e301 e301_ok ha1 ha2 hz1 hz2 hz

-- box ['28539/128000', '457473/2048000', '999/1000', '1999/2000']  interval_lower 158268059/1099511627776
noncomputable def e302 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1344659771097,0,true,221304110784,221304110848⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨854363484455,0,false,-277367923008,-277367922944⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1345115574502,0,true,221676752448,221676752512⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨853907681050,0,false,-277954669632,-277954669568⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1344414622953,0,true,221103637952,221103638016⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨854608632599,0,false,-277052478144,-277052478080⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1344992772529,0,true,221576368256,221576368320⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨854030483023,0,false,-277796558272,-277796558208⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575211594,0,true,63581952,63582016⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448043958,0,false,-63585664,-63585600⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099639052977,0,true,127417792,127417856⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099384202575,0,false,-127432640,-127432576⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511613008,0,false,-14784,-14720⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624100,0,false,-3712,-3648⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1344537193119,0,true,221203875776,221203875840⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨854486062433,0,false,-277210184256,-277210184192⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1345054182643,0,true,221626568960,221626569024⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨853969072909,0,false,-277875622848,-277875622784⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1044677149697,0,false,-56249053888,-56249053824⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1044907814452,0,false,-56006308480,-56006308416⟩
    { al := (28539/128000), au := (457473/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨245148143321,245603946726⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨221304110784,221304110848⟩ : DyadicInterval 40),(⟨-277367923008,-277367922944⟩ : DyadicInterval 40),(⟨734563097584,734563116913⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨221676752448,221676752512⟩ : DyadicInterval 40),(⟨-277954669632,-277954669568⟩ : DyadicInterval 40),(⟨734459635709,734459655039⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨221103637952,221103638016⟩ : DyadicInterval 40),(⟨-277052478144,-277052478080⟩ : DyadicInterval 40),(⟨734618660992,734618680321⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨221576368256,221576368320⟩ : DyadicInterval 40),(⟨-277796558272,-277796558208⟩ : DyadicInterval 40),(⟨734487529828,734487549157⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨63583818,127425201⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63581952,63582016⟩ : DyadicInterval 40),(⟨-63585664,-63585600⟩ : DyadicInterval 40),(⟨762123381730,762123401060⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨127417792,127417856⟩ : DyadicInterval 40),(⟨-127432640,-127432576⟩ : DyadicInterval 40),(⟨762123376208,762123395537⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-14784,-3648⟩ : DyadicInterval 40),(⟨762123385440,762123410272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨245025565343,245542554867⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨221203875776,221203875840⟩ : DyadicInterval 40),(⟨-277210184256,-277210184192⟩ : DyadicInterval 40),(⟨734590887349,734590906679⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨221626568960,221626569024⟩ : DyadicInterval 40),(⟨-277875622848,-277875622784⟩ : DyadicInterval 40),(⟨734473582493,734473601823⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-56249053888,-56006308416⟩ : DyadicInterval 40),(⟨790126537824,790247929824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨221304110784,221676752512⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-277954669632,-277367922944⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e302_ok : ecellOkT e302 = true := by decide +kernel
theorem e302_pos {a z : ℝ} (ha1 : ((28539/128000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((457473/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e302 e302_ok ha1 ha2 hz1 hz2 hz

-- box ['457473/2048000', '229161/1024000', '999/1000', '1999/2000']  interval_lower 170165555/1099511627776
noncomputable def e303 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1345115574501,0,true,221676752448,221676752512⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨853907681051,0,false,-277954669632,-277954669568⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1345571377906,0,true,222049267840,222049267904⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨853451877646,0,false,-278541729536,-278541729472⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1344869970554,0,true,221475974848,221475974912⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨854153284998,0,false,-277638469696,-277638469632⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1345448348032,0,true,221948731392,221948731456⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨853574907520,0,false,-278383240192,-278383240128⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575338779,0,true,63709120,63709184⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447916773,0,false,-63712896,-63712832⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099639307469,0,true,127672256,127672320⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099383948083,0,false,-127687168,-127687104⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511612949,0,false,-14848,-14784⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624085,0,false,-3712,-3648⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1344992768620,0,true,221576365056,221576365120⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨854030486932,0,false,-277796553216,-277796553152⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1345509872096,0,true,221999008256,221999008320⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨853513383456,0,false,-278462493760,-278462493696⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1044473432017,0,false,-56463485504,-56463485440⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1044704576184,0,false,-56220188160,-56220188096⟩
    { al := (457473/2048000), au := (229161/1024000), zl := (999/1000), zu := (1999/2000),
      A := ⟨245603946725,246059750130⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨221676752448,221676752512⟩ : DyadicInterval 40),(⟨-277954669632,-277954669568⟩ : DyadicInterval 40),(⟨734459635710,734459655039⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨222049267840,222049267904⟩ : DyadicInterval 40),(⟨-278541729536,-278541729472⟩ : DyadicInterval 40),(⟨734355974970,734355994300⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨221475974848,221475974912⟩ : DyadicInterval 40),(⟨-277638469696,-277638469632⟩ : DyadicInterval 40),(⟨734515409563,734515428892⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨221948731392,221948731456⟩ : DyadicInterval 40),(⟨-278383240192,-278383240128⟩ : DyadicInterval 40),(⟨734383974546,734383993876⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨63711003,127679693⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63709120,63709184⟩ : DyadicInterval 40),(⟨-63712896,-63712832⟩ : DyadicInterval 40),(⟨762123381748,762123401077⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨127672256,127672320⟩ : DyadicInterval 40),(⟨-127687168,-127687104⟩ : DyadicInterval 40),(⟨762123376181,762123395510⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-14848,-3648⟩ : DyadicInterval 40),(⟨762123385440,762123410304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨245481140844,245998244320⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨221576365056,221576365120⟩ : DyadicInterval 40),(⟨-277796553216,-277796553152⟩ : DyadicInterval 40),(⟨734487530709,734487550039⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨221999008256,221999008320⟩ : DyadicInterval 40),(⟨-278462493760,-278462493696⟩ : DyadicInterval 40),(⟨734369974470,734369993800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-56463485504,-56220188096⟩ : DyadicInterval 40),(⟨790233477664,790355145632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨221676752448,222049267904⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-278541729536,-277954669568⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e303_ok : ecellOkT e303 = true := by decide +kernel
theorem e303_pos {a z : ℝ} (ha1 : ((457473/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((229161/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e303 e303_ok ha1 ha2 hz1 hz2 hz

-- box ['28539/128000', '457473/2048000', '1999/2000', '1']  interval_lower 38811165/274877906944
noncomputable def e304 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1344659771097,0,true,221304110784,221304110848⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨854363484455,0,false,-277367923008,-277367922944⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1345115574502,0,true,221676752448,221676752512⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨853907681050,0,false,-277954669632,-277954669568⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1344537197025,0,true,221203878912,221203878976⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨854486058527,0,false,-277210189248,-277210189184⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575341715,0,true,63712064,63712128⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447913837,0,false,-63715840,-63715776⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624083,0,false,-3712,-3648⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1344598478478,0,true,221253991424,221253991488⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨854424777074,0,false,-277289046144,-277289046080⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1345115583066,0,true,221676759424,221676759488⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨853907672486,0,false,-277954680640,-277954680576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1044649722426,0,false,-56277921152,-56277921088⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1044880496218,0,false,-56035054656,-56035054592⟩
    { al := (28539/128000), au := (457473/2048000), zl := (1999/2000), zu := 1,
      A := ⟨245148143321,245603946726⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨221304110784,221304110848⟩ : DyadicInterval 40),(⟨-277367923008,-277367922944⟩ : DyadicInterval 40),(⟨734563097584,734563116913⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨221676752448,221676752512⟩ : DyadicInterval 40),(⟨-277954669632,-277954669568⟩ : DyadicInterval 40),(⟨734459635709,734459655039⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨221203878912,221203878976⟩ : DyadicInterval 40),(⟨-277210189248,-277210189184⟩ : DyadicInterval 40),(⟨734590886486,734590905816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨221676752448,221676752512⟩ : DyadicInterval 40),(⟨-277954669632,-277954669568⟩ : DyadicInterval 40),(⟨734459635709,734459655039⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,63713939⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63712064,63712128⟩ : DyadicInterval 40),(⟨-63715840,-63715776⟩ : DyadicInterval 40),(⟨762123381747,762123401077⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3712,0⟩ : DyadicInterval 40),(⟨762123383616,762123404736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨245086850702,245603955290⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨221253991424,221253991488⟩ : DyadicInterval 40),(⟨-277289046144,-277289046080⟩ : DyadicInterval 40),(⟨734576995110,734577014439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨221676759424,221676759488⟩ : DyadicInterval 40),(⟨-277954680640,-277954680576⟩ : DyadicInterval 40),(⟨734459633771,734459653100⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-56277921152,-56035054592⟩ : DyadicInterval 40),(⟨790140910912,790262363456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨221304110784,221676752512⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-277954669632,-277367922944⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e304_ok : ecellOkT e304 = true := by decide +kernel
theorem e304_pos {a z : ℝ} (ha1 : ((28539/128000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((457473/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e304 e304_ok ha1 ha2 hz1 hz2 hz

-- box ['457473/2048000', '229161/1024000', '1999/2000', '1']  interval_lower 20890293/137438953472
noncomputable def e305 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1345115574501,0,true,221676752448,221676752512⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨853907681051,0,false,-277954669632,-277954669568⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1345571377906,0,true,222049267840,222049267904⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨853451877646,0,false,-278541729536,-278541729472⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1344992772527,0,true,221576368256,221576368320⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨854030483025,0,false,-277796558272,-277796558208⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575468969,0,true,63839296,63839360⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447786583,0,false,-63843072,-63843008⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624069,0,false,-3712,-3648⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1345054167929,0,true,221626556928,221626556992⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨853969087623,0,false,-277875603904,-277875603840⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1345571386470,0,true,222049274816,222049274880⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨853451869082,0,false,-278541740544,-278541740480⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1044445902849,0,false,-56492465664,-56492465600⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1044677156270,0,false,-56249046976,-56249046912⟩
    { al := (457473/2048000), au := (229161/1024000), zl := (1999/2000), zu := 1,
      A := ⟨245603946725,246059750130⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨221676752448,221676752512⟩ : DyadicInterval 40),(⟨-277954669632,-277954669568⟩ : DyadicInterval 40),(⟨734459635710,734459655039⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨222049267840,222049267904⟩ : DyadicInterval 40),(⟨-278541729536,-278541729472⟩ : DyadicInterval 40),(⟨734355974970,734355994300⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨221576368256,221576368320⟩ : DyadicInterval 40),(⟨-277796558272,-277796558208⟩ : DyadicInterval 40),(⟨734487529828,734487549158⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨222049267840,222049267904⟩ : DyadicInterval 40),(⟨-278541729536,-278541729472⟩ : DyadicInterval 40),(⟨734355974970,734355994300⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,63841193⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63839296,63839360⟩ : DyadicInterval 40),(⟨-63843072,-63843008⟩ : DyadicInterval 40),(⟨762123381733,762123401062⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3712,0⟩ : DyadicInterval 40),(⟨762123383616,762123404736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨245542540153,246059758694⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨221626556928,221626556992⟩ : DyadicInterval 40),(⟨-277875603904,-277875603840⟩ : DyadicInterval 40),(⟨734473585839,734473605168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨222049274816,222049274880⟩ : DyadicInterval 40),(⟨-278541740544,-278541740480⟩ : DyadicInterval 40),(⟨734355973025,734355992354⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-56492465664,-56249046912⟩ : DyadicInterval 40),(⟨790247907072,790369635712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨221676752448,222049267904⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-278541729536,-277954669568⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e305_ok : ecellOkT e305 = true := by decide +kernel
theorem e305_pos {a z : ℝ} (ha1 : ((457473/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((229161/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e305 e305_ok ha1 ha2 hz1 hz2 hz

-- box ['229161/1024000', '459171/2048000', '999/1000', '1999/2000']  interval_lower 182159311/1099511627776
noncomputable def e306 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1345571377905,0,true,222049267840,222049267904⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨853451877647,0,false,-278541729472,-278541729408⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1346027181310,0,true,222421657088,222421657152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨852996074242,0,false,-279129102976,-279129102912⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1345325318154,0,true,221848185728,221848185792⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨853697937398,0,false,-278224773632,-278224773568⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1345903923534,0,true,222320968512,222320968576⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨853119332018,0,false,-278970235264,-278970235200⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575466019,0,true,63836352,63836416⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447789533,0,false,-63840128,-63840064⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099639562068,0,true,127926848,127926912⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099383693484,0,false,-127941760,-127941696⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511612890,0,false,-14912,-14848⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624070,0,false,-3712,-3648⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1345448344131,0,true,221948728192,221948728256⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨853574911421,0,false,-278383235136,-278383235072⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1345965561563,0,true,222371321408,222371321472⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨853057693989,0,false,-279049678016,-279049677952⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1044269336612,0,false,-56678356608,-56678356544⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1044500960382,0,false,-56434506880,-56434506816⟩
    { al := (229161/1024000), au := (459171/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨246059750129,246515553534⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨222049267840,222049267904⟩ : DyadicInterval 40),(⟨-278541729472,-278541729408⟩ : DyadicInterval 40),(⟨734355974946,734355994276⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨222421657088,222421657152⟩ : DyadicInterval 40),(⟨-279129102976,-279129102912⟩ : DyadicInterval 40),(⟨734252115272,734252134602⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨221848185728,221848185792⟩ : DyadicInterval 40),(⟨-278224773632,-278224773568⟩ : DyadicInterval 40),(⟨734411959623,734411978952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨222320968512,222320968576⟩ : DyadicInterval 40),(⟨-278970235264,-278970235200⟩ : DyadicInterval 40),(⟨734280220507,734280239836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨63838243,127934292⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63836352,63836416⟩ : DyadicInterval 40),(⟨-63840128,-63840064⟩ : DyadicInterval 40),(⟨762123381733,762123401062⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨127926848,127926912⟩ : DyadicInterval 40),(⟨-127941760,-127941696⟩ : DyadicInterval 40),(⟨762123376121,762123395451⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-14912,-3648⟩ : DyadicInterval 40),(⟨762123385440,762123410336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨245936716355,246453933787⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨221948728192,221948728256⟩ : DyadicInterval 40),(⟨-278383235136,-278383235072⟩ : DyadicInterval 40),(⟨734383975429,734383994759⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨222371321408,222371321472⟩ : DyadicInterval 40),(⟨-279049678016,-279049677952⟩ : DyadicInterval 40),(⟨734266167625,734266186954⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-56678356608,-56434506816⟩ : DyadicInterval 40),(⟨790340637024,790462581184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨222049267840,222421657152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-279129102976,-278541729408⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e306_ok : ecellOkT e306 = true := by decide +kernel
theorem e306_pos {a z : ℝ} (ha1 : ((229161/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((459171/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e306 e306_ok ha1 ha2 hz1 hz2 hz

-- box ['459171/2048000', '23001/102400', '999/1000', '1999/2000']  interval_lower 194250579/1099511627776
noncomputable def e307 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1346027181309,0,true,222421657088,222421657152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨852996074243,0,false,-279129102976,-279129102912⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1346482984715,0,true,222793920192,222793920256⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨852540270837,0,false,-279716790464,-279716790400⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1345780665755,0,true,222220270656,222220270720⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨853242589797,0,false,-278811390464,-278811390400⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1346359499037,0,true,222693079616,222693079680⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨852663756515,0,false,-279557543872,-279557543808⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575593311,0,true,63963648,63963712⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447662241,0,false,-63967424,-63967360⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099639816773,0,true,128181504,128181568⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099383438779,0,false,-128196480,-128196416⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511612830,0,false,-14976,-14912⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624055,0,false,-3776,-3712⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1345903919637,0,true,222320965312,222320965376⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨853119335915,0,false,-278970230208,-278970230144⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1346421251016,0,true,222743508544,222743508608⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨852602004536,0,false,-279637176064,-279637176000⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1044064863495,0,false,-56893667520,-56893667456⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1044296967054,0,false,-56649264896,-56649264832⟩
    { al := (459171/2048000), au := (23001/102400), zl := (999/1000), zu := (1999/2000),
      A := ⟨246515553533,246971356939⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨222421657088,222421657152⟩ : DyadicInterval 40),(⟨-279129102976,-279129102912⟩ : DyadicInterval 40),(⟨734252115273,734252134602⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨222793920192,222793920256⟩ : DyadicInterval 40),(⟨-279716790464,-279716790400⟩ : DyadicInterval 40),(⟨734148056696,734148076025⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨222220270656,222220270720⟩ : DyadicInterval 40),(⟨-278811390464,-278811390400⟩ : DyadicInterval 40),(⟨734308311215,734308330544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨222693079616,222693079680⟩ : DyadicInterval 40),(⟨-279557543872,-279557543808⟩ : DyadicInterval 40),(⟨734176267741,734176287071⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨63965535,128188997⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63963648,63963712⟩ : DyadicInterval 40),(⟨-63967424,-63967360⟩ : DyadicInterval 40),(⟨762123381718,762123401047⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨128181504,128181568⟩ : DyadicInterval 40),(⟨-128196480,-128196416⟩ : DyadicInterval 40),(⟨762123376094,762123395423⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-14976,-3712⟩ : DyadicInterval 40),(⟨762123385472,762123410368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨246392291861,246909623240⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨222320965312,222320965376⟩ : DyadicInterval 40),(⟨-278970230208,-278970230144⟩ : DyadicInterval 40),(⟨734280221392,734280240722⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨222743508544,222743508608⟩ : DyadicInterval 40),(⟨-279637176064,-279637176000⟩ : DyadicInterval 40),(⟨734162161941,734162181271⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-56893667520,-56649264832⟩ : DyadicInterval 40),(⟨790448016032,790570236640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨222421657088,222793920256⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-279716790464,-279129102912⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e307_ok : ecellOkT e307 = true := by decide +kernel
theorem e307_pos {a z : ℝ} (ha1 : ((459171/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((23001/102400 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e307 e307_ok ha1 ha2 hz1 hz2 hz

-- box ['229161/1024000', '459171/2048000', '1999/2000', '1']  interval_lower 179096029/1099511627776
noncomputable def e308 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1345571377905,0,true,222049267840,222049267904⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨853451877647,0,false,-278541729472,-278541729408⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1346027181310,0,true,222421657088,222421657152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨852996074242,0,false,-279129102976,-279129102912⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1345448348029,0,true,221948731392,221948731456⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨853574907523,0,false,-278383240128,-278383240064⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575596275,0,true,63966592,63966656⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447659277,0,false,-63970368,-63970304⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624054,0,false,-3776,-3712⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1345509857379,0,true,221998996224,221998996288⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨853513398173,0,false,-278462474752,-278462474688⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1346027189886,0,true,222421664064,222421664128⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨852996065666,0,false,-279129114048,-279129113984⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1044241705360,0,false,-56707449984,-56707449920⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1044473438603,0,false,-56463478528,-56463478464⟩
    { al := (229161/1024000), au := (459171/2048000), zl := (1999/2000), zu := 1,
      A := ⟨246059750129,246515553534⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨222049267840,222049267904⟩ : DyadicInterval 40),(⟨-278541729472,-278541729408⟩ : DyadicInterval 40),(⟨734355974946,734355994276⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨222421657088,222421657152⟩ : DyadicInterval 40),(⟨-279129102976,-279129102912⟩ : DyadicInterval 40),(⟨734252115272,734252134602⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨221948731392,221948731456⟩ : DyadicInterval 40),(⟨-278383240128,-278383240064⟩ : DyadicInterval 40),(⟨734383974522,734383993851⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨222421657088,222421657152⟩ : DyadicInterval 40),(⟨-279129102976,-279129102912⟩ : DyadicInterval 40),(⟨734252115272,734252134602⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,63968499⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63966592,63966656⟩ : DyadicInterval 40),(⟨-63970368,-63970304⟩ : DyadicInterval 40),(⟨762123381718,762123401047⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3776,0⟩ : DyadicInterval 40),(⟨762123383616,762123404768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨245998229603,246515562110⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨221998996224,221998996288⟩ : DyadicInterval 40),(⟨-278462474752,-278462474688⟩ : DyadicInterval 40),(⟨734369977804,734369997134⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨222421664064,222421664128⟩ : DyadicInterval 40),(⟨-279129114048,-279129113984⟩ : DyadicInterval 40),(⟨734252113341,734252132671⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-56707449984,-56463478464⟩ : DyadicInterval 40),(⟨790355122848,790477127872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨222049267840,222421657152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-279129102976,-278541729408⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e308_ok : ecellOkT e308 = true := by decide +kernel
theorem e308_pos {a z : ℝ} (ha1 : ((229161/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((459171/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e308 e308_ok ha1 ha2 hz1 hz2 hz

-- box ['459171/2048000', '23001/102400', '1999/2000', '1']  interval_lower 191166919/1099511627776
noncomputable def e309 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1346027181309,0,true,222421657088,222421657152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨852996074243,0,false,-279129102976,-279129102912⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1346482984715,0,true,222793920192,222793920256⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨852540270837,0,false,-279716790464,-279716790400⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1345903923532,0,true,222320968512,222320968576⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨853119332020,0,false,-278970235264,-278970235200⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575723636,0,true,64093952,64094016⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447531916,0,false,-64097792,-64097728⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624039,0,false,-3776,-3712⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1345965546829,0,true,222371309376,222371309440⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨853057708723,0,false,-279049659072,-279049659008⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1346482993280,0,true,222793927232,222793927296⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨852540262272,0,false,-279716801536,-279716801472⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1044037129973,0,false,-56922874304,-56922874240⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1044269343218,0,false,-56678349632,-56678349568⟩
    { al := (459171/2048000), au := (23001/102400), zl := (1999/2000), zu := 1,
      A := ⟨246515553533,246971356939⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨222421657088,222421657152⟩ : DyadicInterval 40),(⟨-279129102976,-279129102912⟩ : DyadicInterval 40),(⟨734252115273,734252134602⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨222793920192,222793920256⟩ : DyadicInterval 40),(⟨-279716790464,-279716790400⟩ : DyadicInterval 40),(⟨734148056696,734148076025⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨222320968512,222320968576⟩ : DyadicInterval 40),(⟨-278970235264,-278970235200⟩ : DyadicInterval 40),(⟨734280220507,734280239837⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨222793920192,222793920256⟩ : DyadicInterval 40),(⟨-279716790464,-279716790400⟩ : DyadicInterval 40),(⟨734148056696,734148076025⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,64095860⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64093952,64094016⟩ : DyadicInterval 40),(⟨-64097792,-64097728⟩ : DyadicInterval 40),(⟨762123381735,762123401064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3776,0⟩ : DyadicInterval 40),(⟨762123383616,762123404768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨246453919053,246971365504⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨222371309376,222371309440⟩ : DyadicInterval 40),(⟨-279049659072,-279049659008⟩ : DyadicInterval 40),(⟨734266171000,734266190329⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨222793927232,222793927296⟩ : DyadicInterval 40),(⟨-279716801536,-279716801472⟩ : DyadicInterval 40),(⟨734148054720,734148074050⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-56922874304,-56678349568⟩ : DyadicInterval 40),(⟨790462558400,790584840032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨222421657088,222793920256⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-279716790464,-279129102912⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e309_ok : ecellOkT e309 = true := by decide +kernel
theorem e309_pos {a z : ℝ} (ha1 : ((459171/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((23001/102400 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e309 e309_ok ha1 ha2 hz1 hz2 hz

-- box ['23001/102400', '460869/2048000', '999/1000', '1999/2000']  interval_lower 51609725/274877906944
noncomputable def e310 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1346482984714,0,true,222793920192,222793920256⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨852540270838,0,false,-279716790464,-279716790400⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1346938788119,0,true,223166057344,223166057408⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨852084467433,0,false,-280304792192,-280304792128⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1346236013357,0,true,222592229760,222592229824⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨852787242195,0,false,-279398320384,-279398320320⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1346815074540,0,true,223065064832,223065064896⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨852208181012,0,false,-280145166400,-280145166336⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575720657,0,true,64091008,64091072⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447534895,0,false,-64094784,-64094720⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099640071586,0,true,128436288,128436352⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099383183966,0,false,-128451328,-128451264⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511612771,0,false,-15040,-14976⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624040,0,false,-3776,-3712⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1346359495144,0,true,222693076416,222693076480⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨852663760408,0,false,-279557538880,-279557538816⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1346876940475,0,true,223115569728,223115569792⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨852146315077,0,false,-280224988224,-280224988160⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1043860012658,0,false,-57109418496,-57109418432⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1044092596195,0,false,-56864462400,-56864462336⟩
    { al := (23001/102400), au := (460869/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨246971356938,247427160343⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨222793920192,222793920256⟩ : DyadicInterval 40),(⟨-279716790464,-279716790400⟩ : DyadicInterval 40),(⟨734148056696,734148076026⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨223166057344,223166057408⟩ : DyadicInterval 40),(⟨-280304792192,-280304792128⟩ : DyadicInterval 40),(⟨734043799082,734043818412⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨222592229760,222592229824⟩ : DyadicInterval 40),(⟨-279398320384,-279398320320⟩ : DyadicInterval 40),(⟨734204464219,734204483548⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨223065064832,223065064896⟩ : DyadicInterval 40),(⟨-280145166400,-280145166336⟩ : DyadicInterval 40),(⟨734072116205,734072135535⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨64092881,128443810⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64091008,64091072⟩ : DyadicInterval 40),(⟨-64094784,-64094720⟩ : DyadicInterval 40),(⟨762123381703,762123401032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨128436288,128436352⟩ : DyadicInterval 40),(⟨-128451328,-128451264⟩ : DyadicInterval 40),(⟨762123376067,762123395396⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-15040,-3712⟩ : DyadicInterval 40),(⟨762123385472,762123410400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨246847867368,247365312699⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨222693076416,222693076480⟩ : DyadicInterval 40),(⟨-279557538880,-279557538816⟩ : DyadicInterval 40),(⟨734176268654,734176287984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨223115569728,223115569792⟩ : DyadicInterval 40),(⟨-280224988224,-280224988160⟩ : DyadicInterval 40),(⟨734057957383,734057976713⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-57109418496,-56864462336⟩ : DyadicInterval 40),(⟨790555614784,790678112128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨222793920192,223166057408⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-280304792192,-279716790400⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e310_ok : ecellOkT e310 = true := by decide +kernel
theorem e310_pos {a z : ℝ} (ha1 : ((23001/102400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((460869/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e310 e310_ok ha1 ha2 hz1 hz2 hz

-- box ['460869/2048000', '230859/1024000', '999/1000', '1999/2000']  interval_lower 109362709/549755813888
noncomputable def e311 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1346938788118,0,true,223166057344,223166057408⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨852084467434,0,false,-280304792192,-280304792128⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1347394591523,0,true,223538068608,223538068672⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨851628664029,0,false,-280893108544,-280893108480⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1346691360957,0,true,222964062976,222964063040⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨852331894595,0,false,-279985563840,-279985563776⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1347270650042,0,true,223436924224,223436924288⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨851752605510,0,false,-280733103168,-280733103104⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575848055,0,true,64218368,64218432⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447407497,0,false,-64222208,-64222144⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099640326504,0,true,128691136,128691200⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099382929048,0,false,-128706304,-128706240⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511612711,0,false,-15104,-15040⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624026,0,false,-3776,-3712⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1346815070642,0,true,223065061632,223065061696⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨852208184910,0,false,-280145161408,-280145161344⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1347332629931,0,true,223487505024,223487505088⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨851690625621,0,false,-280813114752,-280813114688⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1043654784103,0,false,-57325609664,-57325609600⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1043887847811,0,false,-57080099712,-57080099648⟩
    { al := (460869/2048000), au := (230859/1024000), zl := (999/1000), zu := (1999/2000),
      A := ⟨247427160342,247882963747⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨223166057344,223166057408⟩ : DyadicInterval 40),(⟨-280304792192,-280304792128⟩ : DyadicInterval 40),(⟨734043799082,734043818412⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨223538068608,223538068672⟩ : DyadicInterval 40),(⟨-280893108544,-280893108480⟩ : DyadicInterval 40),(⟨733939342422,733939361752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨222964062976,222964063040⟩ : DyadicInterval 40),(⟨-279985563840,-279985563776⟩ : DyadicInterval 40),(⟨734100418732,734100438061⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨223436924224,223436924288⟩ : DyadicInterval 40),(⟨-280733103168,-280733103104⟩ : DyadicInterval 40),(⟨733967765865,733967785194⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨64220279,128698728⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64218368,64218432⟩ : DyadicInterval 40),(⟨-64222208,-64222144⟩ : DyadicInterval 40),(⟨762123381720,762123401050⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨128691136,128691200⟩ : DyadicInterval 40),(⟨-128706304,-128706240⟩ : DyadicInterval 40),(⟨762123376071,762123395400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-15104,-3712⟩ : DyadicInterval 40),(⟨762123385472,762123410432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨247303442866,247821002155⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨223065061632,223065061696⟩ : DyadicInterval 40),(⟨-280145161408,-280145161344⟩ : DyadicInterval 40),(⟨734072117122,734072136452⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨223487505024,223487505088⟩ : DyadicInterval 40),(⟨-280813114752,-280813114688⟩ : DyadicInterval 40),(⟨733953553897,733953573227⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-57325609664,-57080099648⟩ : DyadicInterval 40),(⟨790663433440,790786207712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨223166057344,223538068672⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-280893108544,-280304792128⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e311_ok : ecellOkT e311 = true := by decide +kernel
theorem e311_pos {a z : ℝ} (ha1 : ((460869/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((230859/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e311 e311_ok ha1 ha2 hz1 hz2 hz

-- box ['23001/102400', '460869/2048000', '1999/2000', '1']  interval_lower 50833743/274877906944
noncomputable def e312 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1346482984714,0,true,222793920192,222793920256⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨852540270838,0,false,-279716790464,-279716790400⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1346938788119,0,true,223166057344,223166057408⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨852084467433,0,false,-280304792192,-280304792128⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1346359499035,0,true,222693079616,222693079680⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨852663756517,0,false,-279557543872,-279557543808⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575851049,0,true,64221376,64221440⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447404503,0,false,-64225152,-64225088⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624024,0,false,-3776,-3712⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1346421236272,0,true,222743496512,222743496576⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨852602019280,0,false,-279637157056,-279637156992⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1346938796687,0,true,223166064320,223166064384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨852084458865,0,false,-280304803264,-280304803200⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1043832176673,0,false,-57138738880,-57138738816⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1044064870118,0,false,-56893660544,-56893660480⟩
    { al := (23001/102400), au := (460869/2048000), zl := (1999/2000), zu := 1,
      A := ⟨246971356938,247427160343⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨222793920192,222793920256⟩ : DyadicInterval 40),(⟨-279716790464,-279716790400⟩ : DyadicInterval 40),(⟨734148056696,734148076026⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨223166057344,223166057408⟩ : DyadicInterval 40),(⟨-280304792192,-280304792128⟩ : DyadicInterval 40),(⟨734043799082,734043818412⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨222693079616,222693079680⟩ : DyadicInterval 40),(⟨-279557543872,-279557543808⟩ : DyadicInterval 40),(⟨734176267742,734176287072⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨223166057344,223166057408⟩ : DyadicInterval 40),(⟨-280304792192,-280304792128⟩ : DyadicInterval 40),(⟨734043799082,734043818412⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,64223273⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64221376,64221440⟩ : DyadicInterval 40),(⟨-64225152,-64225088⟩ : DyadicInterval 40),(⟨762123381688,762123401017⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3776,0⟩ : DyadicInterval 40),(⟨762123383616,762123404768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨246909608496,247427168911⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨222743496512,222743496576⟩ : DyadicInterval 40),(⟨-279637157056,-279637156992⟩ : DyadicInterval 40),(⟨734162165307,734162184636⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨223166064320,223166064384⟩ : DyadicInterval 40),(⟨-280304803264,-280304803200⟩ : DyadicInterval 40),(⟨734043797137,734043816467⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-57138738880,-56893660480⟩ : DyadicInterval 40),(⟨790570213856,790692772320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨222793920192,223166057408⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-280304792192,-279716790400⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e312_ok : ecellOkT e312 = true := by decide +kernel
theorem e312_pos {a z : ℝ} (ha1 : ((23001/102400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((460869/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e312 e312_ok ha1 ha2 hz1 hz2 hz

-- box ['460869/2048000', '230859/1024000', '1999/2000', '1']  interval_lower 215600733/1099511627776
noncomputable def e313 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1346938788118,0,true,223166057344,223166057408⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨852084467434,0,false,-280304792192,-280304792128⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1347394591523,0,true,223538068608,223538068672⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨851628664029,0,false,-280893108544,-280893108480⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1346815074537,0,true,223065064832,223065064896⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨852208181015,0,false,-280145166400,-280145166336⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575978516,0,true,64348800,64348864⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447277036,0,false,-64352640,-64352576⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624009,0,false,-3776,-3712⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1346876925718,0,true,223115557632,223115557696⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨852146329834,0,false,-280224969152,-280224969088⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1347394600098,0,true,223538075584,223538075648⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨851628655454,0,false,-280893119616,-280893119552⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1043626845464,0,false,-57355044032,-57355043968⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1043860019299,0,false,-57109411456,-57109411392⟩
    { al := (460869/2048000), au := (230859/1024000), zl := (1999/2000), zu := 1,
      A := ⟨247427160342,247882963747⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨223166057344,223166057408⟩ : DyadicInterval 40),(⟨-280304792192,-280304792128⟩ : DyadicInterval 40),(⟨734043799082,734043818412⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨223538068608,223538068672⟩ : DyadicInterval 40),(⟨-280893108544,-280893108480⟩ : DyadicInterval 40),(⟨733939342422,733939361752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨223065064832,223065064896⟩ : DyadicInterval 40),(⟨-280145166400,-280145166336⟩ : DyadicInterval 40),(⟨734072116206,734072135535⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨223538068608,223538068672⟩ : DyadicInterval 40),(⟨-280893108544,-280893108480⟩ : DyadicInterval 40),(⟨733939342422,733939361752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,64350740⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64348800,64348864⟩ : DyadicInterval 40),(⟨-64352640,-64352576⟩ : DyadicInterval 40),(⟨762123381705,762123401034⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3776,0⟩ : DyadicInterval 40),(⟨762123383616,762123404768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨247365297942,247882972322⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨223115557632,223115557696⟩ : DyadicInterval 40),(⟨-280224969152,-280224969088⟩ : DyadicInterval 40),(⟨734057960779,734057980109⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨223538075584,223538075648⟩ : DyadicInterval 40),(⟨-280893119616,-280893119552⟩ : DyadicInterval 40),(⟨733939340469,733939359799⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-57355044032,-57109411392⟩ : DyadicInterval 40),(⟨790678089312,790800924896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨223166057344,223538068672⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-280893108544,-280304792128⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e313_ok : ecellOkT e313 = true := by decide +kernel
theorem e313_pos {a z : ℝ} (ha1 : ((460869/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((230859/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e313 e313_ok ha1 ha2 hz1 hz2 hz

-- box ['230859/1024000', '462567/2048000', '999/1000', '1999/2000']  interval_lower 115555079/549755813888
noncomputable def e314 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1347394591522,0,true,223538068608,223538068672⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨851628664030,0,false,-280893108544,-280893108480⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1347850394928,0,true,223909953984,223909954048⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨851172860624,0,false,-281481739904,-281481739840⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1347146708558,0,true,223335770560,223335770624⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨851876546994,0,false,-280573121024,-280573120960⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1347726225545,0,true,223808657920,223808657984⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨851297030007,0,false,-281321354432,-281321354368⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575975507,0,true,64345792,64345856⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447280045,0,false,-64349632,-64349568⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099640581532,0,true,128946176,128946240⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099382674020,0,false,-128961344,-128961280⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511612651,0,false,-15168,-15104⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624011,0,false,-3776,-3712⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1347270646157,0,true,223436921088,223436921152⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨851752609395,0,false,-280733098176,-280733098112⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1347788319385,0,true,223859314560,223859314624⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨851234936167,0,false,-281401556032,-281401555968⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1043449177830,0,false,-57542241408,-57542241344⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1043682721889,0,false,-57296177024,-57296176960⟩
    { al := (230859/1024000), au := (462567/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨247882963746,248338767152⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨223538068608,223538068672⟩ : DyadicInterval 40),(⟨-280893108544,-280893108480⟩ : DyadicInterval 40),(⟨733939342423,733939361752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨223909953984,223909954048⟩ : DyadicInterval 40),(⟨-281481739904,-281481739840⟩ : DyadicInterval 40),(⟨733834686749,733834706078⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨223335770560,223335770624⟩ : DyadicInterval 40),(⟨-280573121024,-280573120960⟩ : DyadicInterval 40),(⟨733996174555,733996193885⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨223808657920,223808657984⟩ : DyadicInterval 40),(⟨-281321354432,-281321354368⟩ : DyadicInterval 40),(⟨733863216625,733863235954⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨64347731,128953756⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64345792,64345856⟩ : DyadicInterval 40),(⟨-64349632,-64349568⟩ : DyadicInterval 40),(⟨762123381706,762123401035⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨128946176,128946240⟩ : DyadicInterval 40),(⟨-128961344,-128961280⟩ : DyadicInterval 40),(⟨762123376011,762123395341⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-15168,-3712⟩ : DyadicInterval 40),(⟨762123385472,762123410464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨247759018381,248276691609⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨223436921088,223436921152⟩ : DyadicInterval 40),(⟨-280733098176,-280733098112⟩ : DyadicInterval 40),(⟨733967766744,733967786073⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨223859314560,223859314624⟩ : DyadicInterval 40),(⟨-281401556032,-281401555968⟩ : DyadicInterval 40),(⟨733848951434,733848970764⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-57542241408,-57296176960⟩ : DyadicInterval 40),(⟨790771472096,790894523584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨223538068608,223909954048⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-281481739904,-280893108480⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e314_ok : ecellOkT e314 = true := by decide +kernel
theorem e314_pos {a z : ℝ} (ha1 : ((230859/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((462567/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e314 e314_ok ha1 ha2 hz1 hz2 hz

-- box ['462567/2048000', '57927/256000', '999/1000', '1999/2000']  interval_lower 243593711/1099511627776
noncomputable def e315 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1347850394927,0,true,223909953984,223909954048⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨851172860625,0,false,-281481739904,-281481739840⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1348306198332,0,true,224281713664,224281713728⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨850717057220,0,false,-282070686528,-282070686464⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1347602056159,0,true,223707352512,223707352576⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨851421199393,0,false,-281160992384,-281160992320⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1348181801047,0,true,224180265984,224180266048⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨850841454505,0,false,-281909920640,-281909920576⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576103014,0,true,64473344,64473408⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447152538,0,false,-64477184,-64477120⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099640836668,0,true,129201280,129201344⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099382418884,0,false,-129216512,-129216448⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511612592,0,false,-15232,-15168⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623996,0,false,-3840,-3776⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1347726221659,0,true,223808654720,223808654784⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨851297033893,0,false,-281321349440,-281321349376⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1348244008841,0,true,224230998464,224230998528⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨850779246711,0,false,-281990312448,-281990312384⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1043243193839,0,false,-57759313984,-57759313920⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1043477218444,0,false,-57512694656,-57512694592⟩
    { al := (462567/2048000), au := (57927/256000), zl := (999/1000), zu := (1999/2000),
      A := ⟨248338767151,248794570556⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨223909953984,223909954048⟩ : DyadicInterval 40),(⟨-281481739904,-281481739840⟩ : DyadicInterval 40),(⟨733834686749,733834706078⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨224281713664,224281713728⟩ : DyadicInterval 40),(⟨-282070686528,-282070686464⟩ : DyadicInterval 40),(⟨733729831925,733729851254⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨223707352512,223707352576⟩ : DyadicInterval 40),(⟨-281160992384,-281160992320⟩ : DyadicInterval 40),(⟨733891731745,733891751074⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨224180265984,224180266048⟩ : DyadicInterval 40),(⟨-281909920640,-281909920576⟩ : DyadicInterval 40),(⟨733758468501,733758487831⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨64475238,129208892⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64473344,64473408⟩ : DyadicInterval 40),(⟨-64477184,-64477120⟩ : DyadicInterval 40),(⟨762123381691,762123401020⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨129201280,129201344⟩ : DyadicInterval 40),(⟨-129216512,-129216448⟩ : DyadicInterval 40),(⟨762123375983,762123395313⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-15232,-3776⟩ : DyadicInterval 40),(⟨762123385504,762123410496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨248214593883,248732381065⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨223808654720,223808654784⟩ : DyadicInterval 40),(⟨-281321349440,-281321349376⟩ : DyadicInterval 40),(⟨733863217546,733863236875⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨224230998464,224230998528⟩ : DyadicInterval 40),(⟨-281990312448,-281990312384⟩ : DyadicInterval 40),(⟨733744149946,733744169276⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-57759313984,-57512694592⟩ : DyadicInterval 40),(⟨790879730912,791003059872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨223909953984,224281713728⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-282070686528,-281481739840⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e315_ok : ecellOkT e315 = true := by decide +kernel
theorem e315_pos {a z : ℝ} (ha1 : ((462567/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((57927/256000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e315 e315_ok ha1 ha2 hz1 hz2 hz

-- box ['230859/1024000', '462567/2048000', '1999/2000', '1']  interval_lower 113982513/549755813888
noncomputable def e316 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1347394591522,0,true,223538068608,223538068672⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨851628664030,0,false,-280893108544,-280893108480⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1347850394928,0,true,223909953984,223909954048⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨851172860624,0,false,-281481739904,-281481739840⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1347270650040,0,true,223436924224,223436924288⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨851752605512,0,false,-280733103168,-280733103104⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576106037,0,true,64476352,64476416⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447149515,0,false,-64480192,-64480128⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623994,0,false,-3840,-3776⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1347332615165,0,true,223487492992,223487493056⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨851690640387,0,false,-280813095680,-280813095616⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1347850403491,0,true,223909960960,223909961024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨851172852061,0,false,-281481750912,-281481750848⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1043421136356,0,false,-57571789888,-57571789824⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1043654790760,0,false,-57325602688,-57325602624⟩
    { al := (230859/1024000), au := (462567/2048000), zl := (1999/2000), zu := 1,
      A := ⟨247882963746,248338767152⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨223538068608,223538068672⟩ : DyadicInterval 40),(⟨-280893108544,-280893108480⟩ : DyadicInterval 40),(⟨733939342423,733939361752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨223909953984,223909954048⟩ : DyadicInterval 40),(⟨-281481739904,-281481739840⟩ : DyadicInterval 40),(⟨733834686749,733834706078⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨223436924224,223436924288⟩ : DyadicInterval 40),(⟨-280733103168,-280733103104⟩ : DyadicInterval 40),(⟨733967765865,733967785195⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨223909953984,223909954048⟩ : DyadicInterval 40),(⟨-281481739904,-281481739840⟩ : DyadicInterval 40),(⟨733834686749,733834706078⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,64478261⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64476352,64476416⟩ : DyadicInterval 40),(⟨-64480192,-64480128⟩ : DyadicInterval 40),(⟨762123381690,762123401019⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3840,0⟩ : DyadicInterval 40),(⟨762123383616,762123404800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨247820987389,248338775715⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨223487492992,223487493056⟩ : DyadicInterval 40),(⟨-280813095680,-280813095616⟩ : DyadicInterval 40),(⟨733953557268,733953576598⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨223909960960,223909961024⟩ : DyadicInterval 40),(⟨-281481750912,-281481750848⟩ : DyadicInterval 40),(⟨733834684766,733834704095⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-57571789888,-57325602624⟩ : DyadicInterval 40),(⟨790786184928,790909297824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨223538068608,223909954048⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-281481739904,-280893108480⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e316_ok : ecellOkT e316 = true := by decide +kernel
theorem e316_pos {a z : ℝ} (ha1 : ((230859/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((462567/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e316 e316_ok ha1 ha2 hz1 hz2 hz

-- box ['462567/2048000', '57927/256000', '1999/2000', '1']  interval_lower 240427807/1099511627776
noncomputable def e317 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1347850394927,0,true,223909953984,223909954048⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨851172860625,0,false,-281481739904,-281481739840⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1348306198332,0,true,224281713664,224281713728⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨850717057220,0,false,-282070686528,-282070686464⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1347726225543,0,true,223808657920,223808657984⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨851297030009,0,false,-281321354432,-281321354368⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576233611,0,true,64603904,64603968⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447021941,0,false,-64607744,-64607680⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623979,0,false,-3840,-3776⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1347788304610,0,true,223859302528,223859302592⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨851234950942,0,false,-281401536960,-281401536896⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1348306206896,0,true,224281720640,224281720704⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨850717048656,0,false,-282070697536,-282070697472⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1043215049335,0,false,-57788976896,-57788976832⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1043449184504,0,false,-57542234432,-57542234368⟩
    { al := (462567/2048000), au := (57927/256000), zl := (1999/2000), zu := 1,
      A := ⟨248338767151,248794570556⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨223909953984,223909954048⟩ : DyadicInterval 40),(⟨-281481739904,-281481739840⟩ : DyadicInterval 40),(⟨733834686749,733834706078⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨224281713664,224281713728⟩ : DyadicInterval 40),(⟨-282070686528,-282070686464⟩ : DyadicInterval 40),(⟨733729831925,733729851254⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨223808657920,223808657984⟩ : DyadicInterval 40),(⟨-281321354432,-281321354368⟩ : DyadicInterval 40),(⟨733863216625,733863235954⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨224281713664,224281713728⟩ : DyadicInterval 40),(⟨-282070686528,-282070686464⟩ : DyadicInterval 40),(⟨733729831925,733729851254⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,64605835⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64603904,64603968⟩ : DyadicInterval 40),(⟨-64607744,-64607680⟩ : DyadicInterval 40),(⟨762123381675,762123401004⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3840,0⟩ : DyadicInterval 40),(⟨762123383616,762123404800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨248276676834,248794579120⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨223859302528,223859302592⟩ : DyadicInterval 40),(⟨-281401536960,-281401536896⟩ : DyadicInterval 40),(⟨733848954820,733848974150⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨224281720640,224281720704⟩ : DyadicInterval 40),(⟨-282070697536,-282070697472⟩ : DyadicInterval 40),(⟨733729829934,733729849263⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-57788976896,-57542234368⟩ : DyadicInterval 40),(⟨790894500800,791017891328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨223909953984,224281713728⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-282070686528,-281481739840⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e317_ok : ecellOkT e317 = true := by decide +kernel
theorem e317_pos {a z : ℝ} (ha1 : ((462567/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((57927/256000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e317 e317_ok ha1 ha2 hz1 hz2 hz

-- box ['57927/256000', '92853/409600', '999/1000', '1999/2000']  interval_lower 32022081/137438953472
noncomputable def e318 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1348306198331,0,true,224281713664,224281713728⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨850717057221,0,false,-282070686464,-282070686400⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1348762001736,0,true,224653347712,224653347776⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨850261253816,0,false,-282659948736,-282659948672⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1348057403760,0,true,224078808896,224078808960⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨850965851792,0,false,-281749178240,-281749178176⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1348637376550,0,true,224551748480,224551748544⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨850385879002,0,false,-282498802048,-282498801984⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576230574,0,true,64600896,64600960⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447024978,0,false,-64604736,-64604672⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099641091911,0,true,129456512,129456576⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099382163641,0,false,-129471808,-129471744⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511612531,0,false,-15296,-15232⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623981,0,false,-3840,-3776⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1348181797167,0,true,224180262784,224180262848⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨850841458385,0,false,-281909915648,-281909915584⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1348699698304,0,true,224602556736,224602556800⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨850323557248,0,false,-282579384320,-282579384256⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1043036832125,0,false,-57976827520,-57976827456⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1043271337467,0,false,-57729652800,-57729652736⟩
    { al := (57927/256000), au := (92853/409600), zl := (999/1000), zu := (1999/2000),
      A := ⟨248794570555,249250373960⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨224281713664,224281713728⟩ : DyadicInterval 40),(⟨-282070686464,-282070686400⟩ : DyadicInterval 40),(⟨733729831900,733729851230⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨224653347712,224653347776⟩ : DyadicInterval 40),(⟨-282659948736,-282659948672⟩ : DyadicInterval 40),(⟨733624777917,733624797246⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨224078808896,224078808960⟩ : DyadicInterval 40),(⟨-281749178240,-281749178176⟩ : DyadicInterval 40),(⟨733787090268,733787109598⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨224551748480,224551748544⟩ : DyadicInterval 40),(⟨-282498802048,-282498801984⟩ : DyadicInterval 40),(⟨733653521436,733653540766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨64602798,129464135⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64600896,64600960⟩ : DyadicInterval 40),(⟨-64604736,-64604672⟩ : DyadicInterval 40),(⟨762123381676,762123401005⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨129456512,129456576⟩ : DyadicInterval 40),(⟨-129471808,-129471744⟩ : DyadicInterval 40),(⟨762123375955,762123395285⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-15296,-3776⟩ : DyadicInterval 40),(⟨762123385504,762123410528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨248670169391,249188070528⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨224180262784,224180262848⟩ : DyadicInterval 40),(⟨-281909915648,-281909915584⟩ : DyadicInterval 40),(⟨733758469424,733758488754⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨224602556736,224602556800⟩ : DyadicInterval 40),(⟨-282579384320,-282579384256⟩ : DyadicInterval 40),(⟨733639149439,733639168769⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-57976827520,-57729652736⟩ : DyadicInterval 40),(⟨790988209984,791111816640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨224281713664,224653347776⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-282659948736,-282070686400⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e318_ok : ecellOkT e318 = true := by decide +kernel
theorem e318_pos {a z : ℝ} (ha1 : ((57927/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((92853/409600 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e318 e318_ok ha1 ha2 hz1 hz2 hz

-- box ['92853/409600', '232557/1024000', '999/1000', '1999/2000']  interval_lower 268859463/1099511627776
noncomputable def e319 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1348762001735,0,true,224653347712,224653347776⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨850261253817,0,false,-282659948736,-282659948672⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1349217805140,0,true,225024856128,225024856192⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨849805450412,0,false,-283249526976,-283249526912⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1348512751360,0,true,224450139840,224450139904⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨850510504192,0,false,-282337678976,-282337678912⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1349092952052,0,true,224923105536,224923105600⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨849930303500,0,false,-283087999040,-283087998976⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576358188,0,true,64728448,64728512⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446897364,0,false,-64732352,-64732288⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099641347261,0,true,129711808,129711872⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099381908291,0,false,-129727168,-129727104⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511612471,0,false,-15360,-15296⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623966,0,false,-3840,-3776⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1348637372668,0,true,224551745280,224551745344⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨850385882884,0,false,-282498796992,-282498796928⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1349155387757,0,true,224973989440,224973989504⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨849867867795,0,false,-283168771904,-283168771840⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1042830092698,0,false,-58194782400,-58194782336⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1043065078963,0,false,-57947051712,-57947051648⟩
    { al := (92853/409600), au := (232557/1024000), zl := (999/1000), zu := (1999/2000),
      A := ⟨249250373959,249706177364⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨224653347712,224653347776⟩ : DyadicInterval 40),(⟨-282659948736,-282659948672⟩ : DyadicInterval 40),(⟨733624777917,733624797247⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨225024856128,225024856192⟩ : DyadicInterval 40),(⟨-283249526976,-283249526912⟩ : DyadicInterval 40),(⟨733519524780,733519544110⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨224450139840,224450139904⟩ : DyadicInterval 40),(⟨-282337678976,-282337678912⟩ : DyadicInterval 40),(⟨733682250079,733682269408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨224923105536,224923105600⟩ : DyadicInterval 40),(⟨-283087999040,-283087998976⟩ : DyadicInterval 40),(⟨733548375382,733548394712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨64730412,129719485⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64728448,64728512⟩ : DyadicInterval 40),(⟨-64732352,-64732288⟩ : DyadicInterval 40),(⟨762123381693,762123401022⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨129711808,129711872⟩ : DyadicInterval 40),(⟨-129727168,-129727104⟩ : DyadicInterval 40),(⟨762123375927,762123395256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-15360,-3776⟩ : DyadicInterval 40),(⟨762123385504,762123410560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨249125744892,249643759981⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨224551745280,224551745344⟩ : DyadicInterval 40),(⟨-282498796992,-282498796928⟩ : DyadicInterval 40),(⟨733653522339,733653541668⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨224973989440,224973989504⟩ : DyadicInterval 40),(⟨-283168771904,-283168771840⟩ : DyadicInterval 40),(⟨733533949858,733533969188⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-58194782400,-57947051648⟩ : DyadicInterval 40),(⟨791096909440,791220794080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨224653347712,225024856192⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-283249526976,-282659948672⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e319_ok : ecellOkT e319 = true := by decide +kernel
theorem e319_pos {a z : ℝ} (ha1 : ((92853/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((232557/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e319 e319_ok ha1 ha2 hz1 hz2 hz

-- box ['57927/256000', '92853/409600', '1999/2000', '1']  interval_lower 252989997/1099511627776
noncomputable def e320 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1348306198331,0,true,224281713664,224281713728⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨850717057221,0,false,-282070686464,-282070686400⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1348762001736,0,true,224653347712,224653347776⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨850261253816,0,false,-282659948736,-282659948672⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1348181801045,0,true,224180265984,224180266048⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨850841454507,0,false,-281909920640,-281909920576⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576361240,0,true,64731520,64731584⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446894312,0,false,-64735424,-64735360⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623964,0,false,-3840,-3776⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1348243994059,0,true,224230986432,224230986496⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨850779261493,0,false,-281990293376,-281990293312⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1348762010312,0,true,224653354688,224653354752⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨850261245240,0,false,-282659959808,-282659959744⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1043008584402,0,false,-58006605120,-58006605056⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1043243200528,0,false,-57759306944,-57759306880⟩
    { al := (57927/256000), au := (92853/409600), zl := (1999/2000), zu := 1,
      A := ⟨248794570555,249250373960⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨224281713664,224281713728⟩ : DyadicInterval 40),(⟨-282070686464,-282070686400⟩ : DyadicInterval 40),(⟨733729831900,733729851230⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨224653347712,224653347776⟩ : DyadicInterval 40),(⟨-282659948736,-282659948672⟩ : DyadicInterval 40),(⟨733624777917,733624797246⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨224180265984,224180266048⟩ : DyadicInterval 40),(⟨-281909920640,-281909920576⟩ : DyadicInterval 40),(⟨733758468502,733758487831⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨224653347712,224653347776⟩ : DyadicInterval 40),(⟨-282659948736,-282659948672⟩ : DyadicInterval 40),(⟨733624777917,733624797246⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,64733464⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64731520,64731584⟩ : DyadicInterval 40),(⟨-64735424,-64735360⟩ : DyadicInterval 40),(⟨762123381692,762123401021⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3840,0⟩ : DyadicInterval 40),(⟨762123383616,762123404800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨248732366283,249250382536⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨224230986432,224230986496⟩ : DyadicInterval 40),(⟨-281990293376,-281990293312⟩ : DyadicInterval 40),(⟨733744153348,733744172677⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨224653354688,224653354752⟩ : DyadicInterval 40),(⟨-282659959808,-282659959744⟩ : DyadicInterval 40),(⟨733624775941,733624795270⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-58006605120,-57759306880⟩ : DyadicInterval 40),(⟨791003037056,791126705440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨224281713664,224653347776⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-282659948736,-282070686400⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e320_ok : ecellOkT e320 = true := by decide +kernel
theorem e320_pos {a z : ℝ} (ha1 : ((57927/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((92853/409600 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e320 e320_ok ha1 ha2 hz1 hz2 hz

-- box ['92853/409600', '232557/1024000', '1999/2000', '1']  interval_lower 265651633/1099511627776
noncomputable def e321 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1348762001735,0,true,224653347712,224653347776⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨850261253817,0,false,-282659948736,-282659948672⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1349217805140,0,true,225024856128,225024856192⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨849805450412,0,false,-283249526976,-283249526912⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1348637376547,0,true,224551748480,224551748544⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨850385879005,0,false,-282498802048,-282498801984⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576488923,0,true,64859200,64859264⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446766629,0,false,-64863104,-64863040⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623949,0,false,-3840,-3776⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1348699683507,0,true,224602544640,224602544704⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨850323572045,0,false,-282579365184,-282579365120⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1349217813708,0,true,225024863104,225024863168⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨849805441844,0,false,-283249538048,-283249537984⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1042801741570,0,false,-58224674880,-58224674816⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1043036838834,0,false,-57976820480,-57976820416⟩
    { al := (92853/409600), au := (232557/1024000), zl := (1999/2000), zu := 1,
      A := ⟨249250373959,249706177364⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨224653347712,224653347776⟩ : DyadicInterval 40),(⟨-282659948736,-282659948672⟩ : DyadicInterval 40),(⟨733624777917,733624797247⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨225024856128,225024856192⟩ : DyadicInterval 40),(⟨-283249526976,-283249526912⟩ : DyadicInterval 40),(⟨733519524780,733519544110⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨224551748480,224551748544⟩ : DyadicInterval 40),(⟨-282498802048,-282498801984⟩ : DyadicInterval 40),(⟨733653521437,733653540766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨225024856128,225024856192⟩ : DyadicInterval 40),(⟨-283249526976,-283249526912⟩ : DyadicInterval 40),(⟨733519524780,733519544110⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,64861147⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64859200,64859264⟩ : DyadicInterval 40),(⟨-64863104,-64863040⟩ : DyadicInterval 40),(⟨762123381677,762123401006⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3840,0⟩ : DyadicInterval 40),(⟨762123383616,762123404800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨249188055731,249706185932⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨224602544640,224602544704⟩ : DyadicInterval 40),(⟨-282579365184,-282579365120⟩ : DyadicInterval 40),(⟨733639152871,733639172201⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨225024863104,225024863168⟩ : DyadicInterval 40),(⟨-283249538048,-283249537984⟩ : DyadicInterval 40),(⟨733519522798,733519542128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-58224674880,-57976820416⟩ : DyadicInterval 40),(⟨791111793824,791235740320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨224653347712,225024856192⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-283249526976,-282659948672⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e321_ok : ecellOkT e321 = true := by decide +kernel
theorem e321_pos {a z : ℝ} (ha1 : ((92853/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((232557/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e321 e321_ok ha1 ha2 hz1 hz2 hz

-- box ['232557/1024000', '465963/2048000', '999/1000', '1999/2000']  interval_lower 281642495/1099511627776
noncomputable def e322 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1349217805139,0,true,225024856128,225024856192⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨849805450413,0,false,-283249526976,-283249526912⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1349673608545,0,true,225396239104,225396239168⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨849349647007,0,false,-283839421504,-283839421440⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1348968098961,0,true,224821345472,224821345536⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨850055156591,0,false,-282926494784,-282926494720⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1349548527555,0,true,225294337152,225294337216⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨849474727997,0,false,-283677511872,-283677511808⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576485857,0,true,64856128,64856192⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446769695,0,false,-64860032,-64859968⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099641602721,0,true,129967232,129967296⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099381652831,0,false,-129982656,-129982592⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511612411,0,false,-15424,-15360⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623951,0,false,-3840,-3776⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1349092948177,0,true,224923102336,224923102400⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨849930307375,0,false,-283087993984,-283087993920⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1349611077216,0,true,225345296768,225345296832⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨849412178336,0,false,-283758475584,-283758475520⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1042622975550,0,false,-58413178752,-58413178688⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1042858442927,0,false,-58164891648,-58164891584⟩
    { al := (232557/1024000), au := (465963/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨249706177363,250161980769⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨225024856128,225024856192⟩ : DyadicInterval 40),(⟨-283249526976,-283249526912⟩ : DyadicInterval 40),(⟨733519524780,733519544110⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨225396239104,225396239168⟩ : DyadicInterval 40),(⟨-283839421504,-283839421440⟩ : DyadicInterval 40),(⟨733414072377,733414091707⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨224821345472,224821345536⟩ : DyadicInterval 40),(⟨-282926494784,-282926494720⟩ : DyadicInterval 40),(⟨733577211053,733577230383⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨225294337152,225294337216⟩ : DyadicInterval 40),(⟨-283677511872,-283677511808⟩ : DyadicInterval 40),(⟨733443030320,733443049649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨64858081,129974945⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64856128,64856192⟩ : DyadicInterval 40),(⟨-64860032,-64859968⟩ : DyadicInterval 40),(⟨762123381678,762123401007⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨129967232,129967296⟩ : DyadicInterval 40),(⟨-129982656,-129982592⟩ : DyadicInterval 40),(⟨762123375899,762123395228⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-15424,-3776⟩ : DyadicInterval 40),(⟨762123385504,762123410592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨249581320401,250099449440⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨224923102336,224923102400⟩ : DyadicInterval 40),(⟨-283087993984,-283087993920⟩ : DyadicInterval 40),(⟨733548376286,733548395616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨225345296768,225345296832⟩ : DyadicInterval 40),(⟨-283758475584,-283758475520⟩ : DyadicInterval 40),(⟨733428551111,733428570441⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-58413178752,-58164891584⟩ : DyadicInterval 40),(⟨791205829408,791329992256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨225024856128,225396239168⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-283839421504,-283249526912⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e322_ok : ecellOkT e322 = true := by decide +kernel
theorem e322_pos {a z : ℝ} (ha1 : ((232557/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((465963/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e322 e322_ok ha1 ha2 hz1 hz2 hz

-- box ['465963/2048000', '116703/512000', '999/1000', '1999/2000']  interval_lower 73631559/274877906944
noncomputable def e323 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1349673608544,0,true,225396239104,225396239168⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨849349647008,0,false,-283839421504,-283839421440⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1350129411949,0,true,225767496704,225767496768⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨848893843603,0,false,-284429632704,-284429632640⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1349423446563,0,true,225192425792,225192425856⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨849599808989,0,false,-283515626112,-283515626048⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1350004103058,0,true,225665443520,225665443584⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨849019152494,0,false,-284267340992,-284267340928⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576613579,0,true,64983872,64983936⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446641973,0,false,-64987776,-64987712⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099641858290,0,true,130222784,130222848⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099381397262,0,false,-130238272,-130238208⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511612350,0,false,-15488,-15424⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623936,0,false,-3904,-3840⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1349548523686,0,true,225294334016,225294334080⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨849474731866,0,false,-283677506880,-283677506816⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1350066766678,0,true,225716478720,225716478784⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨848956488874,0,false,-284348495744,-284348495680⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1042415480682,0,false,-58632016960,-58632016896⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1042651429360,0,false,-58383172864,-58383172800⟩
    { al := (465963/2048000), au := (116703/512000), zl := (999/1000), zu := (1999/2000),
      A := ⟨250161980768,250617784173⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨225396239104,225396239168⟩ : DyadicInterval 40),(⟨-283839421504,-283839421440⟩ : DyadicInterval 40),(⟨733414072377,733414091707⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨225767496704,225767496768⟩ : DyadicInterval 40),(⟨-284429632704,-284429632640⟩ : DyadicInterval 40),(⟨733308420698,733308440028⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨225192425792,225192425856⟩ : DyadicInterval 40),(⟨-283515626112,-283515626048⟩ : DyadicInterval 40),(⟨733471973248,733471992577⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨225665443520,225665443584⟩ : DyadicInterval 40),(⟨-284267340992,-284267340928⟩ : DyadicInterval 40),(⟨733337486185,733337505515⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨64985803,130230514⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64983872,64983936⟩ : DyadicInterval 40),(⟨-64987776,-64987712⟩ : DyadicInterval 40),(⟨762123381662,762123400992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨130222784,130222848⟩ : DyadicInterval 40),(⟨-130238272,-130238208⟩ : DyadicInterval 40),(⟨762123375870,762123395200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-15488,-3840⟩ : DyadicInterval 40),(⟨762123385536,762123410624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨250036895910,250555138902⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨225294334016,225294334080⟩ : DyadicInterval 40),(⟨-283677506880,-283677506816⟩ : DyadicInterval 40),(⟨733443031212,733443050541⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨225716478720,225716478784⟩ : DyadicInterval 40),(⟨-284348495744,-284348495680⟩ : DyadicInterval 40),(⟨733322953229,733322972559⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-58632016960,-58383172800⟩ : DyadicInterval 40),(⟨791314970016,791439411360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨225396239104,225767496768⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-284429632704,-283839421440⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e323_ok : ecellOkT e323 = true := by decide +kernel
theorem e323_pos {a z : ℝ} (ha1 : ((465963/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((116703/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e323 e323_ok ha1 ha2 hz1 hz2 hz

-- box ['232557/1024000', '465963/2048000', '1999/2000', '1']  interval_lower 139206699/549755813888
noncomputable def e324 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1349217805139,0,true,225024856128,225024856192⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨849805450413,0,false,-283249526976,-283249526912⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1349673608545,0,true,225396239104,225396239168⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨849349647007,0,false,-283839421504,-283839421440⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1349092952050,0,true,224923105536,224923105600⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨849930303502,0,false,-283087999040,-283087998976⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576616661,0,true,64986944,64987008⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446638891,0,false,-64990848,-64990784⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623934,0,false,-3904,-3840⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1349155372951,0,true,224973977408,224973977472⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨849867882601,0,false,-283168752704,-283168752640⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1349673617117,0,true,225396246080,225396246144⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨849349638435,0,false,-283839432640,-283839432576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1042594520825,0,false,-58443186496,-58443186432⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1042830099423,0,false,-58194775296,-58194775232⟩
    { al := (232557/1024000), au := (465963/2048000), zl := (1999/2000), zu := 1,
      A := ⟨249706177363,250161980769⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨225024856128,225024856192⟩ : DyadicInterval 40),(⟨-283249526976,-283249526912⟩ : DyadicInterval 40),(⟨733519524780,733519544110⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨225396239104,225396239168⟩ : DyadicInterval 40),(⟨-283839421504,-283839421440⟩ : DyadicInterval 40),(⟨733414072377,733414091707⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨224923105536,224923105600⟩ : DyadicInterval 40),(⟨-283087999040,-283087998976⟩ : DyadicInterval 40),(⟨733548375383,733548394712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨225396239104,225396239168⟩ : DyadicInterval 40),(⟨-283839421504,-283839421440⟩ : DyadicInterval 40),(⟨733414072377,733414091707⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,64988885⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64986944,64987008⟩ : DyadicInterval 40),(⟨-64990848,-64990784⟩ : DyadicInterval 40),(⟨762123381662,762123400991⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3904,0⟩ : DyadicInterval 40),(⟨762123383616,762123404832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨249643745175,250161989341⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨224973977408,224973977472⟩ : DyadicInterval 40),(⟨-283168752704,-283168752640⟩ : DyadicInterval 40),(⟨733533953241,733533972571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨225396246080,225396246144⟩ : DyadicInterval 40),(⟨-283839432640,-283839432576⟩ : DyadicInterval 40),(⟨733414070412,733414089741⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-58443186496,-58194775232⟩ : DyadicInterval 40),(⟨791220771232,791344996128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨225024856128,225396239168⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-283839421504,-283249526912⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e324_ok : ecellOkT e324 = true := by decide +kernel
theorem e324_pos {a z : ℝ} (ha1 : ((232557/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((465963/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e324 e324_ok ha1 ha2 hz1 hz2 hz

-- box ['465963/2048000', '116703/512000', '1999/2000', '1']  interval_lower 291275993/1099511627776
noncomputable def e325 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1349673608544,0,true,225396239104,225396239168⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨849349647008,0,false,-283839421504,-283839421440⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1350129411949,0,true,225767496704,225767496768⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨848893843603,0,false,-284429632704,-284429632640⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1349548527553,0,true,225294337152,225294337216⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨849474727999,0,false,-283677511872,-283677511808⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576744453,0,true,65114688,65114752⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446511099,0,false,-65118656,-65118592⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623919,0,false,-3904,-3840⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1349611062399,0,true,225345284736,225345284800⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨849412193153,0,false,-283758456384,-283758456320⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1350129420528,0,true,225767503680,225767503744⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨848893835024,0,false,-284429643840,-284429643776⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1042386922172,0,false,-58662140096,-58662140032⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1042622982292,0,false,-58413171648,-58413171584⟩
    { al := (465963/2048000), au := (116703/512000), zl := (1999/2000), zu := 1,
      A := ⟨250161980768,250617784173⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨225396239104,225396239168⟩ : DyadicInterval 40),(⟨-283839421504,-283839421440⟩ : DyadicInterval 40),(⟨733414072377,733414091707⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨225767496704,225767496768⟩ : DyadicInterval 40),(⟨-284429632704,-284429632640⟩ : DyadicInterval 40),(⟨733308420698,733308440028⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨225294337152,225294337216⟩ : DyadicInterval 40),(⟨-283677511872,-283677511808⟩ : DyadicInterval 40),(⟨733443030320,733443049650⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨225767496704,225767496768⟩ : DyadicInterval 40),(⟨-284429632704,-284429632640⟩ : DyadicInterval 40),(⟨733308420698,733308440028⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,65116677⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65114688,65114752⟩ : DyadicInterval 40),(⟨-65118656,-65118592⟩ : DyadicInterval 40),(⟨762123381679,762123401008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3904,0⟩ : DyadicInterval 40),(⟨762123383616,762123404832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨250099434623,250617792752⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨225345284736,225345284800⟩ : DyadicInterval 40),(⟨-283758456384,-283758456320⟩ : DyadicInterval 40),(⟨733428554510,733428573839⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨225767503680,225767503744⟩ : DyadicInterval 40),(⟨-284429643840,-284429643776⟩ : DyadicInterval 40),(⟨733308418724,733308438053⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-58662140096,-58413171584⟩ : DyadicInterval 40),(⟨791329969408,791454472928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨225396239104,225767496768⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-284429632704,-283839421440⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e325_ok : ecellOkT e325 = true := by decide +kernel
theorem e325_pos {a z : ℝ} (ha1 : ((465963/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((116703/512000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e325 e325_ok ha1 ha2 hz1 hz2 hz

-- box ['116703/512000', '467661/2048000', '999/1000', '1999/2000']  interval_lower 307511361/1099511627776
noncomputable def e326 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1350129411948,0,true,225767496704,225767496768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨848893843604,0,false,-284429632704,-284429632640⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1350585215353,0,true,226138628928,226138628992⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨848438040199,0,false,-285020160896,-285020160832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1349878794163,0,true,225563380864,225563380928⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨849144461389,0,false,-284105073280,-284105073216⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1350459678560,0,true,226036424640,226036424704⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨848563576992,0,false,-284857486720,-284857486656⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576741355,0,true,65111616,65111680⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446514197,0,false,-65115520,-65115456⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099642113967,0,true,130478400,130478464⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099381141585,0,false,-130493952,-130493888⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511612290,0,false,-15488,-15424⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623920,0,false,-3904,-3840⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1350004099189,0,true,225665440384,225665440448⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨849019156363,0,false,-284267336000,-284267335936⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1350522456128,0,true,226087535424,226087535488⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨848500799424,0,false,-284938832704,-284938832640⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1042207608101,0,false,-58851297216,-58851297152⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1042444038267,0,false,-58601895616,-58601895552⟩
    { al := (116703/512000), au := (467661/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨250617784172,251073587577⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨225767496704,225767496768⟩ : DyadicInterval 40),(⟨-284429632704,-284429632640⟩ : DyadicInterval 40),(⟨733308420698,733308440028⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨226138628928,226138628992⟩ : DyadicInterval 40),(⟨-285020160896,-285020160832⟩ : DyadicInterval 40),(⟨733202569748,733202589078⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨225563380864,225563380928⟩ : DyadicInterval 40),(⟨-284105073280,-284105073216⟩ : DyadicInterval 40),(⟨733366536629,733366555958⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨226036424640,226036424704⟩ : DyadicInterval 40),(⟨-284857486720,-284857486656⟩ : DyadicInterval 40),(⟨733231742984,733231762314⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨65113579,130486191⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65111616,65111680⟩ : DyadicInterval 40),(⟨-65115520,-65115456⟩ : DyadicInterval 40),(⟨762123381647,762123400977⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨130478400,130478464⟩ : DyadicInterval 40),(⟨-130493952,-130493888⟩ : DyadicInterval 40),(⟨762123375842,762123395171⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-15488,-3840⟩ : DyadicInterval 40),(⟨762123385536,762123410624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨250492471413,251010828352⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨225665440384,225665440448⟩ : DyadicInterval 40),(⟨-284267336000,-284267335936⟩ : DyadicInterval 40),(⟨733337487080,733337506410⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨226087535424,226087535488⟩ : DyadicInterval 40),(⟨-284938832704,-284938832640⟩ : DyadicInterval 40),(⟨733217156142,733217175471⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-58851297216,-58601895552⟩ : DyadicInterval 40),(⟨791424331392,791549051488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨225767496704,226138628992⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-285020160896,-284429632640⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e326_ok : ecellOkT e326 = true := by decide +kernel
theorem e326_pos {a z : ℝ} (ha1 : ((116703/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((467661/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e326 e326_ok ha1 ha2 hz1 hz2 hz

-- box ['467661/2048000', '46851/204800', '999/1000', '1999/2000']  interval_lower 320597845/1099511627776
noncomputable def e327 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1350585215352,0,true,226138628928,226138628992⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨848438040200,0,false,-285020160896,-285020160832⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1351041018758,0,true,226509635968,226509636032⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨847982236794,0,false,-285611006400,-285611006336⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1350334141764,0,true,225934210880,225934210944⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨848689113788,0,false,-284694836608,-284694836544⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1350915254063,0,true,226407280640,226407280704⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨848108001489,0,false,-285447949312,-285447949248⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576869187,0,true,65239424,65239488⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446386365,0,false,-65243392,-65243328⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099642369754,0,true,130734144,130734208⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099380885798,0,false,-130749760,-130749696⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511612229,0,false,-15552,-15488⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623905,0,false,-3904,-3840⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1350459674694,0,true,226036421504,226036421568⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨848563580858,0,false,-284857481728,-284857481664⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1350978145589,0,true,226458466944,226458467008⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨848045109963,0,false,-285529486720,-285529486656⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1041999357797,0,false,-59071019712,-59071019648⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1042236269644,0,false,-58821060160,-58821060096⟩
    { al := (467661/2048000), au := (46851/204800), zl := (999/1000), zu := (1999/2000),
      A := ⟨251073587576,251529390982⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨226138628928,226138628992⟩ : DyadicInterval 40),(⟨-285020160896,-285020160832⟩ : DyadicInterval 40),(⟨733202569748,733202589078⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨226509635968,226509636032⟩ : DyadicInterval 40),(⟨-285611006400,-285611006336⟩ : DyadicInterval 40),(⟨733096519413,733096538742⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨225934210880,225934210944⟩ : DyadicInterval 40),(⟨-284694836608,-284694836544⟩ : DyadicInterval 40),(⟨733260901082,733260920412⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨226407280640,226407280704⟩ : DyadicInterval 40),(⟨-285447949312,-285447949248⟩ : DyadicInterval 40),(⟨733125800617,733125819946⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨65241411,130741978⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65239424,65239488⟩ : DyadicInterval 40),(⟨-65243392,-65243328⟩ : DyadicInterval 40),(⟨762123381664,762123400993⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨130734144,130734208⟩ : DyadicInterval 40),(⟨-130749760,-130749696⟩ : DyadicInterval 40),(⟨762123375813,762123395142⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-15552,-3840⟩ : DyadicInterval 40),(⟨762123385536,762123410656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨250948046918,251466517813⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨226036421504,226036421568⟩ : DyadicInterval 40),(⟨-284857481728,-284857481664⟩ : DyadicInterval 40),(⟨733231743882,733231763211⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨226458466944,226458467008⟩ : DyadicInterval 40),(⟨-285529486720,-285529486656⟩ : DyadicInterval 40),(⟨733111159783,733111179113⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-59071019712,-58821060096⟩ : DyadicInterval 40),(⟨791533913664,791658912736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨226138628928,226509636032⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-285611006400,-285020160832⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e327_ok : ecellOkT e327 = true := by decide +kernel
theorem e327_pos {a z : ℝ} (ha1 : ((467661/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((46851/204800 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e327 e327_ok ha1 ha2 hz1 hz2 hz

-- box ['116703/512000', '467661/2048000', '1999/2000', '1']  interval_lower 152119737/549755813888
noncomputable def e328 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1350129411948,0,true,225767496704,225767496768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨848893843604,0,false,-284429632704,-284429632640⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1350585215353,0,true,226138628928,226138628992⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨848438040199,0,false,-285020160896,-285020160832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1350004103055,0,true,225665443520,225665443584⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨849019152497,0,false,-284267340992,-284267340928⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576872298,0,true,65242560,65242624⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446383254,0,false,-65246464,-65246400⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623904,0,false,-3904,-3840⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1350066751850,0,true,225716466688,225716466752⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨848956503702,0,false,-284348476544,-284348476480⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1350585223926,0,true,226138635904,226138635968⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨848438031626,0,false,-285020171968,-285020171904⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1042178945618,0,false,-58881536064,-58881536000⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1042415487441,0,false,-58632009856,-58632009792⟩
    { al := (116703/512000), au := (467661/2048000), zl := (1999/2000), zu := 1,
      A := ⟨250617784172,251073587577⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨225767496704,225767496768⟩ : DyadicInterval 40),(⟨-284429632704,-284429632640⟩ : DyadicInterval 40),(⟨733308420698,733308440028⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨226138628928,226138628992⟩ : DyadicInterval 40),(⟨-285020160896,-285020160832⟩ : DyadicInterval 40),(⟨733202569748,733202589078⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨225665443520,225665443584⟩ : DyadicInterval 40),(⟨-284267340992,-284267340928⟩ : DyadicInterval 40),(⟨733337486186,733337505515⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨226138628928,226138628992⟩ : DyadicInterval 40),(⟨-285020160896,-285020160832⟩ : DyadicInterval 40),(⟨733202569748,733202589078⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,65244522⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65242560,65242624⟩ : DyadicInterval 40),(⟨-65246464,-65246400⟩ : DyadicInterval 40),(⟨762123381632,762123400961⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3904,0⟩ : DyadicInterval 40),(⟨762123383616,762123404832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨250555124074,251073596150⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨225716466688,225716466752⟩ : DyadicInterval 40),(⟨-284348476544,-284348476480⟩ : DyadicInterval 40),(⟨733322956643,733322975973⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨226138635904,226138635968⟩ : DyadicInterval 40),(⟨-285020171968,-285020171904⟩ : DyadicInterval 40),(⟨733202567743,733202587072⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-58881536064,-58632009792⟩ : DyadicInterval 40),(⟨791439388512,791564170912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨225767496704,226138628992⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-285020160896,-284429632640⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e328_ok : ecellOkT e328 = true := by decide +kernel
theorem e328_pos {a z : ℝ} (ha1 : ((116703/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((467661/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e328 e328_ok ha1 ha2 hz1 hz2 hz

-- box ['467661/2048000', '46851/204800', '1999/2000', '1']  interval_lower 4957885/17179869184
noncomputable def e329 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1350585215352,0,true,226138628928,226138628992⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨848438040200,0,false,-285020160896,-285020160832⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1351041018758,0,true,226509635968,226509636032⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨847982236794,0,false,-285611006400,-285611006336⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1350459678558,0,true,226036424640,226036424704⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨848563576994,0,false,-284857486720,-284857486656⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577000199,0,true,65370432,65370496⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446255353,0,false,-65374400,-65374336⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623889,0,false,-3904,-3840⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1350522441290,0,true,226087523392,226087523456⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨848500814262,0,false,-284938813440,-284938813376⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1351041027337,0,true,226509642944,226509643008⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨847982228215,0,false,-285611017536,-285611017472⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1041970591150,0,false,-59101374592,-59101374528⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1042207614877,0,false,-58851290048,-58851289984⟩
    { al := (467661/2048000), au := (46851/204800), zl := (1999/2000), zu := 1,
      A := ⟨251073587576,251529390982⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨226138628928,226138628992⟩ : DyadicInterval 40),(⟨-285020160896,-285020160832⟩ : DyadicInterval 40),(⟨733202569748,733202589078⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨226509635968,226509636032⟩ : DyadicInterval 40),(⟨-285611006400,-285611006336⟩ : DyadicInterval 40),(⟨733096519413,733096538742⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨226036424640,226036424704⟩ : DyadicInterval 40),(⟨-284857486720,-284857486656⟩ : DyadicInterval 40),(⟨733231742985,733231762314⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨226509635968,226509636032⟩ : DyadicInterval 40),(⟨-285611006400,-285611006336⟩ : DyadicInterval 40),(⟨733096519413,733096538742⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,65372423⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65370432,65370496⟩ : DyadicInterval 40),(⟨-65374400,-65374336⟩ : DyadicInterval 40),(⟨762123381649,762123400978⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3904,0⟩ : DyadicInterval 40),(⟨762123383616,762123404832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨251010813514,251529399561⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨226087523392,226087523456⟩ : DyadicInterval 40),(⟨-284938813440,-284938813376⟩ : DyadicInterval 40),(⟨733217159546,733217178875⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨226509642944,226509643008⟩ : DyadicInterval 40),(⟨-285611017536,-285611017472⟩ : DyadicInterval 40),(⟨733096517423,733096536752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-59101374592,-58851289984⟩ : DyadicInterval 40),(⟨791549028608,791674090176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨226138628928,226509636032⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-285611006400,-285020160832⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e329_ok : ecellOkT e329 = true := by decide +kernel
theorem e329_pos {a z : ℝ} (ha1 : ((467661/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((46851/204800 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e329 e329_ok ha1 ha2 hz1 hz2 hz

-- box ['46851/204800', '469359/2048000', '999/1000', '1999/2000']  interval_lower 83446659/274877906944
noncomputable def e330 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1351041018757,0,true,226509635968,226509636032⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨847982236795,0,false,-285611006400,-285611006336⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1351496822162,0,true,226880517824,226880517888⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨847526433390,0,false,-286202169600,-286202169536⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1350789489365,0,true,226304915840,226304915904⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨848233766187,0,false,-285284916416,-285284916352⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1351370829566,0,true,226778011648,226778011712⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨847652425986,0,false,-286038729216,-286038729152⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576997072,0,true,65367296,65367360⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446258480,0,false,-65371264,-65371200⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099642625651,0,true,130990016,130990080⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099380629901,0,false,-131005696,-131005632⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511612168,0,false,-15616,-15552⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623890,0,false,-3904,-3840⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1350915250204,0,true,226407277504,226407277568⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨848108005348,0,false,-285447944320,-285447944256⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1351433835047,0,true,226829273408,226829273472⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨847589420505,0,false,-286120458304,-286120458240⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1041790729776,0,false,-59291184832,-59291184768⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1042028123489,0,false,-59040666752,-59040666688⟩
    { al := (46851/204800), au := (469359/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨251529390981,251985194386⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨226509635968,226509636032⟩ : DyadicInterval 40),(⟨-285611006400,-285611006336⟩ : DyadicInterval 40),(⟨733096519413,733096538743⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨226880517824,226880517888⟩ : DyadicInterval 40),(⟨-286202169600,-286202169536⟩ : DyadicInterval 40),(⟨732990269720,732990289050⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨226304915840,226304915904⟩ : DyadicInterval 40),(⟨-285284916416,-285284916352⟩ : DyadicInterval 40),(⟨733155066614,733155085943⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨226778011648,226778011712⟩ : DyadicInterval 40),(⟨-286038729216,-286038729152⟩ : DyadicInterval 40),(⟨733019659059,733019678388⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨65369296,130997875⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65367296,65367360⟩ : DyadicInterval 40),(⟨-65371264,-65371200⟩ : DyadicInterval 40),(⟨762123381649,762123400978⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨130990016,130990080⟩ : DyadicInterval 40),(⟨-131005696,-131005632⟩ : DyadicInterval 40),(⟨762123375784,762123395113⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-15616,-3840⟩ : DyadicInterval 40),(⟨762123385536,762123410688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨251403622428,251922207271⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨226407277504,226407277568⟩ : DyadicInterval 40),(⟨-285447944320,-285447944256⟩ : DyadicInterval 40),(⟨733125801516,733125820846⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨226829273408,226829273472⟩ : DyadicInterval 40),(⟨-286120458304,-286120458240⟩ : DyadicInterval 40),(⟨733004964156,733004983486⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-59291184832,-59040666688⟩ : DyadicInterval 40),(⟨791643716960,791768995296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨226509635968,226880517888⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-286202169600,-285611006336⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e330_ok : ecellOkT e330 = true := by decide +kernel
theorem e330_pos {a z : ℝ} (ha1 : ((46851/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((469359/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e330 e330_ok ha1 ha2 hz1 hz2 hz

-- box ['469359/2048000', '7347/32000', '999/1000', '1999/2000']  interval_lower 347078241/1099511627776
noncomputable def e331 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1351496822161,0,true,226880517824,226880517888⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨847526433391,0,false,-286202169600,-286202169536⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1351952625566,0,true,227251274624,227251274688⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨847070629986,0,false,-286793650816,-286793650752⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1351244836966,0,true,226675495872,226675495936⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨847778418586,0,false,-285875313152,-285875313088⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1351826405068,0,true,227148617664,227148617728⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨847196850484,0,false,-286629826688,-286629826624⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577125013,0,true,65495232,65495296⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446130539,0,false,-65499200,-65499136⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099642881656,0,true,131246016,131246080⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099380373896,0,false,-131261760,-131261696⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511612107,0,false,-15680,-15616⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623875,0,false,-3904,-3840⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1351370825704,0,true,226778008512,226778008576⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨847652429848,0,false,-286038724224,-286038724160⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1351889524503,0,true,227199954816,227199954880⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨847133731049,0,false,-286711747648,-286711747584⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1041581724037,0,false,-59511792768,-59511792704⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1041819599808,0,false,-59260715712,-59260715648⟩
    { al := (469359/2048000), au := (7347/32000), zl := (999/1000), zu := (1999/2000),
      A := ⟨251985194385,252440997790⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨226880517824,226880517888⟩ : DyadicInterval 40),(⟨-286202169600,-286202169536⟩ : DyadicInterval 40),(⟨732990269721,732990289050⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨227251274624,227251274688⟩ : DyadicInterval 40),(⟨-286793650816,-286793650752⟩ : DyadicInterval 40),(⟨732883820597,732883839926⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨226675495872,226675495936⟩ : DyadicInterval 40),(⟨-285875313152,-285875313088⟩ : DyadicInterval 40),(⟨733049033198,733049052528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨227148617664,227148617728⟩ : DyadicInterval 40),(⟨-286629826688,-286629826624⟩ : DyadicInterval 40),(⟨732913318289,732913337618⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨65497237,131253880⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65495232,65495296⟩ : DyadicInterval 40),(⟨-65499200,-65499136⟩ : DyadicInterval 40),(⟨762123381634,762123400963⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨131246016,131246080⟩ : DyadicInterval 40),(⟨-131261760,-131261696⟩ : DyadicInterval 40),(⟨762123375755,762123395084⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-15680,-3840⟩ : DyadicInterval 40),(⟨762123385536,762123410720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨251859197928,252377896727⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨226778008512,226778008576⟩ : DyadicInterval 40),(⟨-286038724224,-286038724160⟩ : DyadicInterval 40),(⟨733019659962,733019679292⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨227199954816,227199954880⟩ : DyadicInterval 40),(⟨-286711747648,-286711747584⟩ : DyadicInterval 40),(⟨732898569216,732898588546⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-59511792768,-59260715648⟩ : DyadicInterval 40),(⟨791753741440,791879299264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨226880517824,227251274688⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-286793650816,-286202169536⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e331_ok : ecellOkT e331 = true := by decide +kernel
theorem e331_pos {a z : ℝ} (ha1 : ((469359/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((7347/32000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e331 e331_ok ha1 ha2 hz1 hz2 hz

-- box ['46851/204800', '469359/2048000', '1999/2000', '1']  interval_lower 330471779/1099511627776
noncomputable def e332 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1351041018757,0,true,226509635968,226509636032⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨847982236795,0,false,-285611006400,-285611006336⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1351496822162,0,true,226880517824,226880517888⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨847526433390,0,false,-286202169600,-286202169536⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1350915254061,0,true,226407280640,226407280704⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨848108001491,0,false,-285447949312,-285447949248⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577128156,0,true,65498368,65498432⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446127396,0,false,-65502336,-65502272⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623873,0,false,-3904,-3840⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1350978130741,0,true,226458454912,226458454976⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨848045124811,0,false,-285529467520,-285529467456⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1351496830737,0,true,226880524800,226880524864⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨847526424815,0,false,-286202180736,-286202180672⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1041761858781,0,false,-59321655872,-59321655808⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1041999364590,0,false,-59071012544,-59071012480⟩
    { al := (46851/204800), au := (469359/2048000), zl := (1999/2000), zu := 1,
      A := ⟨251529390981,251985194386⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨226509635968,226509636032⟩ : DyadicInterval 40),(⟨-285611006400,-285611006336⟩ : DyadicInterval 40),(⟨733096519413,733096538743⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨226880517824,226880517888⟩ : DyadicInterval 40),(⟨-286202169600,-286202169536⟩ : DyadicInterval 40),(⟨732990269720,732990289050⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨226407280640,226407280704⟩ : DyadicInterval 40),(⟨-285447949312,-285447949248⟩ : DyadicInterval 40),(⟨733125800618,733125819947⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨226880517824,226880517888⟩ : DyadicInterval 40),(⟨-286202169600,-286202169536⟩ : DyadicInterval 40),(⟨732990269720,732990289050⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,65500380⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65498368,65498432⟩ : DyadicInterval 40),(⟨-65502336,-65502272⟩ : DyadicInterval 40),(⟨762123381633,762123400963⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3904,0⟩ : DyadicInterval 40),(⟨762123383616,762123404832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨251466502965,251985202961⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨226458454912,226458454976⟩ : DyadicInterval 40),(⟨-285529467520,-285529467456⟩ : DyadicInterval 40),(⟨733111163227,733111182557⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨226880524800,226880524864⟩ : DyadicInterval 40),(⟨-286202180736,-286202180672⟩ : DyadicInterval 40),(⟨732990267724,732990287054⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-59321655872,-59071012480⟩ : DyadicInterval 40),(⟨791658889856,791784230816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨226509635968,226880517888⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-286202169600,-285611006336⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e332_ok : ecellOkT e332 = true := by decide +kernel
theorem e332_pos {a z : ℝ} (ha1 : ((46851/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((469359/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e332 e332_ok ha1 ha2 hz1 hz2 hz

-- box ['469359/2048000', '7347/32000', '1999/2000', '1']  interval_lower 343741617/1099511627776
noncomputable def e333 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1351496822161,0,true,226880517824,226880517888⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨847526433391,0,false,-286202169600,-286202169536⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1351952625566,0,true,227251274624,227251274688⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨847070629986,0,false,-286793650816,-286793650752⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1351370829563,0,true,226778011648,226778011712⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨847652425989,0,false,-286038729216,-286038729152⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577256166,0,true,65626368,65626432⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445999386,0,false,-65630400,-65630336⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623858,0,false,-3968,-3904⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1351433820188,0,true,226829261312,226829261376⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨847589435364,0,false,-286120438976,-286120438912⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1351952634137,0,true,227251281600,227251281664⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨847070621415,0,false,-286793661888,-286793661824⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1041552748503,0,false,-59542380288,-59542380224⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1041790736586,0,false,-59291177664,-59291177600⟩
    { al := (469359/2048000), au := (7347/32000), zl := (1999/2000), zu := 1,
      A := ⟨251985194385,252440997790⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨226880517824,226880517888⟩ : DyadicInterval 40),(⟨-286202169600,-286202169536⟩ : DyadicInterval 40),(⟨732990269721,732990289050⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨227251274624,227251274688⟩ : DyadicInterval 40),(⟨-286793650816,-286793650752⟩ : DyadicInterval 40),(⟨732883820597,732883839926⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨226778011648,226778011712⟩ : DyadicInterval 40),(⟨-286038729216,-286038729152⟩ : DyadicInterval 40),(⟨733019659060,733019678389⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨227251274624,227251274688⟩ : DyadicInterval 40),(⟨-286793650816,-286793650752⟩ : DyadicInterval 40),(⟨732883820597,732883839926⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,65628390⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65626368,65626432⟩ : DyadicInterval 40),(⟨-65630400,-65630336⟩ : DyadicInterval 40),(⟨762123381650,762123400979⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3968,0⟩ : DyadicInterval 40),(⟨762123383616,762123404864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨251922192412,252441006361⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨226829261312,226829261376⟩ : DyadicInterval 40),(⟨-286120438976,-286120438912⟩ : DyadicInterval 40),(⟨733004967607,733004986936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨227251281600,227251281664⟩ : DyadicInterval 40),(⟨-286793661888,-286793661824⟩ : DyadicInterval 40),(⟨732883818569,732883837899⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-59542380288,-59291177600⟩ : DyadicInterval 40),(⟨791768972416,791894593024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨226880517824,227251274688⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-286793650816,-286202169536⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e333_ok : ecellOkT e333 = true := by decide +kernel
theorem e333_pos {a z : ℝ} (ha1 : ((469359/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((7347/32000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e333 e333_ok ha1 ha2 hz1 hz2 hz

-- box ['7347/32000', '471057/2048000', '999/1000', '1999/2000']  interval_lower 180236469/549755813888
noncomputable def e334 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1351952625565,0,true,227251274624,227251274688⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨847070629987,0,false,-286793650816,-286793650752⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1352408428970,0,true,227621906432,227621906496⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨846614826582,0,false,-287385450368,-287385450304⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1351700184567,0,true,227045951040,227045951104⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨847323070985,0,false,-286466027008,-286466026944⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1352281980570,0,true,227519098752,227519098816⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨846741274982,0,false,-287221242112,-287221242048⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577253009,0,true,65623232,65623296⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446002543,0,false,-65627200,-65627136⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099643137773,0,true,131502080,131502144⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099380117779,0,false,-131517888,-131517824⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511612046,0,false,-15744,-15680⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623860,0,false,-3968,-3904⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1351826401210,0,true,227148614528,227148614592⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨847196854342,0,false,-286629821696,-286629821632⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1352345213955,0,true,227570511296,227570511360⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨846678041597,0,false,-287303355136,-287303355072⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1041372340582,0,false,-59732843776,-59732843712⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1041610698596,0,false,-59481207168,-59481207104⟩
    { al := (7347/32000), au := (471057/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨252440997789,252896801194⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨227251274624,227251274688⟩ : DyadicInterval 40),(⟨-286793650816,-286793650752⟩ : DyadicInterval 40),(⟨732883820597,732883839927⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨227621906432,227621906496⟩ : DyadicInterval 40),(⟨-287385450368,-287385450304⟩ : DyadicInterval 40),(⟨732777172006,732777191335⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨227045951040,227045951104⟩ : DyadicInterval 40),(⟨-286466027008,-286466026944⟩ : DyadicInterval 40),(⟨732942800751,732942820080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨227519098752,227519098816⟩ : DyadicInterval 40),(⟨-287221242112,-287221242048⟩ : DyadicInterval 40),(⟨732806778296,732806797626⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨65625233,131509997⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65623232,65623296⟩ : DyadicInterval 40),(⟨-65627200,-65627136⟩ : DyadicInterval 40),(⟨762123381618,762123400948⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨131502080,131502144⟩ : DyadicInterval 40),(⟨-131517888,-131517824⟩ : DyadicInterval 40),(⟨762123375726,762123395055⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-15744,-3904⟩ : DyadicInterval 40),(⟨762123385568,762123410752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨252314773434,252833586179⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨227148614528,227148614592⟩ : DyadicInterval 40),(⟨-286629821696,-286629821632⟩ : DyadicInterval 40),(⟨732913319195,732913338525⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨227570511296,227570511360⟩ : DyadicInterval 40),(⟨-287303355136,-287303355072⟩ : DyadicInterval 40),(⟨732791974911,732791994241⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-59732843776,-59481207104⟩ : DyadicInterval 40),(⟨791863987168,791989824768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨227251274624,227621906496⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-287385450368,-286793650752⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e334_ok : ecellOkT e334 = true := by decide +kernel
theorem e334_pos {a z : ℝ} (ha1 : ((7347/32000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((471057/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e334 e334_ok ha1 ha2 hz1 hz2 hz

-- box ['471057/2048000', '235953/1024000', '999/1000', '1999/2000']  interval_lower 373971013/1099511627776
noncomputable def e335 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1352408428969,0,true,227621906432,227621906496⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨846614826583,0,false,-287385450368,-287385450304⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1352864232375,0,true,227992413376,227992413440⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨846159023177,0,false,-287977568640,-287977568576⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1352155532167,0,true,227416281472,227416281536⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨846867723385,0,false,-287057058432,-287057058368⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1352737556073,0,true,227889455104,227889455168⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨846285699479,0,false,-287812975872,-287812975808⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577381060,0,true,65751296,65751360⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445874492,0,false,-65755264,-65755200⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099643394000,0,true,131758272,131758336⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099379861552,0,false,-131774144,-131774080⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511611985,0,false,-15808,-15744⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623844,0,false,-3968,-3904⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1352281976717,0,true,227519095616,227519095680⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨846741278835,0,false,-287221237120,-287221237056⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1352800903412,0,true,227940942912,227940942976⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨846222352140,0,false,-287895281088,-287895281024⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1041162579406,0,false,-59954338112,-59954338048⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1041401419854,0,false,-59702141440,-59702141376⟩
    { al := (471057/2048000), au := (235953/1024000), zl := (999/1000), zu := (1999/2000),
      A := ⟨252896801193,253352604599⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨227621906432,227621906496⟩ : DyadicInterval 40),(⟨-287385450368,-287385450304⟩ : DyadicInterval 40),(⟨732777172006,732777191335⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨227992413376,227992413440⟩ : DyadicInterval 40),(⟨-287977568640,-287977568576⟩ : DyadicInterval 40),(⟨732670323895,732670343224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨227416281472,227416281536⟩ : DyadicInterval 40),(⟨-287057058432,-287057058368⟩ : DyadicInterval 40),(⟨732836369247,732836388576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨227889455104,227889455168⟩ : DyadicInterval 40),(⟨-287812975872,-287812975808⟩ : DyadicInterval 40),(⟨732700038990,732700058319⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨65753284,131766224⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65751296,65751360⟩ : DyadicInterval 40),(⟨-65755264,-65755200⟩ : DyadicInterval 40),(⟨762123381603,762123400932⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨131758272,131758336⟩ : DyadicInterval 40),(⟨-131774144,-131774080⟩ : DyadicInterval 40),(⟨762123375696,762123395026⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-15808,-3904⟩ : DyadicInterval 40),(⟨762123385568,762123410784⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨252770348941,253289275636⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨227519095616,227519095680⟩ : DyadicInterval 40),(⟨-287221237120,-287221237056⟩ : DyadicInterval 40),(⟨732806779204,732806798534⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨227940942912,227940942976⟩ : DyadicInterval 40),(⟨-287895281088,-287895281024⟩ : DyadicInterval 40),(⟨732685181204,732685200533⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-59954338112,-59702141376⟩ : DyadicInterval 40),(⟨791974454304,792100571936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨227621906432,227992413440⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-287977568640,-287385450304⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e335_ok : ecellOkT e335 = true := by decide +kernel
theorem e335_pos {a z : ℝ} (ha1 : ((471057/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((235953/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e335 e335_ok ha1 ha2 hz1 hz2 hz

-- box ['7347/32000', '471057/2048000', '1999/2000', '1']  interval_lower 357114393/1099511627776
noncomputable def e336 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1351952625565,0,true,227251274624,227251274688⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨847070629987,0,false,-286793650816,-286793650752⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1352408428970,0,true,227621906432,227621906496⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨846614826582,0,false,-287385450368,-287385450304⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1351826405066,0,true,227148617664,227148617728⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨847196850486,0,false,-286629826688,-286629826624⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577384233,0,true,65754432,65754496⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445871319,0,false,-65758464,-65758400⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623843,0,false,-3968,-3904⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1351889509635,0,true,227199942720,227199942784⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨847133745917,0,false,-286711728320,-286711728256⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1352408437538,0,true,227621913408,227621913472⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨846614818014,0,false,-287385461504,-287385461440⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1041343260318,0,false,-59763548032,-59763547968⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1041581730864,0,false,-59511785600,-59511785536⟩
    { al := (7347/32000), au := (471057/2048000), zl := (1999/2000), zu := 1,
      A := ⟨252440997789,252896801194⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨227251274624,227251274688⟩ : DyadicInterval 40),(⟨-286793650816,-286793650752⟩ : DyadicInterval 40),(⟨732883820597,732883839927⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨227621906432,227621906496⟩ : DyadicInterval 40),(⟨-287385450368,-287385450304⟩ : DyadicInterval 40),(⟨732777172006,732777191335⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨227148617664,227148617728⟩ : DyadicInterval 40),(⟨-286629826688,-286629826624⟩ : DyadicInterval 40),(⟨732913318290,732913337619⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨227621906432,227621906496⟩ : DyadicInterval 40),(⟨-287385450368,-287385450304⟩ : DyadicInterval 40),(⟨732777172006,732777191335⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,65756457⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65754432,65754496⟩ : DyadicInterval 40),(⟨-65758464,-65758400⟩ : DyadicInterval 40),(⟨762123381635,762123400964⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3968,0⟩ : DyadicInterval 40),(⟨762123383616,762123404864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨252377881859,252896809762⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨227199942720,227199942784⟩ : DyadicInterval 40),(⟨-286711728320,-286711728256⟩ : DyadicInterval 40),(⟨732898572681,732898592010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨227621913408,227621913472⟩ : DyadicInterval 40),(⟨-287385461504,-287385461440⟩ : DyadicInterval 40),(⟨732777169996,732777189325⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-59763548032,-59511785536⟩ : DyadicInterval 40),(⟨791879276384,792005176896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨227251274624,227621906496⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-287385450368,-286793650752⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e336_ok : ecellOkT e336 = true := by decide +kernel
theorem e336_pos {a z : ℝ} (ha1 : ((7347/32000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((471057/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e336 e336_ok ha1 ha2 hz1 hz2 hz

-- box ['471057/2048000', '235953/1024000', '1999/2000', '1']  interval_lower 185295217/549755813888
noncomputable def e337 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1352408428969,0,true,227621906432,227621906496⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨846614826583,0,false,-287385450368,-287385450304⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1352864232375,0,true,227992413376,227992413440⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨846159023177,0,false,-287977568640,-287977568576⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1352281980568,0,true,227519098752,227519098816⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨846741274984,0,false,-287221242112,-287221242048⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577512354,0,true,65882560,65882624⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445743198,0,false,-65886592,-65886528⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623828,0,false,-3968,-3904⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1352345199076,0,true,227570499200,227570499264⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨846678056476,0,false,-287303335808,-287303335744⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1352864240943,0,true,227992420352,227992420416⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨846159014609,0,false,-287977579712,-287977579648⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1041133394224,0,false,-59985159360,-59985159296⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1041372347426,0,false,-59732836544,-59732836480⟩
    { al := (471057/2048000), au := (235953/1024000), zl := (1999/2000), zu := 1,
      A := ⟨252896801193,253352604599⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨227621906432,227621906496⟩ : DyadicInterval 40),(⟨-287385450368,-287385450304⟩ : DyadicInterval 40),(⟨732777172006,732777191335⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨227992413376,227992413440⟩ : DyadicInterval 40),(⟨-287977568640,-287977568576⟩ : DyadicInterval 40),(⟨732670323895,732670343224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨227519098752,227519098816⟩ : DyadicInterval 40),(⟨-287221242112,-287221242048⟩ : DyadicInterval 40),(⟨732806778296,732806797626⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨227992413376,227992413440⟩ : DyadicInterval 40),(⟨-287977568640,-287977568576⟩ : DyadicInterval 40),(⟨732670323895,732670343224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,65884578⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65882560,65882624⟩ : DyadicInterval 40),(⟨-65886592,-65886528⟩ : DyadicInterval 40),(⟨762123381619,762123400949⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3968,0⟩ : DyadicInterval 40),(⟨762123383616,762123404864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨252833571300,253352613167⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨227570499200,227570499264⟩ : DyadicInterval 40),(⟨-287303335808,-287303335744⟩ : DyadicInterval 40),(⟨732791978392,732791997721⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨227992420352,227992420416⟩ : DyadicInterval 40),(⟨-287977579712,-287977579648⟩ : DyadicInterval 40),(⟨732670321853,732670341183⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-59985159360,-59732836480⟩ : DyadicInterval 40),(⟨791989801856,792115982560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨227621906432,227992413440⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-287977568640,-287385450304⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e337_ok : ecellOkT e337 = true := by decide +kernel
theorem e337_pos {a z : ℝ} (ha1 : ((471057/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((235953/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e337 e337_ok ha1 ha2 hz1 hz2 hz

-- box ['235953/1024000', '94551/409600', '999/1000', '1999/2000']  interval_lower 193786671/549755813888
noncomputable def e338 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1352864232374,0,true,227992413376,227992413440⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨846159023178,0,false,-287977568640,-287977568576⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1353320035779,0,true,228362795520,228362795584⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨845703219773,0,false,-288570005888,-288570005824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1352610879769,0,true,227786487168,227786487232⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨846412375783,0,false,-287648407744,-287648407680⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1353193131576,0,true,228259686720,228259686784⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨845830123976,0,false,-288405028224,-288405028160⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577509166,0,true,65879360,65879424⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445746386,0,false,-65883392,-65883328⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099643650338,0,true,132014592,132014656⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099379605214,0,false,-132030528,-132030464⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511611923,0,false,-15872,-15808⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623829,0,false,-3968,-3904⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1352737552221,0,true,227889451968,227889452032⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨846285703331,0,false,-287812970880,-287812970816⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1353256592872,0,true,228311249792,228311249856⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨845766662680,0,false,-288487525952,-288487525888⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1040952440510,0,false,-60176276096,-60176276032⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1041191763583,0,false,-59923518848,-59923518784⟩
    { al := (235953/1024000), au := (94551/409600), zl := (999/1000), zu := (1999/2000),
      A := ⟨253352604598,253808408003⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨227992413376,227992413440⟩ : DyadicInterval 40),(⟨-287977568640,-287977568576⟩ : DyadicInterval 40),(⟨732670323895,732670343225⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨228362795520,228362795584⟩ : DyadicInterval 40),(⟨-288570005888,-288570005824⟩ : DyadicInterval 40),(⟨732563276204,732563295533⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨227786487168,227786487232⟩ : DyadicInterval 40),(⟨-287648407744,-287648407680⟩ : DyadicInterval 40),(⟨732729738688,732729758018⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨228259686720,228259686784⟩ : DyadicInterval 40),(⟨-288405028224,-288405028160⟩ : DyadicInterval 40),(⟨732593100348,732593119678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨65881390,132022562⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65879360,65879424⟩ : DyadicInterval 40),(⟨-65883392,-65883328⟩ : DyadicInterval 40),(⟨762123381620,762123400949⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨132014592,132014656⟩ : DyadicInterval 40),(⟨-132030528,-132030464⟩ : DyadicInterval 40),(⟨762123375667,762123394996⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-15872,-3904⟩ : DyadicInterval 40),(⟨762123385568,762123410816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨253225924445,253744965096⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨227889451968,227889452032⟩ : DyadicInterval 40),(⟨-287812970880,-287812970816⟩ : DyadicInterval 40),(⟨732700039901,732700059230⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨228311249792,228311249856⟩ : DyadicInterval 40),(⟨-288487525952,-288487525888⟩ : DyadicInterval 40),(⟨732578188067,732578207397⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-60176276096,-59923518784⟩ : DyadicInterval 40),(⟨792085143008,792211540928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨227992413376,228362795584⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-288570005888,-287977568576⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e338_ok : ecellOkT e338 = true := by decide +kernel
theorem e338_pos {a z : ℝ} (ha1 : ((235953/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((94551/409600 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e338 e338_ok ha1 ha2 hz1 hz2 hz

-- box ['94551/409600', '118401/512000', '999/1000', '1999/2000']  interval_lower 50160047/137438953472
noncomputable def e339 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1353320035778,0,true,228362795520,228362795584⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨845703219774,0,false,-288570005888,-288570005824⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1353775839183,0,true,228733052928,228733052992⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨845247416369,0,false,-289162762624,-289162762560⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1353066227369,0,true,228156568256,228156568320⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨845957028183,0,false,-288240075264,-288240075200⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1353648707078,0,true,228629793728,228629793792⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨845374548474,0,false,-288997399552,-288997399488⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577637326,0,true,66007552,66007616⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445618226,0,false,-66011584,-66011520⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099643906786,0,true,132271040,132271104⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099379348766,0,false,-132286976,-132286912⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511611861,0,false,-15936,-15872⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623814,0,false,-3968,-3904⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1353193127729,0,true,228259683648,228259683712⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨845830127823,0,false,-288405023232,-288405023168⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1353712282327,0,true,228681432000,228681432064⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨845310973225,0,false,-289080089920,-289080089856⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1040741923898,0,false,-60398657856,-60398657792⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1040981729781,0,false,-60145339584,-60145339520⟩
    { al := (94551/409600), au := (118401/512000), zl := (999/1000), zu := (1999/2000),
      A := ⟨253808408002,254264211407⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨228362795520,228362795584⟩ : DyadicInterval 40),(⟨-288570005888,-288570005824⟩ : DyadicInterval 40),(⟨732563276204,732563295533⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨228733052928,228733052992⟩ : DyadicInterval 40),(⟨-289162762624,-289162762560⟩ : DyadicInterval 40),(⟨732456028968,732456048298⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨228156568256,228156568320⟩ : DyadicInterval 40),(⟨-288240075264,-288240075200⟩ : DyadicInterval 40),(⟨732622909001,732622928330⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨228629793728,228629793792⟩ : DyadicInterval 40),(⟨-288997399552,-288997399488⟩ : DyadicInterval 40),(⟨732485962320,732485981649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨66009550,132279010⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66007552,66007616⟩ : DyadicInterval 40),(⟨-66011584,-66011520⟩ : DyadicInterval 40),(⟨762123381604,762123400934⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨132271040,132271104⟩ : DyadicInterval 40),(⟨-132286976,-132286912⟩ : DyadicInterval 40),(⟨762123375605,762123394934⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-15936,-3904⟩ : DyadicInterval 40),(⟨762123385568,762123410848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨253681499953,254200654551⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨228259683648,228259683712⟩ : DyadicInterval 40),(⟨-288405023232,-288405023168⟩ : DyadicInterval 40),(⟨732593101222,732593120552⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨228681432000,228681432064⟩ : DyadicInterval 40),(⟨-289080089920,-289080089856⟩ : DyadicInterval 40),(⟨732470995418,732471014747⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-60398657856,-60145339520⟩ : DyadicInterval 40),(⟨792196053376,792322731808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨228362795520,228733052992⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-289162762624,-288570005824⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e339_ok : ecellOkT e339 = true := by decide +kernel
theorem e339_pos {a z : ℝ} (ha1 : ((94551/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((118401/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e339 e339_ok ha1 ha2 hz1 hz2 hz

-- box ['235953/1024000', '94551/409600', '1999/2000', '1']  interval_lower 384170577/1099511627776
noncomputable def e340 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1352864232374,0,true,227992413376,227992413440⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨846159023178,0,false,-287977568640,-287977568576⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1353320035779,0,true,228362795520,228362795584⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨845703219773,0,false,-288570005888,-288570005824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1352737556071,0,true,227889455104,227889455168⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨846285699481,0,false,-287812975872,-287812975808⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577640530,0,true,66010752,66010816⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445615022,0,false,-66014784,-66014720⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623812,0,false,-3968,-3904⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1352800888522,0,true,227940930816,227940930880⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨846222367030,0,false,-287895261760,-287895261696⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1353320044357,0,true,228362802496,228362802560⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨845703211195,0,false,-288570017088,-288570017024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1040923150219,0,false,-60207214528,-60207214464⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1041162586267,0,false,-59954330880,-59954330816⟩
    { al := (235953/1024000), au := (94551/409600), zl := (1999/2000), zu := 1,
      A := ⟨253352604598,253808408003⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨227992413376,227992413440⟩ : DyadicInterval 40),(⟨-287977568640,-287977568576⟩ : DyadicInterval 40),(⟨732670323895,732670343225⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨228362795520,228362795584⟩ : DyadicInterval 40),(⟨-288570005888,-288570005824⟩ : DyadicInterval 40),(⟨732563276204,732563295533⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨227889455104,227889455168⟩ : DyadicInterval 40),(⟨-287812975872,-287812975808⟩ : DyadicInterval 40),(⟨732700038990,732700058320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨228362795520,228362795584⟩ : DyadicInterval 40),(⟨-288570005888,-288570005824⟩ : DyadicInterval 40),(⟨732563276204,732563295533⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,66012754⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66010752,66010816⟩ : DyadicInterval 40),(⟨-66014784,-66014720⟩ : DyadicInterval 40),(⟨762123381604,762123400933⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3968,0⟩ : DyadicInterval 40),(⟨762123383616,762123404864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨253289260746,253808416581⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨227940930816,227940930880⟩ : DyadicInterval 40),(⟨-287895261760,-287895261696⟩ : DyadicInterval 40),(⟨732685184700,732685204030⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨228362802496,228362802560⟩ : DyadicInterval 40),(⟨-288570017088,-288570017024⟩ : DyadicInterval 40),(⟨732563274201,732563293531⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-60207214528,-59954330816⟩ : DyadicInterval 40),(⟨792100549024,792227010144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨227992413376,228362795584⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-288570005888,-287977568576⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e340_ok : ecellOkT e340 = true := by decide +kernel
theorem e340_pos {a z : ℝ} (ha1 : ((235953/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((94551/409600 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e340 e340_ok ha1 ha2 hz1 hz2 hz

-- box ['94551/409600', '118401/512000', '1999/2000', '1']  interval_lower 397855137/1099511627776
noncomputable def e341 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1353320035778,0,true,228362795520,228362795584⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨845703219774,0,false,-288570005888,-288570005824⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1353775839183,0,true,228733052928,228733052992⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨845247416369,0,false,-289162762624,-289162762560⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1353193131573,0,true,228259686720,228259686784⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨845830123979,0,false,-288405028224,-288405028160⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577768762,0,true,66138944,66139008⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445486790,0,false,-66142976,-66142912⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623797,0,false,-4032,-3968⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1353256577972,0,true,228311237696,228311237760⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨845766677580,0,false,-288487506560,-288487506496⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1353775847758,0,true,228733059904,228733059968⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨845247407794,0,false,-289162773760,-289162773696⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1040712528312,0,false,-60429713856,-60429713792⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1040952447388,0,false,-60176268800,-60176268736⟩
    { al := (94551/409600), au := (118401/512000), zl := (1999/2000), zu := 1,
      A := ⟨253808408002,254264211407⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨228362795520,228362795584⟩ : DyadicInterval 40),(⟨-288570005888,-288570005824⟩ : DyadicInterval 40),(⟨732563276204,732563295533⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨228733052928,228733052992⟩ : DyadicInterval 40),(⟨-289162762624,-289162762560⟩ : DyadicInterval 40),(⟨732456028968,732456048298⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨228259686720,228259686784⟩ : DyadicInterval 40),(⟨-288405028224,-288405028160⟩ : DyadicInterval 40),(⟨732593100348,732593119678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨228733052928,228733052992⟩ : DyadicInterval 40),(⟨-289162762624,-289162762560⟩ : DyadicInterval 40),(⟨732456028968,732456048298⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,66140986⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66138944,66139008⟩ : DyadicInterval 40),(⟨-66142976,-66142912⟩ : DyadicInterval 40),(⟨762123381589,762123400918⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4032,0⟩ : DyadicInterval 40),(⟨762123383616,762123404896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨253744950196,254264219982⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨228311237696,228311237760⟩ : DyadicInterval 40),(⟨-288487506560,-288487506496⟩ : DyadicInterval 40),(⟨732578191555,732578210884⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨228733059904,228733059968⟩ : DyadicInterval 40),(⟨-289162773760,-289162773696⟩ : DyadicInterval 40),(⟨732456026935,732456046264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-60429713856,-60176268736⟩ : DyadicInterval 40),(⟨792211517984,792338259808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨228362795520,228733052992⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-289162762624,-288570005824⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e341_ok : ecellOkT e341 = true := by decide +kernel
theorem e341_pos {a z : ℝ} (ha1 : ((94551/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((118401/512000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e341 e341_ok ha1 ha2 hz1 hz2 hz

-- box ['118401/512000', '474453/2048000', '999/1000', '1999/2000']  interval_lower 415092445/1099511627776
noncomputable def e342 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1353775839182,0,true,228733052928,228733052992⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨845247416370,0,false,-289162762624,-289162762560⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1354231642588,0,true,229103185728,229103185792⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨844791612964,0,false,-289755839040,-289755838976⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1353521574970,0,true,228526524864,228526524928⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨845501680582,0,false,-288832061312,-288832061248⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1354104282581,0,true,228999776192,228999776256⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨844918972971,0,false,-289590090176,-289590090112⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577765542,0,true,66135744,66135808⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445490010,0,false,-66139776,-66139712⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099644163346,0,true,132527552,132527616⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099379092206,0,false,-132543616,-132543552⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511611800,0,false,-16000,-15936⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623798,0,false,-4032,-3968⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1353648703237,0,true,228629790656,228629790720⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨845374552315,0,false,-288997394560,-288997394496⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1354167971790,0,true,229051489664,229051489728⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨844855283762,0,false,-289672973440,-289672973376⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1040531029564,0,false,-60621483776,-60621483712⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1040771318450,0,false,-60367603840,-60367603776⟩
    { al := (118401/512000), au := (474453/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨254264211406,254720014812⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨228733052928,228733052992⟩ : DyadicInterval 40),(⟨-289162762624,-289162762560⟩ : DyadicInterval 40),(⟨732456028969,732456048298⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨229103185728,229103185792⟩ : DyadicInterval 40),(⟨-289755839040,-289755838976⟩ : DyadicInterval 40),(⟨732348582063,732348601392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨228526524864,228526524928⟩ : DyadicInterval 40),(⟨-288832061312,-288832061248⟩ : DyadicInterval 40),(⟨732515880108,732515899437⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨228999776192,228999776256⟩ : DyadicInterval 40),(⟨-289590090176,-289590090112⟩ : DyadicInterval 40),(⟨732378624867,732378644196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨66137766,132535570⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66135744,66135808⟩ : DyadicInterval 40),(⟨-66139776,-66139712⟩ : DyadicInterval 40),(⟨762123381589,762123400918⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨132527552,132527616⟩ : DyadicInterval 40),(⟨-132543616,-132543552⟩ : DyadicInterval 40),(⟨762123375608,762123394937⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-16000,-3968⟩ : DyadicInterval 40),(⟨762123385600,762123410880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨254137075461,254656344014⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨228629790656,228629790720⟩ : DyadicInterval 40),(⟨-288997394560,-288997394496⟩ : DyadicInterval 40),(⟨732485963196,732485982525⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨229051489664,229051489728⟩ : DyadicInterval 40),(⟨-289672973440,-289672973376⟩ : DyadicInterval 40),(⟨732363603224,732363622553⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-60621483776,-60367603776⟩ : DyadicInterval 40),(⟨792307185504,792434144768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨228733052928,229103185792⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-289755839040,-289162762560⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e342_ok : ecellOkT e342 = true := by decide +kernel
theorem e342_pos {a z : ℝ} (ha1 : ((118401/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((474453/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e342 e342_ok ha1 ha2 hz1 hz2 hz

-- box ['474453/2048000', '237651/1024000', '999/1000', '1999/2000']  interval_lower 429010247/1099511627776
noncomputable def e343 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1354231642587,0,true,229103185728,229103185792⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨844791612965,0,false,-289755839040,-289755838976⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1354687445992,0,true,229473193920,229473193984⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨844335809560,0,false,-290349235520,-290349235456⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1353976922572,0,true,228896356992,228896357056⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨845046332980,0,false,-289424366272,-289424366208⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1354559858084,0,true,229369634240,229369634304⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨844463397468,0,false,-290183100480,-290183100416⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577893815,0,true,66264000,66264064⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445361737,0,false,-66268096,-66268032⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099644420017,0,true,132784192,132784256⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099378835535,0,false,-132800320,-132800256⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511611738,0,false,-16064,-16000⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623783,0,false,-4032,-3968⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1354104278748,0,true,228999773120,228999773184⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨844918976804,0,false,-289590085184,-289590085120⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1354623661250,0,true,229421422784,229421422848⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨844399594302,0,false,-290266176896,-290266176832⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1040319757513,0,false,-60844754048,-60844753984⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1040560529588,0,false,-60590312064,-60590312000⟩
    { al := (474453/2048000), au := (237651/1024000), zl := (999/1000), zu := (1999/2000),
      A := ⟨254720014811,255175818216⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨229103185728,229103185792⟩ : DyadicInterval 40),(⟨-289755839040,-289755838976⟩ : DyadicInterval 40),(⟨732348582063,732348601393⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨229473193920,229473193984⟩ : DyadicInterval 40),(⟨-290349235520,-290349235456⟩ : DyadicInterval 40),(⟨732240935514,732240954843⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨228896356992,228896357056⟩ : DyadicInterval 40),(⟨-289424366272,-289424366208⟩ : DyadicInterval 40),(⟨732408652036,732408671365⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨229369634240,229369634304⟩ : DyadicInterval 40),(⟨-290183100480,-290183100416⟩ : DyadicInterval 40),(⟨732271087938,732271107267⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨66266039,132792241⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66264000,66264064⟩ : DyadicInterval 40),(⟨-66268096,-66268032⟩ : DyadicInterval 40),(⟨762123381606,762123400935⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨132784192,132784256⟩ : DyadicInterval 40),(⟨-132800320,-132800256⟩ : DyadicInterval 40),(⟨762123375578,762123394907⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-16064,-3968⟩ : DyadicInterval 40),(⟨762123385600,762123410912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨254592650972,255112033474⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨228999773120,228999773184⟩ : DyadicInterval 40),(⟨-289590085184,-289590085120⟩ : DyadicInterval 40),(⟨732378625744,732378645074⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨229421422784,229421422848⟩ : DyadicInterval 40),(⟨-290266176896,-290266176832⟩ : DyadicInterval 40),(⟨732256011515,732256030844⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-60844754048,-60590312000⟩ : DyadicInterval 40),(⟨792418539616,792545779904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨229103185728,229473193984⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-290349235520,-289755838976⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e343_ok : ecellOkT e343 = true := by decide +kernel
theorem e343_pos {a z : ℝ} (ha1 : ((474453/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((237651/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e343 e343_ok ha1 ha2 hz1 hz2 hz

-- box ['118401/512000', '474453/2048000', '1999/2000', '1']  interval_lower 205822341/549755813888
noncomputable def e344 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1353775839182,0,true,228733052928,228733052992⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨845247416370,0,false,-289162762624,-289162762560⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1354231642588,0,true,229103185728,229103185792⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨844791612964,0,false,-289755839040,-289755838976⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1353648707076,0,true,228629793728,228629793792⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨845374548476,0,false,-288997399552,-288997399488⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577897049,0,true,66267264,66267328⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445358503,0,false,-66271296,-66271232⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623781,0,false,-4032,-3968⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1353712267418,0,true,228681419904,228681419968⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨845310988134,0,false,-289080070528,-289080070464⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1354231651172,0,true,229103192704,229103192768⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨844791604380,0,false,-289755850240,-289755850176⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1040501528492,0,false,-60652657536,-60652657472⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1040741930793,0,false,-60398650560,-60398650496⟩
    { al := (118401/512000), au := (474453/2048000), zl := (1999/2000), zu := 1,
      A := ⟨254264211406,254720014812⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨228733052928,228733052992⟩ : DyadicInterval 40),(⟨-289162762624,-289162762560⟩ : DyadicInterval 40),(⟨732456028969,732456048298⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨229103185728,229103185792⟩ : DyadicInterval 40),(⟨-289755839040,-289755838976⟩ : DyadicInterval 40),(⟨732348582063,732348601392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨228629793728,228629793792⟩ : DyadicInterval 40),(⟨-288997399552,-288997399488⟩ : DyadicInterval 40),(⟨732485962320,732485981650⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨229103185728,229103185792⟩ : DyadicInterval 40),(⟨-289755839040,-289755838976⟩ : DyadicInterval 40),(⟨732348582063,732348601392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,66269273⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66267264,66267328⟩ : DyadicInterval 40),(⟨-66271296,-66271232⟩ : DyadicInterval 40),(⟨762123381573,762123400902⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4032,0⟩ : DyadicInterval 40),(⟨762123383616,762123404896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨254200639642,254720023396⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨228681419904,228681419968⟩ : DyadicInterval 40),(⟨-289080070528,-289080070464⟩ : DyadicInterval 40),(⟨732470998920,732471018250⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨229103192704,229103192768⟩ : DyadicInterval 40),(⟨-289755850240,-289755850176⟩ : DyadicInterval 40),(⟨732348580044,732348599374⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-60652657536,-60398650496⟩ : DyadicInterval 40),(⟨792322708864,792449731648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨228733052928,229103185792⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-289755839040,-289162762560⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e344_ok : ecellOkT e344 = true := by decide +kernel
theorem e344_pos {a z : ℝ} (ha1 : ((118401/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((474453/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e344 e344_ok ha1 ha2 hz1 hz2 hz

-- box ['474453/2048000', '237651/1024000', '1999/2000', '1']  interval_lower 106385045/274877906944
noncomputable def e345 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1354231642587,0,true,229103185728,229103185792⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨844791612965,0,false,-289755839040,-289755838976⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1354687445992,0,true,229473193920,229473193984⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨844335809560,0,false,-290349235520,-290349235456⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1354104282579,0,true,228999776192,228999776256⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨844918972973,0,false,-289590090176,-289590090112⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578025392,0,true,66395584,66395648⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445230160,0,false,-66399680,-66399616⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623766,0,false,-4032,-3968⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1354167956870,0,true,229051477568,229051477632⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨844855298682,0,false,-289672954048,-289672953984⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1354687454577,0,true,229473200896,229473200960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨844335800975,0,false,-290349246720,-290349246656⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1040290150768,0,false,-60876045824,-60876045760⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1040531036476,0,false,-60621476480,-60621476416⟩
    { al := (474453/2048000), au := (237651/1024000), zl := (1999/2000), zu := 1,
      A := ⟨254720014811,255175818216⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨229103185728,229103185792⟩ : DyadicInterval 40),(⟨-289755839040,-289755838976⟩ : DyadicInterval 40),(⟨732348582063,732348601393⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨229473193920,229473193984⟩ : DyadicInterval 40),(⟨-290349235520,-290349235456⟩ : DyadicInterval 40),(⟨732240935514,732240954843⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨228999776192,228999776256⟩ : DyadicInterval 40),(⟨-289590090176,-289590090112⟩ : DyadicInterval 40),(⟨732378624867,732378644197⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨229473193920,229473193984⟩ : DyadicInterval 40),(⟨-290349235520,-290349235456⟩ : DyadicInterval 40),(⟨732240935514,732240954843⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,66397616⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66395584,66395648⟩ : DyadicInterval 40),(⟨-66399680,-66399616⟩ : DyadicInterval 40),(⟨762123381590,762123400919⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4032,0⟩ : DyadicInterval 40),(⟨762123383616,762123404896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨254656329094,255175826801⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨229051477568,229051477632⟩ : DyadicInterval 40),(⟨-289672954048,-289672953984⟩ : DyadicInterval 40),(⟨732363606742,732363626071⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨229473200896,229473200960⟩ : DyadicInterval 40),(⟨-290349246720,-290349246656⟩ : DyadicInterval 40),(⟨732240933487,732240952817⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-60876045824,-60621476416⟩ : DyadicInterval 40),(⟨792434121824,792561425792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨229103185728,229473193984⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-290349235520,-289755838976⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e345_ok : ecellOkT e345 = true := by decide +kernel
theorem e345_pos {a z : ℝ} (ha1 : ((474453/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((237651/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e345 e345_ok ha1 ha2 hz1 hz2 hz

-- box ['237651/1024000', '476151/2048000', '999/1000', '1999/2000']  interval_lower 443033697/1099511627776
noncomputable def e346 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1354687445991,0,true,229473193920,229473193984⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨844335809561,0,false,-290349235520,-290349235456⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1355143249396,0,true,229843077632,229843077696⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨843880006156,0,false,-290942952448,-290942952384⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1354432270172,0,true,229266064768,229266064832⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨844590985380,0,false,-290016990464,-290016990400⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1355015433586,0,true,229739367872,229739367936⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨844007821966,0,false,-290776430784,-290776430720⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578022143,0,true,66392320,66392384⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445233409,0,false,-66396416,-66396352⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099644676799,0,true,133040960,133041024⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099378578753,0,false,-133057088,-133057024⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511611676,0,false,-16128,-16064⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623767,0,false,-4032,-3968⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1354559854254,0,true,229369631104,229369631168⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨844463401298,0,false,-290183095488,-290183095424⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1355079350704,0,true,229791231488,229791231552⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨843943904848,0,false,-290859700480,-290859700416⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1040108107747,0,false,-61068468992,-61068468928⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1040349363198,0,false,-60813464320,-60813464256⟩
    { al := (237651/1024000), au := (476151/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨255175818215,255631621620⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨229473193920,229473193984⟩ : DyadicInterval 40),(⟨-290349235520,-290349235456⟩ : DyadicInterval 40),(⟨732240935514,732240954843⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨229843077632,229843077696⟩ : DyadicInterval 40),(⟨-290942952448,-290942952384⟩ : DyadicInterval 40),(⟨732133089268,732133108597⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨229266064768,229266064832⟩ : DyadicInterval 40),(⟨-290016990464,-290016990400⟩ : DyadicInterval 40),(⟨732301224710,732301244039⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨229739367872,229739367936⟩ : DyadicInterval 40),(⟨-290776430784,-290776430720⟩ : DyadicInterval 40),(⟨732163351534,732163370863⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨66394367,133049023⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66392320,66392384⟩ : DyadicInterval 40),(⟨-66396416,-66396352⟩ : DyadicInterval 40),(⟨762123381590,762123400919⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨133040960,133041024⟩ : DyadicInterval 40),(⟨-133057088,-133057024⟩ : DyadicInterval 40),(⟨762123375516,762123394845⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-16128,-3968⟩ : DyadicInterval 40),(⟨762123385600,762123410944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨255048226478,255567722928⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨229369631104,229369631168⟩ : DyadicInterval 40),(⟨-290183095488,-290183095424⟩ : DyadicInterval 40),(⟨732271088857,732271108187⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨229791231488,229791231552⟩ : DyadicInterval 40),(⟨-290859700480,-290859700416⟩ : DyadicInterval 40),(⟨732148220165,732148239494⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-61068468992,-60813464256⟩ : DyadicInterval 40),(⟨792530115744,792657637376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨229473193920,229843077696⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-290942952448,-290349235456⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e346_ok : ecellOkT e346 = true := by decide +kernel
theorem e346_pos {a z : ℝ} (ha1 : ((237651/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((476151/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e346 e346_ok ha1 ha2 hz1 hz2 hz

-- box ['476151/2048000', '477/2048', '999/1000', '1999/2000']  interval_lower 457164345/1099511627776
noncomputable def e347 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1355143249395,0,true,229843077632,229843077696⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨843880006157,0,false,-290942952448,-290942952384⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1355599052800,0,true,230212836992,230212837056⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨843424202752,0,false,-291536990144,-291536990080⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1354887617773,0,true,229635648320,229635648384⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨844135637779,0,false,-290609934272,-290609934208⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1355471009088,0,true,230108977216,230108977280⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨843552246464,0,false,-291370081472,-291370081408⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578150526,0,true,66520704,66520768⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445105026,0,false,-66524800,-66524736⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099644933694,0,true,133297792,133297856⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099378321858,0,false,-133314048,-133313984⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511611613,0,false,-16192,-16128⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623752,0,false,-4032,-3968⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1355015429762,0,true,229739364800,229739364864⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨844007825790,0,false,-290776425792,-290776425728⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1355535040161,0,true,230160915840,230160915904⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨843488215391,0,false,-291453544640,-291453544576⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1039896080260,0,false,-61292628800,-61292628736⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1040137819278,0,false,-61037060992,-61037060928⟩
    { al := (476151/2048000), au := (477/2048), zl := (999/1000), zu := (1999/2000),
      A := ⟨255631621619,256087425024⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨229843077632,229843077696⟩ : DyadicInterval 40),(⟨-290942952448,-290942952384⟩ : DyadicInterval 40),(⟨732133089268,732133108597⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨230212836992,230212837056⟩ : DyadicInterval 40),(⟨-291536990144,-291536990080⟩ : DyadicInterval 40),(⟨732025043246,732025062576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨229635648320,229635648384⟩ : DyadicInterval 40),(⟨-290609934272,-290609934208⟩ : DyadicInterval 40),(⟨732193598075,732193617404⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨230108977216,230108977280⟩ : DyadicInterval 40),(⟨-291370081472,-291370081408⟩ : DyadicInterval 40),(⟨732055415602,732055434931⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨66522750,133305918⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66520704,66520768⟩ : DyadicInterval 40),(⟨-66524800,-66524736⟩ : DyadicInterval 40),(⟨762123381575,762123400904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨133297792,133297856⟩ : DyadicInterval 40),(⟨-133314048,-133313984⟩ : DyadicInterval 40),(⟨762123375517,762123394846⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-16192,-3968⟩ : DyadicInterval 40),(⟨762123385600,762123410976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨255503801986,256023412385⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨229739364800,229739364864⟩ : DyadicInterval 40),(⟨-290776425792,-290776425728⟩ : DyadicInterval 40),(⟨732163352416,732163371745⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨230160915840,230160915904⟩ : DyadicInterval 40),(⟨-291453544640,-291453544576⟩ : DyadicInterval 40),(⟨732040229182,732040248511⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-61292628800,-61037060928⟩ : DyadicInterval 40),(⟨792641914080,792769717280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨229843077632,230212837056⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-291536990144,-290942952384⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e347_ok : ecellOkT e347 = true := by decide +kernel
theorem e347_pos {a z : ℝ} (ha1 : ((476151/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((477/2048 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e347 e347_ok ha1 ha2 hz1 hz2 hz

-- box ['237651/1024000', '476151/2048000', '1999/2000', '1']  interval_lower 54942641/137438953472
noncomputable def e348 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1354687445991,0,true,229473193920,229473193984⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨844335809561,0,false,-290349235520,-290349235456⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1355143249396,0,true,229843077632,229843077696⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨843880006156,0,false,-290942952448,-290942952384⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1354559858081,0,true,229369634240,229369634304⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨844463397471,0,false,-290183100480,-290183100416⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578153792,0,true,66523968,66524032⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445101760,0,false,-66528064,-66528000⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623750,0,false,-4032,-3968⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1354623646320,0,true,229421410624,229421410688⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨844399609232,0,false,-290266157440,-290266157376⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1355143257977,0,true,229843084608,229843084672⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨843879997575,0,false,-290942963648,-290942963584⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1040078395140,0,false,-61099879040,-61099878976⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1040319764442,0,false,-60844746752,-60844746688⟩
    { al := (237651/1024000), au := (476151/2048000), zl := (1999/2000), zu := 1,
      A := ⟨255175818215,255631621620⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨229473193920,229473193984⟩ : DyadicInterval 40),(⟨-290349235520,-290349235456⟩ : DyadicInterval 40),(⟨732240935514,732240954843⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨229843077632,229843077696⟩ : DyadicInterval 40),(⟨-290942952448,-290942952384⟩ : DyadicInterval 40),(⟨732133089268,732133108597⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨229369634240,229369634304⟩ : DyadicInterval 40),(⟨-290183100480,-290183100416⟩ : DyadicInterval 40),(⟨732271087939,732271107268⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨229843077632,229843077696⟩ : DyadicInterval 40),(⟨-290942952448,-290942952384⟩ : DyadicInterval 40),(⟨732133089268,732133108597⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,66526016⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66523968,66524032⟩ : DyadicInterval 40),(⟨-66528064,-66528000⟩ : DyadicInterval 40),(⟨762123381574,762123400903⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4032,0⟩ : DyadicInterval 40),(⟨762123383616,762123404896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨255112018544,255631630201⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨229421410624,229421410688⟩ : DyadicInterval 40),(⟨-290266157440,-290266157376⟩ : DyadicInterval 40),(⟨732256015063,732256034393⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨229843084608,229843084672⟩ : DyadicInterval 40),(⟨-290942963648,-290942963584⟩ : DyadicInterval 40),(⟨732133087234,732133106564⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-61099879040,-60844746688⟩ : DyadicInterval 40),(⟨792545756960,792673342400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨229473193920,229843077696⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-290942952448,-290349235456⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e348_ok : ecellOkT e348 = true := by decide +kernel
theorem e348_pos {a z : ℝ} (ha1 : ((237651/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((476151/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e348 e348_ok ha1 ha2 hz1 hz2 hz

-- box ['476151/2048000', '477/2048', '1999/2000', '1']  interval_lower 113412121/274877906944
noncomputable def e349 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1355143249395,0,true,229843077632,229843077696⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨843880006157,0,false,-290942952448,-290942952384⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1355599052800,0,true,230212836992,230212837056⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨843424202752,0,false,-291536990144,-291536990080⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1355015433584,0,true,229739367872,229739367936⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨844007821968,0,false,-290776430784,-290776430720⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578282247,0,true,66652416,66652480⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444973305,0,false,-66656512,-66656448⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623735,0,false,-4096,-4032⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1355079335765,0,true,229791219328,229791219392⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨843943919787,0,false,-290859681024,-290859680960⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1355599061386,0,true,230212843968,230212844032⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨843424194166,0,false,-291537001344,-291537001280⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1039866261600,0,false,-61324157376,-61324157312⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1040108114692,0,false,-61068461632,-61068461568⟩
    { al := (476151/2048000), au := (477/2048), zl := (1999/2000), zu := 1,
      A := ⟨255631621619,256087425024⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨229843077632,229843077696⟩ : DyadicInterval 40),(⟨-290942952448,-290942952384⟩ : DyadicInterval 40),(⟨732133089268,732133108597⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨230212836992,230212837056⟩ : DyadicInterval 40),(⟨-291536990144,-291536990080⟩ : DyadicInterval 40),(⟨732025043246,732025062576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨229739367872,229739367936⟩ : DyadicInterval 40),(⟨-290776430784,-290776430720⟩ : DyadicInterval 40),(⟨732163351534,732163370864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨230212836992,230212837056⟩ : DyadicInterval 40),(⟨-291536990144,-291536990080⟩ : DyadicInterval 40),(⟨732025043246,732025062576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,66654471⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66652416,66652480⟩ : DyadicInterval 40),(⟨-66656512,-66656448⟩ : DyadicInterval 40),(⟨762123381559,762123400888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4096,0⟩ : DyadicInterval 40),(⟨762123383616,762123404928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨255567707989,256087433610⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨229791219328,229791219392⟩ : DyadicInterval 40),(⟨-290859681024,-290859680960⟩ : DyadicInterval 40),(⟨732148223728,732148243057⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨230212843968,230212844032⟩ : DyadicInterval 40),(⟨-291537001344,-291537001280⟩ : DyadicInterval 40),(⟨732025041205,732025060534⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-61324157376,-61068461568⟩ : DyadicInterval 40),(⟨792657614400,792785481568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨229843077632,230212837056⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-291536990144,-290942952384⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e349_ok : ecellOkT e349 = true := by decide +kernel
theorem e349_pos {a z : ℝ} (ha1 : ((476151/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((477/2048 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e349 e349_ok ha1 ha2 hz1 hz2 hz

-- box ['477/2048', '477849/2048000', '999/1000', '1999/2000']  interval_lower 471401803/1099511627776
noncomputable def e350 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1355599052800,0,true,230212836992,230212837056⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨843424202752,0,false,-291536990144,-291536990080⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1356054856205,0,true,230582472000,230582472064⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨842968399347,0,false,-292131348992,-292131348928⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1355342965374,0,true,230005107648,230005107712⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨843680290178,0,false,-291203198016,-291203197952⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1355926584591,0,true,230478462400,230478462464⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨843096670961,0,false,-291964052800,-291964052736⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578278966,0,true,66649152,66649216⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444976586,0,false,-66653248,-66653184⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099645190701,0,true,133554752,133554816⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099378064851,0,false,-133571072,-133571008⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511611551,0,false,-16256,-16192⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623736,0,false,-4096,-4032⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1355471005270,0,true,230108974144,230108974208⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨843552250282,0,false,-291370076480,-291370076416⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1355990729620,0,true,230530475904,230530475968⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨843032525932,0,false,-292047709760,-292047709696⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1039683675055,0,false,-61517233792,-61517233728⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1039925897829,0,false,-61261102336,-61261102272⟩
    { al := (477/2048), au := (477849/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨256087425024,256543228429⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨230212836992,230212837056⟩ : DyadicInterval 40),(⟨-291536990144,-291536990080⟩ : DyadicInterval 40),(⟨732025043246,732025062576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨230582472000,230582472064⟩ : DyadicInterval 40),(⟨-292131348992,-292131348928⟩ : DyadicInterval 40),(⟨731916797475,731916816804⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨230005107648,230005107712⟩ : DyadicInterval 40),(⟨-291203198016,-291203197952⟩ : DyadicInterval 40),(⟨732085772134,732085791464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨230478462400,230478462464⟩ : DyadicInterval 40),(⟨-291964052800,-291964052736⟩ : DyadicInterval 40),(⟨731947280038,731947299368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨66651190,133562925⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66649152,66649216⟩ : DyadicInterval 40),(⟨-66653248,-66653184⟩ : DyadicInterval 40),(⟨762123381559,762123400888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨133554752,133554816⟩ : DyadicInterval 40),(⟨-133571072,-133571008⟩ : DyadicInterval 40),(⟨762123375487,762123394816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-16256,-4032⟩ : DyadicInterval 40),(⟨762123385632,762123411008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨255959377494,256479101844⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨230108974144,230108974208⟩ : DyadicInterval 40),(⟨-291370076480,-291370076416⟩ : DyadicInterval 40),(⟨732055416486,732055435815⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨230530475904,230530475968⟩ : DyadicInterval 40),(⟨-292047709760,-292047709696⟩ : DyadicInterval 40),(⟨731932038552,731932057882⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-61517233792,-61261102272⟩ : DyadicInterval 40),(⟨792753934752,792882019776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨230212836992,230582472064⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-292131348992,-291536990080⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e350_ok : ecellOkT e350 = true := by decide +kernel
theorem e350_pos {a z : ℝ} (ha1 : ((477/2048 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((477849/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e350 e350_ok ha1 ha2 hz1 hz2 hz

-- box ['477849/2048000', '239349/1024000', '999/1000', '1999/2000']  interval_lower 485746647/1099511627776
noncomputable def e351 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1356054856204,0,true,230582472000,230582472064⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨842968399348,0,false,-292131348992,-292131348928⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1356510659609,0,true,230951982848,230951982912⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨842512595943,0,false,-292726029248,-292726029184⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1355798312975,0,true,230374442880,230374442944⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨843224942577,0,false,-291796782080,-291796782016⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1356382160094,0,true,230847823424,230847823488⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨842641095458,0,false,-292558345216,-292558345152⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578407462,0,true,66777600,66777664⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444848090,0,false,-66781760,-66781696⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099645447820,0,true,133811840,133811904⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099377807732,0,false,-133828224,-133828160⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511611488,0,false,-16320,-16256⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623721,0,false,-4096,-4032⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1355926580770,0,true,230478459264,230478459328⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨843096674782,0,false,-291964047808,-291964047744⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1356446419082,0,true,230899911808,230899911872⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨842576836470,0,false,-292642196096,-292642196032⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1039470892129,0,false,-61742284224,-61742284160⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1039713598854,0,false,-61485588544,-61485588480⟩
    { al := (477849/2048000), au := (239349/1024000), zl := (999/1000), zu := (1999/2000),
      A := ⟨256543228428,256999031833⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨230582472000,230582472064⟩ : DyadicInterval 40),(⟨-292131348992,-292131348928⟩ : DyadicInterval 40),(⟨731916797475,731916816805⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨230951982848,230951982912⟩ : DyadicInterval 40),(⟨-292726029248,-292726029184⟩ : DyadicInterval 40),(⟨731808351811,731808371141⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨230374442880,230374442944⟩ : DyadicInterval 40),(⟨-291796782080,-291796782016⟩ : DyadicInterval 40),(⟨731977746834,731977766163⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨230847823424,230847823488⟩ : DyadicInterval 40),(⟨-292558345216,-292558345152⟩ : DyadicInterval 40),(⟨731838944893,731838964223⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨66779686,133820044⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66777600,66777664⟩ : DyadicInterval 40),(⟨-66781760,-66781696⟩ : DyadicInterval 40),(⟨762123381575,762123400905⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨133811840,133811904⟩ : DyadicInterval 40),(⟨-133828224,-133828160⟩ : DyadicInterval 40),(⟨762123375456,762123394785⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-16320,-4032⟩ : DyadicInterval 40),(⟨762123385632,762123411040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨256414952994,256934791306⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨230478459264,230478459328⟩ : DyadicInterval 40),(⟨-291964047808,-291964047744⟩ : DyadicInterval 40),(⟨731947280965,731947300295⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨230899911808,230899911872⟩ : DyadicInterval 40),(⟨-292642196096,-292642196032⟩ : DyadicInterval 40),(⟨731823648173,731823667502⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-61742284224,-61485588480⟩ : DyadicInterval 40),(⟨792866177856,792994544992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨230582472000,230951982912⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-292726029248,-292131348928⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e351_ok : ecellOkT e351 = true := by decide +kernel
theorem e351_pos {a z : ℝ} (ha1 : ((477849/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((239349/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e351 e351_ok ha1 ha2 hz1 hz2 hz

-- box ['477/2048', '477849/2048000', '1999/2000', '1']  interval_lower 467863049/1099511627776
noncomputable def e352 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1355599052800,0,true,230212836992,230212837056⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨843424202752,0,false,-291536990144,-291536990080⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1356054856205,0,true,230582472000,230582472064⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨842968399347,0,false,-292131348992,-292131348928⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1355471009087,0,true,230108977216,230108977280⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨843552246465,0,false,-291370081408,-291370081344⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578410759,0,true,66780928,66780992⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444844793,0,false,-66785024,-66784960⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623719,0,false,-4096,-4032⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1355535025216,0,true,230160903680,230160903744⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨843488230336,0,false,-291453525184,-291453525120⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1356054864781,0,true,230582478976,230582479040⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨842968390771,0,false,-292131360192,-292131360128⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1039653750159,0,false,-61548881152,-61548881088⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1039896087221,0,false,-61292621440,-61292621376⟩
    { al := (477/2048), au := (477849/2048000), zl := (1999/2000), zu := 1,
      A := ⟨256087425024,256543228429⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨230212836992,230212837056⟩ : DyadicInterval 40),(⟨-291536990144,-291536990080⟩ : DyadicInterval 40),(⟨732025043246,732025062576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨230582472000,230582472064⟩ : DyadicInterval 40),(⟨-292131348992,-292131348928⟩ : DyadicInterval 40),(⟨731916797475,731916816804⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨230108977216,230108977280⟩ : DyadicInterval 40),(⟨-291370081408,-291370081344⟩ : DyadicInterval 40),(⟨732055415577,732055434907⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨230582472000,230582472064⟩ : DyadicInterval 40),(⟨-292131348992,-292131348928⟩ : DyadicInterval 40),(⟨731916797475,731916816804⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,66782983⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66780928,66780992⟩ : DyadicInterval 40),(⟨-66785024,-66784960⟩ : DyadicInterval 40),(⟨762123381543,762123400872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4096,0⟩ : DyadicInterval 40),(⟨762123383616,762123404928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨256023397440,256543237005⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨230160903680,230160903744⟩ : DyadicInterval 40),(⟨-291453525184,-291453525120⟩ : DyadicInterval 40),(⟨732040232760,732040252089⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨230582478976,230582479040⟩ : DyadicInterval 40),(⟨-292131360192,-292131360128⟩ : DyadicInterval 40),(⟨731916795428,731916814757⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-61548881152,-61292621376⟩ : DyadicInterval 40),(⟨792769694304,792897843456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨230212836992,230582472064⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-292131348992,-291536990080⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e352_ok : ecellOkT e352 = true := by decide +kernel
theorem e352_pos {a z : ℝ} (ha1 : ((477/2048 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((477849/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e352 e352_ok ha1 ha2 hz1 hz2 hz

-- box ['477849/2048000', '239349/1024000', '1999/2000', '1']  interval_lower 482184811/1099511627776
noncomputable def e353 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1356054856204,0,true,230582472000,230582472064⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨842968399348,0,false,-292131348992,-292131348928⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1356510659609,0,true,230951982848,230951982912⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨842512595943,0,false,-292726029248,-292726029184⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1355926584589,0,true,230478462336,230478462400⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨843096670963,0,false,-291964052800,-291964052736⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578539326,0,true,66909504,66909568⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444716226,0,false,-66913600,-66913536⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623704,0,false,-4096,-4032⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1355990714653,0,true,230530463744,230530463808⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨843032540899,0,false,-292047690240,-292047690176⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1356510668195,0,true,230951989824,230951989888⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨842512587357,0,false,-292726040448,-292726040384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1039440860802,0,false,-61774050624,-61774050560⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1039683682038,0,false,-61517226432,-61517226368⟩
    { al := (477849/2048000), au := (239349/1024000), zl := (1999/2000), zu := 1,
      A := ⟨256543228428,256999031833⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨230582472000,230582472064⟩ : DyadicInterval 40),(⟨-292131348992,-292131348928⟩ : DyadicInterval 40),(⟨731916797475,731916816805⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨230951982848,230951982912⟩ : DyadicInterval 40),(⟨-292726029248,-292726029184⟩ : DyadicInterval 40),(⟨731808351811,731808371141⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨230478462336,230478462400⟩ : DyadicInterval 40),(⟨-291964052800,-291964052736⟩ : DyadicInterval 40),(⟨731947280078,731947299407⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨230951982848,230951982912⟩ : DyadicInterval 40),(⟨-292726029248,-292726029184⟩ : DyadicInterval 40),(⟨731808351811,731808371141⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,66911550⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66909504,66909568⟩ : DyadicInterval 40),(⟨-66913600,-66913536⟩ : DyadicInterval 40),(⟨762123381527,762123400857⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4096,0⟩ : DyadicInterval 40),(⟨762123383616,762123404928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨256479086877,256999040419⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨230530463744,230530463808⟩ : DyadicInterval 40),(⟨-292047690240,-292047690176⟩ : DyadicInterval 40),(⟨731932042124,731932061453⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨230951989824,230951989888⟩ : DyadicInterval 40),(⟨-292726040448,-292726040384⟩ : DyadicInterval 40),(⟨731808349754,731808369084⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-61774050624,-61517226368⟩ : DyadicInterval 40),(⟨792881996800,793010428192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨230582472000,230951982912⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-292726029248,-292131348928⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e353_ok : ecellOkT e353 = true := by decide +kernel
theorem e353_pos {a z : ℝ} (ha1 : ((477849/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((239349/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e353 e353_ok ha1 ha2 hz1 hz2 hz

-- box ['239349/1024000', '479547/2048000', '999/1000', '1999/2000']  interval_lower 250099797/549755813888
noncomputable def e354 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1356510659608,0,true,230951982848,230951982912⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨842512595944,0,false,-292726029248,-292726029184⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1356966463013,0,true,231321369536,231321369600⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨842056792539,0,false,-293321031360,-293321031296⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1356253660576,0,true,230743654080,230743654144⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨842769594976,0,false,-292390686720,-292390686656⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1356837735596,0,true,231217060352,231217060416⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨842185519956,0,false,-293152958976,-293152958912⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578536013,0,true,66906176,66906240⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444719539,0,false,-66910336,-66910272⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099645705053,0,true,134069056,134069120⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099377550499,0,false,-134085504,-134085440⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511611426,0,false,-16384,-16320⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623705,0,false,-4096,-4032⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1356382156281,0,true,230847820288,230847820352⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨842641099271,0,false,-292558340224,-292558340160⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1356902108536,0,true,231269223680,231269223744⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨842121147016,0,false,-293237004032,-293237003968⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1039257731489,0,false,-61967780352,-61967780288⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1039500922344,0,false,-61710519872,-61710519808⟩
    { al := (239349/1024000), au := (479547/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨256999031832,257454835237⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨230951982848,230951982912⟩ : DyadicInterval 40),(⟨-292726029248,-292726029184⟩ : DyadicInterval 40),(⟨731808351811,731808371141⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨231321369536,231321369600⟩ : DyadicInterval 40),(⟨-293321031360,-293321031296⟩ : DyadicInterval 40),(⟨731699706304,731699725633⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨230743654080,230743654144⟩ : DyadicInterval 40),(⟨-292390686720,-292390686656⟩ : DyadicInterval 40),(⟨731869522111,731869541440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨231217060352,231217060416⟩ : DyadicInterval 40),(⟨-293152958976,-293152958912⟩ : DyadicInterval 40),(⟨731730410103,731730429433⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨66908237,134077277⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66906176,66906240⟩ : DyadicInterval 40),(⟨-66910336,-66910272⟩ : DyadicInterval 40),(⟨762123381560,762123400889⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨134069056,134069120⟩ : DyadicInterval 40),(⟨-134085504,-134085440⟩ : DyadicInterval 40),(⟨762123375426,762123394755⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-16384,-4032⟩ : DyadicInterval 40),(⟨762123385632,762123411072⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨256870528505,257390480760⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨230847820288,230847820352⟩ : DyadicInterval 40),(⟨-292558340224,-292558340160⟩ : DyadicInterval 40),(⟨731838945822,731838965152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨231269223680,231269223744⟩ : DyadicInterval 40),(⟨-293237004032,-293237003968⟩ : DyadicInterval 40),(⟨731715057992,731715077321⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-61967780352,-61710519808⟩ : DyadicInterval 40),(⟨792978643520,793107293056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨230951982848,231321369600⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-293321031360,-292726029184⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e354_ok : ecellOkT e354 = true := by decide +kernel
theorem e354_pos {a z : ℝ} (ha1 : ((239349/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((479547/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e354 e354_ok ha1 ha2 hz1 hz2 hz

-- box ['479547/2048000', '120099/512000', '999/1000', '1999/2000']  interval_lower 514761177/1099511627776
noncomputable def e355 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1356966463012,0,true,231321369536,231321369600⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨842056792540,0,false,-293321031360,-293321031296⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1357422266418,0,true,231690632128,231690632192⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨841600989134,0,false,-293916355584,-293916355520⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1356709008176,0,true,231112741312,231112741376⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨842314247376,0,false,-292984912320,-292984912256⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1357293311099,0,true,231586173376,231586173440⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨841729944453,0,false,-293747894528,-293747894464⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578664621,0,true,67034752,67034816⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444590931,0,false,-67038912,-67038848⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099645962399,0,true,134326400,134326464⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099377293153,0,false,-134342848,-134342784⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511611363,0,false,-16448,-16384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623689,0,false,-4096,-4032⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1356837731786,0,true,231217057280,231217057344⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨842185523766,0,false,-293152954048,-293152953984⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1357357797991,0,true,231638411520,231638411584⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨841665457561,0,false,-293832133888,-293832133824⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1039044193130,0,false,-62193722368,-62193722304⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1039287868307,0,false,-61935896704,-61935896640⟩
    { al := (479547/2048000), au := (120099/512000), zl := (999/1000), zu := (1999/2000),
      A := ⟨257454835236,257910638642⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨231321369536,231321369600⟩ : DyadicInterval 40),(⟨-293321031360,-293321031296⟩ : DyadicInterval 40),(⟨731699706304,731699725633⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨231690632128,231690632192⟩ : DyadicInterval 40),(⟨-293916355584,-293916355520⟩ : DyadicInterval 40),(⟨731590860887,731590880216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨231112741312,231112741376⟩ : DyadicInterval 40),(⟨-292984912320,-292984912256⟩ : DyadicInterval 40),(⟨731761097950,731761117280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨231586173376,231586173440⟩ : DyadicInterval 40),(⟨-293747894528,-293747894464⟩ : DyadicInterval 40),(⟨731621675599,731621694928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨67036845,134334623⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67034752,67034816⟩ : DyadicInterval 40),(⟨-67038912,-67038848⟩ : DyadicInterval 40),(⟨762123381544,762123400873⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨134326400,134326464⟩ : DyadicInterval 40),(⟨-134342848,-134342784⟩ : DyadicInterval 40),(⟨762123375363,762123394692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-16448,-4032⟩ : DyadicInterval 40),(⟨762123385632,762123411104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨257326104010,257846170215⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨231217057280,231217057344⟩ : DyadicInterval 40),(⟨-293152954048,-293152953984⟩ : DyadicInterval 40),(⟨731730411020,731730430350⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨231638411520,231638411584⟩ : DyadicInterval 40),(⟨-293832133888,-293832133824⟩ : DyadicInterval 40),(⟨731606268006,731606287336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-62193722368,-61935896640⟩ : DyadicInterval 40),(⟨793091331936,793220264064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨231321369536,231690632192⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-293916355584,-293321031296⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e355_ok : ecellOkT e355 = true := by decide +kernel
theorem e355_pos {a z : ℝ} (ha1 : ((479547/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((120099/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e355 e355_ok ha1 ha2 hz1 hz2 hz

-- box ['239349/1024000', '479547/2048000', '1999/2000', '1']  interval_lower 496614977/1099511627776
noncomputable def e356 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1356510659608,0,true,230951982848,230951982912⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨842512595944,0,false,-292726029248,-292726029184⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1356966463013,0,true,231321369536,231321369600⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨842056792539,0,false,-293321031360,-293321031296⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1356382160092,0,true,230847823360,230847823424⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨842641095460,0,false,-292558345216,-292558345152⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578667950,0,true,67038080,67038144⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444587602,0,false,-67042240,-67042176⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623688,0,false,-4096,-4032⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1356446404105,0,true,230899899712,230899899776⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨842576851447,0,false,-292642176512,-292642176448⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1356966471600,0,true,231321376448,231321376512⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨842056783952,0,false,-293321042560,-293321042496⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1039227593542,0,false,-61999666048,-61999665984⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1039470899130,0,false,-61742276800,-61742276736⟩
    { al := (239349/1024000), au := (479547/2048000), zl := (1999/2000), zu := 1,
      A := ⟨256999031832,257454835237⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨230951982848,230951982912⟩ : DyadicInterval 40),(⟨-292726029248,-292726029184⟩ : DyadicInterval 40),(⟨731808351811,731808371141⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨231321369536,231321369600⟩ : DyadicInterval 40),(⟨-293321031360,-293321031296⟩ : DyadicInterval 40),(⟨731699706304,731699725633⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨230847823360,230847823424⟩ : DyadicInterval 40),(⟨-292558345216,-292558345152⟩ : DyadicInterval 40),(⟨731838944933,731838964262⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨231321369536,231321369600⟩ : DyadicInterval 40),(⟨-293321031360,-293321031296⟩ : DyadicInterval 40),(⟨731699706304,731699725633⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,67040174⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67038080,67038144⟩ : DyadicInterval 40),(⟨-67042240,-67042176⟩ : DyadicInterval 40),(⟨762123381544,762123400873⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4096,0⟩ : DyadicInterval 40),(⟨762123383616,762123404928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨256934776329,257454843824⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨230899899712,230899899776⟩ : DyadicInterval 40),(⟨-292642176512,-292642176448⟩ : DyadicInterval 40),(⟨731823651696,731823671025⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨231321376448,231321376512⟩ : DyadicInterval 40),(⟨-293321042560,-293321042496⟩ : DyadicInterval 40),(⟨731699704278,731699723608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-61999666048,-61742276736⟩ : DyadicInterval 40),(⟨792994521984,793123235904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨230951982848,231321369600⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-293321031360,-292726029184⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e356_ok : ecellOkT e356 = true := by decide +kernel
theorem e356_pos {a z : ℝ} (ha1 : ((239349/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((479547/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e356 e356_ok ha1 ha2 hz1 hz2 hz

-- box ['479547/2048000', '120099/512000', '1999/2000', '1']  interval_lower 255576597/549755813888
noncomputable def e357 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1356966463012,0,true,231321369536,231321369600⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨842056792540,0,false,-293321031360,-293321031296⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1357422266418,0,true,231690632128,231690632192⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨841600989134,0,false,-293916355584,-293916355520⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1356837735594,0,true,231217060352,231217060416⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨842185519958,0,false,-293152958976,-293152958912⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578796631,0,true,67166784,67166848⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444458921,0,false,-67170944,-67170880⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623672,0,false,-4160,-4096⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1356902093555,0,true,231269211520,231269211584⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨842121161997,0,false,-293236984448,-293236984384⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1357422275004,0,true,231690639104,231690639168⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨841600980548,0,false,-293916366848,-293916366784⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1039013948376,0,false,-62225727680,-62225727616⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1039257738504,0,false,-61967772928,-61967772864⟩
    { al := (479547/2048000), au := (120099/512000), zl := (1999/2000), zu := 1,
      A := ⟨257454835236,257910638642⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨231321369536,231321369600⟩ : DyadicInterval 40),(⟨-293321031360,-293321031296⟩ : DyadicInterval 40),(⟨731699706304,731699725633⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨231690632128,231690632192⟩ : DyadicInterval 40),(⟨-293916355584,-293916355520⟩ : DyadicInterval 40),(⟨731590860887,731590880216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨231217060352,231217060416⟩ : DyadicInterval 40),(⟨-293152958976,-293152958912⟩ : DyadicInterval 40),(⟨731730410104,731730429433⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨231690632128,231690632192⟩ : DyadicInterval 40),(⟨-293916355584,-293916355520⟩ : DyadicInterval 40),(⟨731590860887,731590880216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,67168855⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67166784,67166848⟩ : DyadicInterval 40),(⟨-67170944,-67170880⟩ : DyadicInterval 40),(⟨762123381528,762123400857⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4160,0⟩ : DyadicInterval 40),(⟨762123383616,762123404960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨257390465779,257910647228⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨231269211520,231269211584⟩ : DyadicInterval 40),(⟨-293236984448,-293236984384⟩ : DyadicInterval 40),(⟨731715061569,731715080898⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨231690639104,231690639168⟩ : DyadicInterval 40),(⟨-293916366848,-293916366784⟩ : DyadicInterval 40),(⟨731590858840,731590878169⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-62225727680,-61967772864⟩ : DyadicInterval 40),(⟨793107270048,793236266720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨231321369536,231690632192⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-293916355584,-293321031296⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e357_ok : ecellOkT e357 = true := by decide +kernel
theorem e357_pos {a z : ℝ} (ha1 : ((479547/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((120099/512000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e357 e357_ok ha1 ha2 hz1 hz2 hz

-- box ['120099/512000', '96249/409600', '999/1000', '1999/2000']  interval_lower 529432047/1099511627776
noncomputable def e358 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1357422266417,0,true,231690632128,231690632192⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨841600989135,0,false,-293916355584,-293916355520⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1357878069822,0,true,232059770816,232059770880⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨841145185730,0,false,-294512002368,-294512002304⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1357164355778,0,true,231481704768,231481704832⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨841858899774,0,false,-293579459264,-293579459200⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1357748886602,0,true,231955162560,231955162624⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨841274368950,0,false,-294343152192,-294343152128⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578793286,0,true,67163456,67163520⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444462266,0,false,-67167616,-67167552⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099646219857,0,true,134583808,134583872⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099377035695,0,false,-134600320,-134600256⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511611300,0,false,-16512,-16448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623674,0,false,-4160,-4096⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1357293307296,0,true,231586170304,231586170368⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨841729948256,0,false,-293747889536,-293747889472⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1357813487451,0,true,232007475392,232007475456⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨841209768101,0,false,-294427586112,-294427586048⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1038830277050,0,false,-62420110656,-62420110592⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1039074436739,0,false,-62161719232,-62161719168⟩
    { al := (120099/512000), au := (96249/409600), zl := (999/1000), zu := (1999/2000),
      A := ⟨257910638641,258366442046⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨231690632128,231690632192⟩ : DyadicInterval 40),(⟨-293916355584,-293916355520⟩ : DyadicInterval 40),(⟨731590860888,731590880217⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨232059770816,232059770880⟩ : DyadicInterval 40),(⟨-294512002368,-294512002304⟩ : DyadicInterval 40),(⟨731481815493,731481834822⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨231481704768,231481704832⟩ : DyadicInterval 40),(⟨-293579459264,-293579459200⟩ : DyadicInterval 40),(⟨731652474258,731652493588⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨231955162560,231955162624⟩ : DyadicInterval 40),(⟨-294343152192,-294343152128⟩ : DyadicInterval 40),(⟨731512741339,731512760669⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨67165510,134592081⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67163456,67163520⟩ : DyadicInterval 40),(⟨-67167616,-67167552⟩ : DyadicInterval 40),(⟨762123381528,762123400858⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨134583808,134583872⟩ : DyadicInterval 40),(⟨-134600320,-134600256⟩ : DyadicInterval 40),(⟨762123375332,762123394661⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-16512,-4096⟩ : DyadicInterval 40),(⟨762123385664,762123411136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨257781679520,258301859675⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨231586170304,231586170368⟩ : DyadicInterval 40),(⟨-293747889536,-293747889472⟩ : DyadicInterval 40),(⟨731621676492,731621695822⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨232007475392,232007475456⟩ : DyadicInterval 40),(⟨-294427586112,-294427586048⟩ : DyadicInterval 40),(⟨731497278224,731497297554⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-62420110656,-62161719168⟩ : DyadicInterval 40),(⟨793204243200,793333458208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨231690632128,232059770880⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-294512002368,-293916355520⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e358_ok : ecellOkT e358 = true := by decide +kernel
theorem e358_pos {a z : ℝ} (ha1 : ((120099/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((96249/409600 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e358 e358_ok ha1 ha2 hz1 hz2 hz

-- box ['96249/409600', '241047/1024000', '999/1000', '1999/2000']  interval_lower 544212475/1099511627776
noncomputable def e359 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1357878069821,0,true,232059770816,232059770880⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨841145185731,0,false,-294512002368,-294512002304⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1358333873226,0,true,232428785536,232428785600⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨840689382326,0,false,-295107971968,-295107971904⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1357619703378,0,true,231850544384,231850544448⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨841403552174,0,false,-294174327872,-294174327808⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1358204462104,0,true,232324027904,232324027968⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨840818793448,0,false,-294938732224,-294938732160⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578922007,0,true,67292160,67292224⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444333545,0,false,-67296320,-67296256⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099646477429,0,true,134841344,134841408⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099376778123,0,false,-134857984,-134857920⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511611237,0,false,-16576,-16512⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623658,0,false,-4160,-4096⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1357748882803,0,true,231955159488,231955159552⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨841274372749,0,false,-294343147200,-294343147136⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1358269176905,0,true,232376415488,232376415552⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨840754078647,0,false,-295023360960,-295023360896⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1038615983255,0,false,-62646945408,-62646945344⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1038860627642,0,false,-62387987648,-62387987584⟩
    { al := (96249/409600), au := (241047/1024000), zl := (999/1000), zu := (1999/2000),
      A := ⟨258366442045,258822245450⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨232059770816,232059770880⟩ : DyadicInterval 40),(⟨-294512002368,-294512002304⟩ : DyadicInterval 40),(⟨731481815493,731481834822⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨232428785536,232428785600⟩ : DyadicInterval 40),(⟨-295107971968,-295107971904⟩ : DyadicInterval 40),(⟨731372570133,731372589463⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨231850544384,231850544448⟩ : DyadicInterval 40),(⟨-294174327872,-294174327808⟩ : DyadicInterval 40),(⟨731543651075,731543670404⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨232324027904,232324027968⟩ : DyadicInterval 40),(⟨-294938732224,-294938732160⟩ : DyadicInterval 40),(⟨731403607299,731403626629⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨67294231,134849653⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67292160,67292224⟩ : DyadicInterval 40),(⟨-67296320,-67296256⟩ : DyadicInterval 40),(⟨762123381513,762123400842⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨134841344,134841408⟩ : DyadicInterval 40),(⟨-134857984,-134857920⟩ : DyadicInterval 40),(⟨762123375333,762123394662⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-16576,-4096⟩ : DyadicInterval 40),(⟨762123385664,762123411168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨258237255027,258757549129⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨231955159488,231955159552⟩ : DyadicInterval 40),(⟨-294343147200,-294343147136⟩ : DyadicInterval 40),(⟨731512742235,731512761565⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨232376415488,232376415552⟩ : DyadicInterval 40),(⟨-295023360960,-295023360896⟩ : DyadicInterval 40),(⟨731388088504,731388107834⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-62646945408,-62387987584⟩ : DyadicInterval 40),(⟨793317377408,793446875584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨232059770816,232428785600⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-295107971968,-294512002304⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e359_ok : ecellOkT e359 = true := by decide +kernel
theorem e359_pos {a z : ℝ} (ha1 : ((96249/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((241047/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e359 e359_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B005

end


