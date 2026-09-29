-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B019
-- name    : CK_CKLaneC2R_EpCells_B019
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T18:24:21.383742+00:00
-- url     : https://prove2.me/theorems/f309cd8a-ba54-4bf9-881d-f8b3ee41d272
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B019` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B019` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B019` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B019 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B019.lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheckT

-- ===== source module CKLaneC2R.EpCells.B019 =====
section

namespace CKLaneC2R.EpCells.B019

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['817311/4096000', '10227/51200', '3997/4000', '1999/2000']  interval_lower 491784369/1099511627776
noncomputable def e1140 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1318906878754,0,true,200042028288,200042028352⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨880116376798,0,false,-244715268800,-244715268736⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1319134780457,0,true,200232003008,200232003072⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨879888475095,0,false,-245000018624,-245000018560⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1318742332315,0,true,199904844992,199904845056⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨880280923237,0,false,-244509723456,-244509723392⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1319024968881,0,true,200140470144,200140470208⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨879998286671,0,false,-244862806272,-244862806208⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568108218,0,true,56478976,56479040⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455147334,0,false,-56481920,-56481856⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099596443009,0,true,84811904,84811968⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099426812543,0,false,-84818560,-84818496⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621233,0,false,-6592,-6528⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624875,0,false,-2944,-2880⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1318824600848,0,true,199973434880,199973434944⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨880198654704,0,false,-244612485440,-244612485376⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1319079883601,0,true,200186244992,200186245056⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨879943371951,0,false,-244931421504,-244931421440⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1055664689055,0,false,-44745176512,-44745176448⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1055766587758,0,false,-44639050560,-44639050496⟩
    { al := (817311/4096000), au := (10227/51200), zl := (3997/4000), zu := (1999/2000),
      A := ⟨219395250978,219623152681⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200042028288,200042028352⟩ : DyadicInterval 40),(⟨-244715268800,-244715268736⟩ : DyadicInterval 40),(⟨740086831049,740086850378⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200232003008,200232003072⟩ : DyadicInterval 40),(⟨-245000018624,-245000018560⟩ : DyadicInterval 40),(⟨740040712792,740040732122⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199904844992,199904845056⟩ : DyadicInterval 40),(⟨-244509723456,-244509723392⟩ : DyadicInterval 40),(⟨740120098093,740120117422⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200140470144,200140470208⟩ : DyadicInterval 40),(⟨-244862806272,-244862806208⟩ : DyadicInterval 40),(⟨740062940447,740062959776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨56480442,84815233⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56478976,56479040⟩ : DyadicInterval 40),(⟨-56481920,-56481856⟩ : DyadicInterval 40),(⟨762123382122,762123401451⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨84811904,84811968⟩ : DyadicInterval 40),(⟨-84818560,-84818496⟩ : DyadicInterval 40),(⟨762123380337,762123399666⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6592,-2880⟩ : DyadicInterval 40),(⟨762123385056,762123406176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨219312973072,219568255825⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199973434880,199973434944⟩ : DyadicInterval 40),(⟨-244612485440,-244612485376⟩ : DyadicInterval 40),(⟨740103468707,740103488036⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200186244992,200186245056⟩ : DyadicInterval 40),(⟨-244931421504,-244931421440⟩ : DyadicInterval 40),(⟨740051826243,740051845572⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-44745176512,-44639050496⟩ : DyadicInterval 40),(⟨784442908864,784495991136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨200042028288,200232003072⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-245000018624,-244715268736⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1140_ok : ecellOkT e1140 = true := by decide +kernel
theorem e1140_pos {a z : ℝ} (ha1 : ((817311/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((10227/51200 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1140 e1140_ok ha1 ha2 hz1 hz2 hz

-- box ['203691/1024000', '815613/4096000', '1999/2000', '3999/4000']  interval_lower 119227063/274877906944
noncomputable def e1141 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1318223173648,0,true,199471907200,199471907264⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨880800081904,0,false,-243861461376,-243861461312⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1318451075351,0,true,199661980416,199661980480⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨880572180201,0,false,-244145990208,-244145990144⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1318113817875,0,true,199380691264,199380691328⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨880909437677,0,false,-243724959936,-243724959872⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1318396340490,0,true,199616333760,199616333824⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨880626915062,0,false,-244077648512,-244077648448⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539774826,0,true,28146688,28146752⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483480726,0,false,-28147456,-28147392⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567985227,0,true,56355968,56356032⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455270325,0,false,-56358912,-56358848⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624887,0,false,-2944,-2880⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627056,0,false,-768,-704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1318168490587,0,true,199426295872,199426295936⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨880854764965,0,false,-243793202048,-243793201984⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1318423716547,0,true,199639164544,199639164608⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨880599539005,0,false,-244111829568,-244111829504⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1055926365556,0,false,-44472665024,-44472664960⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1056027936975,0,false,-44366906176,-44366906112⟩
    { al := (203691/1024000), au := (815613/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨218711545872,218939447575⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199471907200,199471907264⟩ : DyadicInterval 40),(⟨-243861461376,-243861461312⟩ : DyadicInterval 40),(⟨740224890533,740224909862⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199661980416,199661980480⟩ : DyadicInterval 40),(⟨-244145990208,-244145990144⟩ : DyadicInterval 40),(⟨740178919899,740178939229⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199380691264,199380691328⟩ : DyadicInterval 40),(⟨-243724959936,-243724959872⟩ : DyadicInterval 40),(⟨740246931519,740246950849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199616333760,199616333824⟩ : DyadicInterval 40),(⟨-244077648512,-244077648448⟩ : DyadicInterval 40),(⟨740189965083,740189984412⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨28147050,56357451⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28146688,28146752⟩ : DyadicInterval 40),(⟨-28147456,-28147392⟩ : DyadicInterval 40),(⟨762123383215,762123402544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56355968,56356032⟩ : DyadicInterval 40),(⟨-56358912,-56358848⟩ : DyadicInterval 40),(⟨762123382135,762123401464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2944,-704⟩ : DyadicInterval 40),(⟨762123383968,762123404352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨218656862811,218912088771⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199426295872,199426295936⟩ : DyadicInterval 40),(⟨-243793202048,-243793201984⟩ : DyadicInterval 40),(⟨740235913466,740235932795⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199639164544,199639164608⟩ : DyadicInterval 40),(⟨-244111829568,-244111829504⟩ : DyadicInterval 40),(⟨740184441077,740184460407⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-44472665024,-44366906112⟩ : DyadicInterval 40),(⟨784306836672,784359735392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨199471907200,199661980480⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-244145990208,-243861461312⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1141_ok : ecellOkT e1141 = true := by decide +kernel
theorem e1141_pos {a z : ℝ} (ha1 : ((203691/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((815613/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1141 e1141_ok ha1 ha2 hz1 hz2 hz

-- box ['815613/4096000', '408231/2048000', '1999/2000', '3999/4000']  interval_lower 481559083/1099511627776
noncomputable def e1142 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1318451075350,0,true,199661980416,199661980480⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨880572180202,0,false,-244145990208,-244145990144⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1318678977053,0,true,199852020800,199852020864⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨880344278499,0,false,-244430592640,-244430592576⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1318341605626,0,true,199570685248,199570685312⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨880681649926,0,false,-244009311168,-244009311104⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1318624185216,0,true,199806334528,199806334592⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨880399070336,0,false,-244362162176,-244362162112⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539805904,0,true,28177728,28177792⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483449648,0,false,-28178496,-28178432⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568047399,0,true,56418112,56418176⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455208153,0,false,-56421120,-56421056⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624880,0,false,-2944,-2880⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627054,0,false,-768,-704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1318396335311,0,true,199616329472,199616329536⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨880626920241,0,false,-244077642048,-244077641984⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1318651589765,0,true,199829185088,199829185152⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨880371665787,0,false,-244396387648,-244396387584⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1055835579494,0,false,-44567202560,-44567202496⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1055937268050,0,false,-44461312576,-44461312512⟩
    { al := (815613/4096000), au := (408231/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨218939447574,219167349277⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199661980416,199661980480⟩ : DyadicInterval 40),(⟨-244145990208,-244145990144⟩ : DyadicInterval 40),(⟨740178919899,740178939229⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199852020800,199852020864⟩ : DyadicInterval 40),(⟨-244430592640,-244430592576⟩ : DyadicInterval 40),(⟨740132900045,740132919375⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199570685248,199570685312⟩ : DyadicInterval 40),(⟨-244009311168,-244009311104⟩ : DyadicInterval 40),(⟨740201007448,740201026777⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199806334528,199806334592⟩ : DyadicInterval 40),(⟨-244362162176,-244362162112⟩ : DyadicInterval 40),(⟨740143968581,740143987910⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨28178128,56419623⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28177728,28177792⟩ : DyadicInterval 40),(⟨-28178496,-28178432⟩ : DyadicInterval 40),(⟨762123383213,762123402542⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56418112,56418176⟩ : DyadicInterval 40),(⟨-56421120,-56421056⟩ : DyadicInterval 40),(⟨762123382160,762123401489⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2944,-704⟩ : DyadicInterval 40),(⟨762123383968,762123404352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨218884707535,219139961989⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199616329472,199616329536⟩ : DyadicInterval 40),(⟨-244077642048,-244077641984⟩ : DyadicInterval 40),(⟨740189966110,740189985439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199829185088,199829185152⟩ : DyadicInterval 40),(⟨-244396387648,-244396387584⟩ : DyadicInterval 40),(⟨740138432929,740138452258⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-44567202560,-44461312512⟩ : DyadicInterval 40),(⟨784354039872,784407004160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨199661980416,199852020864⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-244430592640,-244145990144⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1142_ok : ecellOkT e1142 = true := by decide +kernel
theorem e1142_pos {a z : ℝ} (ha1 : ((815613/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((408231/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1142 e1142_ok ha1 ha2 hz1 hz2 hz

-- box ['203691/1024000', '815613/4096000', '3999/4000', '1']  interval_lower 476050159/1099511627776
noncomputable def e1143 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1318223173648,0,true,199471907200,199471907264⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨880800081904,0,false,-243861461376,-243861461312⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1318451075351,0,true,199661980416,199661980480⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨880572180201,0,false,-244145990208,-244145990144⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1318168495761,0,true,199426300160,199426300224⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨880854759791,0,false,-243793208512,-243793208448⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539806840,0,true,28178688,28178752⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483448712,0,false,-28179456,-28179392⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627053,0,false,-768,-704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1318195829234,0,true,199449099392,199449099456⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨880827426318,0,false,-243827327616,-243827327552⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1318451083877,0,true,199661987520,199661987584⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨880572171675,0,false,-244146000832,-244146000768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1055915467238,0,false,-44484013248,-44484013184⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1056017062772,0,false,-44378228224,-44378228160⟩
    { al := (203691/1024000), au := (815613/4096000), zl := (3999/4000), zu := 1,
      A := ⟨218711545872,218939447575⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199471907200,199471907264⟩ : DyadicInterval 40),(⟨-243861461376,-243861461312⟩ : DyadicInterval 40),(⟨740224890533,740224909862⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199661980416,199661980480⟩ : DyadicInterval 40),(⟨-244145990208,-244145990144⟩ : DyadicInterval 40),(⟨740178919899,740178939229⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199426300160,199426300224⟩ : DyadicInterval 40),(⟨-243793208512,-243793208448⟩ : DyadicInterval 40),(⟨740235912442,740235931772⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199661980416,199661980480⟩ : DyadicInterval 40),(⟨-244145990208,-244145990144⟩ : DyadicInterval 40),(⟨740178919899,740178939229⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,28179064⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28178688,28178752⟩ : DyadicInterval 40),(⟨-28179456,-28179392⟩ : DyadicInterval 40),(⟨762123383213,762123402542⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-768,0⟩ : DyadicInterval 40),(⟨762123383616,762123403264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨218684201458,218939456101⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199449099392,199449099456⟩ : DyadicInterval 40),(⟨-243827327616,-243827327552⟩ : DyadicInterval 40),(⟨740230402933,740230422262⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199661987520,199661987584⟩ : DyadicInterval 40),(⟨-244146000832,-244146000768⟩ : DyadicInterval 40),(⟨740178918173,740178937503⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-44484013248,-44378228160⟩ : DyadicInterval 40),(⟨784312497696,784365409504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨199471907200,199661980480⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-244145990208,-243861461312⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1143_ok : ecellOkT e1143 = true := by decide +kernel
theorem e1143_pos {a z : ℝ} (ha1 : ((203691/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((815613/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1143 e1143_ok ha1 ha2 hz1 hz2 hz

-- box ['815613/4096000', '408231/2048000', '3999/4000', '1']  interval_lower 480697671/1099511627776
noncomputable def e1144 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1318451075350,0,true,199661980416,199661980480⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨880572180202,0,false,-244145990208,-244145990144⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1318678977053,0,true,199852020800,199852020864⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨880344278499,0,false,-244430592640,-244430592576⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1318396340488,0,true,199616333760,199616333824⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨880626915064,0,false,-244077648512,-244077648448⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539837926,0,true,28209728,28209792⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483417626,0,false,-28210560,-28210496⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627052,0,false,-768,-704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1318423702445,0,true,199639152768,199639152832⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨880599553107,0,false,-244111811968,-244111811904⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1318678985586,0,true,199852027904,199852027968⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨880344269966,0,false,-244430603264,-244430603200⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1055824658474,0,false,-44578575360,-44578575296⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1055926371172,0,false,-44472659200,-44472659136⟩
    { al := (815613/4096000), au := (408231/2048000), zl := (3999/4000), zu := 1,
      A := ⟨218939447574,219167349277⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199661980416,199661980480⟩ : DyadicInterval 40),(⟨-244145990208,-244145990144⟩ : DyadicInterval 40),(⟨740178919899,740178939229⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199852020800,199852020864⟩ : DyadicInterval 40),(⟨-244430592640,-244430592576⟩ : DyadicInterval 40),(⟨740132900045,740132919375⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199616333760,199616333824⟩ : DyadicInterval 40),(⟨-244077648512,-244077648448⟩ : DyadicInterval 40),(⟨740189965083,740189984412⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199852020800,199852020864⟩ : DyadicInterval 40),(⟨-244430592640,-244430592576⟩ : DyadicInterval 40),(⟨740132900045,740132919375⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,28210150⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28209728,28209792⟩ : DyadicInterval 40),(⟨-28210560,-28210496⟩ : DyadicInterval 40),(⟨762123383244,762123402573⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-768,0⟩ : DyadicInterval 40),(⟨762123383616,762123403264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨218912074669,219167357810⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199639152768,199639152832⟩ : DyadicInterval 40),(⟨-244111811968,-244111811904⟩ : DyadicInterval 40),(⟨740184443935,740184463265⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199852027904,199852027968⟩ : DyadicInterval 40),(⟨-244430603264,-244430603200⟩ : DyadicInterval 40),(⟨740132898315,740132917644⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-44578575360,-44472659136⟩ : DyadicInterval 40),(⟨784359713184,784412690560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨199661980416,199852020864⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-244430592640,-244145990144⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1144_ok : ecellOkT e1144 = true := by decide +kernel
theorem e1144_pos {a z : ℝ} (ha1 : ((815613/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((408231/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1144 e1144_ok ha1 ha2 hz1 hz2 hz

-- box ['408231/2048000', '817311/4096000', '1999/2000', '3999/4000']  interval_lower 486228517/1099511627776
noncomputable def e1145 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1318678977052,0,true,199852020800,199852020864⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨880344278500,0,false,-244430592640,-244430592576⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1318906878755,0,true,200042028288,200042028352⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨880116376797,0,false,-244715268800,-244715268736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1318569393377,0,true,199760646336,199760646400⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨880453862175,0,false,-244293735936,-244293735872⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1318852029943,0,true,199996302400,199996302464⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨880171225609,0,false,-244646749376,-244646749312⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539836989,0,true,28208832,28208896⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483418563,0,false,-28209600,-28209536⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568109581,0,true,56480320,56480384⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455145971,0,false,-56483264,-56483200⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624874,0,false,-2944,-2880⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627053,0,false,-768,-704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1318624180034,0,true,199806330176,199806330240⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨880399075518,0,false,-244362155648,-244362155584⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1318879462976,0,true,200019172800,200019172864⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨880143792576,0,false,-244681019328,-244681019264⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1055744698982,0,false,-44661846528,-44661846464⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1055846504694,0,false,-44555825472,-44555825408⟩
    { al := (408231/2048000), au := (817311/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨219167349276,219395250979⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199852020800,199852020864⟩ : DyadicInterval 40),(⟨-244430592640,-244430592576⟩ : DyadicInterval 40),(⟨740132900046,740132919375⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200042028288,200042028352⟩ : DyadicInterval 40),(⟨-244715268800,-244715268736⟩ : DyadicInterval 40),(⟨740086831048,740086850378⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199760646336,199760646400⟩ : DyadicInterval 40),(⟨-244293735936,-244293735872⟩ : DyadicInterval 40),(⟨740155034272,740155053602⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199996302400,199996302464⟩ : DyadicInterval 40),(⟨-244646749376,-244646749312⟩ : DyadicInterval 40),(⟨740097922911,740097942241⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨28209213,56481805⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28208832,28208896⟩ : DyadicInterval 40),(⟨-28209600,-28209536⟩ : DyadicInterval 40),(⟨762123383212,762123402541⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56480320,56480384⟩ : DyadicInterval 40),(⟨-56483264,-56483200⟩ : DyadicInterval 40),(⟨762123382122,762123401451⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2944,-704⟩ : DyadicInterval 40),(⟨762123383968,762123404352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨219112552258,219367835200⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199806330176,199806330240⟩ : DyadicInterval 40),(⟨-244362155648,-244362155584⟩ : DyadicInterval 40),(⟨740143969624,740143988953⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200019172800,200019172864⟩ : DyadicInterval 40),(⟨-244681019328,-244681019264⟩ : DyadicInterval 40),(⟨740092375574,740092394904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-44661846528,-44555825408⟩ : DyadicInterval 40),(⟨784401296320,784454326144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨199852020800,200042028352⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-244715268800,-244430592576⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1145_ok : ecellOkT e1145 = true := by decide +kernel
theorem e1145_pos {a z : ℝ} (ha1 : ((408231/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((817311/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1145 e1145_ok ha1 ha2 hz1 hz2 hz

-- box ['817311/4096000', '10227/51200', '1999/2000', '3999/4000']  interval_lower 245458443/549755813888
noncomputable def e1146 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1318906878754,0,true,200042028288,200042028352⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨880116376798,0,false,-244715268800,-244715268736⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1319134780457,0,true,200232003008,200232003072⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨879888475095,0,false,-245000018624,-245000018560⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1318797181128,0,true,199950574656,199950574720⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨880226074424,0,false,-244578234304,-244578234240⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1319079874670,0,true,200186237504,200186237568⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨879943380882,0,false,-244931410304,-244931410240⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539868080,0,true,28239936,28240000⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483387472,0,false,-28240704,-28240640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568171775,0,true,56542528,56542592⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455083777,0,false,-56545472,-56545408⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624868,0,false,-2944,-2880⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627051,0,false,-768,-704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1318852024755,0,true,199996298112,199996298176⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨880171230797,0,false,-244646742912,-244646742848⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1319107336196,0,true,200209127680,200209127744⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨879915919356,0,false,-244965724736,-244965724672⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1055653724013,0,false,-44756596992,-44756596928⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1055755646911,0,false,-44650444800,-44650444736⟩
    { al := (817311/4096000), au := (10227/51200), zl := (1999/2000), zu := (3999/4000),
      A := ⟨219395250978,219623152681⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200042028288,200042028352⟩ : DyadicInterval 40),(⟨-244715268800,-244715268736⟩ : DyadicInterval 40),(⟨740086831049,740086850378⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200232003008,200232003072⟩ : DyadicInterval 40),(⟨-245000018624,-245000018560⟩ : DyadicInterval 40),(⟨740040712792,740040732122⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199950574656,199950574720⟩ : DyadicInterval 40),(⟨-244578234304,-244578234240⟩ : DyadicInterval 40),(⟨740109011931,740109031260⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200186237504,200186237568⟩ : DyadicInterval 40),(⟨-244931410304,-244931410240⟩ : DyadicInterval 40),(⟨740051828060,740051847390⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨28240304,56543999⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28239936,28240000⟩ : DyadicInterval 40),(⟨-28240704,-28240640⟩ : DyadicInterval 40),(⟨762123383210,762123402539⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56542528,56542592⟩ : DyadicInterval 40),(⟨-56545472,-56545408⟩ : DyadicInterval 40),(⟨762123382116,762123401445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2944,-704⟩ : DyadicInterval 40),(⟨762123383968,762123404352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨219340396979,219595708420⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199996298112,199996298176⟩ : DyadicInterval 40),(⟨-244646742912,-244646742848⟩ : DyadicInterval 40),(⟨740097923945,740097943274⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200209127680,200209127744⟩ : DyadicInterval 40),(⟨-244965724736,-244965724672⟩ : DyadicInterval 40),(⟨740046269050,740046288379⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-44756596992,-44650444736⟩ : DyadicInterval 40),(⟨784448605984,784501701376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨200042028288,200232003072⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-245000018624,-244715268736⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1146_ok : ecellOkT e1146 = true := by decide +kernel
theorem e1146_pos {a z : ℝ} (ha1 : ((817311/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((10227/51200 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1146 e1146_ok ha1 ha2 hz1 hz2 hz

-- box ['408231/2048000', '817311/4096000', '3999/4000', '1']  interval_lower 485363901/1099511627776
noncomputable def e1147 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1318678977052,0,true,199852020800,199852020864⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨880344278500,0,false,-244430592640,-244430592576⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1318906878755,0,true,200042028288,200042028352⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨880116376797,0,false,-244715268800,-244715268736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1318624185214,0,true,199806334528,199806334592⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨880399070338,0,false,-244362162112,-244362162048⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539869019,0,true,28240832,28240896⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483386533,0,false,-28241664,-28241600⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627050,0,false,-768,-704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1318651575660,0,true,199829173312,199829173376⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨880371679892,0,false,-244396370048,-244396369984⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1318906887281,0,true,200042035392,200042035456⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨880116368271,0,false,-244715279424,-244715279360⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1055733755239,0,false,-44673243968,-44673243904⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1055835585118,0,false,-44567196672,-44567196608⟩
    { al := (408231/2048000), au := (817311/4096000), zl := (3999/4000), zu := 1,
      A := ⟨219167349276,219395250979⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199852020800,199852020864⟩ : DyadicInterval 40),(⟨-244430592640,-244430592576⟩ : DyadicInterval 40),(⟨740132900046,740132919375⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200042028288,200042028352⟩ : DyadicInterval 40),(⟨-244715268800,-244715268736⟩ : DyadicInterval 40),(⟨740086831048,740086850378⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199806334528,199806334592⟩ : DyadicInterval 40),(⟨-244362162112,-244362162048⟩ : DyadicInterval 40),(⟨740143968556,740143987886⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200042028288,200042028352⟩ : DyadicInterval 40),(⟨-244715268800,-244715268736⟩ : DyadicInterval 40),(⟨740086831048,740086850378⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,28241243⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28240832,28240896⟩ : DyadicInterval 40),(⟨-28241664,-28241600⟩ : DyadicInterval 40),(⟨762123383242,762123402571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-768,0⟩ : DyadicInterval 40),(⟨762123383616,762123403264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨219139947884,219395259505⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199829173312,199829173376⟩ : DyadicInterval 40),(⟨-244396370048,-244396369984⟩ : DyadicInterval 40),(⟨740138435793,740138455123⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200042035392,200042035456⟩ : DyadicInterval 40),(⟨-244715279424,-244715279360⟩ : DyadicInterval 40),(⟨740086829315,740086848645⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-44673243968,-44567196608⟩ : DyadicInterval 40),(⟨784406981920,784460024864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨199852020800,200042028352⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-244715268800,-244430592576⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1147_ok : ecellOkT e1147 = true := by decide +kernel
theorem e1147_pos {a z : ℝ} (ha1 : ((408231/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((817311/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1147 e1147_ok ha1 ha2 hz1 hz2 hz

-- box ['817311/4096000', '10227/51200', '3999/4000', '1']  interval_lower 490048919/1099511627776
noncomputable def e1148 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1318906878754,0,true,200042028288,200042028352⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨880116376798,0,false,-244715268800,-244715268736⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1319134780457,0,true,200232003008,200232003072⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨879888475095,0,false,-245000018624,-245000018560⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1318852029941,0,true,199996302400,199996302464⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨880171225611,0,false,-244646749376,-244646749312⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539900117,0,true,28271936,28272000⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483355435,0,false,-28272768,-28272704⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627049,0,false,-768,-704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1318879448862,0,true,200019161024,200019161088⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨880143806690,0,false,-244681001664,-244681001600⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1319134788993,0,true,200232010112,200232010176⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨879888466559,0,false,-245000029312,-245000029248⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1055642757520,0,false,-44768019200,-44768019136⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1055744704615,0,false,-44661840640,-44661840576⟩
    { al := (817311/4096000), au := (10227/51200), zl := (3999/4000), zu := 1,
      A := ⟨219395250978,219623152681⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200042028288,200042028352⟩ : DyadicInterval 40),(⟨-244715268800,-244715268736⟩ : DyadicInterval 40),(⟨740086831049,740086850378⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200232003008,200232003072⟩ : DyadicInterval 40),(⟨-245000018624,-245000018560⟩ : DyadicInterval 40),(⟨740040712792,740040732122⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199996302400,199996302464⟩ : DyadicInterval 40),(⟨-244646749376,-244646749312⟩ : DyadicInterval 40),(⟨740097922911,740097942241⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200232003008,200232003072⟩ : DyadicInterval 40),(⟨-245000018624,-245000018560⟩ : DyadicInterval 40),(⟨740040712792,740040732122⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,28272341⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28271936,28272000⟩ : DyadicInterval 40),(⟨-28272768,-28272704⟩ : DyadicInterval 40),(⟨762123383241,762123402570⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-768,0⟩ : DyadicInterval 40),(⟨762123383616,762123403264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨219367821086,219623161217⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200019161024,200019161088⟩ : DyadicInterval 40),(⟨-244681001664,-244681001600⟩ : DyadicInterval 40),(⟨740092378421,740092397751⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200232010112,200232010176⟩ : DyadicInterval 40),(⟨-245000029312,-245000029248⟩ : DyadicInterval 40),(⟨740040711080,740040730409⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-44768019200,-44661840576⟩ : DyadicInterval 40),(⟨784454303904,784507412480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨200042028288,200232003072⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-245000018624,-244715268736⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1148_ok : ecellOkT e1148 = true := by decide +kernel
theorem e1148_pos {a z : ℝ} (ha1 : ((817311/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((10227/51200 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1148 e1148_ok ha1 ha2 hz1 hz2 hz

-- box ['10227/51200', '819009/4096000', '999/1000', '3997/4000']  interval_lower 124341179/274877906944
noncomputable def e1149 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1319134780456,0,true,200232003008,200232003072⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨879888475096,0,false,-245000018624,-245000018560⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1319362682160,0,true,200421944832,200421944896⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨879660573392,0,false,-245284842240,-245284842176⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1318915157303,0,true,200048929728,200048929792⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨880108098249,0,false,-244725611072,-244725611008⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1319197793870,0,true,200284524032,200284524096⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨879825461682,0,false,-245078763264,-245078763200⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099596441219,0,true,84810112,84810176⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099426814333,0,false,-84816768,-84816704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099624838224,0,true,113204608,113204672⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099398417328,0,false,-113216320,-113216256⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511616119,0,false,-11712,-11648⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621234,0,false,-6592,-6528⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1319024964895,0,true,200140466816,200140466880⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨879998290657,0,false,-244862801280,-244862801216⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1319280247446,0,true,200353244416,200353244480⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨879743008106,0,false,-245181809728,-245181809664⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1055584628759,0,false,-44828565248,-44828565184⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1055686620422,0,false,-44722334464,-44722334400⟩
    { al := (10227/51200), au := (819009/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨219623152680,219851054384⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200232003008,200232003072⟩ : DyadicInterval 40),(⟨-245000018624,-245000018560⟩ : DyadicInterval 40),(⟨740040712793,740040732122⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200421944832,200421944896⟩ : DyadicInterval 40),(⟨-245284842240,-245284842176⟩ : DyadicInterval 40),(⟨739994545393,739994564722⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200048929728,200048929792⟩ : DyadicInterval 40),(⟨-244725611072,-244725611008⟩ : DyadicInterval 40),(⟨740085156650,740085175979⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200284524032,200284524096⟩ : DyadicInterval 40),(⟨-245078763264,-245078763200⟩ : DyadicInterval 40),(⟨740027952733,740027972062⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨84813443,113210448⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨84810112,84810176⟩ : DyadicInterval 40),(⟨-84816768,-84816704⟩ : DyadicInterval 40),(⟨762123380337,762123399666⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨113204608,113204672⟩ : DyadicInterval 40),(⟨-113216320,-113216256⟩ : DyadicInterval 40),(⟨762123377750,762123397080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-11712,-6528⟩ : DyadicInterval 40),(⟨762123386880,762123408736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨219513337119,219768619670⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200140466816,200140466880⟩ : DyadicInterval 40),(⟨-244862801280,-244862801216⟩ : DyadicInterval 40),(⟨740062941252,740062960581⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200353244416,200353244480⟩ : DyadicInterval 40),(⟨-245181809728,-245181809664⟩ : DyadicInterval 40),(⟨740011250392,740011269721⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-44828565248,-44722334400⟩ : DyadicInterval 40),(⟨784484550816,784537685504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨200232003008,200421944896⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-245284842240,-245000018560⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1149_ok : ecellOkT e1149 = true := by decide +kernel
theorem e1149_pos {a z : ℝ} (ha1 : ((10227/51200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((819009/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1149 e1149_ok ha1 ha2 hz1 hz2 hz

-- box ['819009/4096000', '409929/2048000', '999/1000', '3997/4000']  interval_lower 502097453/1099511627776
noncomputable def e1150 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1319362682159,0,true,200421944832,200421944896⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨879660573393,0,false,-245284842240,-245284842176⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1319590583862,0,true,200611853888,200611853952⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨879432671690,0,false,-245569739712,-245569739648⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1319142831104,0,true,200238713280,200238713344⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨879880424448,0,false,-245010078784,-245010078720⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1319425524646,0,true,200474314368,200474314432⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨879597730906,0,false,-245363393600,-245363393536⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099596534521,0,true,84903424,84903488⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099426721031,0,false,-84910080,-84910016⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099624962653,0,true,113329024,113329088⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099398292899,0,false,-113340736,-113340672⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511616093,0,false,-11712,-11648⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621220,0,false,-6592,-6528⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1319252752647,0,true,200330329536,200330329600⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨879770502905,0,false,-245147446976,-245147446912⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1319508063685,0,true,200543094144,200543094208⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨879515191867,0,false,-245466573632,-245466573568⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1055493510468,0,false,-44923479424,-44923479360⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1055595619305,0,false,-44817117376,-44817117312⟩
    { al := (819009/4096000), au := (409929/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨219851054383,220078956086⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200421944832,200421944896⟩ : DyadicInterval 40),(⟨-245284842240,-245284842176⟩ : DyadicInterval 40),(⟨739994545393,739994564723⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200611853888,200611853952⟩ : DyadicInterval 40),(⟨-245569739712,-245569739648⟩ : DyadicInterval 40),(⟨739948328787,739948348116⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200238713280,200238713344⟩ : DyadicInterval 40),(⟨-245010078784,-245010078720⟩ : DyadicInterval 40),(⟨740039082762,740039102091⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200474314368,200474314432⟩ : DyadicInterval 40),(⟨-245363393600,-245363393536⟩ : DyadicInterval 40),(⟨739981806361,739981825691⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨84906745,113334877⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨84903424,84903488⟩ : DyadicInterval 40),(⟨-84910080,-84910016⟩ : DyadicInterval 40),(⟨762123380323,762123399652⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨113329024,113329088⟩ : DyadicInterval 40),(⟨-113340736,-113340672⟩ : DyadicInterval 40),(⟨762123377725,762123397055⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-11712,-6528⟩ : DyadicInterval 40),(⟨762123386880,762123408736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨219741124871,219996435909⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200330329536,200330329600⟩ : DyadicInterval 40),(⟨-245147446976,-245147446912⟩ : DyadicInterval 40),(⟨740016820629,740016839958⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200543094144,200543094208⟩ : DyadicInterval 40),(⟨-245466573632,-245466573568⟩ : DyadicInterval 40),(⟨739965068894,739965088224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-44923479424,-44817117312⟩ : DyadicInterval 40),(⟨784531942272,784585142592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨200421944832,200611853952⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-245569739712,-245284842176⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1150_ok : ecellOkT e1150 = true := by decide +kernel
theorem e1150_pos {a z : ℝ} (ha1 : ((819009/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((409929/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1150 e1150_ok ha1 ha2 hz1 hz2 hz

-- box ['10227/51200', '819009/4096000', '3997/4000', '1999/2000']  interval_lower 248247435/549755813888
noncomputable def e1151 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1319134780456,0,true,200232003008,200232003072⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨879888475096,0,false,-245000018624,-245000018560⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1319362682160,0,true,200421944832,200421944896⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨879660573392,0,false,-245284842240,-245284842176⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1318970063091,0,true,200094700864,200094700928⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨880053192461,0,false,-244794206528,-244794206464⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1319252756633,0,true,200330332864,200330332928⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨879770498919,0,false,-245147451968,-245147451904⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568170410,0,true,56541120,56541184⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455085142,0,false,-56544128,-56544064⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099596536315,0,true,84905216,84905280⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099426719237,0,false,-84911872,-84911808⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621219,0,false,-6592,-6528⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624869,0,false,-2944,-2880⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1319052417087,0,true,200163350144,200163350208⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨879970838465,0,false,-244897101888,-244897101824⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1319307728327,0,true,200376147264,200376147328⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨879715527225,0,false,-245216156096,-245216156032⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1055573642404,0,false,-44840008832,-44840008768⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1055675658284,0,false,-44733751680,-44733751616⟩
    { al := (10227/51200), au := (819009/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨219623152680,219851054384⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200232003008,200232003072⟩ : DyadicInterval 40),(⟨-245000018624,-245000018560⟩ : DyadicInterval 40),(⟨740040712793,740040732122⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200421944832,200421944896⟩ : DyadicInterval 40),(⟨-245284842240,-245284842176⟩ : DyadicInterval 40),(⟨739994545393,739994564722⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200094700864,200094700928⟩ : DyadicInterval 40),(⟨-244794206528,-244794206464⟩ : DyadicInterval 40),(⟨740074049989,740074069319⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200330332864,200330332928⟩ : DyadicInterval 40),(⟨-245147451968,-245147451904⟩ : DyadicInterval 40),(⟨740016819822,740016839151⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨56542634,84908539⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56541120,56541184⟩ : DyadicInterval 40),(⟨-56544128,-56544064⟩ : DyadicInterval 40),(⟨762123382148,762123401477⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨84905216,84905280⟩ : DyadicInterval 40),(⟨-84911872,-84911808⟩ : DyadicInterval 40),(⟨762123380322,762123399652⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6592,-2880⟩ : DyadicInterval 40),(⟨762123385056,762123406176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨219540789311,219796100551⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200163350144,200163350208⟩ : DyadicInterval 40),(⟨-244897101888,-244897101824⟩ : DyadicInterval 40),(⟨740057385563,740057404892⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200376147264,200376147328⟩ : DyadicInterval 40),(⟨-245216156096,-245216156032⟩ : DyadicInterval 40),(⟨740005682208,740005701537⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-44840008832,-44733751616⟩ : DyadicInterval 40),(⟨784490259424,784543407296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨200232003008,200421944896⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-245284842240,-245000018560⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1151_ok : ecellOkT e1151 = true := by decide +kernel
theorem e1151_pos {a z : ℝ} (ha1 : ((10227/51200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((819009/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1151 e1151_ok ha1 ha2 hz1 hz2 hz

-- box ['819009/4096000', '409929/2048000', '3997/4000', '1999/2000']  interval_lower 501224607/1099511627776
noncomputable def e1152 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1319362682159,0,true,200421944832,200421944896⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨879660573393,0,false,-245284842240,-245284842176⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1319590583862,0,true,200611853888,200611853952⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨879432671690,0,false,-245569739712,-245569739648⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1319197793868,0,true,200284524032,200284524096⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨879825461684,0,false,-245078763200,-245078763136⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1319480544385,0,true,200520162816,200520162880⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨879542711167,0,false,-245432171328,-245432171264⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568232612,0,true,56603328,56603392⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455022940,0,false,-56606336,-56606272⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099596629639,0,true,84998528,84998592⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099426625913,0,false,-85005184,-85005120⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621204,0,false,-6592,-6528⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624862,0,false,-2944,-2880⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1319280233328,0,true,200353232704,200353232768⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨879743022224,0,false,-245181792064,-245181792000⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1319535573055,0,true,200566016768,200566016832⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨879487682497,0,false,-245500964544,-245500964480⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1055482501322,0,false,-44934947712,-44934947648⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1055584634404,0,false,-44828559360,-44828559296⟩
    { al := (819009/4096000), au := (409929/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨219851054383,220078956086⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200421944832,200421944896⟩ : DyadicInterval 40),(⟨-245284842240,-245284842176⟩ : DyadicInterval 40),(⟨739994545393,739994564723⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200611853888,200611853952⟩ : DyadicInterval 40),(⟨-245569739712,-245569739648⟩ : DyadicInterval 40),(⟨739948328787,739948348116⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200284524032,200284524096⟩ : DyadicInterval 40),(⟨-245078763200,-245078763136⟩ : DyadicInterval 40),(⟨740027952707,740027972037⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200520162816,200520162880⟩ : DyadicInterval 40),(⟨-245432171328,-245432171264⟩ : DyadicInterval 40),(⟨739970650017,739970669347⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨56604836,85001863⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56603328,56603392⟩ : DyadicInterval 40),(⟨-56606336,-56606272⟩ : DyadicInterval 40),(⟨762123382141,762123401470⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨84998528,84998592⟩ : DyadicInterval 40),(⟨-85005184,-85005120⟩ : DyadicInterval 40),(⟨762123380308,762123399637⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6592,-2880⟩ : DyadicInterval 40),(⟨762123385056,762123406176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨219768605552,220023945279⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200353232704,200353232768⟩ : DyadicInterval 40),(⟨-245181792064,-245181792000⟩ : DyadicInterval 40),(⟨740011253212,740011272542⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200566016768,200566016832⟩ : DyadicInterval 40),(⟨-245500964544,-245500964480⟩ : DyadicInterval 40),(⟨739959489017,739959508347⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-44934947712,-44828559296⟩ : DyadicInterval 40),(⟨784537663264,784590876736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨200421944832,200611853952⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-245569739712,-245284842176⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1152_ok : ecellOkT e1152 = true := by decide +kernel
theorem e1152_pos {a z : ℝ} (ha1 : ((819009/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((409929/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1152 e1152_ok ha1 ha2 hz1 hz2 hz

-- box ['409929/2048000', '820707/4096000', '999/1000', '3997/4000']  interval_lower 506849517/1099511627776
noncomputable def e1153 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1319590583861,0,true,200611853888,200611853952⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨879432671691,0,false,-245569739712,-245569739648⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1319818485564,0,true,200801730176,200801730240⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨879204769988,0,false,-245854710976,-245854710912⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1319370504904,0,true,200428464064,200428464128⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨879652750648,0,false,-245294620160,-245294620096⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1319653255421,0,true,200664072000,200664072064⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨879370000131,0,false,-245648097664,-245648097600⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099596627840,0,true,84996736,84996800⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099426627712,0,false,-85003392,-85003328⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099625087103,0,true,113453440,113453504⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099398168449,0,false,-113465216,-113465152⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511616068,0,false,-11712,-11648⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621205,0,false,-6592,-6528⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1319480540395,0,true,200520159488,200520159552⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨879542715157,0,false,-245432166336,-245432166272⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1319735879932,0,true,200732911104,200732911168⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨879287375620,0,false,-245751411264,-245751411200⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1055402297767,0,false,-45018500160,-45018500096⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1055504523807,0,false,-44912006848,-44912006784⟩
    { al := (409929/2048000), au := (820707/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨220078956085,220306857788⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200611853888,200611853952⟩ : DyadicInterval 40),(⟨-245569739712,-245569739648⟩ : DyadicInterval 40),(⟨739948328787,739948348116⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200801730176,200801730240⟩ : DyadicInterval 40),(⟨-245854710976,-245854710912⟩ : DyadicInterval 40),(⟨739902062934,739902082264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200428464064,200428464128⟩ : DyadicInterval 40),(⟨-245294620160,-245294620096⟩ : DyadicInterval 40),(⟨739992959799,739992979129⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200664072000,200664072064⟩ : DyadicInterval 40),(⟨-245648097664,-245648097600⟩ : DyadicInterval 40),(⟨739935610838,739935630167⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨85000064,113459327⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨84996736,84996800⟩ : DyadicInterval 40),(⟨-85003392,-85003328⟩ : DyadicInterval 40),(⟨762123380308,762123399638⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨113453440,113453504⟩ : DyadicInterval 40),(⟨-113465216,-113465152⟩ : DyadicInterval 40),(⟨762123377731,762123397061⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-11712,-6528⟩ : DyadicInterval 40),(⟨762123386880,762123408736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨219968912619,220224252156⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200520159488,200520159552⟩ : DyadicInterval 40),(⟨-245432166336,-245432166272⟩ : DyadicInterval 40),(⟨739970650827,739970670156⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200732911104,200732911168⟩ : DyadicInterval 40),(⟨-245751411264,-245751411200⟩ : DyadicInterval 40),(⟨739918838202,739918857532⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45018500160,-44912006784⟩ : DyadicInterval 40),(⟨784579387008,784632652960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨200611853888,200801730240⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-245854710976,-245569739648⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1153_ok : ecellOkT e1153 = true := by decide +kernel
theorem e1153_pos {a z : ℝ} (ha1 : ((409929/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((820707/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1153 e1153_ok ha1 ha2 hz1 hz2 hz

-- box ['820707/4096000', '205389/1024000', '999/1000', '3997/4000']  interval_lower 511620251/1099511627776
noncomputable def e1154 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1319818485563,0,true,200801730176,200801730240⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨879204769989,0,false,-245854710976,-245854710912⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1320046387266,0,true,200991573696,200991573760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨878976868286,0,false,-246139756096,-246139756032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1319598178705,0,true,200618182080,200618182144⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨879425076847,0,false,-245579235200,-245579235136⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1319880986197,0,true,200853796864,200853796928⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨879142269355,0,false,-245932875456,-245932875392⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099596721177,0,true,85090048,85090112⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099426534375,0,false,-85096704,-85096640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099625211579,0,true,113577920,113577984⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099398043973,0,false,-113589696,-113589632⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511616042,0,false,-11776,-11712⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621191,0,false,-6592,-6528⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1319708328146,0,true,200709956672,200709956736⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨879314927406,0,false,-245716959488,-245716959424⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1319963696180,0,true,200922695296,200922695360⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨879059559372,0,false,-246036322752,-246036322688⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1055310990660,0,false,-45113627456,-45113627392⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1055413333926,0,false,-45007002816,-45007002752⟩
    { al := (820707/4096000), au := (205389/1024000), zl := (999/1000), zu := (3997/4000),
      A := ⟨220306857787,220534759490⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200801730176,200801730240⟩ : DyadicInterval 40),(⟨-245854710976,-245854710912⟩ : DyadicInterval 40),(⟨739902062935,739902082264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200991573696,200991573760⟩ : DyadicInterval 40),(⟨-246139756096,-246139756032⟩ : DyadicInterval 40),(⟨739855747849,739855767179⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200618182080,200618182144⟩ : DyadicInterval 40),(⟨-245579235200,-245579235136⟩ : DyadicInterval 40),(⟨739946787748,739946807078⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200853796864,200853796928⟩ : DyadicInterval 40),(⟨-245932875456,-245932875392⟩ : DyadicInterval 40),(⟨739889366187,739889385516⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨85093401,113583803⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨85090048,85090112⟩ : DyadicInterval 40),(⟨-85096704,-85096640⟩ : DyadicInterval 40),(⟨762123380294,762123399623⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨113577920,113577984⟩ : DyadicInterval 40),(⟨-113589696,-113589632⟩ : DyadicInterval 40),(⟨762123377705,762123397035⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-11776,-6528⟩ : DyadicInterval 40),(⟨762123386880,762123408768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨220196700370,220452068404⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200709956672,200709956736⟩ : DyadicInterval 40),(⟨-245716959488,-245716959424⟩ : DyadicInterval 40),(⟨739924431883,739924451213⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200922695296,200922695360⟩ : DyadicInterval 40),(⟨-246036322752,-246036322688⟩ : DyadicInterval 40),(⟨739872558355,739872577685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45113627456,-45007002752⟩ : DyadicInterval 40),(⟨784626884992,784680216608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨200801730176,200991573760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-246139756096,-245854710912⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1154_ok : ecellOkT e1154 = true := by decide +kernel
theorem e1154_pos {a z : ℝ} (ha1 : ((820707/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((205389/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1154 e1154_ok ha1 ha2 hz1 hz2 hz

-- box ['409929/2048000', '820707/4096000', '3997/4000', '1999/2000']  interval_lower 505972931/1099511627776
noncomputable def e1155 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1319590583861,0,true,200611853888,200611853952⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨879432671691,0,false,-245569739712,-245569739648⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1319818485564,0,true,200801730176,200801730240⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨879204769988,0,false,-245854710976,-245854710912⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1319425524643,0,true,200474314368,200474314432⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨879597730909,0,false,-245363393600,-245363393536⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1319708332136,0,true,200709959936,200709960000⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨879314923416,0,false,-245716964480,-245716964416⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568294827,0,true,56665536,56665600⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454960725,0,false,-56668544,-56668480⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099596722979,0,true,85091904,85091968⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099426532573,0,false,-85098560,-85098496⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621190,0,false,-6592,-6528⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624856,0,false,-2944,-2880⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1319508049558,0,true,200543082368,200543082432⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨879515205994,0,false,-245466555968,-245466555904⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1319763417780,0,true,200755853440,200755853504⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨879259837772,0,false,-245785846720,-245785846656⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1055391265813,0,false,-45029993216,-45029993152⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1055493516122,0,false,-44923473536,-44923473472⟩
    { al := (409929/2048000), au := (820707/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨220078956085,220306857788⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200611853888,200611853952⟩ : DyadicInterval 40),(⟨-245569739712,-245569739648⟩ : DyadicInterval 40),(⟨739948328787,739948348116⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200801730176,200801730240⟩ : DyadicInterval 40),(⟨-245854710976,-245854710912⟩ : DyadicInterval 40),(⟨739902062934,739902082264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200474314368,200474314432⟩ : DyadicInterval 40),(⟨-245363393600,-245363393536⟩ : DyadicInterval 40),(⟨739981806362,739981825692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200709959936,200709960000⟩ : DyadicInterval 40),(⟨-245716964480,-245716964416⟩ : DyadicInterval 40),(⟨739924431110,739924450440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨56667051,85095203⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56665536,56665600⟩ : DyadicInterval 40),(⟨-56668544,-56668480⟩ : DyadicInterval 40),(⟨762123382135,762123401464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨85091904,85091968⟩ : DyadicInterval 40),(⟨-85098560,-85098496⟩ : DyadicInterval 40),(⟨762123380293,762123399623⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6592,-2880⟩ : DyadicInterval 40),(⟨762123385056,762123406176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨219996421782,220251790004⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200543082368,200543082432⟩ : DyadicInterval 40),(⟨-245466555968,-245466555904⟩ : DyadicInterval 40),(⟨739965071761,739965091090⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200755853440,200755853504⟩ : DyadicInterval 40),(⟨-245785846720,-245785846656⟩ : DyadicInterval 40),(⟨739913246647,739913265976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45029993216,-44923473472⟩ : DyadicInterval 40),(⟨784585120352,784638399488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨200611853888,200801730240⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-245854710976,-245569739648⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1155_ok : ecellOkT e1155 = true := by decide +kernel
theorem e1155_pos {a z : ℝ} (ha1 : ((409929/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((820707/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1155 e1155_ok ha1 ha2 hz1 hz2 hz

-- box ['820707/4096000', '205389/1024000', '3997/4000', '1999/2000']  interval_lower 31921271/68719476736
noncomputable def e1156 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1319818485563,0,true,200801730176,200801730240⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨879204769989,0,false,-245854710976,-245854710912⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1320046387266,0,true,200991573696,200991573760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨878976868286,0,false,-246139756096,-246139756032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1319653255419,0,true,200664072000,200664072064⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨879370000133,0,false,-245648097664,-245648097600⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1319936119887,0,true,200899724352,200899724416⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨879087135665,0,false,-246001831360,-246001831296⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568357052,0,true,56727808,56727872⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454898500,0,false,-56730752,-56730688⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099596816337,0,true,85185216,85185280⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099426439215,0,false,-85191872,-85191808⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621175,0,false,-6656,-6592⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624850,0,false,-2944,-2880⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1319735865799,0,true,200732899328,200732899392⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨879287389753,0,false,-245751393600,-245751393536⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1319991262515,0,true,200945657408,200945657472⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨879031993037,0,false,-246070802752,-246070802688⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1055299935869,0,false,-45125145280,-45125145216⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1055402303430,0,false,-45018494208,-45018494144⟩
    { al := (820707/4096000), au := (205389/1024000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨220306857787,220534759490⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200801730176,200801730240⟩ : DyadicInterval 40),(⟨-245854710976,-245854710912⟩ : DyadicInterval 40),(⟨739902062935,739902082264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200991573696,200991573760⟩ : DyadicInterval 40),(⟨-246139756096,-246139756032⟩ : DyadicInterval 40),(⟨739855747849,739855767179⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200664072000,200664072064⟩ : DyadicInterval 40),(⟨-245648097664,-245648097600⟩ : DyadicInterval 40),(⟨739935610838,739935630168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200899724352,200899724416⟩ : DyadicInterval 40),(⟨-246001831360,-246001831296⟩ : DyadicInterval 40),(⟨739878162985,739878182315⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨56729276,85188561⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56727808,56727872⟩ : DyadicInterval 40),(⟨-56730752,-56730688⟩ : DyadicInterval 40),(⟨762123382096,762123401426⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨85185216,85185280⟩ : DyadicInterval 40),(⟨-85191872,-85191808⟩ : DyadicInterval 40),(⟨762123380279,762123399608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6656,-2880⟩ : DyadicInterval 40),(⟨762123385056,762123406208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨220224238023,220479634739⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200732899328,200732899392⟩ : DyadicInterval 40),(⟨-245751393600,-245751393536⟩ : DyadicInterval 40),(⟨739918841076,739918860406⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200945657408,200945657472⟩ : DyadicInterval 40),(⟨-246070802752,-246070802688⟩ : DyadicInterval 40),(⟨739866955056,739866974385⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45125145280,-45018494144⟩ : DyadicInterval 40),(⟨784632630688,784685975520⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨200801730176,200991573760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-246139756096,-245854710912⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1156_ok : ecellOkT e1156 = true := by decide +kernel
theorem e1156_pos {a z : ℝ} (ha1 : ((820707/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((205389/1024000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1156 e1156_ok ha1 ha2 hz1 hz2 hz

-- box ['10227/51200', '819009/4096000', '1999/2000', '3999/4000']  interval_lower 495624189/1099511627776
noncomputable def e1157 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1319134780456,0,true,200232003008,200232003072⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨879888475096,0,false,-245000018624,-245000018560⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1319362682160,0,true,200421944832,200421944896⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨879660573392,0,false,-245284842240,-245284842176⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1319024968879,0,true,200140470144,200140470208⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨879998286673,0,false,-244862806272,-244862806208⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1319307719397,0,true,200376139840,200376139904⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨879715536155,0,false,-245216144960,-245216144896⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539899176,0,true,28270976,28271040⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483356376,0,false,-28271808,-28271744⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568233980,0,true,56604736,56604800⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455021572,0,false,-56607680,-56607616⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624861,0,false,-2944,-2880⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627050,0,false,-768,-704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1319079869483,0,true,200186233216,200186233280⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨879943386069,0,false,-244931403840,-244931403776⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1319335209412,0,true,200399049792,200399049856⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨879688046140,0,false,-245250503872,-245250503808⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1055562654593,0,false,-44851454080,-44851454016⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1055664694694,0,false,-44745170624,-44745170560⟩
    { al := (10227/51200), au := (819009/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨219623152680,219851054384⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200232003008,200232003072⟩ : DyadicInterval 40),(⟨-245000018624,-245000018560⟩ : DyadicInterval 40),(⟨740040712793,740040732122⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200421944832,200421944896⟩ : DyadicInterval 40),(⟨-245284842240,-245284842176⟩ : DyadicInterval 40),(⟨739994545393,739994564722⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200140470144,200140470208⟩ : DyadicInterval 40),(⟨-244862806272,-244862806208⟩ : DyadicInterval 40),(⟨740062940447,740062959777⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200376139840,200376139904⟩ : DyadicInterval 40),(⟨-245216144960,-245216144896⟩ : DyadicInterval 40),(⟨740005684016,740005703346⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨28271400,56606204⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28270976,28271040⟩ : DyadicInterval 40),(⟨-28271808,-28271744⟩ : DyadicInterval 40),(⟨762123383241,762123402570⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56604736,56604800⟩ : DyadicInterval 40),(⟨-56607680,-56607616⟩ : DyadicInterval 40),(⟨762123382109,762123401438⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2944,-704⟩ : DyadicInterval 40),(⟨762123383968,762123404352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨219568241707,219823581636⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200186233216,200186233280⟩ : DyadicInterval 40),(⟨-244931403840,-244931403776⟩ : DyadicInterval 40),(⟨740051829096,740051848426⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200399049792,200399049856⟩ : DyadicInterval 40),(⟨-245250503872,-245250503808⟩ : DyadicInterval 40),(⟨740000113307,740000132636⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-44851454080,-44745170560⟩ : DyadicInterval 40),(⟨784495968896,784549129920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨200232003008,200421944896⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-245284842240,-245000018560⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1157_ok : ecellOkT e1157 = true := by decide +kernel
theorem e1157_pos {a z : ℝ} (ha1 : ((10227/51200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((819009/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1157 e1157_ok ha1 ha2 hz1 hz2 hz

-- box ['819009/4096000', '409929/2048000', '1999/2000', '3999/4000']  interval_lower 500350227/1099511627776
noncomputable def e1158 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1319362682159,0,true,200421944832,200421944896⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨879660573393,0,false,-245284842240,-245284842176⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1319590583862,0,true,200611853888,200611853952⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨879432671690,0,false,-245569739712,-245569739648⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1319252756631,0,true,200330332864,200330332928⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨879770498921,0,false,-245147451968,-245147451904⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1319535564124,0,true,200566009344,200566009408⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨879487691428,0,false,-245500953344,-245500953280⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539930278,0,true,28302080,28302144⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483325274,0,false,-28302912,-28302848⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568296198,0,true,56666944,56667008⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454959354,0,false,-56669888,-56669824⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624855,0,false,-2944,-2880⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627048,0,false,-768,-704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1319307714203,0,true,200376135488,200376135552⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨879715541349,0,false,-245216138496,-245216138432⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1319563082625,0,true,200588939072,200588939136⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨879460172927,0,false,-245535356800,-245535356736⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1055471490720,0,false,-44946417728,-44946417664⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1055573648051,0,false,-44840002944,-44840002880⟩
    { al := (819009/4096000), au := (409929/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨219851054383,220078956086⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200421944832,200421944896⟩ : DyadicInterval 40),(⟨-245284842240,-245284842176⟩ : DyadicInterval 40),(⟨739994545393,739994564723⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200611853888,200611853952⟩ : DyadicInterval 40),(⟨-245569739712,-245569739648⟩ : DyadicInterval 40),(⟨739948328787,739948348116⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200330332864,200330332928⟩ : DyadicInterval 40),(⟨-245147451968,-245147451904⟩ : DyadicInterval 40),(⟨740016819822,740016839152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200566009344,200566009408⟩ : DyadicInterval 40),(⟨-245500953344,-245500953280⟩ : DyadicInterval 40),(⟨739959490804,739959510134⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨28302502,56668422⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28302080,28302144⟩ : DyadicInterval 40),(⟨-28302912,-28302848⟩ : DyadicInterval 40),(⟨762123383239,762123402568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56666944,56667008⟩ : DyadicInterval 40),(⟨-56669888,-56669824⟩ : DyadicInterval 40),(⟨762123382103,762123401432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2944,-704⟩ : DyadicInterval 40),(⟨762123383968,762123404352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨219796086427,220051454849⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200376135488,200376135552⟩ : DyadicInterval 40),(⟨-245216138496,-245216138432⟩ : DyadicInterval 40),(⟨740005685094,740005704423⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200588939072,200588939136⟩ : DyadicInterval 40),(⟨-245535356800,-245535356736⟩ : DyadicInterval 40),(⟨739953908395,739953927725⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-44946417728,-44840002880⟩ : DyadicInterval 40),(⟨784543385056,784596611744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨200421944832,200611853952⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-245569739712,-245284842176⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1158_ok : ecellOkT e1158 = true := by decide +kernel
theorem e1158_pos {a z : ℝ} (ha1 : ((819009/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((409929/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1158 e1158_ok ha1 ha2 hz1 hz2 hz

-- box ['10227/51200', '819009/4096000', '3999/4000', '1']  interval_lower 247376501/549755813888
noncomputable def e1159 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1319134780456,0,true,200232003008,200232003072⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨879888475096,0,false,-245000018624,-245000018560⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1319362682160,0,true,200421944832,200421944896⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨879660573392,0,false,-245284842240,-245284842176⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1319079874667,0,true,200186237504,200186237568⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨879943380885,0,false,-244931410304,-244931410240⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539931220,0,true,28303040,28303104⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483324332,0,false,-28303872,-28303808⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627047,0,false,-768,-704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1319107322076,0,true,200209115904,200209115968⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨879915933476,0,false,-244965707072,-244965707008⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1319362690690,0,true,200421951936,200421952000⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨879660564862,0,false,-245284852928,-245284852864⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1055551665331,0,false,-44862900928,-44862900864⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1055653729654,0,false,-44756591168,-44756591104⟩
    { al := (10227/51200), au := (819009/4096000), zl := (3999/4000), zu := 1,
      A := ⟨219623152680,219851054384⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200232003008,200232003072⟩ : DyadicInterval 40),(⟨-245000018624,-245000018560⟩ : DyadicInterval 40),(⟨740040712793,740040732122⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200421944832,200421944896⟩ : DyadicInterval 40),(⟨-245284842240,-245284842176⟩ : DyadicInterval 40),(⟨739994545393,739994564722⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200186237504,200186237568⟩ : DyadicInterval 40),(⟨-244931410304,-244931410240⟩ : DyadicInterval 40),(⟨740051828061,740051847391⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200421944832,200421944896⟩ : DyadicInterval 40),(⟨-245284842240,-245284842176⟩ : DyadicInterval 40),(⟨739994545393,739994564722⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,28303444⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28303040,28303104⟩ : DyadicInterval 40),(⟨-28303872,-28303808⟩ : DyadicInterval 40),(⟨762123383239,762123402568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-768,0⟩ : DyadicInterval 40),(⟨762123383616,762123403264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨219595694300,219851062914⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200209115904,200209115968⟩ : DyadicInterval 40),(⟨-244965707072,-244965707008⟩ : DyadicInterval 40),(⟨740046271904,740046291233⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200421951936,200421952000⟩ : DyadicInterval 40),(⟨-245284852928,-245284852864⟩ : DyadicInterval 40),(⟨739994543677,739994563007⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-44862900928,-44756591104⟩ : DyadicInterval 40),(⟨784501679168,784554853344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨200232003008,200421944896⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-245284842240,-245000018560⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1159_ok : ecellOkT e1159 = true := by decide +kernel
theorem e1159_pos {a z : ℝ} (ha1 : ((10227/51200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((819009/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1159 e1159_ok ha1 ha2 hz1 hz2 hz

-- box ['819009/4096000', '409929/2048000', '3999/4000', '1']  interval_lower 499475951/1099511627776
noncomputable def e1160 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1319362682159,0,true,200421944832,200421944896⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨879660573393,0,false,-245284842240,-245284842176⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1319590583862,0,true,200611853888,200611853952⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨879432671690,0,false,-245569739712,-245569739648⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1319307719395,0,true,200376139840,200376139904⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨879715536157,0,false,-245216144960,-245216144896⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539962329,0,true,28334144,28334208⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483293223,0,false,-28334976,-28334912⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627045,0,false,-768,-704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1319335195287,0,true,200399038016,200399038080⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨879688060265,0,false,-245250486208,-245250486144⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1319590592386,0,true,200611860992,200611861056⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨879432663166,0,false,-245569750336,-245569750272⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1055460478665,0,false,-44957889280,-44957889216⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1055562660242,0,false,-44851448192,-44851448128⟩
    { al := (819009/4096000), au := (409929/2048000), zl := (3999/4000), zu := 1,
      A := ⟨219851054383,220078956086⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200421944832,200421944896⟩ : DyadicInterval 40),(⟨-245284842240,-245284842176⟩ : DyadicInterval 40),(⟨739994545393,739994564723⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200611853888,200611853952⟩ : DyadicInterval 40),(⟨-245569739712,-245569739648⟩ : DyadicInterval 40),(⟨739948328787,739948348116⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200376139840,200376139904⟩ : DyadicInterval 40),(⟨-245216144960,-245216144896⟩ : DyadicInterval 40),(⟨740005684017,740005703346⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200611853888,200611853952⟩ : DyadicInterval 40),(⟨-245569739712,-245569739648⟩ : DyadicInterval 40),(⟨739948328787,739948348116⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,28334553⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28334144,28334208⟩ : DyadicInterval 40),(⟨-28334976,-28334912⟩ : DyadicInterval 40),(⟨762123383237,762123402566⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-768,0⟩ : DyadicInterval 40),(⟨762123383616,762123403264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨219823567511,220078964610⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200399038016,200399038080⟩ : DyadicInterval 40),(⟨-245250486208,-245250486144⟩ : DyadicInterval 40),(⟨740000116168,740000135497⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200611860992,200611861056⟩ : DyadicInterval 40),(⟨-245569750336,-245569750272⟩ : DyadicInterval 40),(⟨739948327043,739948346372⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-44957889280,-44851448128⟩ : DyadicInterval 40),(⟨784549107680,784602347520⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨200421944832,200611853952⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-245569739712,-245284842176⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1160_ok : ecellOkT e1160 = true := by decide +kernel
theorem e1160_pos {a z : ℝ} (ha1 : ((819009/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((409929/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1160 e1160_ok ha1 ha2 hz1 hz2 hz

-- box ['409929/2048000', '820707/4096000', '1999/2000', '3999/4000']  interval_lower 505095617/1099511627776
noncomputable def e1161 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1319590583861,0,true,200611853888,200611853952⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨879432671691,0,false,-245569739712,-245569739648⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1319818485564,0,true,200801730176,200801730240⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨879204769988,0,false,-245854710976,-245854710912⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1319480544382,0,true,200520162816,200520162880⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨879542711170,0,false,-245432171328,-245432171264⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1319763408850,0,true,200755846016,200755846080⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨879259846702,0,false,-245785835584,-245785835520⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539961386,0,true,28333184,28333248⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483294166,0,false,-28334016,-28333952⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568358426,0,true,56729152,56729216⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454897126,0,false,-56732160,-56732096⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624848,0,false,-2944,-2880⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627046,0,false,-768,-704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1319535558926,0,true,200566004992,200566005056⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨879487696626,0,false,-245500946880,-245500946816⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1319790955835,0,true,200778795520,200778795584⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨879232299717,0,false,-245820283520,-245820283456⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1055380232396,0,false,-45041487936,-45041487872⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1055482506978,0,false,-44934941824,-44934941760⟩
    { al := (409929/2048000), au := (820707/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨220078956085,220306857788⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200611853888,200611853952⟩ : DyadicInterval 40),(⟨-245569739712,-245569739648⟩ : DyadicInterval 40),(⟨739948328787,739948348116⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200801730176,200801730240⟩ : DyadicInterval 40),(⟨-245854710976,-245854710912⟩ : DyadicInterval 40),(⟨739902062934,739902082264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200520162816,200520162880⟩ : DyadicInterval 40),(⟨-245432171328,-245432171264⟩ : DyadicInterval 40),(⟨739970650018,739970669347⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200755846016,200755846080⟩ : DyadicInterval 40),(⟨-245785835584,-245785835520⟩ : DyadicInterval 40),(⟨739913248463,739913267793⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨28333610,56730650⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28333184,28333248⟩ : DyadicInterval 40),(⟨-28334016,-28333952⟩ : DyadicInterval 40),(⟨762123383237,762123402566⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56729152,56729216⟩ : DyadicInterval 40),(⟨-56732160,-56732096⟩ : DyadicInterval 40),(⟨762123382128,762123401457⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2944,-704⟩ : DyadicInterval 40),(⟨762123383968,762123404352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨220023931150,220279328059⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200566004992,200566005056⟩ : DyadicInterval 40),(⟨-245500946880,-245500946816⟩ : DyadicInterval 40),(⟨739959491885,739959511214⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200778795520,200778795584⟩ : DyadicInterval 40),(⟨-245820283520,-245820283456⟩ : DyadicInterval 40),(⟨739907654304,739907673633⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45041487936,-44934941760⟩ : DyadicInterval 40),(⟨784590854496,784644146848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨200611853888,200801730240⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-245854710976,-245569739648⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1161_ok : ecellOkT e1161 = true := by decide +kernel
theorem e1161_pos {a z : ℝ} (ha1 : ((409929/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((820707/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1161 e1161_ok ha1 ha2 hz1 hz2 hz

-- box ['820707/4096000', '205389/1024000', '1999/2000', '3999/4000']  interval_lower 509859701/1099511627776
noncomputable def e1162 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1319818485563,0,true,200801730176,200801730240⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨879204769989,0,false,-245854710976,-245854710912⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1320046387266,0,true,200991573696,200991573760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨878976868286,0,false,-246139756096,-246139756032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1319708332134,0,true,200709959936,200709960000⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨879314923418,0,false,-245716964480,-245716964416⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1319991253577,0,true,200945649984,200945650048⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨879032001975,0,false,-246070791552,-246070791488⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539992500,0,true,28364352,28364416⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483263052,0,false,-28365120,-28365056⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568420666,0,true,56791360,56791424⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454834886,0,false,-56794368,-56794304⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624842,0,false,-2944,-2880⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627045,0,false,-768,-704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1319763403646,0,true,200755841664,200755841728⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨879259851906,0,false,-245785829056,-245785828992⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1320018829060,0,true,200968619264,200968619328⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨879004426492,0,false,-246105284096,-246105284032⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1055288879612,0,false,-45136664832,-45136664768⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1055391271476,0,false,-45029987328,-45029987264⟩
    { al := (820707/4096000), au := (205389/1024000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨220306857787,220534759490⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200801730176,200801730240⟩ : DyadicInterval 40),(⟨-245854710976,-245854710912⟩ : DyadicInterval 40),(⟨739902062935,739902082264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200991573696,200991573760⟩ : DyadicInterval 40),(⟨-246139756096,-246139756032⟩ : DyadicInterval 40),(⟨739855747849,739855767179⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200709959936,200709960000⟩ : DyadicInterval 40),(⟨-245716964480,-245716964416⟩ : DyadicInterval 40),(⟨739924431111,739924450440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200945649984,200945650048⟩ : DyadicInterval 40),(⟨-246070791552,-246070791488⟩ : DyadicInterval 40),(⟨739866956852,739866976181⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨28364724,56792890⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28364352,28364416⟩ : DyadicInterval 40),(⟨-28365120,-28365056⟩ : DyadicInterval 40),(⟨762123383204,762123402533⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56791360,56791424⟩ : DyadicInterval 40),(⟨-56794368,-56794304⟩ : DyadicInterval 40),(⟨762123382122,762123401451⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2944,-704⟩ : DyadicInterval 40),(⟨762123383968,762123404352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨220251775870,220507201284⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200755841664,200755841728⟩ : DyadicInterval 40),(⟨-245785829056,-245785828992⟩ : DyadicInterval 40),(⟨739913249522,739913268851⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200968619264,200968619328⟩ : DyadicInterval 40),(⟨-246105284096,-246105284032⟩ : DyadicInterval 40),(⟨739861350964,739861370294⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45136664832,-45029987264⟩ : DyadicInterval 40),(⟨784638377248,784691735296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨200801730176,200991573760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-246139756096,-245854710912⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1162_ok : ecellOkT e1162 = true := by decide +kernel
theorem e1162_pos {a z : ℝ} (ha1 : ((820707/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((205389/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1162 e1162_ok ha1 ha2 hz1 hz2 hz

-- box ['409929/2048000', '820707/4096000', '3999/4000', '1']  interval_lower 252108853/549755813888
noncomputable def e1163 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1319590583861,0,true,200611853888,200611853952⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨879432671691,0,false,-245569739712,-245569739648⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1319818485564,0,true,200801730176,200801730240⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨879204769988,0,false,-245854710976,-245854710912⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1319535564121,0,true,200566009280,200566009344⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨879487691431,0,false,-245500953344,-245500953280⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539993444,0,true,28365248,28365312⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483262108,0,false,-28366080,-28366016⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627044,0,false,-768,-704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1319563068490,0,true,200588927296,200588927360⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨879460187062,0,false,-245535339136,-245535339072⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1319818494093,0,true,200801737280,200801737344⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨879204761459,0,false,-245854721664,-245854721600⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1055369197518,0,false,-45052984320,-45052984256⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1055471496379,0,false,-44946411840,-44946411776⟩
    { al := (409929/2048000), au := (820707/4096000), zl := (3999/4000), zu := 1,
      A := ⟨220078956085,220306857788⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200611853888,200611853952⟩ : DyadicInterval 40),(⟨-245569739712,-245569739648⟩ : DyadicInterval 40),(⟨739948328787,739948348116⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200801730176,200801730240⟩ : DyadicInterval 40),(⟨-245854710976,-245854710912⟩ : DyadicInterval 40),(⟨739902062934,739902082264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200566009280,200566009344⟩ : DyadicInterval 40),(⟨-245500953344,-245500953280⟩ : DyadicInterval 40),(⟨739959490843,739959510173⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200801730176,200801730240⟩ : DyadicInterval 40),(⟨-245854710976,-245854710912⟩ : DyadicInterval 40),(⟨739902062934,739902082264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,28365668⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28365248,28365312⟩ : DyadicInterval 40),(⟨-28366080,-28366016⟩ : DyadicInterval 40),(⟨762123383236,762123402565⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-768,0⟩ : DyadicInterval 40),(⟨762123383616,762123403264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨220051440714,220306866317⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200588927296,200588927360⟩ : DyadicInterval 40),(⟨-245535339136,-245535339072⟩ : DyadicInterval 40),(⟨739953911265,739953930594⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200801737280,200801737344⟩ : DyadicInterval 40),(⟨-245854721664,-245854721600⟩ : DyadicInterval 40),(⟨739902061211,739902080541⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45052984320,-44946411776⟩ : DyadicInterval 40),(⟨784596589504,784649895040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨200611853888,200801730240⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-245854710976,-245569739648⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1163_ok : ecellOkT e1163 = true := by decide +kernel
theorem e1163_pos {a z : ℝ} (ha1 : ((409929/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((820707/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1163 e1163_ok ha1 ha2 hz1 hz2 hz

-- box ['820707/4096000', '205389/1024000', '3999/4000', '1']  interval_lower 508978201/1099511627776
noncomputable def e1164 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1319818485563,0,true,200801730176,200801730240⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨879204769989,0,false,-245854710976,-245854710912⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1320046387266,0,true,200991573696,200991573760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨878976868286,0,false,-246139756096,-246139756032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1319763408848,0,true,200755846016,200755846080⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨879259846704,0,false,-245785835584,-245785835520⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540024565,0,true,28396416,28396480⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483230987,0,false,-28397184,-28397120⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627042,0,false,-768,-704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1319790941701,0,true,200778783744,200778783808⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨879232313851,0,false,-245820265856,-245820265792⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1320046395804,0,true,200991580800,200991580864⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨878976859748,0,false,-246139766784,-246139766720⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1055277821892,0,false,-45148185984,-45148185920⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1055380238060,0,false,-45041482048,-45041481984⟩
    { al := (820707/4096000), au := (205389/1024000), zl := (3999/4000), zu := 1,
      A := ⟨220306857787,220534759490⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200801730176,200801730240⟩ : DyadicInterval 40),(⟨-245854710976,-245854710912⟩ : DyadicInterval 40),(⟨739902062935,739902082264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200991573696,200991573760⟩ : DyadicInterval 40),(⟨-246139756096,-246139756032⟩ : DyadicInterval 40),(⟨739855747849,739855767179⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200755846016,200755846080⟩ : DyadicInterval 40),(⟨-245785835584,-245785835520⟩ : DyadicInterval 40),(⟨739913248463,739913267793⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200991573696,200991573760⟩ : DyadicInterval 40),(⟨-246139756096,-246139756032⟩ : DyadicInterval 40),(⟨739855747849,739855767179⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,28396789⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28396416,28396480⟩ : DyadicInterval 40),(⟨-28397184,-28397120⟩ : DyadicInterval 40),(⟨762123383202,762123402531⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-768,0⟩ : DyadicInterval 40),(⟨762123383616,762123403264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨220279313925,220534768028⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200778783744,200778783808⟩ : DyadicInterval 40),(⟨-245820265856,-245820265792⟩ : DyadicInterval 40),(⟨739907657179,739907676509⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200991580800,200991580864⟩ : DyadicInterval 40),(⟨-246139766784,-246139766720⟩ : DyadicInterval 40),(⟨739855746121,739855765451⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45148185984,-45041481984⟩ : DyadicInterval 40),(⟨784644124608,784697495872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨200801730176,200991573760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-246139756096,-245854710912⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1164_ok : ecellOkT e1164 = true := by decide +kernel
theorem e1164_pos {a z : ℝ} (ha1 : ((820707/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((205389/1024000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1164 e1164_ok ha1 ha2 hz1 hz2 hz

-- box ['205389/1024000', '164481/819200', '999/1000', '3997/4000']  interval_lower 258205203/549755813888
noncomputable def e1165 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1320046387265,0,true,200991573696,200991573760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨878976868287,0,false,-246139756096,-246139756032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1320274288968,0,true,201181384384,201181384448⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨878748966584,0,false,-246424875200,-246424875136⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1319825852505,0,true,200807867392,200807867456⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨879197403047,0,false,-245863923904,-245863923840⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1320108716973,0,true,201043488960,201043489024⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨878914538579,0,false,-246217727104,-246217727040⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099596814531,0,true,85183424,85183488⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099426441021,0,false,-85190080,-85190016⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099625336076,0,true,113702400,113702464⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099397919476,0,false,-113714240,-113714176⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511616016,0,false,-11776,-11712⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621176,0,false,-6656,-6592⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1319936115902,0,true,200899721024,200899721088⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨879087139650,0,false,-246001826368,-246001826304⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1320191512412,0,true,201112446720,201112446784⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨878831743140,0,false,-246321308032,-246321307968⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1055219589153,0,false,-45208861312,-45208861248⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1055322049660,0,false,-45102105280,-45102105216⟩
    { al := (205389/1024000), au := (164481/819200), zl := (999/1000), zu := (3997/4000),
      A := ⟨220534759489,220762661192⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200991573696,200991573760⟩ : DyadicInterval 40),(⟨-246139756096,-246139756032⟩ : DyadicInterval 40),(⟨739855747850,739855767179⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201181384384,201181384448⟩ : DyadicInterval 40),(⟨-246424875200,-246424875136⟩ : DyadicInterval 40),(⟨739809383608,739809402938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200807867392,200807867456⟩ : DyadicInterval 40),(⟨-245863923904,-245863923840⟩ : DyadicInterval 40),(⟨739900566559,739900585888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201043488960,201043489024⟩ : DyadicInterval 40),(⟨-246217727104,-246217727040⟩ : DyadicInterval 40),(⟨739843072447,739843091776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨85186755,113708300⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨85183424,85183488⟩ : DyadicInterval 40),(⟨-85190080,-85190016⟩ : DyadicInterval 40),(⟨762123380279,762123399609⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨113702400,113702464⟩ : DyadicInterval 40),(⟨-113714240,-113714176⟩ : DyadicInterval 40),(⟨762123377712,762123397042⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-11776,-6592⟩ : DyadicInterval 40),(⟨762123386912,762123408768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨220424488126,220679884636⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200899721024,200899721088⟩ : DyadicInterval 40),(⟨-246001826368,-246001826304⟩ : DyadicInterval 40),(⟨739878163797,739878183127⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201112446720,201112446784⟩ : DyadicInterval 40),(⟨-246321308032,-246321307968⟩ : DyadicInterval 40),(⟨739826229319,739826248648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45208861312,-45102105216⟩ : DyadicInterval 40),(⟨784674436224,784727833536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨200991573696,201181384448⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-246424875200,-246139756032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1165_ok : ecellOkT e1165 = true := by decide +kernel
theorem e1165_pos {a z : ℝ} (ha1 : ((205389/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((164481/819200 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1165 e1165_ok ha1 ha2 hz1 hz2 hz

-- box ['164481/819200', '411627/2048000', '999/1000', '3997/4000']  interval_lower 521219533/1099511627776
noncomputable def e1166 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1320274288967,0,true,201181384384,201181384448⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨878748966585,0,false,-246424875200,-246424875136⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1320502190670,0,true,201371162304,201371162368⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨878521064882,0,false,-246710068224,-246710068160⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1320053526305,0,true,200997520000,200997520064⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨878969729247,0,false,-246148686400,-246148686336⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1320336447748,0,true,201233148416,201233148480⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨878686807804,0,false,-246502652480,-246502652416⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099596907902,0,true,85276800,85276864⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099426347650,0,false,-85283456,-85283392⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099625460597,0,true,113826880,113826944⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099397794955,0,false,-113838720,-113838656⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511615990,0,false,-11840,-11776⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621162,0,false,-6656,-6592⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1320163903648,0,true,201089452736,201089452800⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨878859351904,0,false,-246286767104,-246286767040⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1320419328656,0,true,201302165376,201302165440⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨878603926896,0,false,-246606367296,-246606367232⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1055128093236,0,false,-45304201856,-45304201792⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1055230671016,0,false,-45197314368,-45197314304⟩
    { al := (164481/819200), au := (411627/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨220762661191,220990562894⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201181384384,201181384448⟩ : DyadicInterval 40),(⟨-246424875200,-246424875136⟩ : DyadicInterval 40),(⟨739809383609,739809402938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201371162304,201371162368⟩ : DyadicInterval 40),(⟨-246710068224,-246710068160⟩ : DyadicInterval 40),(⟨739762970135,739762989464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200997520000,200997520064⟩ : DyadicInterval 40),(⟨-246148686400,-246148686336⟩ : DyadicInterval 40),(⟨739854296268,739854315598⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201233148416,201233148480⟩ : DyadicInterval 40),(⟨-246502652480,-246502652416⟩ : DyadicInterval 40),(⟨739796729478,739796748807⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨85280126,113832821⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨85276800,85276864⟩ : DyadicInterval 40),(⟨-85283456,-85283392⟩ : DyadicInterval 40),(⟨762123380265,762123399594⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨113826880,113826944⟩ : DyadicInterval 40),(⟨-113838720,-113838656⟩ : DyadicInterval 40),(⟨762123377686,762123397016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-11840,-6592⟩ : DyadicInterval 40),(⟨762123386912,762123408800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨220652275872,220907700880⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201089452736,201089452800⟩ : DyadicInterval 40),(⟨-246286767104,-246286767040⟩ : DyadicInterval 40),(⟨739831846496,739831865825⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201302165376,201302165440⟩ : DyadicInterval 40),(⟨-246606367296,-246606367232⟩ : DyadicInterval 40),(⟨739779851151,739779870480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45304201856,-45197314304⟩ : DyadicInterval 40),(⟨784722040768,784775503808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨201181384384,201371162368⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-246710068224,-246424875136⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1166_ok : ecellOkT e1166 = true := by decide +kernel
theorem e1166_pos {a z : ℝ} (ha1 : ((164481/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((411627/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1166 e1166_ok ha1 ha2 hz1 hz2 hz

-- box ['205389/1024000', '164481/819200', '3997/4000', '1999/2000']  interval_lower 32220439/68719476736
noncomputable def e1167 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1320046387265,0,true,200991573696,200991573760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨878976868287,0,false,-246139756096,-246139756032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1320274288968,0,true,201181384384,201181384448⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨878748966584,0,false,-246424875200,-246424875136⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1319880986195,0,true,200853796864,200853796928⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨879142269357,0,false,-245932875456,-245932875392⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1320163907638,0,true,201089456064,201089456128⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨878859347914,0,false,-246286772096,-246286772032⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568419289,0,true,56790016,56790080⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454836263,0,false,-56793024,-56792960⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099596909712,0,true,85278592,85278656⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099426345840,0,false,-85285248,-85285184⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621161,0,false,-6656,-6592⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624843,0,false,-2944,-2880⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1319963682041,0,true,200922683520,200922683584⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨879059573511,0,false,-246036305088,-246036305024⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1320219107243,0,true,201135428608,201135428672⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨878804148309,0,false,-246355832640,-246355832576⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1055208511499,0,false,-45220404032,-45220403968⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1055310996331,0,false,-45113621504,-45113621440⟩
    { al := (205389/1024000), au := (164481/819200), zl := (3997/4000), zu := (1999/2000),
      A := ⟨220534759489,220762661192⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200991573696,200991573760⟩ : DyadicInterval 40),(⟨-246139756096,-246139756032⟩ : DyadicInterval 40),(⟨739855747850,739855767179⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201181384384,201181384448⟩ : DyadicInterval 40),(⟨-246424875200,-246424875136⟩ : DyadicInterval 40),(⟨739809383608,739809402938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200853796864,200853796928⟩ : DyadicInterval 40),(⟨-245932875456,-245932875392⟩ : DyadicInterval 40),(⟨739889366187,739889385517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201089456064,201089456128⟩ : DyadicInterval 40),(⟨-246286772096,-246286772032⟩ : DyadicInterval 40),(⟨739831845682,739831865011⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨56791513,85281936⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56790016,56790080⟩ : DyadicInterval 40),(⟨-56793024,-56792960⟩ : DyadicInterval 40),(⟨762123382122,762123401451⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨85278592,85278656⟩ : DyadicInterval 40),(⟨-85285248,-85285184⟩ : DyadicInterval 40),(⟨762123380264,762123399594⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6656,-2880⟩ : DyadicInterval 40),(⟨762123385056,762123406208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨220452054265,220707479467⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200922683520,200922683584⟩ : DyadicInterval 40),(⟨-246036305088,-246036305024⟩ : DyadicInterval 40),(⟨739872561236,739872580566⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201135428608,201135428672⟩ : DyadicInterval 40),(⟨-246355832640,-246355832576⟩ : DyadicInterval 40),(⟨739820614272,739820633602⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45220404032,-45113621440⟩ : DyadicInterval 40),(⟨784680194336,784733604896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨200991573696,201181384448⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-246424875200,-246139756032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1167_ok : ecellOkT e1167 = true := by decide +kernel
theorem e1167_pos {a z : ℝ} (ha1 : ((205389/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((164481/819200 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1167 e1167_ok ha1 ha2 hz1 hz2 hz

-- box ['164481/819200', '411627/2048000', '3997/4000', '1999/2000']  interval_lower 130083271/274877906944
noncomputable def e1168 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1320274288967,0,true,201181384384,201181384448⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨878748966585,0,false,-246424875200,-246424875136⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1320502190670,0,true,201371162304,201371162368⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨878521064882,0,false,-246710068224,-246710068160⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1320108716971,0,true,201043488960,201043489024⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨878914538581,0,false,-246217727104,-246217727040⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1320391695389,0,true,201279154944,201279155008⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨878631560163,0,false,-246571786688,-246571786624⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568481540,0,true,56852288,56852352⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454774012,0,false,-56855296,-56855232⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099597003106,0,true,85371968,85372032⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099426252446,0,false,-85378688,-85378624⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621146,0,false,-6656,-6592⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624837,0,false,-2944,-2880⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1320191498268,0,true,201112434944,201112435008⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨878831757284,0,false,-246321290368,-246321290304⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1320446951965,0,true,201325167040,201325167104⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨878576303587,0,false,-246640936448,-246640936384⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1055116992702,0,false,-45315769408,-45315769344⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1055219594832,0,false,-45208855424,-45208855360⟩
    { al := (164481/819200), au := (411627/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨220762661191,220990562894⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201181384384,201181384448⟩ : DyadicInterval 40),(⟨-246424875200,-246424875136⟩ : DyadicInterval 40),(⟨739809383609,739809402938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201371162304,201371162368⟩ : DyadicInterval 40),(⟨-246710068224,-246710068160⟩ : DyadicInterval 40),(⟨739762970135,739762989464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201043488960,201043489024⟩ : DyadicInterval 40),(⟨-246217727104,-246217727040⟩ : DyadicInterval 40),(⟨739843072447,739843091777⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201279154944,201279155008⟩ : DyadicInterval 40),(⟨-246571786688,-246571786624⟩ : DyadicInterval 40),(⟨739785479261,739785498591⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨56853764,85375330⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56852288,56852352⟩ : DyadicInterval 40),(⟨-56855296,-56855232⟩ : DyadicInterval 40),(⟨762123382116,762123401445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨85371968,85372032⟩ : DyadicInterval 40),(⟨-85378688,-85378624⟩ : DyadicInterval 40),(⟨762123380282,762123399612⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6656,-2880⟩ : DyadicInterval 40),(⟨762123385056,762123406208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨220679870492,220935324189⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201112434944,201112435008⟩ : DyadicInterval 40),(⟨-246321290368,-246321290304⟩ : DyadicInterval 40),(⟨739826232207,739826251537⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201325167040,201325167104⟩ : DyadicInterval 40),(⟨-246640936448,-246640936384⟩ : DyadicInterval 40),(⟨739774224310,739774243639⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45315769408,-45208855360⟩ : DyadicInterval 40),(⟨784727811296,784781287584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨201181384384,201371162368⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-246710068224,-246424875136⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1168_ok : ecellOkT e1168 = true := by decide +kernel
theorem e1168_pos {a z : ℝ} (ha1 : ((164481/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((411627/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1168 e1168_ok ha1 ha2 hz1 hz2 hz

-- box ['411627/2048000', '824103/4096000', '999/1000', '3997/4000']  interval_lower 526047841/1099511627776
noncomputable def e1169 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1320502190669,0,true,201371162304,201371162368⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨878521064883,0,false,-246710068224,-246710068160⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1320730092372,0,true,201560907520,201560907584⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨878293163180,0,false,-246995335232,-246995335168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1320281200106,0,true,201187139904,201187139968⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨878742055446,0,false,-246433522624,-246433522560⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1320564178524,0,true,201422775104,201422775168⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨878459077028,0,false,-246787651712,-246787651648⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099597001291,0,true,85370176,85370240⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099426254261,0,false,-85376832,-85376768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099625585142,0,true,113951424,113951488⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099397670410,0,false,-113963328,-113963264⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511615965,0,false,-11840,-11776⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621148,0,false,-6656,-6592⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1320391691397,0,true,201279151616,201279151680⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨878631564155,0,false,-246571781696,-246571781632⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1320647144900,0,true,201491851328,201491851392⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨878376110652,0,false,-246891500416,-246891500352⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1055036502912,0,false,-45399649024,-45399648960⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1055139197988,0,false,-45292630016,-45292629952⟩
    { al := (411627/2048000), au := (824103/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨220990562893,221218464596⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201371162304,201371162368⟩ : DyadicInterval 40),(⟨-246710068224,-246710068160⟩ : DyadicInterval 40),(⟨739762970135,739762989465⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201560907520,201560907584⟩ : DyadicInterval 40),(⟨-246995335232,-246995335168⟩ : DyadicInterval 40),(⟨739716507402,739716526732⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201187139904,201187139968⟩ : DyadicInterval 40),(⟨-246433522624,-246433522560⟩ : DyadicInterval 40),(⟨739807976839,739807996169⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201422775104,201422775168⟩ : DyadicInterval 40),(⟨-246787651712,-246787651648⟩ : DyadicInterval 40),(⟨739750337394,739750356724⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨85373515,113957366⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨85370176,85370240⟩ : DyadicInterval 40),(⟨-85376832,-85376768⟩ : DyadicInterval 40),(⟨762123380250,762123399580⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨113951424,113951488⟩ : DyadicInterval 40),(⟨-113963328,-113963264⟩ : DyadicInterval 40),(⟨762123377692,762123397022⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-11840,-6592⟩ : DyadicInterval 40),(⟨762123386912,762123408800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨220880063621,221135517124⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201279151616,201279151680⟩ : DyadicInterval 40),(⟨-246571781696,-246571781632⟩ : DyadicInterval 40),(⟨739785480078,739785499408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201491851328,201491851392⟩ : DyadicInterval 40),(⟨-246891500416,-246891500352⟩ : DyadicInterval 40),(⟨739733423752,739733443082⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45399649024,-45292629952⟩ : DyadicInterval 40),(⟨784769698592,784823227392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨201371162304,201560907584⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-246995335232,-246710068160⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1169_ok : ecellOkT e1169 = true := by decide +kernel
theorem e1169_pos {a z : ℝ} (ha1 : ((411627/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((824103/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1169 e1169_ok ha1 ha2 hz1 hz2 hz

-- box ['824103/4096000', '103119/512000', '999/1000', '3997/4000']  interval_lower 66361959/137438953472
noncomputable def e1170 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1320730092371,0,true,201560907520,201560907584⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨878293163181,0,false,-246995335232,-246995335168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1320957994075,0,true,201750619968,201750620032⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨878065261477,0,false,-247280676288,-247280676224⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1320508873906,0,true,201376727104,201376727168⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨878514381646,0,false,-246718432640,-246718432576⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1320791909301,0,true,201612369088,201612369152⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨878231346251,0,false,-247072724864,-247072724800⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099597094697,0,true,85463552,85463616⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099426160855,0,false,-85470272,-85470208⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099625709710,0,true,114075968,114076032⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099397545842,0,false,-114087872,-114087808⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511615939,0,false,-11840,-11776⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621133,0,false,-6656,-6592⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1320619479151,0,true,201468817856,201468817920⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨878403776401,0,false,-246856870208,-246856870144⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1320874961140,0,true,201681504576,201681504640⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨878148294412,0,false,-247176707520,-247176707456⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1054944818185,0,false,-45495202880,-45495202816⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1055047630576,0,false,-45388052352,-45388052288⟩
    { al := (824103/4096000), au := (103119/512000), zl := (999/1000), zu := (3997/4000),
      A := ⟨221218464595,221446366299⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201560907520,201560907584⟩ : DyadicInterval 40),(⟨-246995335232,-246995335168⟩ : DyadicInterval 40),(⟨739716507402,739716526732⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201750619968,201750620032⟩ : DyadicInterval 40),(⟨-247280676288,-247280676224⟩ : DyadicInterval 40),(⟨739669995463,739670014792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201376727104,201376727168⟩ : DyadicInterval 40),(⟨-246718432640,-246718432576⟩ : DyadicInterval 40),(⟨739761608284,739761627614⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201612369088,201612369152⟩ : DyadicInterval 40),(⟨-247072724864,-247072724800⟩ : DyadicInterval 40),(⟨739703896171,739703915500⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨85466921,114081934⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨85463552,85463616⟩ : DyadicInterval 40),(⟨-85470272,-85470208⟩ : DyadicInterval 40),(⟨762123380268,762123399597⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨114075968,114076032⟩ : DyadicInterval 40),(⟨-114087872,-114087808⟩ : DyadicInterval 40),(⟨762123377666,762123396996⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-11840,-6592⟩ : DyadicInterval 40),(⟨762123386912,762123408800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨221107851375,221363333364⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201468817856,201468817920⟩ : DyadicInterval 40),(⟨-246856870208,-246856870144⟩ : DyadicInterval 40),(⟨739739064442,739739083772⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201681504576,201681504640⟩ : DyadicInterval 40),(⟨-247176707520,-247176707456⟩ : DyadicInterval 40),(⟨739686947161,739686966491⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45495202880,-45388052288⟩ : DyadicInterval 40),(⟨784817409760,784871004320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨201560907520,201750620032⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-247280676288,-246995335168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1170_ok : ecellOkT e1170 = true := by decide +kernel
theorem e1170_pos {a z : ℝ} (ha1 : ((824103/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((103119/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1170 e1170_ok ha1 ha2 hz1 hz2 hz

-- box ['411627/2048000', '824103/4096000', '3997/4000', '1999/2000']  interval_lower 525157851/1099511627776
noncomputable def e1171 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1320502190669,0,true,201371162304,201371162368⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨878521064883,0,false,-246710068224,-246710068160⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1320730092372,0,true,201560907520,201560907584⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨878293163180,0,false,-246995335232,-246995335168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1320336447746,0,true,201233148416,201233148480⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨878686807806,0,false,-246502652480,-246502652416⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1320619483140,0,true,201468821184,201468821248⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨878403772412,0,false,-246856875200,-246856875136⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568543799,0,true,56914496,56914560⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454711753,0,false,-56917504,-56917440⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099597096517,0,true,85465408,85465472⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099426159035,0,false,-85472064,-85472000⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621132,0,false,-6656,-6592⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624830,0,false,-3008,-2944⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1320419314507,0,true,201302153600,201302153664⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨878603941045,0,false,-246606349568,-246606349504⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1320674796697,0,true,201514872768,201514872832⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨878348458855,0,false,-246926114240,-246926114176⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1055025379471,0,false,-45411241408,-45411241344⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1055128098922,0,false,-45304195904,-45304195840⟩
    { al := (411627/2048000), au := (824103/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨220990562893,221218464596⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201371162304,201371162368⟩ : DyadicInterval 40),(⟨-246710068224,-246710068160⟩ : DyadicInterval 40),(⟨739762970135,739762989465⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201560907520,201560907584⟩ : DyadicInterval 40),(⟨-246995335232,-246995335168⟩ : DyadicInterval 40),(⟨739716507402,739716526732⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201233148416,201233148480⟩ : DyadicInterval 40),(⟨-246502652480,-246502652416⟩ : DyadicInterval 40),(⟨739796729478,739796748808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201468821184,201468821248⟩ : DyadicInterval 40),(⟨-246856875200,-246856875136⟩ : DyadicInterval 40),(⟨739739063624,739739082954⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨56916023,85468741⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56914496,56914560⟩ : DyadicInterval 40),(⟨-56917504,-56917440⟩ : DyadicInterval 40),(⟨762123382109,762123401438⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨85465408,85465472⟩ : DyadicInterval 40),(⟨-85472064,-85472000⟩ : DyadicInterval 40),(⟨762123380235,762123399565⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6656,-2944⟩ : DyadicInterval 40),(⟨762123385088,762123406208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨220907686731,221163168921⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201302153600,201302153664⟩ : DyadicInterval 40),(⟨-246606349568,-246606349504⟩ : DyadicInterval 40),(⟨739779854021,739779873351⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201514872768,201514872832⟩ : DyadicInterval 40),(⟨-246926114240,-246926114176⟩ : DyadicInterval 40),(⟨739727785139,739727804468⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45411241408,-45304195840⟩ : DyadicInterval 40),(⟨784775481536,784829023584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨201371162304,201560907584⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-246995335232,-246710068160⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1171_ok : ecellOkT e1171 = true := by decide +kernel
theorem e1171_pos {a z : ℝ} (ha1 : ((411627/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((824103/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1171 e1171_ok ha1 ha2 hz1 hz2 hz

-- box ['824103/4096000', '103119/512000', '3997/4000', '1999/2000']  interval_lower 530002083/1099511627776
noncomputable def e1172 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1320730092371,0,true,201560907520,201560907584⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨878293163181,0,false,-246995335232,-246995335168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1320957994075,0,true,201750619968,201750620032⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨878065261477,0,false,-247280676288,-247280676224⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1320564178522,0,true,201422775104,201422775168⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨878459077030,0,false,-246787651712,-246787651648⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1320847270893,0,true,201658454656,201658454720⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨878175984659,0,false,-247142037632,-247142037568⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568606072,0,true,56976768,56976832⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454649480,0,false,-56979776,-56979712⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099597189944,0,true,85558784,85558848⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099426065608,0,false,-85565504,-85565440⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621117,0,false,-6720,-6656⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624824,0,false,-3008,-2944⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1320647130745,0,true,201491839552,201491839616⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨878376124807,0,false,-246891482688,-246891482624⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1320902641423,0,true,201704545728,201704545792⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨878120614129,0,false,-247211365952,-247211365888⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1054933671813,0,false,-45506820224,-45506820160⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1055036508607,0,false,-45399643072,-45399643008⟩
    { al := (824103/4096000), au := (103119/512000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨221218464595,221446366299⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201560907520,201560907584⟩ : DyadicInterval 40),(⟨-246995335232,-246995335168⟩ : DyadicInterval 40),(⟨739716507402,739716526732⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201750619968,201750620032⟩ : DyadicInterval 40),(⟨-247280676288,-247280676224⟩ : DyadicInterval 40),(⟨739669995463,739670014792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201422775104,201422775168⟩ : DyadicInterval 40),(⟨-246787651712,-246787651648⟩ : DyadicInterval 40),(⟨739750337395,739750356725⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201658454656,201658454720⟩ : DyadicInterval 40),(⟨-247142037632,-247142037568⟩ : DyadicInterval 40),(⟨739692598833,739692618162⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨56978296,85562168⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56976768,56976832⟩ : DyadicInterval 40),(⟨-56979776,-56979712⟩ : DyadicInterval 40),(⟨762123382103,762123401432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨85558784,85558848⟩ : DyadicInterval 40),(⟨-85565504,-85565440⟩ : DyadicInterval 40),(⟨762123380253,762123399582⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6720,-2944⟩ : DyadicInterval 40),(⟨762123385088,762123406240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨221135502969,221391013647⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201491839552,201491839616⟩ : DyadicInterval 40),(⟨-246891482688,-246891482624⟩ : DyadicInterval 40),(⟨739733426629,739733445959⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201704545728,201704545792⟩ : DyadicInterval 40),(⟨-247211365952,-247211365888⟩ : DyadicInterval 40),(⟨739681296763,739681316093⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45506820224,-45399643008⟩ : DyadicInterval 40),(⟨784823205120,784876812992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨201560907520,201750620032⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-247280676288,-246995335168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1172_ok : ecellOkT e1172 = true := by decide +kernel
theorem e1172_pos {a z : ℝ} (ha1 : ((824103/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((103119/512000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1172 e1172_ok ha1 ha2 hz1 hz2 hz

-- box ['205389/1024000', '164481/819200', '1999/2000', '3999/4000']  interval_lower 257321561/549755813888
noncomputable def e1173 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1320046387265,0,true,200991573696,200991573760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨878976868287,0,false,-246139756096,-246139756032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1320274288968,0,true,201181384384,201181384448⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨878748966584,0,false,-246424875200,-246424875136⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1319936119885,0,true,200899724352,200899724416⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨879087135667,0,false,-246001831360,-246001831296⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1320219098303,0,true,201135421184,201135421248⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨878804157249,0,false,-246355821504,-246355821440⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540023619,0,true,28395456,28395520⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483231933,0,false,-28396224,-28396160⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568482918,0,true,56853632,56853696⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454772634,0,false,-56856640,-56856576⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624836,0,false,-2944,-2880⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627043,0,false,-768,-704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1319991248376,0,true,200945645632,200945645696⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨879032007176,0,false,-246070785088,-246070785024⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1320246702269,0,true,201158410176,201158410240⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨878776553283,0,false,-246390358592,-246390358528⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1055197432381,0,false,-45231948352,-45231948288⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1055299941541,0,false,-45125139392,-45125139328⟩
    { al := (205389/1024000), au := (164481/819200), zl := (1999/2000), zu := (3999/4000),
      A := ⟨220534759489,220762661192⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200991573696,200991573760⟩ : DyadicInterval 40),(⟨-246139756096,-246139756032⟩ : DyadicInterval 40),(⟨739855747850,739855767179⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201181384384,201181384448⟩ : DyadicInterval 40),(⟨-246424875200,-246424875136⟩ : DyadicInterval 40),(⟨739809383608,739809402938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200899724352,200899724416⟩ : DyadicInterval 40),(⟨-246001831360,-246001831296⟩ : DyadicInterval 40),(⟨739878162986,739878182315⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201135421184,201135421248⟩ : DyadicInterval 40),(⟨-246355821504,-246355821440⟩ : DyadicInterval 40),(⟨739820616098,739820635428⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨28395843,56855142⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28395456,28395520⟩ : DyadicInterval 40),(⟨-28396224,-28396160⟩ : DyadicInterval 40),(⟨762123383202,762123402531⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56853632,56853696⟩ : DyadicInterval 40),(⟨-56856640,-56856576⟩ : DyadicInterval 40),(⟨762123382115,762123401445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2944,-704⟩ : DyadicInterval 40),(⟨762123383968,762123404352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨220479620600,220735074493⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200945645632,200945645696⟩ : DyadicInterval 40),(⟨-246070785088,-246070785024⟩ : DyadicInterval 40),(⟨739866957937,739866977267⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201158410176,201158410240⟩ : DyadicInterval 40),(⟨-246390358592,-246390358528⟩ : DyadicInterval 40),(⟨739814998472,739815017801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45231948352,-45125139328⟩ : DyadicInterval 40),(⟨784685953280,784739377056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨200991573696,201181384448⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-246424875200,-246139756032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1173_ok : ecellOkT e1173 = true := by decide +kernel
theorem e1173_pos {a z : ℝ} (ha1 : ((205389/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((164481/819200 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1173 e1173_ok ha1 ha2 hz1 hz2 hz

-- box ['164481/819200', '411627/2048000', '1999/2000', '3999/4000']  interval_lower 8116335/17179869184
noncomputable def e1174 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1320274288967,0,true,201181384384,201181384448⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨878748966585,0,false,-246424875200,-246424875136⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1320502190670,0,true,201371162304,201371162368⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨878521064882,0,false,-246710068224,-246710068160⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1320163907636,0,true,201089456000,201089456064⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨878859347916,0,false,-246286772096,-246286772032⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1320446943030,0,true,201325159616,201325159680⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨878576312522,0,false,-246640925312,-246640925248⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540054744,0,true,28426560,28426624⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483200808,0,false,-28427392,-28427328⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568545181,0,true,56915904,56915968⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454710371,0,false,-56918912,-56918848⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624829,0,false,-3008,-2944⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627042,0,false,-768,-704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1320219093093,0,true,201135416832,201135416896⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨878804162459,0,false,-246355814976,-246355814912⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1320474575479,0,true,201348168384,201348168448⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨878548680073,0,false,-246675507008,-246675506944⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1055105890697,0,false,-45327338560,-45327338496⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1055208517181,0,false,-45220398080,-45220398016⟩
    { al := (164481/819200), au := (411627/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨220762661191,220990562894⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201181384384,201181384448⟩ : DyadicInterval 40),(⟨-246424875200,-246424875136⟩ : DyadicInterval 40),(⟨739809383609,739809402938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201371162304,201371162368⟩ : DyadicInterval 40),(⟨-246710068224,-246710068160⟩ : DyadicInterval 40),(⟨739762970135,739762989464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201089456000,201089456064⟩ : DyadicInterval 40),(⟨-246286772096,-246286772032⟩ : DyadicInterval 40),(⟨739831845720,739831865050⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201325159616,201325159680⟩ : DyadicInterval 40),(⟨-246640925312,-246640925248⟩ : DyadicInterval 40),(⟨739774226139,739774245468⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨28426968,56917405⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28426560,28426624⟩ : DyadicInterval 40),(⟨-28427392,-28427328⟩ : DyadicInterval 40),(⟨762123383233,762123402562⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56915904,56915968⟩ : DyadicInterval 40),(⟨-56918912,-56918848⟩ : DyadicInterval 40),(⟨762123382109,762123401438⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3008,-704⟩ : DyadicInterval 40),(⟨762123383968,762123404384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨220707465317,220962947703⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201135416832,201135416896⟩ : DyadicInterval 40),(⟨-246355814976,-246355814912⟩ : DyadicInterval 40),(⟨739820617163,739820636492⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201348168384,201348168448⟩ : DyadicInterval 40),(⟨-246675507008,-246675506944⟩ : DyadicInterval 40),(⟨739768596735,739768616064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45327338560,-45220398016⟩ : DyadicInterval 40),(⟨784733582624,784787072160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨201181384384,201371162368⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-246710068224,-246424875136⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1174_ok : ecellOkT e1174 = true := by decide +kernel
theorem e1174_pos {a z : ℝ} (ha1 : ((164481/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((411627/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1174 e1174_ok ha1 ha2 hz1 hz2 hz

-- box ['205389/1024000', '164481/819200', '3999/4000', '1']  interval_lower 128439609/274877906944
noncomputable def e1175 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1320046387265,0,true,200991573696,200991573760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨878976868287,0,false,-246139756096,-246139756032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1320274288968,0,true,201181384384,201181384448⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨878748966584,0,false,-246424875200,-246424875136⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1319991253575,0,true,200945649984,200945650048⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨879032001977,0,false,-246070791552,-246070791488⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540055692,0,true,28427520,28427584⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483199860,0,false,-28428288,-28428224⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627040,0,false,-768,-704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1320018814920,0,true,200968607488,200968607552⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨879004440632,0,false,-246105266432,-246105266368⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1320274297499,0,true,201181391488,201181391552⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨878748958053,0,false,-246424885888,-246424885824⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1055186351797,0,false,-45243494336,-45243494272⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1055288885284,0,false,-45136658944,-45136658880⟩
    { al := (205389/1024000), au := (164481/819200), zl := (3999/4000), zu := 1,
      A := ⟨220534759489,220762661192⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200991573696,200991573760⟩ : DyadicInterval 40),(⟨-246139756096,-246139756032⟩ : DyadicInterval 40),(⟨739855747850,739855767179⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201181384384,201181384448⟩ : DyadicInterval 40),(⟨-246424875200,-246424875136⟩ : DyadicInterval 40),(⟨739809383608,739809402938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200945649984,200945650048⟩ : DyadicInterval 40),(⟨-246070791552,-246070791488⟩ : DyadicInterval 40),(⟨739866956852,739866976182⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201181384384,201181384448⟩ : DyadicInterval 40),(⟨-246424875200,-246424875136⟩ : DyadicInterval 40),(⟨739809383608,739809402938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,28427916⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28427520,28427584⟩ : DyadicInterval 40),(⟨-28428288,-28428224⟩ : DyadicInterval 40),(⟨762123383200,762123402530⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-768,0⟩ : DyadicInterval 40),(⟨762123383616,762123403264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨220507187144,220762669723⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200968607488,200968607552⟩ : DyadicInterval 40),(⟨-246105266432,-246105266368⟩ : DyadicInterval 40),(⟨739861353847,739861373176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201181391488,201181391552⟩ : DyadicInterval 40),(⟨-246424885888,-246424885824⟩ : DyadicInterval 40),(⟨739809381878,739809401207⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45243494336,-45136658880⟩ : DyadicInterval 40),(⟨784691713056,784745150048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨200991573696,201181384448⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-246424875200,-246139756032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1175_ok : ecellOkT e1175 = true := by decide +kernel
theorem e1175_pos {a z : ℝ} (ha1 : ((205389/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((164481/819200 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1175 e1175_ok ha1 ha2 hz1 hz2 hz

-- box ['164481/819200', '411627/2048000', '3999/4000', '1']  interval_lower 259278799/549755813888
noncomputable def e1176 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1320274288967,0,true,201181384384,201181384448⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨878748966585,0,false,-246424875200,-246424875136⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1320502190670,0,true,201371162304,201371162368⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨878521064882,0,false,-246710068224,-246710068160⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1320219098301,0,true,201135421184,201135421248⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨878804157251,0,false,-246355821504,-246355821440⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540086824,0,true,28458624,28458688⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483168728,0,false,-28459456,-28459392⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627039,0,false,-768,-704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1320246688123,0,true,201158398400,201158398464⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨878776567429,0,false,-246390340864,-246390340800⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1320502199195,0,true,201371169408,201371169472⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨878521056357,0,false,-246710078848,-246710078784⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1055094787223,0,false,-45338909440,-45338909376⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1055197438062,0,false,-45231942464,-45231942400⟩
    { al := (164481/819200), au := (411627/2048000), zl := (3999/4000), zu := 1,
      A := ⟨220762661191,220990562894⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201181384384,201181384448⟩ : DyadicInterval 40),(⟨-246424875200,-246424875136⟩ : DyadicInterval 40),(⟨739809383609,739809402938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201371162304,201371162368⟩ : DyadicInterval 40),(⟨-246710068224,-246710068160⟩ : DyadicInterval 40),(⟨739762970135,739762989464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201135421184,201135421248⟩ : DyadicInterval 40),(⟨-246355821504,-246355821440⟩ : DyadicInterval 40),(⟨739820616099,739820635428⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201371162304,201371162368⟩ : DyadicInterval 40),(⟨-246710068224,-246710068160⟩ : DyadicInterval 40),(⟨739762970135,739762989464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,28459048⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28458624,28458688⟩ : DyadicInterval 40),(⟨-28459456,-28459392⟩ : DyadicInterval 40),(⟨762123383231,762123402560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-768,0⟩ : DyadicInterval 40),(⟨762123383616,762123403264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨220735060347,220990571419⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201158398400,201158398464⟩ : DyadicInterval 40),(⟨-246390340864,-246390340800⟩ : DyadicInterval 40),(⟨739815001337,739815020666⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201371169408,201371169472⟩ : DyadicInterval 40),(⟨-246710078848,-246710078784⟩ : DyadicInterval 40),(⟨739762968376,739762987705⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45338909440,-45231942400⟩ : DyadicInterval 40),(⟨784739354816,784792857600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨201181384384,201371162368⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-246710068224,-246424875136⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1176_ok : ecellOkT e1176 = true := by decide +kernel
theorem e1176_pos {a z : ℝ} (ha1 : ((164481/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((411627/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1176 e1176_ok ha1 ha2 hz1 hz2 hz

-- box ['411627/2048000', '824103/4096000', '1999/2000', '3999/4000']  interval_lower 262133519/549755813888
noncomputable def e1177 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1320502190669,0,true,201371162304,201371162368⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨878521064883,0,false,-246710068224,-246710068160⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1320730092372,0,true,201560907520,201560907584⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨878293163180,0,false,-246995335232,-246995335168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1320391695387,0,true,201279154944,201279155008⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨878631560165,0,false,-246571786688,-246571786624⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1320674787757,0,true,201514865280,201514865344⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨878348467795,0,false,-246926103040,-246926102976⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540085875,0,true,28457728,28457792⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483169677,0,false,-28458496,-28458432⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568607457,0,true,56978176,56978240⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454648095,0,false,-56981184,-56981120⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624823,0,false,-3008,-2944⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627040,0,false,-768,-704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1320446937815,0,true,201325155264,201325155328⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨878576317737,0,false,-246640918784,-246640918720⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1320702448694,0,true,201537893824,201537893888⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨878320806858,0,false,-246960729408,-246960729344⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1055014254558,0,false,-45422835520,-45422835456⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1055116998389,0,false,-45315763456,-45315763392⟩
    { al := (411627/2048000), au := (824103/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨220990562893,221218464596⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201371162304,201371162368⟩ : DyadicInterval 40),(⟨-246710068224,-246710068160⟩ : DyadicInterval 40),(⟨739762970135,739762989465⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201560907520,201560907584⟩ : DyadicInterval 40),(⟨-246995335232,-246995335168⟩ : DyadicInterval 40),(⟨739716507402,739716526732⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201279154944,201279155008⟩ : DyadicInterval 40),(⟨-246571786688,-246571786624⟩ : DyadicInterval 40),(⟨739785479262,739785498592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201514865280,201514865344⟩ : DyadicInterval 40),(⟨-246926103040,-246926102976⟩ : DyadicInterval 40),(⟨739727786986,739727806315⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨28458099,56979681⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28457728,28457792⟩ : DyadicInterval 40),(⟨-28458496,-28458432⟩ : DyadicInterval 40),(⟨762123383199,762123402528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56978176,56978240⟩ : DyadicInterval 40),(⟨-56981184,-56981120⟩ : DyadicInterval 40),(⟨762123382103,762123401432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3008,-704⟩ : DyadicInterval 40),(⟨762123383968,762123404384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨220935310039,221190820918⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201325155264,201325155328⟩ : DyadicInterval 40),(⟨-246640918784,-246640918720⟩ : DyadicInterval 40),(⟨739774227206,739774246535⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201537893824,201537893888⟩ : DyadicInterval 40),(⟨-246960729408,-246960729344⟩ : DyadicInterval 40),(⟨739722145803,739722165132⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45422835520,-45315763392⟩ : DyadicInterval 40),(⟨784781265312,784834820640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨201371162304,201560907584⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-246995335232,-246710068160⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1177_ok : ecellOkT e1177 = true := by decide +kernel
theorem e1177_pos {a z : ℝ} (ha1 : ((411627/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((824103/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1177 e1177_ok ha1 ha2 hz1 hz2 hz

-- box ['824103/4096000', '103119/512000', '1999/2000', '3999/4000']  interval_lower 264554021/549755813888
noncomputable def e1178 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1320730092371,0,true,201560907520,201560907584⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨878293163181,0,false,-246995335232,-246995335168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1320957994075,0,true,201750619968,201750620032⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨878065261477,0,false,-247280676288,-247280676224⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1320619483138,0,true,201468821184,201468821248⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨878403772414,0,false,-246856875200,-246856875136⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1320902632484,0,true,201704538304,201704538368⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨878120623068,0,false,-247211354752,-247211354688⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540117012,0,true,28488832,28488896⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483138540,0,false,-28489664,-28489600⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568669743,0,true,57040448,57040512⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454585809,0,false,-57043456,-57043392⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624816,0,false,-3008,-2944⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627038,0,false,-768,-704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1320674782542,0,true,201514860992,201514861056⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨878348473010,0,false,-246926096512,-246926096448⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1320930321914,0,true,201727586560,201727586624⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨878092933638,0,false,-247246025792,-247246025728⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1054922523963,0,false,-45518439168,-45518439104⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1055025385166,0,false,-45411235520,-45411235456⟩
    { al := (824103/4096000), au := (103119/512000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨221218464595,221446366299⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201560907520,201560907584⟩ : DyadicInterval 40),(⟨-246995335232,-246995335168⟩ : DyadicInterval 40),(⟨739716507402,739716526732⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201750619968,201750620032⟩ : DyadicInterval 40),(⟨-247280676288,-247280676224⟩ : DyadicInterval 40),(⟨739669995463,739670014792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201468821184,201468821248⟩ : DyadicInterval 40),(⟨-246856875200,-246856875136⟩ : DyadicInterval 40),(⟨739739063625,739739082954⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201704538304,201704538368⟩ : DyadicInterval 40),(⟨-247211354752,-247211354688⟩ : DyadicInterval 40),(⟨739681298575,739681317905⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨28489236,57041967⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28488832,28488896⟩ : DyadicInterval 40),(⟨-28489664,-28489600⟩ : DyadicInterval 40),(⟨762123383229,762123402558⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57040448,57040512⟩ : DyadicInterval 40),(⟨-57043456,-57043392⟩ : DyadicInterval 40),(⟨762123382096,762123401425⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3008,-704⟩ : DyadicInterval 40),(⟨762123383968,762123404384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨221163154766,221418694138⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201514860992,201514861056⟩ : DyadicInterval 40),(⟨-246926096512,-246926096448⟩ : DyadicInterval 40),(⟨739727788017,739727807346⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201727586560,201727586624⟩ : DyadicInterval 40),(⟨-247246025792,-247246025728⟩ : DyadicInterval 40),(⟨739675645624,739675664954⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45518439168,-45411235456⟩ : DyadicInterval 40),(⟨784829001344,784882622464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨201560907520,201750620032⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-247280676288,-246995335168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1178_ok : ecellOkT e1178 = true := by decide +kernel
theorem e1178_pos {a z : ℝ} (ha1 : ((824103/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((103119/512000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1178 e1178_ok ha1 ha2 hz1 hz2 hz

-- box ['411627/2048000', '824103/4096000', '3999/4000', '1']  interval_lower 523375689/1099511627776
noncomputable def e1179 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1320502190669,0,true,201371162304,201371162368⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨878521064883,0,false,-246710068224,-246710068160⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1320730092372,0,true,201560907520,201560907584⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨878293163180,0,false,-246995335232,-246995335168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1320446943028,0,true,201325159616,201325159680⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨878576312524,0,false,-246640925248,-246640925184⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540117963,0,true,28489792,28489856⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483137589,0,false,-28490560,-28490496⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627037,0,false,-768,-704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1320474561332,0,true,201348156608,201348156672⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨878548694220,0,false,-246675489280,-246675489216⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1320730100901,0,true,201560914624,201560914688⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨878293154651,0,false,-246995345920,-246995345856⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1055003128169,0,false,-45434431232,-45434431168⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1055105896384,0,false,-45327332672,-45327332608⟩
    { al := (411627/2048000), au := (824103/4096000), zl := (3999/4000), zu := 1,
      A := ⟨220990562893,221218464596⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201371162304,201371162368⟩ : DyadicInterval 40),(⟨-246710068224,-246710068160⟩ : DyadicInterval 40),(⟨739762970135,739762989465⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201560907520,201560907584⟩ : DyadicInterval 40),(⟨-246995335232,-246995335168⟩ : DyadicInterval 40),(⟨739716507402,739716526732⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201325159616,201325159680⟩ : DyadicInterval 40),(⟨-246640925248,-246640925184⟩ : DyadicInterval 40),(⟨739774226114,739774245443⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201560907520,201560907584⟩ : DyadicInterval 40),(⟨-246995335232,-246995335168⟩ : DyadicInterval 40),(⟨739716507402,739716526732⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,28490187⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28489792,28489856⟩ : DyadicInterval 40),(⟨-28490560,-28490496⟩ : DyadicInterval 40),(⟨762123383197,762123402526⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-768,0⟩ : DyadicInterval 40),(⟨762123383616,762123403264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨220962933556,221218473125⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201348156608,201348156672⟩ : DyadicInterval 40),(⟨-246675489280,-246675489216⟩ : DyadicInterval 40),(⟨739768599606,739768618935⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201560914624,201560914688⟩ : DyadicInterval 40),(⟨-246995345920,-246995345856⟩ : DyadicInterval 40),(⟨739716505665,739716524994⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45434431232,-45327332608⟩ : DyadicInterval 40),(⟨784787049920,784840618496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨201371162304,201560907584⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-246995335232,-246710068160⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1179_ok : ecellOkT e1179 = true := by decide +kernel
theorem e1179_pos {a z : ℝ} (ha1 : ((411627/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((824103/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1179 e1179_ok ha1 ha2 hz1 hz2 hz

-- box ['824103/4096000', '103119/512000', '3999/4000', '1']  interval_lower 515833/1073741824
noncomputable def e1180 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1320730092371,0,true,201560907520,201560907584⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨878293163181,0,false,-246995335232,-246995335168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1320957994075,0,true,201750619968,201750620032⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨878065261477,0,false,-247280676288,-247280676224⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1320674787754,0,true,201514865280,201514865344⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨878348467798,0,false,-246926103040,-246926102976⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540149106,0,true,28520960,28521024⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483106446,0,false,-28521728,-28521664⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627036,0,false,-768,-704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1320702434538,0,true,201537882048,201537882112⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨878320821014,0,false,-246960711680,-246960711616⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1320958002601,0,true,201750627072,201750627136⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨878065252951,0,false,-247280686912,-247280686848⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1054911374641,0,false,-45530059840,-45530059776⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1055014260254,0,false,-45422829568,-45422829504⟩
    { al := (824103/4096000), au := (103119/512000), zl := (3999/4000), zu := 1,
      A := ⟨221218464595,221446366299⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201560907520,201560907584⟩ : DyadicInterval 40),(⟨-246995335232,-246995335168⟩ : DyadicInterval 40),(⟨739716507402,739716526732⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201750619968,201750620032⟩ : DyadicInterval 40),(⟨-247280676288,-247280676224⟩ : DyadicInterval 40),(⟨739669995463,739670014792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201514865280,201514865344⟩ : DyadicInterval 40),(⟨-246926103040,-246926102976⟩ : DyadicInterval 40),(⟨739727786986,739727806316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201750619968,201750620032⟩ : DyadicInterval 40),(⟨-247280676288,-247280676224⟩ : DyadicInterval 40),(⟨739669995463,739670014792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,28521330⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28520960,28521024⟩ : DyadicInterval 40),(⟨-28521728,-28521664⟩ : DyadicInterval 40),(⟨762123383196,762123402525⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-768,0⟩ : DyadicInterval 40),(⟨762123383616,762123403264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨221190806762,221446374825⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201537882048,201537882112⟩ : DyadicInterval 40),(⟨-246960711680,-246960711616⟩ : DyadicInterval 40),(⟨739722148682,739722168011⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201750627072,201750627136⟩ : DyadicInterval 40),(⟨-247280686912,-247280686848⟩ : DyadicInterval 40),(⟨739669993696,739670013026⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45530059840,-45422829504⟩ : DyadicInterval 40),(⟨784834798368,784888432800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨201560907520,201750620032⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-247280676288,-246995335168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1180_ok : ecellOkT e1180 = true := by decide +kernel
theorem e1180_pos {a z : ℝ} (ha1 : ((824103/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((103119/512000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1180 e1180_ok ha1 ha2 hz1 hz2 hz

-- box ['103119/512000', '825801/4096000', '999/1000', '3997/4000']  interval_lower 267881239/549755813888
noncomputable def e1181 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1320957994074,0,true,201750619968,201750620032⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨878065261478,0,false,-247280676288,-247280676224⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1321185895777,0,true,201940299712,201940299776⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨877837359775,0,false,-247566091392,-247566091328⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1320736547707,0,true,201566281600,201566281664⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨878286707845,0,false,-247003416512,-247003416448⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1321019640077,0,true,201801930432,201801930496⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨878003615475,0,false,-247357872000,-247357871936⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099597188120,0,true,85556992,85557056⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099426067432,0,false,-85563712,-85563648⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099625834301,0,true,114200576,114200640⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099397421251,0,false,-114212480,-114212416⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511615913,0,false,-11904,-11840⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621118,0,false,-6720,-6656⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1320847266901,0,true,201658451328,201658451392⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨878175988651,0,false,-247142032640,-247142032576⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1321102777383,0,true,201871125120,201871125184⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨877920478169,0,false,-247461988608,-247461988544⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1054853039050,0,false,-45590863424,-45590863360⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1054955968783,0,false,-45483581312,-45483581248⟩
    { al := (103119/512000), au := (825801/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨221446366298,221674268001⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201750619968,201750620032⟩ : DyadicInterval 40),(⟨-247280676288,-247280676224⟩ : DyadicInterval 40),(⟨739669995463,739670014792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201940299712,201940299776⟩ : DyadicInterval 40),(⟨-247566091392,-247566091328⟩ : DyadicInterval 40),(⟨739623434264,739623453594⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201566281600,201566281664⟩ : DyadicInterval 40),(⟨-247003416512,-247003416448⟩ : DyadicInterval 40),(⟨739715190616,739715209946⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201801930432,201801930496⟩ : DyadicInterval 40),(⟨-247357872000,-247357871936⟩ : DyadicInterval 40),(⟨739657405782,739657425111⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨85560344,114206525⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨85556992,85557056⟩ : DyadicInterval 40),(⟨-85563712,-85563648⟩ : DyadicInterval 40),(⟨762123380253,762123399583⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨114200576,114200640⟩ : DyadicInterval 40),(⟨-114212480,-114212416⟩ : DyadicInterval 40),(⟨762123377640,762123396970⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-11904,-6656⟩ : DyadicInterval 40),(⟨762123386944,762123408832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨221335639125,221591149607⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201658451328,201658451392⟩ : DyadicInterval 40),(⟨-247142032640,-247142032576⟩ : DyadicInterval 40),(⟨739692599653,739692618982⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201871125120,201871125184⟩ : DyadicInterval 40),(⟨-247461988608,-247461988544⟩ : DyadicInterval 40),(⟨739640421365,739640440694⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45590863424,-45483581248⟩ : DyadicInterval 40),(⟨784865174240,784918834592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨201750619968,201940299776⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-247566091392,-247280676224⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1181_ok : ecellOkT e1181 = true := by decide +kernel
theorem e1181_pos {a z : ℝ} (ha1 : ((103119/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((825801/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1181 e1181_ok ha1 ha2 hz1 hz2 hz

-- box ['825801/4096000', '16533/81920', '999/1000', '3997/4000']  interval_lower 135162141/274877906944
noncomputable def e1182 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1321185895776,0,true,201940299712,201940299776⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨877837359776,0,false,-247566091392,-247566091328⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1321413797479,0,true,202129946752,202129946816⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨877609458073,0,false,-247851580608,-247851580544⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1320964221507,0,true,201755803456,201755803520⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨878059034045,0,false,-247288474240,-247288474176⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1321247370852,0,true,201991459072,201991459136⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨877775884700,0,false,-247643092992,-247643092928⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099597281561,0,true,85650432,85650496⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099425973991,0,false,-85657152,-85657088⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099625958914,0,true,114325184,114325248⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099397296638,0,false,-114337088,-114337024⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511615887,0,false,-11904,-11840⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621104,0,false,-6720,-6656⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1321075054656,0,true,201848052096,201848052160⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨877948200896,0,false,-247427269056,-247427268992⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1321330593631,0,true,202060712960,202060713024⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨877692661921,0,false,-247747343744,-247747343680⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1054761165507,0,false,-45686630720,-45686630656⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1054864212605,0,false,-45579216896,-45579216832⟩
    { al := (825801/4096000), au := (16533/81920), zl := (999/1000), zu := (3997/4000),
      A := ⟨221674268000,221902169703⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201940299712,201940299776⟩ : DyadicInterval 40),(⟨-247566091392,-247566091328⟩ : DyadicInterval 40),(⟨739623434264,739623453594⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202129946752,202129946816⟩ : DyadicInterval 40),(⟨-247851580608,-247851580544⟩ : DyadicInterval 40),(⟨739576823820,739576843149⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201755803456,201755803520⟩ : DyadicInterval 40),(⟨-247288474240,-247288474176⟩ : DyadicInterval 40),(⟨739668723783,739668743113⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201991459072,201991459136⟩ : DyadicInterval 40),(⟨-247643092992,-247643092928⟩ : DyadicInterval 40),(⟨739610866202,739610885531⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨85653785,114331138⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨85650432,85650496⟩ : DyadicInterval 40),(⟨-85657152,-85657088⟩ : DyadicInterval 40),(⟨762123380239,762123399568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨114325184,114325248⟩ : DyadicInterval 40),(⟨-114337088,-114337024⟩ : DyadicInterval 40),(⟨762123377615,762123396944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-11904,-6656⟩ : DyadicInterval 40),(⟨762123386944,762123408832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨221563426880,221818965855⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201848052096,201848052160⟩ : DyadicInterval 40),(⟨-247427269056,-247427268992⟩ : DyadicInterval 40),(⟨739646085683,739646105012⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202060712960,202060713024⟩ : DyadicInterval 40),(⟨-247747343744,-247747343680⟩ : DyadicInterval 40),(⟨739593846373,739593865703⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45686630720,-45579216832⟩ : DyadicInterval 40),(⟨784912992032,784966718240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨201940299712,202129946816⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-247851580608,-247566091328⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1182_ok : ecellOkT e1182 = true := by decide +kernel
theorem e1182_pos {a z : ℝ} (ha1 : ((825801/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((16533/81920 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1182 e1182_ok ha1 ha2 hz1 hz2 hz

-- box ['103119/512000', '825801/4096000', '3997/4000', '1999/2000']  interval_lower 133716435/274877906944
noncomputable def e1183 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1320957994074,0,true,201750619968,201750620032⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨878065261478,0,false,-247280676288,-247280676224⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1321185895777,0,true,201940299712,201940299776⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨877837359775,0,false,-247566091392,-247566091328⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1320791909299,0,true,201612369088,201612369152⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨878231346253,0,false,-247072724864,-247072724800⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1321075058644,0,true,201848055424,201848055488⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨877948196908,0,false,-247427274048,-247427273984⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568668355,0,true,57039040,57039104⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454587197,0,false,-57042112,-57042048⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099597283389,0,true,85652224,85652288⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099425972163,0,false,-85659008,-85658944⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621103,0,false,-6720,-6656⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624817,0,false,-3008,-2944⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1320874946980,0,true,201681492800,201681492864⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨878148308572,0,false,-247176689792,-247176689728⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1321130486152,0,true,201894185984,201894186048⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨877892769400,0,false,-247496691712,-247496691648⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1054841869724,0,false,-45602505728,-45602505664⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1054944823887,0,false,-45495196928,-45495196864⟩
    { al := (103119/512000), au := (825801/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨221446366298,221674268001⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201750619968,201750620032⟩ : DyadicInterval 40),(⟨-247280676288,-247280676224⟩ : DyadicInterval 40),(⟨739669995463,739670014792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201940299712,201940299776⟩ : DyadicInterval 40),(⟨-247566091392,-247566091328⟩ : DyadicInterval 40),(⟨739623434264,739623453594⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201612369088,201612369152⟩ : DyadicInterval 40),(⟨-247072724864,-247072724800⟩ : DyadicInterval 40),(⟨739703896171,739703915501⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201848055424,201848055488⟩ : DyadicInterval 40),(⟨-247427274048,-247427273984⟩ : DyadicInterval 40),(⟨739646084862,739646104191⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57040579,85655613⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57039040,57039104⟩ : DyadicInterval 40),(⟨-57042112,-57042048⟩ : DyadicInterval 40),(⟨762123382128,762123401457⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨85652224,85652288⟩ : DyadicInterval 40),(⟨-85659008,-85658944⟩ : DyadicInterval 40),(⟨762123380270,762123399600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6720,-2944⟩ : DyadicInterval 40),(⟨762123385088,762123406240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨221363319204,221618858376⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201681492800,201681492864⟩ : DyadicInterval 40),(⟨-247176689792,-247176689728⟩ : DyadicInterval 40),(⟨739686950046,739686969375⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201894185984,201894186048⟩ : DyadicInterval 40),(⟨-247496691712,-247496691648⟩ : DyadicInterval 40),(⟨739634759181,739634778510⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45602505728,-45495196864⟩ : DyadicInterval 40),(⟨784870982048,784924655744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨201750619968,201940299776⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-247566091392,-247280676224⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1183_ok : ecellOkT e1183 = true := by decide +kernel
theorem e1183_pos {a z : ℝ} (ha1 : ((103119/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((825801/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1183 e1183_ok ha1 ha2 hz1 hz2 hz

-- box ['825801/4096000', '16533/81920', '3997/4000', '1999/2000']  interval_lower 539748567/1099511627776
noncomputable def e1184 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1321185895776,0,true,201940299712,201940299776⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨877837359776,0,false,-247566091392,-247566091328⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1321413797479,0,true,202129946752,202129946816⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨877609458073,0,false,-247851580608,-247851580544⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1321019640074,0,true,201801930432,201801930496⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨878003615478,0,false,-247357872000,-247357871936⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1321302846395,0,true,202037623552,202037623616⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨877720409157,0,false,-247712584512,-247712584448⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568730650,0,true,57101376,57101440⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454524902,0,false,-57104384,-57104320⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099597376852,0,true,85745728,85745792⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099425878700,0,false,-85752448,-85752384⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621088,0,false,-6720,-6656⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624811,0,false,-3008,-2944⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1321102763218,0,true,201871113344,201871113408⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨877920492334,0,false,-247461970816,-247461970752⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1321358330882,0,true,202083793536,202083793600⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨877664924670,0,false,-247782091520,-247782091456⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1054749973205,0,false,-45698297984,-45698297920⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1054853044760,0,false,-45590857472,-45590857408⟩
    { al := (825801/4096000), au := (16533/81920), zl := (3997/4000), zu := (1999/2000),
      A := ⟨221674268000,221902169703⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201940299712,201940299776⟩ : DyadicInterval 40),(⟨-247566091392,-247566091328⟩ : DyadicInterval 40),(⟨739623434264,739623453594⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202129946752,202129946816⟩ : DyadicInterval 40),(⟨-247851580608,-247851580544⟩ : DyadicInterval 40),(⟨739576823820,739576843149⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201801930432,201801930496⟩ : DyadicInterval 40),(⟨-247357872000,-247357871936⟩ : DyadicInterval 40),(⟨739657405783,739657425112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202037623552,202037623616⟩ : DyadicInterval 40),(⟨-247712584512,-247712584448⟩ : DyadicInterval 40),(⟨739599521686,739599541015⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57102874,85749076⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57101376,57101440⟩ : DyadicInterval 40),(⟨-57104384,-57104320⟩ : DyadicInterval 40),(⟨762123382090,762123401419⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨85745728,85745792⟩ : DyadicInterval 40),(⟨-85752448,-85752384⟩ : DyadicInterval 40),(⟨762123380224,762123399553⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6720,-2944⟩ : DyadicInterval 40),(⟨762123385088,762123406240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨221591135442,221846703106⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201871113344,201871113408⟩ : DyadicInterval 40),(⟨-247461970816,-247461970752⟩ : DyadicInterval 40),(⟨739640424231,739640443560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202083793536,202083793600⟩ : DyadicInterval 40),(⟨-247782091520,-247782091456⟩ : DyadicInterval 40),(⟨739588172379,739588191708⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45698297984,-45590857408⟩ : DyadicInterval 40),(⟨784918812320,784972551872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨201940299712,202129946816⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-247851580608,-247566091328⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1184_ok : ecellOkT e1184 = true := by decide +kernel
theorem e1184_pos {a z : ℝ} (ha1 : ((825801/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((16533/81920 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1184 e1184_ok ha1 ha2 hz1 hz2 hz

-- box ['16533/81920', '827499/4096000', '999/1000', '3997/4000']  interval_lower 272777141/549755813888
noncomputable def e1185 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1321413797478,0,true,202129946752,202129946816⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨877609458074,0,false,-247851580608,-247851580544⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1321641699181,0,true,202319561024,202319561088⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨877381556371,0,false,-248137143936,-248137143872⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1321191895308,0,true,201945292608,201945292672⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨877831360244,0,false,-247573605952,-247573605888⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1321475101628,0,true,202180955008,202180955072⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨877548153924,0,false,-247928388096,-247928388032⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099597375020,0,true,85743872,85743936⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099425880532,0,false,-85750592,-85750528⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099626083552,0,true,114449792,114449856⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099397172000,0,false,-114461760,-114461696⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511615861,0,false,-11968,-11904⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621089,0,false,-6720,-6656⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1321302842408,0,true,202037620224,202037620288⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨877720413144,0,false,-247712579520,-247712579456⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1321558409866,0,true,202250268096,202250268160⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨877464845686,0,false,-248032772928,-248032772864⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1054669197563,0,false,-45782504832,-45782504768⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1054772362047,0,false,-45674959232,-45674959168⟩
    { al := (16533/81920), au := (827499/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨221902169702,222130071405⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202129946752,202129946816⟩ : DyadicInterval 40),(⟨-247851580608,-247851580544⟩ : DyadicInterval 40),(⟨739576823820,739576843150⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202319561024,202319561088⟩ : DyadicInterval 40),(⟨-248137143936,-248137143872⟩ : DyadicInterval 40),(⟨739530164155,739530183485⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201945292608,201945292672⟩ : DyadicInterval 40),(⟨-247573605952,-247573605888⟩ : DyadicInterval 40),(⟨739622207863,739622227192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202180955008,202180955072⟩ : DyadicInterval 40),(⟨-247928388096,-247928388032⟩ : DyadicInterval 40),(⟨739564277520,739564296849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨85747244,114455776⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨85743872,85743936⟩ : DyadicInterval 40),(⟨-85750592,-85750528⟩ : DyadicInterval 40),(⟨762123380224,762123399554⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨114449792,114449856⟩ : DyadicInterval 40),(⟨-114461760,-114461696⟩ : DyadicInterval 40),(⟨762123377621,762123396950⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-11968,-6656⟩ : DyadicInterval 40),(⟨762123386944,762123408864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨221791214632,222046782090⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202037620224,202037620288⟩ : DyadicInterval 40),(⟨-247712579520,-247712579456⟩ : DyadicInterval 40),(⟨739599522508,739599541838⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202250268096,202250268160⟩ : DyadicInterval 40),(⟨-248032772928,-248032772864⟩ : DyadicInterval 40),(⟨739547222179,739547241509⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45782504832,-45674959168⟩ : DyadicInterval 40),(⟨784960863200,785014655296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨202129946752,202319561088⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-248137143936,-247851580544⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1185_ok : ecellOkT e1185 = true := by decide +kernel
theorem e1185_pos {a z : ℝ} (ha1 : ((16533/81920 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((827499/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1185 e1185_ok ha1 ha2 hz1 hz2 hz

-- box ['827499/4096000', '207087/1024000', '999/1000', '3997/4000']  interval_lower 550479487/1099511627776
noncomputable def e1186 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1321641699180,0,true,202319561024,202319561088⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨877381556372,0,false,-248137143936,-248137143872⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1321869600883,0,true,202509142656,202509142720⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨877153654669,0,false,-248422781504,-248422781440⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1321419569108,0,true,202134749120,202134749184⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨877603686444,0,false,-247858811584,-247858811520⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1321702832404,0,true,202370418368,202370418432⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨877320423148,0,false,-248213757184,-248213757120⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099597468496,0,true,85837312,85837376⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099425787056,0,false,-85844096,-85844032⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099626208212,0,true,114574464,114574528⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099397047340,0,false,-114586432,-114586368⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511615835,0,false,-11968,-11904⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621075,0,false,-6720,-6656⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1321530630157,0,true,202227155648,202227155712⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨877492625395,0,false,-247997963968,-247997963904⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1321786226113,0,true,202439790592,202439790656⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨877237029439,0,false,-248318276224,-248318276160⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1054577135208,0,false,-45878485632,-45878485568⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1054680417107,0,false,-45770808320,-45770808256⟩
    { al := (827499/4096000), au := (207087/1024000), zl := (999/1000), zu := (3997/4000),
      A := ⟨222130071404,222357973107⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202319561024,202319561088⟩ : DyadicInterval 40),(⟨-248137143936,-248137143872⟩ : DyadicInterval 40),(⟨739530164155,739530183485⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202509142656,202509142720⟩ : DyadicInterval 40),(⟨-248422781504,-248422781440⟩ : DyadicInterval 40),(⟨739483455232,739483474561⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202134749120,202134749184⟩ : DyadicInterval 40),(⟨-247858811584,-247858811520⟩ : DyadicInterval 40),(⟨739575642778,739575662108⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202370418368,202370418432⟩ : DyadicInterval 40),(⟨-248213757184,-248213757120⟩ : DyadicInterval 40),(⟨739517639596,739517658925⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨85840720,114580436⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨85837312,85837376⟩ : DyadicInterval 40),(⟨-85844096,-85844032⟩ : DyadicInterval 40),(⟨762123380242,762123399571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨114574464,114574528⟩ : DyadicInterval 40),(⟨-114586432,-114586368⟩ : DyadicInterval 40),(⟨762123377595,762123396924⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-11968,-6656⟩ : DyadicInterval 40),(⟨762123386944,762123408864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨222019002381,222274598337⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202227155648,202227155712⟩ : DyadicInterval 40),(⟨-247997963968,-247997963904⟩ : DyadicInterval 40),(⟨739552910130,739552929459⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202439790592,202439790656⟩ : DyadicInterval 40),(⟨-248318276224,-248318276160⟩ : DyadicInterval 40),(⟨739500548751,739500568081⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45878485632,-45770808256⟩ : DyadicInterval 40),(⟨785008787744,785062645696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨202319561024,202509142720⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-248422781504,-248137143872⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1186_ok : ecellOkT e1186 = true := by decide +kernel
theorem e1186_pos {a z : ℝ} (ha1 : ((827499/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((207087/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1186 e1186_ok ha1 ha2 hz1 hz2 hz

-- box ['16533/81920', '827499/4096000', '3997/4000', '1999/2000']  interval_lower 544651001/1099511627776
noncomputable def e1187 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1321413797478,0,true,202129946752,202129946816⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨877609458074,0,false,-247851580608,-247851580544⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1321641699181,0,true,202319561024,202319561088⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨877381556371,0,false,-248137143936,-248137143872⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1321247370850,0,true,201991459072,201991459136⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨877775884702,0,false,-247643092992,-247643092928⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1321530634146,0,true,202227158976,202227159040⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨877492621406,0,false,-247997968960,-247997968896⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568792958,0,true,57163648,57163712⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454462594,0,false,-57166720,-57166656⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099597470332,0,true,85839168,85839232⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099425785220,0,false,-85845952,-85845888⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621073,0,false,-6720,-6656⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624804,0,false,-3008,-2944⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1321330579461,0,true,202060701184,202060701248⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨877692676091,0,false,-247747325952,-247747325888⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1321586175612,0,true,202273368448,202273368512⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨877437079940,0,false,-248067565504,-248067565440⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1054657982256,0,false,-45794197056,-45794196992⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1054761171225,0,false,-45686624768,-45686624704⟩
    { al := (16533/81920), au := (827499/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨221902169702,222130071405⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202129946752,202129946816⟩ : DyadicInterval 40),(⟨-247851580608,-247851580544⟩ : DyadicInterval 40),(⟨739576823820,739576843150⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202319561024,202319561088⟩ : DyadicInterval 40),(⟨-248137143936,-248137143872⟩ : DyadicInterval 40),(⟨739530164155,739530183485⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201991459072,201991459136⟩ : DyadicInterval 40),(⟨-247643092992,-247643092928⟩ : DyadicInterval 40),(⟨739610866202,739610885532⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202227158976,202227159040⟩ : DyadicInterval 40),(⟨-247997968960,-247997968896⟩ : DyadicInterval 40),(⟨739552909305,739552928634⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57165182,85842556⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57163648,57163712⟩ : DyadicInterval 40),(⟨-57166720,-57166656⟩ : DyadicInterval 40),(⟨762123382115,762123401444⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨85839168,85839232⟩ : DyadicInterval 40),(⟨-85845952,-85845888⟩ : DyadicInterval 40),(⟨762123380241,762123399571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6720,-2944⟩ : DyadicInterval 40),(⟨762123385088,762123406240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨221818951685,222074547836⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202060701184,202060701248⟩ : DyadicInterval 40),(⟨-247747325952,-247747325888⟩ : DyadicInterval 40),(⟨739593849247,739593868576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202273368448,202273368512⟩ : DyadicInterval 40),(⟨-248067565504,-248067565440⟩ : DyadicInterval 40),(⟨739541536358,739541555687⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45794197056,-45686624704⟩ : DyadicInterval 40),(⟨784966695968,785020501408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨202129946752,202319561088⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-248137143936,-247851580544⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1187_ok : ecellOkT e1187 = true := by decide +kernel
theorem e1187_pos {a z : ℝ} (ha1 : ((16533/81920 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((827499/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1187 e1187_ok ha1 ha2 hz1 hz2 hz

-- box ['827499/4096000', '207087/1024000', '3997/4000', '1999/2000']  interval_lower 549572629/1099511627776
noncomputable def e1188 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1321641699180,0,true,202319561024,202319561088⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨877381556372,0,false,-248137143936,-248137143872⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1321869600883,0,true,202509142656,202509142720⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨877153654669,0,false,-248422781504,-248422781440⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1321475101626,0,true,202180955008,202180955072⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨877548153926,0,false,-247928388096,-247928388032⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1321758421897,0,true,202416661760,202416661824⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨877264833655,0,false,-248283427520,-248283427456⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568855276,0,true,57225984,57226048⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454400276,0,false,-57228992,-57228928⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099597563829,0,true,85932672,85932736⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099425691723,0,false,-85939456,-85939392⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621059,0,false,-6720,-6656⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624798,0,false,-3008,-2944⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1321558395691,0,true,202250256320,202250256384⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨877464859861,0,false,-248032755136,-248032755072⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1321814020343,0,true,202462910592,202462910656⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨877209235209,0,false,-248353113536,-248353113472⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1054565896878,0,false,-45890202880,-45890202816⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1054669203289,0,false,-45782498816,-45782498752⟩
    { al := (827499/4096000), au := (207087/1024000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨222130071404,222357973107⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202319561024,202319561088⟩ : DyadicInterval 40),(⟨-248137143936,-248137143872⟩ : DyadicInterval 40),(⟨739530164155,739530183485⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202509142656,202509142720⟩ : DyadicInterval 40),(⟨-248422781504,-248422781440⟩ : DyadicInterval 40),(⟨739483455232,739483474561⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202180955008,202180955072⟩ : DyadicInterval 40),(⟨-247928388096,-247928388032⟩ : DyadicInterval 40),(⟨739564277520,739564296850⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202416661760,202416661824⟩ : DyadicInterval 40),(⟨-248283427520,-248283427456⟩ : DyadicInterval 40),(⟨739506247718,739506267048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57227500,85936053⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57225984,57226048⟩ : DyadicInterval 40),(⟨-57228992,-57228928⟩ : DyadicInterval 40),(⟨762123382077,762123401406⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨85932672,85932736⟩ : DyadicInterval 40),(⟨-85939456,-85939392⟩ : DyadicInterval 40),(⟨762123380227,762123399556⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6720,-2944⟩ : DyadicInterval 40),(⟨762123385088,762123406240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨222046767915,222302392567⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202250256320,202250256384⟩ : DyadicInterval 40),(⟨-248032755136,-248032755072⟩ : DyadicInterval 40),(⟨739547225060,739547244389⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202462910592,202462910656⟩ : DyadicInterval 40),(⟨-248353113536,-248353113472⟩ : DyadicInterval 40),(⟨739494851130,739494870460⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45890202880,-45782498752⟩ : DyadicInterval 40),(⟨785014632992,785068504320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨202319561024,202509142720⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-248422781504,-248137143872⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1188_ok : ecellOkT e1188 = true := by decide +kernel
theorem e1188_pos {a z : ℝ} (ha1 : ((827499/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((207087/1024000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1188 e1188_ok ha1 ha2 hz1 hz2 hz

-- box ['103119/512000', '825801/4096000', '1999/2000', '3999/4000']  interval_lower 66746031/137438953472
noncomputable def e1189 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1320957994074,0,true,201750619968,201750620032⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨878065261478,0,false,-247280676288,-247280676224⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1321185895777,0,true,201940299712,201940299776⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨877837359775,0,false,-247566091392,-247566091328⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1320847270890,0,true,201658454656,201658454720⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨878175984662,0,false,-247142037632,-247142037568⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1321130477211,0,true,201894178560,201894178624⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨877892778341,0,false,-247496680512,-247496680448⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540148155,0,true,28520000,28520064⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483107397,0,false,-28520768,-28520704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568732042,0,true,57102720,57102784⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454523510,0,false,-57105792,-57105728⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624810,0,false,-3008,-2944⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627037,0,false,-768,-704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1320902627263,0,true,201704533952,201704534016⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨878120628289,0,false,-247211348224,-247211348160⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1321158195130,0,true,201917246592,201917246656⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨877865060422,0,false,-247531396224,-247531396160⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1054830698917,0,false,-45614149632,-45614149568⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1054933677516,0,false,-45506814272,-45506814208⟩
    { al := (103119/512000), au := (825801/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨221446366298,221674268001⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201750619968,201750620032⟩ : DyadicInterval 40),(⟨-247280676288,-247280676224⟩ : DyadicInterval 40),(⟨739669995463,739670014792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201940299712,201940299776⟩ : DyadicInterval 40),(⟨-247566091392,-247566091328⟩ : DyadicInterval 40),(⟨739623434264,739623453594⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201658454656,201658454720⟩ : DyadicInterval 40),(⟨-247142037632,-247142037568⟩ : DyadicInterval 40),(⟨739692598833,739692618162⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201894178560,201894178624⟩ : DyadicInterval 40),(⟨-247496680512,-247496680448⟩ : DyadicInterval 40),(⟨739634760997,739634780326⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨28520379,57104266⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28520000,28520064⟩ : DyadicInterval 40),(⟨-28520768,-28520704⟩ : DyadicInterval 40),(⟨762123383196,762123402525⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57102720,57102784⟩ : DyadicInterval 40),(⟨-57105792,-57105728⟩ : DyadicInterval 40),(⟨762123382122,762123401451⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3008,-704⟩ : DyadicInterval 40),(⟨762123383968,762123404384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨221390999487,221646567354⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201704533952,201704534016⟩ : DyadicInterval 40),(⟨-247211348224,-247211348160⟩ : DyadicInterval 40),(⟨739681299648,739681318978⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201917246592,201917246656⟩ : DyadicInterval 40),(⟨-247531396224,-247531396160⟩ : DyadicInterval 40),(⟨739629096214,739629115544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45614149632,-45506814208⟩ : DyadicInterval 40),(⟨784876790720,784930477696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨201750619968,201940299776⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-247566091392,-247280676224⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1189_ok : ecellOkT e1189 = true := by decide +kernel
theorem e1189_pos {a z : ℝ} (ha1 : ((103119/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((825801/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1189 e1189_ok ha1 ha2 hz1 hz2 hz

-- box ['825801/4096000', '16533/81920', '1999/2000', '3999/4000']  interval_lower 269423773/549755813888
noncomputable def e1190 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1321185895776,0,true,201940299712,201940299776⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨877837359776,0,false,-247566091392,-247566091328⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1321413797479,0,true,202129946752,202129946816⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨877609458073,0,false,-247851580608,-247851580544⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1321075058641,0,true,201848055424,201848055488⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨877948196911,0,false,-247427274048,-247427273984⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1321358321937,0,true,202083786112,202083786176⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨877664933615,0,false,-247782080320,-247782080256⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540179303,0,true,28551104,28551168⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483076249,0,false,-28551936,-28551872⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568794351,0,true,57165056,57165120⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454461201,0,false,-57168064,-57168000⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624803,0,false,-3008,-2944⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627035,0,false,-768,-704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1321130471985,0,true,201894174208,201894174272⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨877892783567,0,false,-247496673984,-247496673920⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1321386068346,0,true,202106873856,202106873920⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨877637187206,0,false,-247816840768,-247816840704⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1054738779418,0,false,-45709966848,-45709966784⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1054841875436,0,false,-45602499776,-45602499712⟩
    { al := (825801/4096000), au := (16533/81920), zl := (1999/2000), zu := (3999/4000),
      A := ⟨221674268000,221902169703⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201940299712,201940299776⟩ : DyadicInterval 40),(⟨-247566091392,-247566091328⟩ : DyadicInterval 40),(⟨739623434264,739623453594⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202129946752,202129946816⟩ : DyadicInterval 40),(⟨-247851580608,-247851580544⟩ : DyadicInterval 40),(⟨739576823820,739576843149⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201848055424,201848055488⟩ : DyadicInterval 40),(⟨-247427274048,-247427273984⟩ : DyadicInterval 40),(⟨739646084862,739646104192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202083786112,202083786176⟩ : DyadicInterval 40),(⟨-247782080320,-247782080256⟩ : DyadicInterval 40),(⟨739588174200,739588193529⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨28551527,57166575⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28551104,28551168⟩ : DyadicInterval 40),(⟨-28551936,-28551872⟩ : DyadicInterval 40),(⟨762123383226,762123402555⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57165056,57165120⟩ : DyadicInterval 40),(⟨-57168064,-57168000⟩ : DyadicInterval 40),(⟨762123382083,762123401412⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3008,-704⟩ : DyadicInterval 40),(⟨762123383968,762123404384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨221618844209,221874440570⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201894174208,201894174272⟩ : DyadicInterval 40),(⟨-247496673984,-247496673920⟩ : DyadicInterval 40),(⟨739634762073,739634781403⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202106873856,202106873920⟩ : DyadicInterval 40),(⟨-247816840768,-247816840704⟩ : DyadicInterval 40),(⟨739582497623,739582516953⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45709966848,-45602499712⟩ : DyadicInterval 40),(⟨784924633472,784978386304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨201940299712,202129946816⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-247851580608,-247566091328⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1190_ok : ecellOkT e1190 = true := by decide +kernel
theorem e1190_pos {a z : ℝ} (ha1 : ((825801/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((16533/81920 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1190 e1190_ok ha1 ha2 hz1 hz2 hz

-- box ['103119/512000', '825801/4096000', '3999/4000', '1']  interval_lower 533069877/1099511627776
noncomputable def e1191 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1320957994074,0,true,201750619968,201750620032⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨878065261478,0,false,-247280676288,-247280676224⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1321185895777,0,true,201940299712,201940299776⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨877837359775,0,false,-247566091392,-247566091328⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1320902632482,0,true,201704538304,201704538368⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨878120623070,0,false,-247211354752,-247211354688⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540180256,0,true,28552064,28552128⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483075296,0,false,-28552896,-28552832⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627034,0,false,-768,-704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1320930307753,0,true,201727574784,201727574848⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨878092947799,0,false,-247246008064,-247246008000⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1321185904306,0,true,201940306816,201940306880⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨877837351246,0,false,-247566102080,-247566102016⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1054819526634,0,false,-45625795200,-45625795136⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1054922529668,0,false,-45518433216,-45518433152⟩
    { al := (103119/512000), au := (825801/4096000), zl := (3999/4000), zu := 1,
      A := ⟨221446366298,221674268001⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201750619968,201750620032⟩ : DyadicInterval 40),(⟨-247280676288,-247280676224⟩ : DyadicInterval 40),(⟨739669995463,739670014792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201940299712,201940299776⟩ : DyadicInterval 40),(⟨-247566091392,-247566091328⟩ : DyadicInterval 40),(⟨739623434264,739623453594⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201704538304,201704538368⟩ : DyadicInterval 40),(⟨-247211354752,-247211354688⟩ : DyadicInterval 40),(⟨739681298575,739681317905⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201940299712,201940299776⟩ : DyadicInterval 40),(⟨-247566091392,-247566091328⟩ : DyadicInterval 40),(⟨739623434264,739623453594⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,28552480⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28552064,28552128⟩ : DyadicInterval 40),(⟨-28552896,-28552832⟩ : DyadicInterval 40),(⟨762123383226,762123402555⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-768,0⟩ : DyadicInterval 40),(⟨762123383616,762123403264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨221418679977,221674276530⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201727574784,201727574848⟩ : DyadicInterval 40),(⟨-247246008064,-247246008000⟩ : DyadicInterval 40),(⟨739675648511,739675667840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201940306816,201940306880⟩ : DyadicInterval 40),(⟨-247566102080,-247566102016⟩ : DyadicInterval 40),(⟨739623432519,739623451849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45625795200,-45518433152⟩ : DyadicInterval 40),(⟨784882600192,784936300480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨201750619968,201940299776⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-247566091392,-247280676224⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1191_ok : ecellOkT e1191 = true := by decide +kernel
theorem e1191_pos {a z : ℝ} (ha1 : ((103119/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((825801/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1191 e1191_ok ha1 ha2 hz1 hz2 hz

-- box ['825801/4096000', '16533/81920', '3999/4000', '1']  interval_lower 537945827/1099511627776
noncomputable def e1192 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1321185895776,0,true,201940299712,201940299776⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨877837359776,0,false,-247566091392,-247566091328⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1321413797479,0,true,202129946752,202129946816⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨877609458073,0,false,-247851580608,-247851580544⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1321130477208,0,true,201894178560,201894178624⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨877892778344,0,false,-247496680512,-247496680448⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540211412,0,true,28583232,28583296⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483044140,0,false,-28584064,-28584000⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627032,0,false,-768,-704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1321158180963,0,true,201917234752,201917234816⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨877865074589,0,false,-247531378496,-247531378432⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1321413806013,0,true,202129953856,202129953920⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨877609449539,0,false,-247851591296,-247851591232⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1054727584149,0,false,-45721637440,-45721637376⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1054830704630,0,false,-45614143680,-45614143616⟩
    { al := (825801/4096000), au := (16533/81920), zl := (3999/4000), zu := 1,
      A := ⟨221674268000,221902169703⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201940299712,201940299776⟩ : DyadicInterval 40),(⟨-247566091392,-247566091328⟩ : DyadicInterval 40),(⟨739623434264,739623453594⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202129946752,202129946816⟩ : DyadicInterval 40),(⟨-247851580608,-247851580544⟩ : DyadicInterval 40),(⟨739576823820,739576843149⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201894178560,201894178624⟩ : DyadicInterval 40),(⟨-247496680512,-247496680448⟩ : DyadicInterval 40),(⟨739634760998,739634780327⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202129946752,202129946816⟩ : DyadicInterval 40),(⟨-247851580608,-247851580544⟩ : DyadicInterval 40),(⟨739576823820,739576843149⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,28583636⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28583232,28583296⟩ : DyadicInterval 40),(⟨-28584064,-28584000⟩ : DyadicInterval 40),(⟨762123383224,762123402553⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-768,0⟩ : DyadicInterval 40),(⟨762123383616,762123403264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨221646553187,221902178237⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨201917234752,201917234816⟩ : DyadicInterval 40),(⟨-247531378496,-247531378432⟩ : DyadicInterval 40),(⟨739629099146,739629118476⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202129953856,202129953920⟩ : DyadicInterval 40),(⟨-247851591296,-247851591232⟩ : DyadicInterval 40),(⟨739576822070,739576841400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45721637440,-45614143616⟩ : DyadicInterval 40),(⟨784930455424,784984221600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨201940299712,202129946816⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-247851580608,-247566091328⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1192_ok : ecellOkT e1192 = true := by decide +kernel
theorem e1192_pos {a z : ℝ} (ha1 : ((825801/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((16533/81920 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1192 e1192_ok ha1 ha2 hz1 hz2 hz

-- box ['16533/81920', '827499/4096000', '1999/2000', '3999/4000']  interval_lower 271873193/549755813888
noncomputable def e1193 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1321413797478,0,true,202129946752,202129946816⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨877609458074,0,false,-247851580608,-247851580544⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1321641699181,0,true,202319561024,202319561088⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨877381556371,0,false,-248137143936,-248137143872⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1321302846393,0,true,202037623552,202037623616⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨877720409159,0,false,-247712584512,-247712584448⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1321586166664,0,true,202273360960,202273361024⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨877437088888,0,false,-248067554240,-248067554176⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540210458,0,true,28582272,28582336⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483045094,0,false,-28583104,-28583040⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568856672,0,true,57227392,57227456⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454398880,0,false,-57230400,-57230336⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624797,0,false,-3008,-2944⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627033,0,false,-768,-704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1321358316711,0,true,202083781760,202083781824⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨877664938841,0,false,-247782073792,-247782073728⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1321613941559,0,true,202296468416,202296468480⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨877409313993,0,false,-248102359360,-248102359296⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1054646765466,0,false,-45805890944,-45805890880⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1054749978924,0,false,-45698292032,-45698291968⟩
    { al := (16533/81920), au := (827499/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨221902169702,222130071405⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202129946752,202129946816⟩ : DyadicInterval 40),(⟨-247851580608,-247851580544⟩ : DyadicInterval 40),(⟨739576823820,739576843150⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202319561024,202319561088⟩ : DyadicInterval 40),(⟨-248137143936,-248137143872⟩ : DyadicInterval 40),(⟨739530164155,739530183485⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202037623552,202037623616⟩ : DyadicInterval 40),(⟨-247712584512,-247712584448⟩ : DyadicInterval 40),(⟨739599521686,739599541016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202273360960,202273361024⟩ : DyadicInterval 40),(⟨-248067554240,-248067554176⟩ : DyadicInterval 40),(⟨739541538196,739541557526⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨28582682,57228896⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28582272,28582336⟩ : DyadicInterval 40),(⟨-28583104,-28583040⟩ : DyadicInterval 40),(⟨762123383224,762123402553⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57227392,57227456⟩ : DyadicInterval 40),(⟨-57230400,-57230336⟩ : DyadicInterval 40),(⟨762123382077,762123401406⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3008,-704⟩ : DyadicInterval 40),(⟨762123383968,762123404384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨221846688935,222102313783⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202083781760,202083781824⟩ : DyadicInterval 40),(⟨-247782073792,-247782073728⟩ : DyadicInterval 40),(⟨739588175278,739588194608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202296468416,202296468480⟩ : DyadicInterval 40),(⟨-248102359360,-248102359296⟩ : DyadicInterval 40),(⟨739535849775,739535869104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45805890944,-45698291968⟩ : DyadicInterval 40),(⟨784972529600,785026348352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨202129946752,202319561088⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-248137143936,-247851580544⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1193_ok : ecellOkT e1193 = true := by decide +kernel
theorem e1193_pos {a z : ℝ} (ha1 : ((16533/81920 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((827499/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1193 e1193_ok ha1 ha2 hz1 hz2 hz

-- box ['827499/4096000', '207087/1024000', '1999/2000', '3999/4000']  interval_lower 137166129/274877906944
noncomputable def e1194 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1321641699180,0,true,202319561024,202319561088⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨877381556372,0,false,-248137143936,-248137143872⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1321869600883,0,true,202509142656,202509142720⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨877153654669,0,false,-248422781504,-248422781440⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1321530634144,0,true,202227158976,202227159040⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨877492621408,0,false,-247997968960,-247997968896⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1321814011390,0,true,202462903168,202462903232⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨877209244162,0,false,-248353102336,-248353102272⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540241617,0,true,28613440,28613504⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483013935,0,false,-28614272,-28614208⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568919006,0,true,57289728,57289792⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454336546,0,false,-57292736,-57292672⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624790,0,false,-3008,-2944⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627032,0,false,-768,-704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1321586161436,0,true,202273356608,202273356672⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨877437094116,0,false,-248067547712,-248067547648⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1321841814774,0,true,202486030336,202486030400⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨877181440778,0,false,-248387952192,-248387952128⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1054554657061,0,false,-45901921792,-45901921728⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1054657987984,0,false,-45794191040,-45794190976⟩
    { al := (827499/4096000), au := (207087/1024000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨222130071404,222357973107⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202319561024,202319561088⟩ : DyadicInterval 40),(⟨-248137143936,-248137143872⟩ : DyadicInterval 40),(⟨739530164155,739530183485⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202509142656,202509142720⟩ : DyadicInterval 40),(⟨-248422781504,-248422781440⟩ : DyadicInterval 40),(⟨739483455232,739483474561⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202227158976,202227159040⟩ : DyadicInterval 40),(⟨-247997968960,-247997968896⟩ : DyadicInterval 40),(⟨739552909305,739552928634⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202462903168,202462903232⟩ : DyadicInterval 40),(⟨-248353102336,-248353102272⟩ : DyadicInterval 40),(⟨739494852960,739494872289⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨28613841,57291230⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28613440,28613504⟩ : DyadicInterval 40),(⟨-28614272,-28614208⟩ : DyadicInterval 40),(⟨762123383223,762123402552⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57289728,57289792⟩ : DyadicInterval 40),(⟨-57292736,-57292672⟩ : DyadicInterval 40),(⟨762123382070,762123401399⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3008,-704⟩ : DyadicInterval 40),(⟨762123383968,762123404384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨222074533660,222330186998⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202273356608,202273356672⟩ : DyadicInterval 40),(⟨-248067547712,-248067547648⟩ : DyadicInterval 40),(⟨739541539277,739541558607⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202486030336,202486030400⟩ : DyadicInterval 40),(⟨-248387952192,-248387952128⟩ : DyadicInterval 40),(⟨739489152693,739489172022⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45901921792,-45794190976⟩ : DyadicInterval 40),(⟨785020479104,785074363776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨202319561024,202509142720⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-248422781504,-248137143872⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1194_ok : ecellOkT e1194 = true := by decide +kernel
theorem e1194_pos {a z : ℝ} (ha1 : ((827499/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((207087/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1194 e1194_ok ha1 ha2 hz1 hz2 hz

-- box ['16533/81920', '827499/4096000', '3999/4000', '1']  interval_lower 67855179/137438953472
noncomputable def e1195 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1321413797478,0,true,202129946752,202129946816⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨877609458074,0,false,-247851580608,-247851580544⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1321641699181,0,true,202319561024,202319561088⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨877381556371,0,false,-248137143936,-248137143872⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1321358321935,0,true,202083786112,202083786176⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨877664933617,0,false,-247782080320,-247782080256⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540242573,0,true,28614400,28614464⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483012979,0,false,-28615232,-28615168⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627031,0,false,-768,-704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1321386054175,0,true,202106862080,202106862144⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨877637201377,0,false,-247816822976,-247816822912⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1321641707714,0,true,202319568128,202319568192⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨877381547838,0,false,-248137154624,-248137154560⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1054635547190,0,false,-45817586496,-45817586432⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1054738785138,0,false,-45709960896,-45709960832⟩
    { al := (16533/81920), au := (827499/4096000), zl := (3999/4000), zu := 1,
      A := ⟨221902169702,222130071405⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202129946752,202129946816⟩ : DyadicInterval 40),(⟨-247851580608,-247851580544⟩ : DyadicInterval 40),(⟨739576823820,739576843150⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202319561024,202319561088⟩ : DyadicInterval 40),(⟨-248137143936,-248137143872⟩ : DyadicInterval 40),(⟨739530164155,739530183485⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202083786112,202083786176⟩ : DyadicInterval 40),(⟨-247782080320,-247782080256⟩ : DyadicInterval 40),(⟨739588174200,739588193530⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202319561024,202319561088⟩ : DyadicInterval 40),(⟨-248137143936,-248137143872⟩ : DyadicInterval 40),(⟨739530164155,739530183485⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,28614797⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28614400,28614464⟩ : DyadicInterval 40),(⟨-28615232,-28615168⟩ : DyadicInterval 40),(⟨762123383223,762123402552⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-768,0⟩ : DyadicInterval 40),(⟨762123383616,762123403264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨221874426399,222130079938⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202106862080,202106862144⟩ : DyadicInterval 40),(⟨-247816822976,-247816822912⟩ : DyadicInterval 40),(⟨739582500498,739582519828⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202319568128,202319568192⟩ : DyadicInterval 40),(⟨-248137154624,-248137154560⟩ : DyadicInterval 40),(⟨739530162402,739530181732⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45817586496,-45709960832⟩ : DyadicInterval 40),(⟨784978364032,785032196128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨202129946752,202319561088⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-248137143936,-247851580544⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1195_ok : ecellOkT e1195 = true := by decide +kernel
theorem e1195_pos {a z : ℝ} (ha1 : ((16533/81920 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((827499/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1195 e1195_ok ha1 ha2 hz1 hz2 hz

-- box ['827499/4096000', '207087/1024000', '3999/4000', '1']  interval_lower 547756055/1099511627776
noncomputable def e1196 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1321641699180,0,true,202319561024,202319561088⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨877381556372,0,false,-248137143936,-248137143872⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1321869600883,0,true,202509142656,202509142720⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨877153654669,0,false,-248422781504,-248422781440⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1321586166662,0,true,202273360960,202273361024⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨877437088890,0,false,-248067554240,-248067554176⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540273740,0,true,28645568,28645632⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482981812,0,false,-28646400,-28646336⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627029,0,false,-768,-704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1321613927382,0,true,202296456640,202296456704⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨877409328170,0,false,-248102341632,-248102341568⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1321869609417,0,true,202509149760,202509149824⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨877153646135,0,false,-248422792192,-248422792128⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1054543415753,0,false,-45913642432,-45913642368⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1054646771195,0,false,-45805884928,-45805884864⟩
    { al := (827499/4096000), au := (207087/1024000), zl := (3999/4000), zu := 1,
      A := ⟨222130071404,222357973107⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202319561024,202319561088⟩ : DyadicInterval 40),(⟨-248137143936,-248137143872⟩ : DyadicInterval 40),(⟨739530164155,739530183485⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202509142656,202509142720⟩ : DyadicInterval 40),(⟨-248422781504,-248422781440⟩ : DyadicInterval 40),(⟨739483455232,739483474561⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202273360960,202273361024⟩ : DyadicInterval 40),(⟨-248067554240,-248067554176⟩ : DyadicInterval 40),(⟨739541538196,739541557526⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202509142656,202509142720⟩ : DyadicInterval 40),(⟨-248422781504,-248422781440⟩ : DyadicInterval 40),(⟨739483455232,739483474561⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,28645964⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28645568,28645632⟩ : DyadicInterval 40),(⟨-28646400,-28646336⟩ : DyadicInterval 40),(⟨762123383221,762123402550⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-768,0⟩ : DyadicInterval 40),(⟨762123383616,762123403264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨222102299606,222357981641⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202296456640,202296456704⟩ : DyadicInterval 40),(⟨-248102341632,-248102341568⟩ : DyadicInterval 40),(⟨739535852682,739535872012⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202509149760,202509149824⟩ : DyadicInterval 40),(⟨-248422792192,-248422792128⟩ : DyadicInterval 40),(⟨739483453475,739483472804⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45913642432,-45805884864⟩ : DyadicInterval 40),(⟨785026326048,785080224096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨202319561024,202509142720⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-248422781504,-248137143872⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1196_ok : ecellOkT e1196 = true := by decide +kernel
theorem e1196_pos {a z : ℝ} (ha1 : ((827499/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((207087/1024000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1196 e1196_ok ha1 ha2 hz1 hz2 hz

-- box ['207087/1024000', '829197/4096000', '999/1000', '3997/4000']  interval_lower 277712045/549755813888
noncomputable def e1197 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1321869600882,0,true,202509142656,202509142720⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨877153654670,0,false,-248422781504,-248422781440⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1322097502585,0,true,202698691584,202698691648⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨876925752967,0,false,-248708493312,-248708493248⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1321647242908,0,true,202324172992,202324173056⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨877376012644,0,false,-248144091264,-248144091200⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1321930563180,0,true,202559849024,202559849088⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨877092692372,0,false,-248499200384,-248499200320⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099597561989,0,true,85930816,85930880⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099425693563,0,false,-85937600,-85937536⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099626332896,0,true,114699136,114699200⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099396922656,0,false,-114711104,-114711040⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511615809,0,false,-11968,-11904⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621060,0,false,-6720,-6656⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1321758417906,0,true,202416658432,202416658496⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨877264837646,0,false,-248283422528,-248283422464⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1322014042351,0,true,202629280384,202629280448⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨877009213201,0,false,-248603853696,-248603853632⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1054484978451,0,false,-45974573312,-45974573248⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1054588377785,0,false,-45866764096,-45866764032⟩
    { al := (207087/1024000), au := (829197/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨222357973106,222585874809⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202509142656,202509142720⟩ : DyadicInterval 40),(⟨-248422781504,-248422781440⟩ : DyadicInterval 40),(⟨739483455232,739483474562⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202698691584,202698691648⟩ : DyadicInterval 40),(⟨-248708493312,-248708493248⟩ : DyadicInterval 40),(⟨739436697075,739436716404⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202324172992,202324173056⟩ : DyadicInterval 40),(⟨-248144091264,-248144091200⟩ : DyadicInterval 40),(⟨739529028567,739529047897⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202559849024,202559849088⟩ : DyadicInterval 40),(⟨-248499200384,-248499200320⟩ : DyadicInterval 40),(⟨739470952544,739470971873⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨85934213,114705120⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨85930816,85930880⟩ : DyadicInterval 40),(⟨-85937600,-85937536⟩ : DyadicInterval 40),(⟨762123380227,762123399556⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨114699136,114699200⟩ : DyadicInterval 40),(⟨-114711104,-114711040⟩ : DyadicInterval 40),(⟨762123377569,762123396898⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-11968,-6656⟩ : DyadicInterval 40),(⟨762123386944,762123408864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨222246790130,222502414575⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202416658432,202416658496⟩ : DyadicInterval 40),(⟨-248283422528,-248283422464⟩ : DyadicInterval 40),(⟨739506248545,739506267874⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202629280384,202629280448⟩ : DyadicInterval 40),(⟨-248603853696,-248603853632⟩ : DyadicInterval 40),(⟨739453826144,739453845474⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45974573312,-45866764032⟩ : DyadicInterval 40),(⟨785056765632,785110689536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨202509142656,202698691648⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-248708493312,-248422781440⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1197_ok : ecellOkT e1197 = true := by decide +kernel
theorem e1197_pos {a z : ℝ} (ha1 : ((207087/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((829197/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1197 e1197_ok ha1 ha2 hz1 hz2 hz

-- box ['829197/4096000', '415023/2048000', '999/1000', '3997/4000']  interval_lower 560388121/1099511627776
noncomputable def e1198 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1322097502584,0,true,202698691584,202698691648⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨876925752968,0,false,-248708493312,-248708493248⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1322325404287,0,true,202888207872,202888207936⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨876697851265,0,false,-248994279360,-248994279296⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1321874916709,0,true,202513564288,202513564352⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨877148338843,0,false,-248429444928,-248429444864⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1322158293955,0,true,202749247104,202749247168⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨876864961597,0,false,-248784717696,-248784717632⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099597655499,0,true,86024320,86024384⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099425600053,0,false,-86031104,-86031040⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099626457604,0,true,114823808,114823872⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099396797948,0,false,-114835840,-114835776⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511615783,0,false,-12032,-11968⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621046,0,false,-6784,-6720⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1321986205660,0,true,202606128512,202606128576⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨877037049892,0,false,-248568955264,-248568955200⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1322241858596,0,true,202818737536,202818737600⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨876781396956,0,false,-248889505408,-248889505344⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1054392727286,0,false,-46070767808,-46070767744⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1054496244079,0,false,-45962826688,-45962826624⟩
    { al := (829197/4096000), au := (415023/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨222585874808,222813776511⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202698691584,202698691648⟩ : DyadicInterval 40),(⟨-248708493312,-248708493248⟩ : DyadicInterval 40),(⟨739436697075,739436716404⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202888207872,202888207936⟩ : DyadicInterval 40),(⟨-248994279360,-248994279296⟩ : DyadicInterval 40),(⟨739389889633,739389908962⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202513564288,202513564352⟩ : DyadicInterval 40),(⟨-248429444928,-248429444864⟩ : DyadicInterval 40),(⟨739482365153,739482384482⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202749247104,202749247168⟩ : DyadicInterval 40),(⟨-248784717696,-248784717632⟩ : DyadicInterval 40),(⟨739424216275,739424235604⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨86027723,114829828⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨86024320,86024384⟩ : DyadicInterval 40),(⟨-86031104,-86031040⟩ : DyadicInterval 40),(⟨762123380212,762123399542⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨114823808,114823872⟩ : DyadicInterval 40),(⟨-114835840,-114835776⟩ : DyadicInterval 40),(⟨762123377575,762123396904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-12032,-6720⟩ : DyadicInterval 40),(⟨762123386976,762123408896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨222474577884,222730230820⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202606128512,202606128576⟩ : DyadicInterval 40),(⟨-248568955264,-248568955200⟩ : DyadicInterval 40),(⟨739459537805,739459557135⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202818737536,202818737600⟩ : DyadicInterval 40),(⟨-248889505408,-248889505344⟩ : DyadicInterval 40),(⟨739407054330,739407073659⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-46070767808,-45962826624⟩ : DyadicInterval 40),(⟨785104796928,785158786784⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨202698691584,202888207936⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-248994279360,-248708493248⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1198_ok : ecellOkT e1198 = true := by decide +kernel
theorem e1198_pos {a z : ℝ} (ha1 : ((829197/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((415023/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1198 e1198_ok ha1 ha2 hz1 hz2 hz

-- box ['207087/1024000', '829197/4096000', '3997/4000', '1999/2000']  interval_lower 69314191/137438953472
noncomputable def e1199 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1321869600882,0,true,202509142656,202509142720⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨877153654670,0,false,-248422781504,-248422781440⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1322097502585,0,true,202698691584,202698691648⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨876925752967,0,false,-248708493312,-248708493248⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1321702832402,0,true,202370418368,202370418432⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨877320423150,0,false,-248213757184,-248213757120⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1321986209648,0,true,202606131840,202606131904⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨877037045904,0,false,-248568960256,-248568960192⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568917607,0,true,57288320,57288384⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454337945,0,false,-57291328,-57291264⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099597657345,0,true,86026176,86026240⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099425598207,0,false,-86032960,-86032896⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621044,0,false,-6784,-6720⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624791,0,false,-3008,-2944⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1321786211932,0,true,202439778752,202439778816⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨877237043620,0,false,-248318258496,-248318258432⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1322041865066,0,true,202652420096,202652420160⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨876981390486,0,false,-248638735808,-248638735744⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1054473717073,0,false,-45986315648,-45986315584⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1054577140943,0,false,-45878479680,-45878479616⟩
    { al := (207087/1024000), au := (829197/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨222357973106,222585874809⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202509142656,202509142720⟩ : DyadicInterval 40),(⟨-248422781504,-248422781440⟩ : DyadicInterval 40),(⟨739483455232,739483474562⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202698691584,202698691648⟩ : DyadicInterval 40),(⟨-248708493312,-248708493248⟩ : DyadicInterval 40),(⟨739436697075,739436716404⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202370418368,202370418432⟩ : DyadicInterval 40),(⟨-248213757184,-248213757120⟩ : DyadicInterval 40),(⟨739517639596,739517658925⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202606131840,202606131904⟩ : DyadicInterval 40),(⟨-248568960256,-248568960192⟩ : DyadicInterval 40),(⟨739459536977,739459556307⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57289831,86029569⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57288320,57288384⟩ : DyadicInterval 40),(⟨-57291328,-57291264⟩ : DyadicInterval 40),(⟨762123382070,762123401400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨86026176,86026240⟩ : DyadicInterval 40),(⟨-86032960,-86032896⟩ : DyadicInterval 40),(⟨762123380212,762123399542⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6784,-2944⟩ : DyadicInterval 40),(⟨762123385088,762123406272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨222274584156,222530237290⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202439778752,202439778816⟩ : DyadicInterval 40),(⟨-248318258496,-248318258432⟩ : DyadicInterval 40),(⟨739500551703,739500571033⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202652420096,202652420160⟩ : DyadicInterval 40),(⟨-248638735808,-248638735744⟩ : DyadicInterval 40),(⟨739448116684,739448136014⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45986315648,-45878479616⟩ : DyadicInterval 40),(⟨785062623424,785116560704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨202509142656,202698691648⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-248708493312,-248422781440⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1199_ok : ecellOkT e1199 = true := by decide +kernel
theorem e1199_pos {a z : ℝ} (ha1 : ((207087/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((829197/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1199 e1199_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B019

end


