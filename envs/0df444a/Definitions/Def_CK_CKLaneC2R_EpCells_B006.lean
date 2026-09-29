-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B006
-- name    : CK_CKLaneC2R_EpCells_B006
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:30:49.724655+00:00
-- url     : https://prove2.me/theorems/8f429621-c9bf-40db-b25a-0833034d7ac5
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B006` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B006` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B006` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B006 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B006.lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheckT

-- ===== source module CKLaneC2R.EpCells.B006 =====
section

namespace CKLaneC2R.EpCells.B006

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['120099/512000', '96249/409600', '1999/2000', '1']  interval_lower 525800491/1099511627776
noncomputable def e360 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1357422266417,0,true,231690632128,231690632192⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨841600989135,0,false,-293916355584,-293916355520⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1357878069822,0,true,232059770816,232059770880⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨841145185730,0,false,-294512002368,-294512002304⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1357293311097,0,true,231586173376,231586173440⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨841729944455,0,false,-293747894528,-293747894464⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578925368,0,true,67295488,67295552⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444330184,0,false,-67299712,-67299648⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623656,0,false,-4160,-4096⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1357357783000,0,true,231638399360,231638399424⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨841665472552,0,false,-293832114304,-293832114240⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1357878078414,0,true,232059777728,232059777792⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨841145177138,0,false,-294512013632,-294512013568⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1038799925299,0,false,-62452235840,-62452235776⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1039044200162,0,false,-62193714944,-62193714880⟩
    { al := (120099/512000), au := (96249/409600), zl := (1999/2000), zu := 1,
      A := ⟨257910638641,258366442046⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨231690632128,231690632192⟩ : DyadicInterval 40),(⟨-293916355584,-293916355520⟩ : DyadicInterval 40),(⟨731590860888,731590880217⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨232059770816,232059770880⟩ : DyadicInterval 40),(⟨-294512002368,-294512002304⟩ : DyadicInterval 40),(⟨731481815493,731481834822⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨231586173376,231586173440⟩ : DyadicInterval 40),(⟨-293747894528,-293747894464⟩ : DyadicInterval 40),(⟨731621675599,731621694928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨232059770816,232059770880⟩ : DyadicInterval 40),(⟨-294512002368,-294512002304⟩ : DyadicInterval 40),(⟨731481815493,731481834822⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,67297592⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67295488,67295552⟩ : DyadicInterval 40),(⟨-67299712,-67299648⟩ : DyadicInterval 40),(⟨762123381544,762123400874⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4160,0⟩ : DyadicInterval 40),(⟨762123383616,762123404960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨257846155224,258366450638⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨231638399360,231638399424⟩ : DyadicInterval 40),(⟨-293832114304,-293832114240⟩ : DyadicInterval 40),(⟨731606271598,731606290928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨232059777728,232059777792⟩ : DyadicInterval 40),(⟨-294512013632,-294512013568⟩ : DyadicInterval 40),(⟨731481813476,731481832805⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-62452235840,-62193714880⟩ : DyadicInterval 40),(⟨793220241056,793349520800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨231690632128,232059770880⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-294512002368,-293916355520⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e360_ok : ecellOkT e360 = true := by decide +kernel
theorem e360_pos {a z : ℝ} (ha1 : ((120099/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((96249/409600 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e360 e360_ok ha1 ha2 hz1 hz2 hz

-- box ['96249/409600', '241047/1024000', '1999/2000', '1']  interval_lower 270278591/549755813888
noncomputable def e361 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1357878069821,0,true,232059770816,232059770880⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨841145185731,0,false,-294512002368,-294512002304⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1358333873226,0,true,232428785536,232428785600⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨840689382326,0,false,-295107971968,-295107971904⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1357748886599,0,true,231955162560,231955162624⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨841274368953,0,false,-294343152128,-294343152064⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579054163,0,true,67424256,67424320⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444201389,0,false,-67428480,-67428416⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623641,0,false,-4160,-4096⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1357813472453,0,true,232007463232,232007463296⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨841209783099,0,false,-294427566528,-294427566464⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1358333881813,0,true,232428792512,232428792576⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨840689373739,0,false,-295107983232,-295107983168⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1038585524320,0,false,-62679190720,-62679190656⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1038830284098,0,false,-62420103232,-62420103168⟩
    { al := (96249/409600), au := (241047/1024000), zl := (1999/2000), zu := 1,
      A := ⟨258366442045,258822245450⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨232059770816,232059770880⟩ : DyadicInterval 40),(⟨-294512002368,-294512002304⟩ : DyadicInterval 40),(⟨731481815493,731481834822⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨232428785536,232428785600⟩ : DyadicInterval 40),(⟨-295107971968,-295107971904⟩ : DyadicInterval 40),(⟨731372570133,731372589463⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨231955162560,231955162624⟩ : DyadicInterval 40),(⟨-294343152128,-294343152064⟩ : DyadicInterval 40),(⟨731512741315,731512760645⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨232428785536,232428785600⟩ : DyadicInterval 40),(⟨-295107971968,-295107971904⟩ : DyadicInterval 40),(⟨731372570133,731372589463⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,67426387⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67424256,67424320⟩ : DyadicInterval 40),(⟨-67428480,-67428416⟩ : DyadicInterval 40),(⟨762123381529,762123400858⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4160,0⟩ : DyadicInterval 40),(⟨762123383616,762123404960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨258301844677,258822254037⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨232007463232,232007463296⟩ : DyadicInterval 40),(⟨-294427566528,-294427566464⟩ : DyadicInterval 40),(⟨731497281831,731497301161⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨232428792512,232428792576⟩ : DyadicInterval 40),(⟨-295107983232,-295107983168⟩ : DyadicInterval 40),(⟨731372568071,731372587400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-62679190720,-62420103168⟩ : DyadicInterval 40),(⟨793333435200,793462998240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨232059770816,232428785600⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-295107971968,-294512002304⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e361_ok : ecellOkT e361 = true := by decide +kernel
theorem e361_pos {a z : ℝ} (ha1 : ((96249/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((241047/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e361 e361_ok ha1 ha2 hz1 hz2 hz

-- box ['241047/1024000', '482943/2048000', '999/1000', '1999/2000']  interval_lower 139775683/274877906944
noncomputable def e362 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1358333873225,0,true,232428785536,232428785600⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨840689382327,0,false,-295107971968,-295107971904⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1358789676631,0,true,232797676480,232797676544⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨840233578921,0,false,-295704264832,-295704264768⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1358075050979,0,true,232219260352,232219260416⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨840948204573,0,false,-294769518464,-294769518400⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1358660037607,0,true,232692769600,232692769664⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨840363217945,0,false,-295534635072,-295534635008⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579050786,0,true,67420928,67420992⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444204766,0,false,-67425088,-67425024⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099646735115,0,true,135099008,135099072⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099376520437,0,false,-135115648,-135115584⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511611174,0,false,-16640,-16576⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623642,0,false,-4160,-4096⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1358204458311,0,true,232324024832,232324024896⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨840818797241,0,false,-294938727232,-294938727168⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1358724866363,0,true,232745231808,232745231872⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨840298389189,0,false,-295619458752,-295619458688⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1038401311739,0,false,-62874226944,-62874226880⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1038646441016,0,false,-62614702336,-62614702272⟩
    { al := (241047/1024000), au := (482943/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨258822245449,259278048855⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨232428785536,232428785600⟩ : DyadicInterval 40),(⟨-295107971968,-295107971904⟩ : DyadicInterval 40),(⟨731372570134,731372589463⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨232797676480,232797676544⟩ : DyadicInterval 40),(⟨-295704264832,-295704264768⟩ : DyadicInterval 40),(⟨731263124738,731263144067⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨232219260352,232219260416⟩ : DyadicInterval 40),(⟨-294769518464,-294769518400⟩ : DyadicInterval 40),(⟨731434628280,731434647609⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨232692769600,232692769664⟩ : DyadicInterval 40),(⟨-295534635072,-295534635008⟩ : DyadicInterval 40),(⟨731294273408,731294292738⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨67423010,135107339⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67420928,67420992⟩ : DyadicInterval 40),(⟨-67425088,-67425024⟩ : DyadicInterval 40),(⟨762123381497,762123400826⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨135099008,135099072⟩ : DyadicInterval 40),(⟨-135115648,-135115584⟩ : DyadicInterval 40),(⟨762123375270,762123394599⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-16640,-4096⟩ : DyadicInterval 40),(⟨762123385664,762123411200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨258692830535,259213238587⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨232324024832,232324024896⟩ : DyadicInterval 40),(⟨-294938727232,-294938727168⟩ : DyadicInterval 40),(⟨731403608197,731403627527⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨232745231808,232745231872⟩ : DyadicInterval 40),(⟨-295619458752,-295619458688⟩ : DyadicInterval 40),(⟨731278698843,731278718173⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-62874226944,-62614702272⟩ : DyadicInterval 40),(⟨793430734752,793560516352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨232428785536,232797676544⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-295704264832,-295107971904⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e362_ok : ecellOkT e362 = true := by decide +kernel
theorem e362_pos {a z : ℝ} (ha1 : ((241047/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((482943/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e362 e362_ok ha1 ha2 hz1 hz2 hz

-- box ['482943/2048000', '30237/128000', '999/1000', '1999/2000']  interval_lower 574103871/1099511627776
noncomputable def e363 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1358789676630,0,true,232797676480,232797676544⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨840233578922,0,false,-295704264832,-295704264768⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1359245480035,0,true,233166443712,233166443776⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨839777775517,0,false,-296300881216,-296300881152⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1358530398581,0,true,232587852672,232587852736⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨840492856971,0,false,-295365031488,-295365031424⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1359115613110,0,true,233061387648,233061387712⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨839907642442,0,false,-296130861056,-296130860992⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579179621,0,true,67549760,67549824⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444075931,0,false,-67553984,-67553920⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099646992916,0,true,135356800,135356864⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099376262636,0,false,-135373504,-135373440⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511611110,0,false,-16704,-16640⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623626,0,false,-4160,-4096⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1358660033811,0,true,232692766528,232692766592⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨840363221741,0,false,-295534630080,-295534630016⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1359180555823,0,true,233113924416,233113924480⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨839842699729,0,false,-296215879936,-296215879872⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1038186262504,0,false,-63101955520,-63101955456⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1038431876864,0,false,-62841863552,-62841863488⟩
    { al := (482943/2048000), au := (30237/128000), zl := (999/1000), zu := (1999/2000),
      A := ⟨259278048854,259733852259⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨232797676480,232797676544⟩ : DyadicInterval 40),(⟨-295704264832,-295704264768⟩ : DyadicInterval 40),(⟨731263124738,731263144068⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨233166443712,233166443776⟩ : DyadicInterval 40),(⟨-296300881216,-296300881152⟩ : DyadicInterval 40),(⟨731153479241,731153498571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨232587852672,232587852736⟩ : DyadicInterval 40),(⟨-295365031488,-295365031424⟩ : DyadicInterval 40),(⟨731325405922,731325425251⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨233061387648,233061387712⟩ : DyadicInterval 40),(⟨-296130861056,-296130860992⟩ : DyadicInterval 40),(⟨731184739665,731184758994⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨67551845,135365140⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67549760,67549824⟩ : DyadicInterval 40),(⟨-67553984,-67553920⟩ : DyadicInterval 40),(⟨762123381513,762123400842⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨135356800,135356864⟩ : DyadicInterval 40),(⟨-135373504,-135373440⟩ : DyadicInterval 40),(⟨762123375238,762123394567⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-16704,-4096⟩ : DyadicInterval 40),(⟨762123385664,762123411232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨259148406035,259668928047⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨232692766528,232692766592⟩ : DyadicInterval 40),(⟨-295534630080,-295534630016⟩ : DyadicInterval 40),(⟨731294274311,731294293640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨233113924416,233113924480⟩ : DyadicInterval 40),(⟨-296215879936,-296215879872⟩ : DyadicInterval 40),(⟨731169109249,731169128579⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-63101955520,-62841863488⟩ : DyadicInterval 40),(⟨793544315360,793674380640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨232797676480,233166443776⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-296300881216,-295704264768⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e363_ok : ecellOkT e363 = true := by decide +kernel
theorem e363_pos {a z : ℝ} (ha1 : ((482943/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((30237/128000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e363 e363_ok ha1 ha2 hz1 hz2 hz

-- box ['241047/1024000', '482943/2048000', '1999/2000', '1']  interval_lower 555424035/1099511627776
noncomputable def e364 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1358333873225,0,true,232428785536,232428785600⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨840689382327,0,false,-295107971968,-295107971904⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1358789676631,0,true,232797676480,232797676544⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨840233578921,0,false,-295704264832,-295704264768⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1358204462102,0,true,232324027904,232324027968⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨840818793450,0,false,-294938732224,-294938732160⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579183014,0,true,67553152,67553216⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444072538,0,false,-67557376,-67557312⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623625,0,false,-4160,-4096⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1358269161893,0,true,232376403328,232376403392⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨840754093659,0,false,-295023341312,-295023341248⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1358789685212,0,true,232797683456,232797683520⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨840233570340,0,false,-295704276032,-295704275968⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1038370745433,0,false,-62906592576,-62906592512⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1038615990322,0,false,-62646937984,-62646937920⟩
    { al := (241047/1024000), au := (482943/2048000), zl := (1999/2000), zu := 1,
      A := ⟨258822245449,259278048855⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨232428785536,232428785600⟩ : DyadicInterval 40),(⟨-295107971968,-295107971904⟩ : DyadicInterval 40),(⟨731372570134,731372589463⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨232797676480,232797676544⟩ : DyadicInterval 40),(⟨-295704264832,-295704264768⟩ : DyadicInterval 40),(⟨731263124738,731263144067⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨232324027904,232324027968⟩ : DyadicInterval 40),(⟨-294938732224,-294938732160⟩ : DyadicInterval 40),(⟨731403607300,731403626629⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨232797676480,232797676544⟩ : DyadicInterval 40),(⟨-295704264832,-295704264768⟩ : DyadicInterval 40),(⟨731263124738,731263144067⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,67555238⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67553152,67553216⟩ : DyadicInterval 40),(⟨-67557376,-67557312⟩ : DyadicInterval 40),(⟨762123381513,762123400842⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4160,0⟩ : DyadicInterval 40),(⟨762123383616,762123404960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨258757534117,259278057436⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨232376403328,232376403392⟩ : DyadicInterval 40),(⟨-295023341312,-295023341248⟩ : DyadicInterval 40),(⟨731388092104,731388111433⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨232797683456,232797683520⟩ : DyadicInterval 40),(⟨-295704276032,-295704275968⟩ : DyadicInterval 40),(⟨731263122645,731263141974⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-62906592576,-62646937920⟩ : DyadicInterval 40),(⟨793446852576,793576699168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨232428785536,232797676544⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-295704264832,-295107971904⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e364_ok : ecellOkT e364 = true := by decide +kernel
theorem e364_pos {a z : ℝ} (ha1 : ((241047/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((482943/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e364 e364_ok ha1 ha2 hz1 hz2 hz

-- box ['482943/2048000', '30237/128000', '1999/2000', '1']  interval_lower 142600265/274877906944
noncomputable def e365 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1358789676630,0,true,232797676480,232797676544⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨840233578922,0,false,-295704264832,-295704264768⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1359245480035,0,true,233166443712,233166443776⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨839777775517,0,false,-296300881216,-296300881152⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1358660037605,0,true,232692769600,232692769664⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨840363217947,0,false,-295534635072,-295534635008⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579311922,0,true,67682048,67682112⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443943630,0,false,-67686272,-67686208⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623609,0,false,-4224,-4160⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1358724851342,0,true,232745219648,232745219712⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨840298404210,0,false,-295619439104,-295619439040⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1359245488618,0,true,233166450688,233166450752⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨839777766934,0,false,-296300892480,-296300892416⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1038155588636,0,false,-63134441728,-63134441664⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1038401318823,0,false,-62874219456,-62874219392⟩
    { al := (482943/2048000), au := (30237/128000), zl := (1999/2000), zu := 1,
      A := ⟨259278048854,259733852259⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨232797676480,232797676544⟩ : DyadicInterval 40),(⟨-295704264832,-295704264768⟩ : DyadicInterval 40),(⟨731263124738,731263144068⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨233166443712,233166443776⟩ : DyadicInterval 40),(⟨-296300881216,-296300881152⟩ : DyadicInterval 40),(⟨731153479241,731153498571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨232692769600,232692769664⟩ : DyadicInterval 40),(⟨-295534635072,-295534635008⟩ : DyadicInterval 40),(⟨731294273409,731294292738⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨233166443712,233166443776⟩ : DyadicInterval 40),(⟨-296300881216,-296300881152⟩ : DyadicInterval 40),(⟨731153479241,731153498571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,67684146⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67682048,67682112⟩ : DyadicInterval 40),(⟨-67686272,-67686208⟩ : DyadicInterval 40),(⟨762123381497,762123400826⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4224,0⟩ : DyadicInterval 40),(⟨762123383616,762123404992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨259213223566,259733860842⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨232745219648,232745219712⟩ : DyadicInterval 40),(⟨-295619439104,-295619439040⟩ : DyadicInterval 40),(⟨731278702458,731278721788⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨233166450688,233166450752⟩ : DyadicInterval 40),(⟨-296300892480,-296300892416⟩ : DyadicInterval 40),(⟨731153477164,731153496494⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-63134441728,-62874219392⟩ : DyadicInterval 40),(⟨793560493312,793690623744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨232797676480,233166443776⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-296300881216,-295704264768⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e365_ok : ecellOkT e365 = true := by decide +kernel
theorem e365_pos {a z : ℝ} (ha1 : ((482943/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((30237/128000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e365 e365_ok ha1 ha2 hz1 hz2 hz

-- box ['30237/128000', '484641/2048000', '999/1000', '1999/2000']  interval_lower 589216101/1099511627776
noncomputable def e366 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1359245480034,0,true,233166443712,233166443776⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨839777775518,0,false,-296300881216,-296300881152⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1359701283439,0,true,233535087296,233535087360⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨839321972113,0,false,-296897821504,-296897821440⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1358985746181,0,true,232956321536,232956321600⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨840037509371,0,false,-295960867200,-295960867136⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1359571188612,0,true,233429882112,233429882176⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨839452066940,0,false,-296727410560,-296727410496⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579308512,0,true,67678592,67678656⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443947040,0,false,-67682880,-67682816⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099647250830,0,true,135614656,135614720⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099376004722,0,false,-135631424,-135631360⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511611047,0,false,-16768,-16704⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623610,0,false,-4224,-4160⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1359115609322,0,true,233061384576,233061384640⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨839907646230,0,false,-296130856128,-296130856064⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1359636245275,0,true,233482493440,233482493504⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨839387010277,0,false,-296812624832,-296812624768⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1037970835555,0,false,-63330131328,-63330131264⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1038216935177,0,false,-63069471488,-63069471424⟩
    { al := (30237/128000), au := (484641/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨259733852258,260189655663⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨233166443712,233166443776⟩ : DyadicInterval 40),(⟨-296300881216,-296300881152⟩ : DyadicInterval 40),(⟨731153479241,731153498571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨233535087296,233535087360⟩ : DyadicInterval 40),(⟨-296897821504,-296897821440⟩ : DyadicInterval 40),(⟨731043633625,731043652955⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨232956321536,232956321600⟩ : DyadicInterval 40),(⟨-295960867200,-295960867136⟩ : DyadicInterval 40),(⟨731215983857,731216003187⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨233429882112,233429882176⟩ : DyadicInterval 40),(⟨-296727410560,-296727410496⟩ : DyadicInterval 40),(⟨731075006052,731075025382⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨67680736,135623054⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67678592,67678656⟩ : DyadicInterval 40),(⟨-67682880,-67682816⟩ : DyadicInterval 40),(⟨762123381529,762123400859⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨135614656,135614720⟩ : DyadicInterval 40),(⟨-135631424,-135631360⟩ : DyadicInterval 40),(⟨762123375207,762123394536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-16768,-4160⟩ : DyadicInterval 40),(⟨762123385696,762123411264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨259603981546,260124617499⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨233061384576,233061384640⟩ : DyadicInterval 40),(⟨-296130856128,-296130856064⟩ : DyadicInterval 40),(⟨731184740593,731184759922⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨233482493440,233482493504⟩ : DyadicInterval 40),(⟨-296812624832,-296812624768⟩ : DyadicInterval 40),(⟨731059319642,731059338972⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-63330131328,-63069471424⟩ : DyadicInterval 40),(⟨793658119328,793788468544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨233166443712,233535087360⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-296897821504,-296300881152⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e366_ok : ecellOkT e366 = true := by decide +kernel
theorem e366_pos {a z : ℝ} (ha1 : ((30237/128000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((484641/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e366 e366_ok ha1 ha2 hz1 hz2 hz

-- box ['484641/2048000', '48549/204800', '999/1000', '1999/2000']  interval_lower 604440119/1099511627776
noncomputable def e367 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1359701283438,0,true,233535087296,233535087360⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨839321972114,0,false,-296897821504,-296897821440⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1360157086843,0,true,233903607360,233903607424⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨838866168709,0,false,-297495086080,-297495086016⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1359441093782,0,true,233324666880,233324666944⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨839582161770,0,false,-296557025920,-296557025856⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1360026764114,0,true,233798253184,233798253248⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨838996491438,0,false,-297324283840,-297324283776⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579437461,0,true,67807552,67807616⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443818091,0,false,-67811840,-67811776⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099647508859,0,true,135872640,135872704⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099375746693,0,false,-135889536,-135889472⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511610983,0,false,-16832,-16768⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623595,0,false,-4224,-4160⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1359571184828,0,true,233429879104,233429879168⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨839452070724,0,false,-296727405568,-296727405504⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1360091934739,0,true,233850939008,233850939072⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨838931320813,0,false,-297409693760,-297409693696⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1037755030881,0,false,-63558754752,-63558754688⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1038001615963,0,false,-63297526464,-63297526400⟩
    { al := (484641/2048000), au := (48549/204800), zl := (999/1000), zu := (1999/2000),
      A := ⟨260189655662,260645459067⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨233535087296,233535087360⟩ : DyadicInterval 40),(⟨-296897821504,-296897821440⟩ : DyadicInterval 40),(⟨731043633626,731043652955⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨233903607360,233903607424⟩ : DyadicInterval 40),(⟨-297495086080,-297495086016⟩ : DyadicInterval 40),(⟨730933587834,730933607163⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨233324666880,233324666944⟩ : DyadicInterval 40),(⟨-296557025920,-296557025856⟩ : DyadicInterval 40),(⟨731106362123,731106381452⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨233798253184,233798253248⟩ : DyadicInterval 40),(⟨-297324283840,-297324283776⟩ : DyadicInterval 40),(⟨730965072424,730965091753⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨67809685,135881083⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67807552,67807616⟩ : DyadicInterval 40),(⟨-67811840,-67811776⟩ : DyadicInterval 40),(⟨762123381513,762123400843⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨135872640,135872704⟩ : DyadicInterval 40),(⟨-135889536,-135889472⟩ : DyadicInterval 40),(⟨762123375207,762123394536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-16832,-4160⟩ : DyadicInterval 40),(⟨762123385696,762123411296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨260059557052,260580306963⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨233429879104,233429879168⟩ : DyadicInterval 40),(⟨-296727405568,-296727405504⟩ : DyadicInterval 40),(⟨731075006918,731075026248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨233850939008,233850939072⟩ : DyadicInterval 40),(⟨-297409693760,-297409693696⟩ : DyadicInterval 40),(⟨730949329937,730949349267⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-63558754752,-63297526400⟩ : DyadicInterval 40),(⟨793772146816,793902780256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨233535087296,233903607424⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-297495086080,-296897821440⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e367_ok : ecellOkT e367 = true := by decide +kernel
theorem e367_pos {a z : ℝ} (ha1 : ((484641/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((48549/204800 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e367 e367_ok ha1 ha2 hz1 hz2 hz

-- box ['30237/128000', '484641/2048000', '1999/2000', '1']  interval_lower 585489047/1099511627776
noncomputable def e368 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1359245480034,0,true,233166443712,233166443776⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨839777775518,0,false,-296300881216,-296300881152⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1359701283439,0,true,233535087296,233535087360⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨839321972113,0,false,-296897821504,-296897821440⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1359115613107,0,true,233061387648,233061387712⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨839907642445,0,false,-296130861056,-296130860992⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579440887,0,true,67811008,67811072⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443814665,0,false,-67815232,-67815168⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623593,0,false,-4224,-4160⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1359180540790,0,true,233113912256,233113912320⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨839842714762,0,false,-296215860288,-296215860224⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1359701292024,0,true,233535094272,233535094336⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨839321963528,0,false,-296897832768,-296897832704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1037940053932,0,false,-63362738496,-63362738432⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1038186269606,0,false,-63101947968,-63101947904⟩
    { al := (30237/128000), au := (484641/2048000), zl := (1999/2000), zu := 1,
      A := ⟨259733852258,260189655663⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨233166443712,233166443776⟩ : DyadicInterval 40),(⟨-296300881216,-296300881152⟩ : DyadicInterval 40),(⟨731153479241,731153498571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨233535087296,233535087360⟩ : DyadicInterval 40),(⟨-296897821504,-296897821440⟩ : DyadicInterval 40),(⟨731043633625,731043652955⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨233061387648,233061387712⟩ : DyadicInterval 40),(⟨-296130861056,-296130860992⟩ : DyadicInterval 40),(⟨731184739665,731184758995⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨233535087296,233535087360⟩ : DyadicInterval 40),(⟨-296897821504,-296897821440⟩ : DyadicInterval 40),(⟨731043633625,731043652955⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,67813111⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67811008,67811072⟩ : DyadicInterval 40),(⟨-67815232,-67815168⟩ : DyadicInterval 40),(⟨762123381481,762123400810⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4224,0⟩ : DyadicInterval 40),(⟨762123383616,762123404992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨259668913014,260189664248⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨233113912256,233113912320⟩ : DyadicInterval 40),(⟨-296215860288,-296215860224⟩ : DyadicInterval 40),(⟨731169112879,731169132209⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨233535094272,233535094336⟩ : DyadicInterval 40),(⟨-296897832768,-296897832704⟩ : DyadicInterval 40),(⟨731043631540,731043650870⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-63362738496,-63101947904⟩ : DyadicInterval 40),(⟨793674357568,793804772128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨233166443712,233535087360⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-296897821504,-296300881152⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e368_ok : ecellOkT e368 = true := by decide +kernel
theorem e368_pos {a z : ℝ} (ha1 : ((30237/128000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((484641/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e368 e368_ok ha1 ha2 hz1 hz2 hz

-- box ['484641/2048000', '48549/204800', '1999/2000', '1']  interval_lower 600688669/1099511627776
noncomputable def e369 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1359701283438,0,true,233535087296,233535087360⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨839321972114,0,false,-296897821504,-296897821440⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1360157086843,0,true,233903607360,233903607424⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨838866168709,0,false,-297495086080,-297495086016⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1359571188610,0,true,233429882112,233429882176⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨839452066942,0,false,-296727410496,-296727410432⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579569910,0,true,67940032,67940096⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443685642,0,false,-67944256,-67944192⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623577,0,false,-4224,-4160⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1359636230237,0,true,233482481280,233482481344⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨839387025315,0,false,-296812605120,-296812605056⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1360157095433,0,true,233903614272,233903614336⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨838866160119,0,false,-297495097344,-297495097280⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1037724141319,0,false,-63591483008,-63591482944⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1037970842671,0,false,-63330123776,-63330123712⟩
    { al := (484641/2048000), au := (48549/204800), zl := (1999/2000), zu := 1,
      A := ⟨260189655662,260645459067⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨233535087296,233535087360⟩ : DyadicInterval 40),(⟨-296897821504,-296897821440⟩ : DyadicInterval 40),(⟨731043633626,731043652955⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨233903607360,233903607424⟩ : DyadicInterval 40),(⟨-297495086080,-297495086016⟩ : DyadicInterval 40),(⟨730933587834,730933607163⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨233429882112,233429882176⟩ : DyadicInterval 40),(⟨-296727410496,-296727410432⟩ : DyadicInterval 40),(⟨731075006028,731075025357⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨233903607360,233903607424⟩ : DyadicInterval 40),(⟨-297495086080,-297495086016⟩ : DyadicInterval 40),(⟨730933587834,730933607163⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,67942134⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67940032,67940096⟩ : DyadicInterval 40),(⟨-67944256,-67944192⟩ : DyadicInterval 40),(⟨762123381465,762123400794⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4224,0⟩ : DyadicInterval 40),(⟨762123383616,762123404992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨260124602461,260645467657⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨233482481280,233482481344⟩ : DyadicInterval 40),(⟨-296812605120,-296812605056⟩ : DyadicInterval 40),(⟨731059323263,731059342592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨233903614272,233903614336⟩ : DyadicInterval 40),(⟨-297495097344,-297495097280⟩ : DyadicInterval 40),(⟨730933585779,730933605109⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-63591483008,-63330123712⟩ : DyadicInterval 40),(⟨793788445472,793919144384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨233535087296,233903607424⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-297495086080,-296897821440⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e369_ok : ecellOkT e369 = true := by decide +kernel
theorem e369_pos {a z : ℝ} (ha1 : ((484641/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((48549/204800 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e369 e369_ok ha1 ha2 hz1 hz2 hz

-- box ['48549/204800', '486339/2048000', '999/1000', '1999/2000']  interval_lower 619775973/1099511627776
noncomputable def e370 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1360157086842,0,true,233903607360,233903607424⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨838866168710,0,false,-297495086080,-297495086016⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1360612890248,0,true,234272003904,234272003968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨838410365304,0,false,-298092675264,-298092675200⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1359896441382,0,true,233692888896,233692888960⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨839126814170,0,false,-297153508096,-297153508032⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1360482339617,0,true,234166500864,234166500928⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨838540915935,0,false,-297921481344,-297921481280⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579566468,0,true,67936576,67936640⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443689084,0,false,-67940800,-67940736⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099647767004,0,true,136130752,136130816⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099375488548,0,false,-136147712,-136147648⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511610919,0,false,-16896,-16832⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623579,0,false,-4224,-4160⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1360026760337,0,true,233798250112,233798250176⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨838996495215,0,false,-297324278912,-297324278848⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1360547624198,0,true,234219261120,234219261184⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨838475631354,0,false,-298007087104,-298007087040⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1037538848492,0,false,-63787825984,-63787825920⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1037785919218,0,false,-63526028736,-63526028672⟩
    { al := (48549/204800), au := (486339/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨260645459066,261101262472⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨233903607360,233903607424⟩ : DyadicInterval 40),(⟨-297495086080,-297495086016⟩ : DyadicInterval 40),(⟨730933587834,730933607163⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨234272003904,234272003968⟩ : DyadicInterval 40),(⟨-298092675264,-298092675200⟩ : DyadicInterval 40),(⟨730823341862,730823361192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨233692888896,233692888960⟩ : DyadicInterval 40),(⟨-297153508096,-297153508032⟩ : DyadicInterval 40),(⟨730996540647,730996559977⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨234166500864,234166500928⟩ : DyadicInterval 40),(⟨-297921481344,-297921481280⟩ : DyadicInterval 40),(⟨730854938827,730854958157⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨67938692,136139228⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67936576,67936640⟩ : DyadicInterval 40),(⟨-67940800,-67940736⟩ : DyadicInterval 40),(⟨762123381465,762123400795⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨136130752,136130816⟩ : DyadicInterval 40),(⟨-136147712,-136147648⟩ : DyadicInterval 40),(⟨762123375175,762123394504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-16896,-4160⟩ : DyadicInterval 40),(⟨762123385696,762123411328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨260515132561,261035996422⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨233798250112,233798250176⟩ : DyadicInterval 40),(⟨-297324278912,-297324278848⟩ : DyadicInterval 40),(⟨730965073356,730965092685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨234219261120,234219261184⟩ : DyadicInterval 40),(⟨-298007087104,-298007087040⟩ : DyadicInterval 40),(⟨730839140159,730839159489⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-63787825984,-63526028672⟩ : DyadicInterval 40),(⟨793886397952,794017315872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨233903607360,234272003968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-298092675264,-297495086016⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e370_ok : ecellOkT e370 = true := by decide +kernel
theorem e370_pos {a z : ℝ} (ha1 : ((48549/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((486339/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e370 e370_ok ha1 ha2 hz1 hz2 hz

-- box ['486339/2048000', '121797/512000', '999/1000', '1999/2000']  interval_lower 635224575/1099511627776
noncomputable def e371 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1360612890247,0,true,234272003904,234272003968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨838410365305,0,false,-298092675264,-298092675200⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1361068693652,0,true,234640277056,234640277120⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨837954561900,0,false,-298690589440,-298690589376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1360351788984,0,true,234060987648,234060987712⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨838671466568,0,false,-297750314048,-297750313984⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1360937915120,0,true,234534625216,234534625280⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨838085340432,0,false,-298519003392,-298519003328⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579695532,0,true,68065600,68065664⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443560020,0,false,-68069888,-68069824⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099648025262,0,true,136388992,136389056⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099375230290,0,false,-136405952,-136405888⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511610855,0,false,-16960,-16896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623563,0,false,-4224,-4160⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1360482335843,0,true,234166497792,234166497856⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨838540919709,0,false,-297921476416,-297921476352⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1361003313649,0,true,234587459904,234587459968⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨838019941903,0,false,-298604805184,-298604805120⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1037322288388,0,false,-64017345280,-64017345216⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1037569844944,0,false,-63754978560,-63754978496⟩
    { al := (486339/2048000), au := (121797/512000), zl := (999/1000), zu := (1999/2000),
      A := ⟨261101262471,261557065876⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨234272003904,234272003968⟩ : DyadicInterval 40),(⟨-298092675264,-298092675200⟩ : DyadicInterval 40),(⟨730823341862,730823361192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨234640277056,234640277120⟩ : DyadicInterval 40),(⟨-298690589440,-298690589376⟩ : DyadicInterval 40),(⟨730712895655,730712914984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨234060987648,234060987712⟩ : DyadicInterval 40),(⟨-297750314048,-297750313984⟩ : DyadicInterval 40),(⟨730886519388,730886538718⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨234534625216,234534625280⟩ : DyadicInterval 40),(⟨-298519003392,-298519003328⟩ : DyadicInterval 40),(⟨730744605220,730744624549⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨68067756,136397486⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68065600,68065664⟩ : DyadicInterval 40),(⟨-68069888,-68069824⟩ : DyadicInterval 40),(⟨762123381481,762123400811⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨136388992,136389056⟩ : DyadicInterval 40),(⟨-136405952,-136405888⟩ : DyadicInterval 40),(⟨762123375111,762123394440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-16960,-4160⟩ : DyadicInterval 40),(⟨762123385696,762123411360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨260970708067,261491685873⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨234166497792,234166497856⟩ : DyadicInterval 40),(⟨-297921476416,-297921476352⟩ : DyadicInterval 40),(⟨730854939762,730854959091⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨234587459904,234587459968⟩ : DyadicInterval 40),(⟨-298604805184,-298604805120⟩ : DyadicInterval 40),(⟨730728750228,730728769557⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-64017345280,-63754978496⟩ : DyadicInterval 40),(⟨794000872864,794132075520⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨234272003904,234640277120⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-298690589440,-298092675200⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e371_ok : ecellOkT e371 = true := by decide +kernel
theorem e371_pos {a z : ℝ} (ha1 : ((486339/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((121797/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e371 e371_ok ha1 ha2 hz1 hz2 hz

-- box ['48549/204800', '486339/2048000', '1999/2000', '1']  interval_lower 154000177/274877906944
noncomputable def e372 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1360157086842,0,true,233903607360,233903607424⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨838866168710,0,false,-297495086080,-297495086016⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1360612890248,0,true,234272003904,234272003968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨838410365304,0,false,-298092675264,-298092675200⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1360026764112,0,true,233798253184,233798253248⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨838996491440,0,false,-297324283840,-297324283776⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579698991,0,true,68069056,68069120⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443556561,0,false,-68073344,-68073280⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623561,0,false,-4224,-4160⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1360091919687,0,true,233850926848,233850926912⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨838931335865,0,false,-297409674048,-297409673984⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1360612898836,0,true,234272010880,234272010944⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨838410356716,0,false,-298092686528,-298092686464⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1037507850801,0,false,-63820675648,-63820675584⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1037755038017,0,false,-63558747200,-63558747136⟩
    { al := (48549/204800), au := (486339/2048000), zl := (1999/2000), zu := 1,
      A := ⟨260645459066,261101262472⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨233903607360,233903607424⟩ : DyadicInterval 40),(⟨-297495086080,-297495086016⟩ : DyadicInterval 40),(⟨730933587834,730933607163⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨234272003904,234272003968⟩ : DyadicInterval 40),(⟨-298092675264,-298092675200⟩ : DyadicInterval 40),(⟨730823341862,730823361192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨233798253184,233798253248⟩ : DyadicInterval 40),(⟨-297324283840,-297324283776⟩ : DyadicInterval 40),(⟨730965072425,730965091754⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨234272003904,234272003968⟩ : DyadicInterval 40),(⟨-298092675264,-298092675200⟩ : DyadicInterval 40),(⟨730823341862,730823361192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,68071215⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68069056,68069120⟩ : DyadicInterval 40),(⟨-68073344,-68073280⟩ : DyadicInterval 40),(⟨762123381481,762123400810⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4224,0⟩ : DyadicInterval 40),(⟨762123383616,762123404992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨260580291911,261101271060⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨233850926848,233850926912⟩ : DyadicInterval 40),(⟨-297409674048,-297409673984⟩ : DyadicInterval 40),(⟨730949333574,730949352904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨234272010880,234272010944⟩ : DyadicInterval 40),(⟨-298092686528,-298092686464⟩ : DyadicInterval 40),(⟨730823339762,730823359091⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-63820675648,-63558747136⟩ : DyadicInterval 40),(⟨793902757184,794033740704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨233903607360,234272003968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-298092675264,-297495086016⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e372_ok : ecellOkT e372 = true := by decide +kernel
theorem e372_pos {a z : ℝ} (ha1 : ((48549/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((486339/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e372 e372_ok ha1 ha2 hz1 hz2 hz

-- box ['486339/2048000', '121797/512000', '1999/2000', '1']  interval_lower 631424737/1099511627776
noncomputable def e373 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1360612890247,0,true,234272003904,234272003968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨838410365305,0,false,-298092675264,-298092675200⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1361068693652,0,true,234640277056,234640277120⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨837954561900,0,false,-298690589440,-298690589376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1360482339615,0,true,234166500864,234166500928⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨838540915937,0,false,-297921481344,-297921481280⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579828129,0,true,68198208,68198272⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443427423,0,false,-68202496,-68202432⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623545,0,false,-4288,-4224⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1360547609135,0,true,234219248960,234219249024⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨838475646417,0,false,-298007067392,-298007067328⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1361068702234,0,true,234640284032,234640284096⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨837954553318,0,false,-298690600704,-298690600640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1037291182379,0,false,-64050316608,-64050316544⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1037538855645,0,false,-63787818368,-63787818304⟩
    { al := (486339/2048000), au := (121797/512000), zl := (1999/2000), zu := 1,
      A := ⟨261101262471,261557065876⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨234272003904,234272003968⟩ : DyadicInterval 40),(⟨-298092675264,-298092675200⟩ : DyadicInterval 40),(⟨730823341862,730823361192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨234640277056,234640277120⟩ : DyadicInterval 40),(⟨-298690589440,-298690589376⟩ : DyadicInterval 40),(⟨730712895655,730712914984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨234166500864,234166500928⟩ : DyadicInterval 40),(⟨-297921481344,-297921481280⟩ : DyadicInterval 40),(⟨730854938828,730854958158⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨234640277056,234640277120⟩ : DyadicInterval 40),(⟨-298690589440,-298690589376⟩ : DyadicInterval 40),(⟨730712895655,730712914984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,68200353⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68198208,68198272⟩ : DyadicInterval 40),(⟨-68202496,-68202432⟩ : DyadicInterval 40),(⟨762123381465,762123400794⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4288,0⟩ : DyadicInterval 40),(⟨762123383616,762123405024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨261035981359,261557074458⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨234219248960,234219249024⟩ : DyadicInterval 40),(⟨-298007067392,-298007067328⟩ : DyadicInterval 40),(⟨730839143813,730839163142⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨234640284032,234640284096⟩ : DyadicInterval 40),(⟨-298690600704,-298690600640⟩ : DyadicInterval 40),(⟨730712893548,730712912877⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-64050316608,-63787818304⟩ : DyadicInterval 40),(⟨794017292768,794148561184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨234272003904,234640277120⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-298690589440,-298092675200⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e373_ok : ecellOkT e373 = true := by decide +kernel
theorem e373_pos {a z : ℝ} (ha1 : ((486339/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((121797/512000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e373 e373_ok ha1 ha2 hz1 hz2 hz

-- box ['121797/512000', '488037/2048000', '999/1000', '1999/2000']  interval_lower 162696655/274877906944
noncomputable def e374 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1361068693651,0,true,234640277056,234640277120⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨837954561901,0,false,-298690589440,-298690589376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1361524497056,0,true,235008426944,235008427008⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨837498758496,0,false,-299288828864,-299288828800⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1360807136585,0,true,234428963200,234428963264⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨838216118967,0,false,-298347444096,-298347444032⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1361393490622,0,true,234902626368,234902626432⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨837629764930,0,false,-299116850304,-299116850240⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579824653,0,true,68194752,68194816⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443430899,0,false,-68199040,-68198976⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099648283638,0,true,136647360,136647424⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099374971914,0,false,-136664384,-136664320⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511610791,0,false,-17024,-16960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623547,0,false,-4288,-4224⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1360937911348,0,true,234534622208,234534622272⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨838085344204,0,false,-298518998464,-298518998400⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1361459003112,0,true,234955535424,234955535488⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨837564252440,0,false,-299202848448,-299202848384⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1037105350559,0,false,-64247312960,-64247312896⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1037353393142,0,false,-63984376256,-63984376192⟩
    { al := (121797/512000), au := (488037/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨261557065875,262012869280⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨234640277056,234640277120⟩ : DyadicInterval 40),(⟨-298690589440,-298690589376⟩ : DyadicInterval 40),(⟨730712895655,730712914984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨235008426944,235008427008⟩ : DyadicInterval 40),(⟨-299288828864,-299288828800⟩ : DyadicInterval 40),(⟨730602249103,730602268432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨234428963200,234428963264⟩ : DyadicInterval 40),(⟨-298347444096,-298347444032⟩ : DyadicInterval 40),(⟨730776298305,730776317634⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨234902626368,234902626432⟩ : DyadicInterval 40),(⟨-299116850304,-299116850240⟩ : DyadicInterval 40),(⟨730634071519,730634090848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨68196877,136655862⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68194752,68194816⟩ : DyadicInterval 40),(⟨-68199040,-68198976⟩ : DyadicInterval 40),(⟨762123381465,762123400795⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨136647360,136647424⟩ : DyadicInterval 40),(⟨-136664384,-136664320⟩ : DyadicInterval 40),(⟨762123375079,762123394408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-17024,-4224⟩ : DyadicInterval 40),(⟨762123385728,762123411392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨261426283572,261947375336⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨234534622208,234534622272⟩ : DyadicInterval 40),(⟨-298518998464,-298518998400⟩ : DyadicInterval 40),(⟨730744606117,730744625447⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨234955535424,234955535488⟩ : DyadicInterval 40),(⟨-299202848448,-299202848384⟩ : DyadicInterval 40),(⟨730618160143,730618179473⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-64247312960,-63984376192⟩ : DyadicInterval 40),(⟨794115571712,794247059360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨234640277056,235008427008⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-299288828864,-298690589376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e374_ok : ecellOkT e374 = true := by decide +kernel
theorem e374_pos {a z : ℝ} (ha1 : ((121797/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((488037/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e374 e374_ok ha1 ha2 hz1 hz2 hz

-- box ['488037/2048000', '244443/1024000', '999/1000', '1999/2000']  interval_lower 333231111/549755813888
noncomputable def e375 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1361524497055,0,true,235008426944,235008427008⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨837498758497,0,false,-299288828864,-299288828800⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1361980300461,0,true,235376453568,235376453632⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨837042955091,0,false,-299887394048,-299887393984⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1361262484185,0,true,234796815680,234796815744⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨837760771367,0,false,-298944898688,-298944898624⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1361849066125,0,true,235270504448,235270504512⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨837174189427,0,false,-299715022528,-299715022464⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579953832,0,true,68323904,68323968⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443301720,0,false,-68328192,-68328128⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099648542129,0,true,136905792,136905856⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099374713423,0,false,-136922880,-136922816⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511610727,0,false,-17088,-17024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623531,0,false,-4288,-4224⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1361393486861,0,true,234902623360,234902623424⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨837629768691,0,false,-299116845376,-299116845312⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1361914692570,0,true,235323487744,235323487808⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨837108562982,0,false,-299801217088,-299801217024⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1036888035015,0,false,-64477729280,-64477729216⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1037136563807,0,false,-64214222016,-64214221952⟩
    { al := (488037/2048000), au := (244443/1024000), zl := (999/1000), zu := (1999/2000),
      A := ⟨262012869279,262468672685⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨235008426944,235008427008⟩ : DyadicInterval 40),(⟨-299288828864,-299288828800⟩ : DyadicInterval 40),(⟨730602249103,730602268432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨235376453568,235376453632⟩ : DyadicInterval 40),(⟨-299887394048,-299887393984⟩ : DyadicInterval 40),(⟨730491402276,730491421605⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨234796815680,234796815744⟩ : DyadicInterval 40),(⟨-298944898688,-298944898624⟩ : DyadicInterval 40),(⟨730665877363,730665896692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨235270504448,235270504512⟩ : DyadicInterval 40),(⟨-299715022528,-299715022464⟩ : DyadicInterval 40),(⟨730523337690,730523357019⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨68326056,136914353⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68323904,68323968⟩ : DyadicInterval 40),(⟨-68328192,-68328128⟩ : DyadicInterval 40),(⟨762123381449,762123400779⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨136905792,136905856⟩ : DyadicInterval 40),(⟨-136922880,-136922816⟩ : DyadicInterval 40),(⟨762123375046,762123394376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-17088,-4224⟩ : DyadicInterval 40),(⟨762123385728,762123411424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨261881859085,262403064794⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨234902623360,234902623424⟩ : DyadicInterval 40),(⟨-299116845376,-299116845312⟩ : DyadicInterval 40),(⟨730634072417,730634091747⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨235323487744,235323487808⟩ : DyadicInterval 40),(⟨-299801217088,-299801217024⟩ : DyadicInterval 40),(⟨730507369817,730507389147⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-64477729280,-64214221952⟩ : DyadicInterval 40),(⟨794230494592,794362267520⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨235008426944,235376453632⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-299887394048,-299288828800⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e375_ok : ecellOkT e375 = true := by decide +kernel
theorem e375_pos {a z : ℝ} (ha1 : ((488037/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((244443/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e375 e375_ok ha1 ha2 hz1 hz2 hz

-- box ['121797/512000', '488037/2048000', '1999/2000', '1']  interval_lower 323481001/549755813888
noncomputable def e376 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1361068693651,0,true,234640277056,234640277120⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨837954561901,0,false,-298690589440,-298690589376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1361524497056,0,true,235008426944,235008427008⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨837498758496,0,false,-299288828864,-299288828800⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1360937915118,0,true,234534625216,234534625280⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨838085340434,0,false,-298519003392,-298519003328⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579957325,0,true,68327424,68327488⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443298227,0,false,-68331712,-68331648⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623529,0,false,-4288,-4224⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1361003298576,0,true,234587447744,234587447808⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨838019956976,0,false,-298604785408,-298604785344⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1361524505651,0,true,235008433856,235008433920⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨837498749901,0,false,-299288840192,-299288840128⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1037074136040,0,false,-64280406272,-64280406208⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1037322295558,0,false,-64017337664,-64017337600⟩
    { al := (121797/512000), au := (488037/2048000), zl := (1999/2000), zu := 1,
      A := ⟨261557065875,262012869280⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨234640277056,234640277120⟩ : DyadicInterval 40),(⟨-298690589440,-298690589376⟩ : DyadicInterval 40),(⟨730712895655,730712914984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨235008426944,235008427008⟩ : DyadicInterval 40),(⟨-299288828864,-299288828800⟩ : DyadicInterval 40),(⟨730602249103,730602268432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨234534625216,234534625280⟩ : DyadicInterval 40),(⟨-298519003392,-298519003328⟩ : DyadicInterval 40),(⟨730744605220,730744624550⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨235008426944,235008427008⟩ : DyadicInterval 40),(⟨-299288828864,-299288828800⟩ : DyadicInterval 40),(⟨730602249103,730602268432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,68329549⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68327424,68327488⟩ : DyadicInterval 40),(⟨-68331712,-68331648⟩ : DyadicInterval 40),(⟨762123381449,762123400778⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4288,0⟩ : DyadicInterval 40),(⟨762123383616,762123405024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨261491670800,262012877875⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨234587447744,234587447808⟩ : DyadicInterval 40),(⟨-298604785408,-298604785344⟩ : DyadicInterval 40),(⟨730728753872,730728773202⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨235008433856,235008433920⟩ : DyadicInterval 40),(⟨-299288840192,-299288840128⟩ : DyadicInterval 40),(⟨730602247049,730602266379⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-64280406272,-64017337600⟩ : DyadicInterval 40),(⟨794132052416,794263606016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨234640277056,235008427008⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-299288828864,-298690589376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e376_ok : ecellOkT e376 = true := by decide +kernel
theorem e376_pos {a z : ℝ} (ha1 : ((121797/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((488037/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e376 e376_ok ha1 ha2 hz1 hz2 hz

-- box ['488037/2048000', '244443/1024000', '1999/2000', '1']  interval_lower 82826641/137438953472
noncomputable def e377 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1361524497055,0,true,235008426944,235008427008⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨837498758497,0,false,-299288828864,-299288828800⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1361980300461,0,true,235376453568,235376453632⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨837042955091,0,false,-299887394048,-299887393984⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1361393490620,0,true,234902626368,234902626432⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨837629764932,0,false,-299116850304,-299116850240⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580086578,0,true,68456640,68456704⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443168974,0,false,-68460992,-68460928⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623513,0,false,-4288,-4224⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1361458988030,0,true,234955523264,234955523328⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨837564267522,0,false,-299202828608,-299202828544⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1361980309051,0,true,235376460480,235376460544⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨837042946501,0,false,-299887405312,-299887405248⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1036856711802,0,false,-64510944768,-64510944704⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1037105357747,0,false,-64247305344,-64247305280⟩
    { al := (488037/2048000), au := (244443/1024000), zl := (1999/2000), zu := 1,
      A := ⟨262012869279,262468672685⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨235008426944,235008427008⟩ : DyadicInterval 40),(⟨-299288828864,-299288828800⟩ : DyadicInterval 40),(⟨730602249103,730602268432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨235376453568,235376453632⟩ : DyadicInterval 40),(⟨-299887394048,-299887393984⟩ : DyadicInterval 40),(⟨730491402276,730491421605⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨234902626368,234902626432⟩ : DyadicInterval 40),(⟨-299116850304,-299116850240⟩ : DyadicInterval 40),(⟨730634071519,730634090849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨235376453568,235376453632⟩ : DyadicInterval 40),(⟨-299887394048,-299887393984⟩ : DyadicInterval 40),(⟨730491402276,730491421605⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,68458802⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68456640,68456704⟩ : DyadicInterval 40),(⟨-68460992,-68460928⟩ : DyadicInterval 40),(⟨762123381465,762123400794⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4288,0⟩ : DyadicInterval 40),(⟨762123383616,762123405024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨261947360254,262468681275⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨234955523264,234955523328⟩ : DyadicInterval 40),(⟨-299202828608,-299202828544⟩ : DyadicInterval 40),(⟨730618163779,730618183108⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨235376460480,235376460544⟩ : DyadicInterval 40),(⟨-299887405312,-299887405248⟩ : DyadicInterval 40),(⟨730491400192,730491419521⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-64510944768,-64247305280⟩ : DyadicInterval 40),(⟨794247036256,794378875264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨235008426944,235376453632⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-299887394048,-299288828800⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e377_ok : ecellOkT e377 = true := by decide +kernel
theorem e377_pos {a z : ℝ} (ha1 : ((488037/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((244443/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e377 e377_ok ha1 ha2 hz1 hz2 hz

-- box ['244443/1024000', '97947/409600', '999/1000', '1999/2000']  interval_lower 170563005/274877906944
noncomputable def e378 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1361980300460,0,true,235376453568,235376453632⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨837042955092,0,false,-299887394048,-299887393984⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1362436103865,0,true,235744357056,235744357120⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨836587151687,0,false,-300486285248,-300486285184⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1361717831787,0,true,235164545088,235164545152⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨837305423765,0,false,-299542678016,-299542677952⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1362304641628,0,true,235638259456,235638259520⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨836718613924,0,false,-300313520320,-300313520256⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580083070,0,true,68453120,68453184⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443172482,0,false,-68457472,-68457408⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099648800736,0,true,137164352,137164416⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099374454816,0,false,-137181568,-137181504⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511610662,0,false,-17152,-17088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623514,0,false,-4288,-4224⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1361849062366,0,true,235270501376,235270501440⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨837174193186,0,false,-299715017600,-299715017536⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1362370382028,0,true,235691316992,235691317056⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨836652873524,0,false,-300399911552,-300399911488⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1036670341752,0,false,-64708594560,-64708594496⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1036919356946,0,false,-64444516160,-64444516096⟩
    { al := (244443/1024000), au := (97947/409600), zl := (999/1000), zu := (1999/2000),
      A := ⟨262468672684,262924476089⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨235376453568,235376453632⟩ : DyadicInterval 40),(⟨-299887394048,-299887393984⟩ : DyadicInterval 40),(⟨730491402276,730491421606⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨235744357056,235744357120⟩ : DyadicInterval 40),(⟨-300486285248,-300486285184⟩ : DyadicInterval 40),(⟨730380355067,730380374396⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨235164545088,235164545152⟩ : DyadicInterval 40),(⟨-299542678016,-299542677952⟩ : DyadicInterval 40),(⟨730555256510,730555275839⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨235638259456,235638259520⟩ : DyadicInterval 40),(⟨-300313520320,-300313520256⟩ : DyadicInterval 40),(⟨730412403705,730412423035⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨68455294,137172960⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68453120,68453184⟩ : DyadicInterval 40),(⟨-68457472,-68457408⟩ : DyadicInterval 40),(⟨762123381465,762123400795⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨137164352,137164416⟩ : DyadicInterval 40),(⟨-137181568,-137181504⟩ : DyadicInterval 40),(⟨762123375046,762123394375⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-17152,-4224⟩ : DyadicInterval 40),(⟨762123385728,762123411456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨262337434590,262858754252⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨235270501376,235270501440⟩ : DyadicInterval 40),(⟨-299715017600,-299715017536⟩ : DyadicInterval 40),(⟨730523338631,730523357961⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨235691316992,235691317056⟩ : DyadicInterval 40),(⟨-300399911552,-300399911488⟩ : DyadicInterval 40),(⟨730396379215,730396398544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-64708594560,-64444516096⟩ : DyadicInterval 40),(⟨794345641664,794477700160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨235376453568,235744357120⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-300486285248,-299887393984⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e378_ok : ecellOkT e378 = true := by decide +kernel
theorem e378_pos {a z : ℝ} (ha1 : ((244443/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((97947/409600 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e378 e378_ok ha1 ha2 hz1 hz2 hz

-- box ['97947/409600', '61323/256000', '999/1000', '1999/2000']  interval_lower 349078353/549755813888
noncomputable def e379 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1362436103864,0,true,235744357056,235744357120⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨836587151688,0,false,-300486285248,-300486285184⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1362891907269,0,true,236112137472,236112137536⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨836131348283,0,false,-301085502784,-301085502720⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1362173179387,0,true,235532151552,235532151616⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨836850076165,0,false,-300140782528,-300140782464⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1362760217130,0,true,236005891456,236005891520⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨836263038422,0,false,-300912344064,-300912344000⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580212364,0,true,68582400,68582464⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443043188,0,false,-68586752,-68586688⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099649059458,0,true,137423040,137423104⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099374196094,0,false,-137440320,-137440256⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511610597,0,false,-17216,-17152⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623498,0,false,-4288,-4224⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1362304637872,0,true,235638256384,235638256448⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨836718617680,0,false,-300313515392,-300313515328⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1362826071484,0,true,236059023232,236059023296⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨836197184068,0,false,-300998932224,-300998932160⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1036452270772,0,false,-64939908928,-64939908864⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1036701772555,0,false,-64675258944,-64675258880⟩
    { al := (97947/409600), au := (61323/256000), zl := (999/1000), zu := (1999/2000),
      A := ⟨262924476088,263380279493⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨235744357056,235744357120⟩ : DyadicInterval 40),(⟨-300486285248,-300486285184⟩ : DyadicInterval 40),(⟨730380355067,730380374397⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨236112137472,236112137536⟩ : DyadicInterval 40),(⟨-301085502784,-301085502720⟩ : DyadicInterval 40),(⟨730269107431,730269126760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨235532151552,235532151616⟩ : DyadicInterval 40),(⟨-300140782528,-300140782464⟩ : DyadicInterval 40),(⟨730444435713,730444455042⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨236005891456,236005891520⟩ : DyadicInterval 40),(⟨-300912344064,-300912344000⟩ : DyadicInterval 40),(⟨730301269546,730301288875⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨68584588,137431682⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68582400,68582464⟩ : DyadicInterval 40),(⟨-68586752,-68586688⟩ : DyadicInterval 40),(⟨762123381449,762123400779⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨137423040,137423104⟩ : DyadicInterval 40),(⟨-137440320,-137440256⟩ : DyadicInterval 40),(⟨762123375013,762123394343⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-17216,-4224⟩ : DyadicInterval 40),(⟨762123385728,762123411488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨262793010096,263314443708⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨235638256384,235638256448⟩ : DyadicInterval 40),(⟨-300313515392,-300313515328⟩ : DyadicInterval 40),(⟨730412404649,730412423979⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨236059023232,236059023296⟩ : DyadicInterval 40),(⟨-300998932224,-300998932160⟩ : DyadicInterval 40),(⟨730285188316,730285207646⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-64939908928,-64675258880⟩ : DyadicInterval 40),(⟨794461013056,794593357344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨235744357056,236112137536⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-301085502784,-300486285184⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e379_ok : ecellOkT e379 = true := by decide +kernel
theorem e379_pos {a z : ℝ} (ha1 : ((97947/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((61323/256000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e379 e379_ok ha1 ha2 hz1 hz2 hz

-- box ['244443/1024000', '97947/409600', '1999/2000', '1']  interval_lower 678378095/1099511627776
noncomputable def e380 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1361980300460,0,true,235376453568,235376453632⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨837042955092,0,false,-299887394048,-299887393984⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1362436103865,0,true,235744357056,235744357120⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨836587151687,0,false,-300486285248,-300486285184⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1361849066123,0,true,235270504448,235270504512⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨837174189429,0,false,-299715022528,-299715022464⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580215890,0,true,68585920,68585984⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443039662,0,false,-68590272,-68590208⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623497,0,false,-4288,-4224⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1361914677477,0,true,235323475584,235323475648⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨837108578075,0,false,-299801197248,-299801197184⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1362436112453,0,true,235744363968,235744364032⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨836587143099,0,false,-300486296512,-300486296448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1036638909656,0,false,-64741932480,-64741932416⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1036888042220,0,false,-64477721664,-64477721600⟩
    { al := (244443/1024000), au := (97947/409600), zl := (1999/2000), zu := 1,
      A := ⟨262468672684,262924476089⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨235376453568,235376453632⟩ : DyadicInterval 40),(⟨-299887394048,-299887393984⟩ : DyadicInterval 40),(⟨730491402276,730491421606⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨235744357056,235744357120⟩ : DyadicInterval 40),(⟨-300486285248,-300486285184⟩ : DyadicInterval 40),(⟨730380355067,730380374396⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨235270504448,235270504512⟩ : DyadicInterval 40),(⟨-299715022528,-299715022464⟩ : DyadicInterval 40),(⟨730523337690,730523357020⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨235744357056,235744357120⟩ : DyadicInterval 40),(⟨-300486285248,-300486285184⟩ : DyadicInterval 40),(⟨730380355067,730380374396⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,68588114⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68585920,68585984⟩ : DyadicInterval 40),(⟨-68590272,-68590208⟩ : DyadicInterval 40),(⟨762123381449,762123400778⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4288,0⟩ : DyadicInterval 40),(⟨762123383616,762123405024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨262403049701,262924484677⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨235323475584,235323475648⟩ : DyadicInterval 40),(⟨-299801197248,-299801197184⟩ : DyadicInterval 40),(⟨730507373469,730507392798⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨235744363968,235744364032⟩ : DyadicInterval 40),(⟨-300486296512,-300486296448⟩ : DyadicInterval 40),(⟨730380352975,730380372305⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-64741932480,-64477721600⟩ : DyadicInterval 40),(⟨794362244416,794494369120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨235376453568,235744357120⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-300486285248,-299887393984⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e380_ok : ecellOkT e380 = true := by decide +kernel
theorem e380_pos {a z : ℝ} (ha1 : ((244443/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((97947/409600 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e380 e380_ok ha1 ha2 hz1 hz2 hz

-- box ['97947/409600', '61323/256000', '1999/2000', '1']  interval_lower 173564383/274877906944
noncomputable def e381 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1362436103864,0,true,235744357056,235744357120⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨836587151688,0,false,-300486285248,-300486285184⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1362891907269,0,true,236112137472,236112137536⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨836131348283,0,false,-301085502784,-301085502720⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1362304641625,0,true,235638259456,235638259520⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨836718613927,0,false,-300313520320,-300313520256⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580345259,0,true,68715328,68715392⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442910293,0,false,-68719680,-68719616⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623481,0,false,-4352,-4288⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1362370366924,0,true,235691304832,235691304896⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨836652888628,0,false,-300399891712,-300399891648⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1362891915860,0,true,236112144384,236112144448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨836131339692,0,false,-301085514112,-301085514048⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1036420729600,0,false,-64973369664,-64973369600⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1036670348975,0,false,-64708586880,-64708586816⟩
    { al := (97947/409600), au := (61323/256000), zl := (1999/2000), zu := 1,
      A := ⟨262924476088,263380279493⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨235744357056,235744357120⟩ : DyadicInterval 40),(⟨-300486285248,-300486285184⟩ : DyadicInterval 40),(⟨730380355067,730380374397⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨236112137472,236112137536⟩ : DyadicInterval 40),(⟨-301085502784,-301085502720⟩ : DyadicInterval 40),(⟨730269107431,730269126760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨235638259456,235638259520⟩ : DyadicInterval 40),(⟨-300313520320,-300313520256⟩ : DyadicInterval 40),(⟨730412403706,730412423036⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨236112137472,236112137536⟩ : DyadicInterval 40),(⟨-301085502784,-301085502720⟩ : DyadicInterval 40),(⟨730269107431,730269126760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,68717483⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68715328,68715392⟩ : DyadicInterval 40),(⟨-68719680,-68719616⟩ : DyadicInterval 40),(⟨762123381433,762123400762⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4352,0⟩ : DyadicInterval 40),(⟨762123383616,762123405056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨262858739148,263380288084⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨235691304832,235691304896⟩ : DyadicInterval 40),(⟨-300399891712,-300399891648⟩ : DyadicInterval 40),(⟨730396382882,730396402212⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨236112144384,236112144448⟩ : DyadicInterval 40),(⟨-301085514112,-301085514048⟩ : DyadicInterval 40),(⟨730269105356,730269124685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-64973369664,-64708586816⟩ : DyadicInterval 40),(⟨794477677024,794610087712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨235744357056,236112137536⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-301085502784,-300486285184⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e381_ok : ecellOkT e381 = true := by decide +kernel
theorem e381_pos {a z : ℝ} (ha1 : ((97947/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((61323/256000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e381 e381_ok ha1 ha2 hz1 hz2 hz

-- box ['61323/256000', '491433/2048000', '999/1000', '1999/2000']  interval_lower 178544201/274877906944
noncomputable def e382 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1362891907268,0,true,236112137472,236112137536⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨836131348284,0,false,-301085502784,-301085502720⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1363347710673,0,true,236479794944,236479795008⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨835675544879,0,false,-301685047104,-301685047040⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1362628526988,0,true,235899635200,235899635264⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨836394728564,0,false,-300739212608,-300739212544⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1363215792632,0,true,236373400640,236373400704⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨835807462920,0,false,-301511494144,-301511494080⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580341717,0,true,68711744,68711808⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442913835,0,false,-68716096,-68716032⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099649318298,0,true,137681856,137681920⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099373937254,0,false,-137699200,-137699136⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511610533,0,false,-17280,-17216⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623482,0,false,-4352,-4288⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1362760213383,0,true,236005888448,236005888512⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨836263042169,0,false,-300912339136,-300912339072⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1363281760945,0,true,236426606528,236426606592⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨835741494607,0,false,-301598279424,-301598279360⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1036233822071,0,false,-65171672832,-65171672768⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1036483810632,0,false,-64906450688,-64906450624⟩
    { al := (61323/256000), au := (491433/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨263380279492,263836082897⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨236112137472,236112137536⟩ : DyadicInterval 40),(⟨-301085502784,-301085502720⟩ : DyadicInterval 40),(⟨730269107431,730269126761⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨236479794944,236479795008⟩ : DyadicInterval 40),(⟨-301685047104,-301685047040⟩ : DyadicInterval 40),(⟨730157659333,730157678662⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨235899635200,235899635264⟩ : DyadicInterval 40),(⟨-300739212608,-300739212544⟩ : DyadicInterval 40),(⟨730333414912,730333434241⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨236373400640,236373400704⟩ : DyadicInterval 40),(⟨-301511494144,-301511494080⟩ : DyadicInterval 40),(⟨730189935112,730189954441⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨68713941,137690522⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68711744,68711808⟩ : DyadicInterval 40),(⟨-68716096,-68716032⟩ : DyadicInterval 40),(⟨762123381433,762123400762⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨137681856,137681920⟩ : DyadicInterval 40),(⟨-137699200,-137699136⟩ : DyadicInterval 40),(⟨762123374981,762123394310⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-17280,-4288⟩ : DyadicInterval 40),(⟨762123385760,762123411520⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨263248585607,263770133169⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨236005888448,236005888512⟩ : DyadicInterval 40),(⟨-300912339136,-300912339072⟩ : DyadicInterval 40),(⟨730301270450,730301289780⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨236426606528,236426606592⟩ : DyadicInterval 40),(⟨-301598279424,-301598279360⟩ : DyadicInterval 40),(⟨730173797076,730173816405⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-65171672832,-64906450624⟩ : DyadicInterval 40),(⟨794576608928,794709239296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨236112137472,236479795008⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-301685047104,-301085502720⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e382_ok : ecellOkT e382 = true := by decide +kernel
theorem e382_pos {a z : ℝ} (ha1 : ((61323/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((491433/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e382 e382_ok ha1 ha2 hz1 hz2 hz

-- box ['491433/2048000', '246141/1024000', '999/1000', '1999/2000']  interval_lower 730312297/1099511627776
noncomputable def e383 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1363347710672,0,true,236479794944,236479795008⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨835675544880,0,false,-301685047104,-301685047040⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1363803514078,0,true,236847329472,236847329536⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨835219741474,0,false,-302284918528,-302284918464⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1363083874589,0,true,236266996032,236266996096⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨835939380963,0,false,-301337968576,-301337968512⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1363671368136,0,true,236740786944,236740787008⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨835351887416,0,false,-302110970880,-302110970816⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580471129,0,true,68841152,68841216⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442784423,0,false,-68845568,-68845504⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099649577255,0,true,137940800,137940864⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099373678297,0,false,-137958144,-137958080⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511610468,0,false,-17344,-17280⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623466,0,false,-4352,-4288⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1363215788891,0,true,236373397568,236373397632⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨835807466661,0,false,-301511489216,-301511489152⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1363737450395,0,true,236794067008,236794067072⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨835285805157,0,false,-302197953472,-302197953408⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1036014995657,0,false,-65403886464,-65403886400⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1036265471181,0,false,-65138091584,-65138091520⟩
    { al := (491433/2048000), au := (246141/1024000), zl := (999/1000), zu := (1999/2000),
      A := ⟨263836082896,264291886302⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨236479794944,236479795008⟩ : DyadicInterval 40),(⟨-301685047104,-301685047040⟩ : DyadicInterval 40),(⟨730157659333,730157678663⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨236847329472,236847329536⟩ : DyadicInterval 40),(⟨-302284918528,-302284918464⟩ : DyadicInterval 40),(⟨730046010767,730046030096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨236266996032,236266996096⟩ : DyadicInterval 40),(⟨-301337968576,-301337968512⟩ : DyadicInterval 40),(⟨730222194103,730222213432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨236740786944,236740787008⟩ : DyadicInterval 40),(⟨-302110970880,-302110970816⟩ : DyadicInterval 40),(⟨730078400437,730078419766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨68843353,137949479⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68841152,68841216⟩ : DyadicInterval 40),(⟨-68845568,-68845504⟩ : DyadicInterval 40),(⟨762123381449,762123400778⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨137940800,137940864⟩ : DyadicInterval 40),(⟨-137958144,-137958080⟩ : DyadicInterval 40),(⟨762123374916,762123394245⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-17344,-4288⟩ : DyadicInterval 40),(⟨762123385760,762123411552⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨263704161115,264225822619⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨236373397568,236373397632⟩ : DyadicInterval 40),(⟨-301511489216,-301511489152⟩ : DyadicInterval 40),(⟨730189936058,730189955387⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨236794067008,236794067072⟩ : DyadicInterval 40),(⟨-302197953472,-302197953408⟩ : DyadicInterval 40),(⟨730062205412,730062224742⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-65403886464,-65138091520⟩ : DyadicInterval 40),(⟨794692429376,794825346112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨236479794944,236847329536⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-302284918528,-301685047040⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e383_ok : ecellOkT e383 = true := by decide +kernel
theorem e383_pos {a z : ℝ} (ha1 : ((491433/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((246141/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e383 e383_ok ha1 ha2 hz1 hz2 hz

-- box ['61323/256000', '491433/2048000', '1999/2000', '1']  interval_lower 44390765/68719476736
noncomputable def e384 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1362891907268,0,true,236112137472,236112137536⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨836131348284,0,false,-301085502784,-301085502720⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1363347710673,0,true,236479794944,236479795008⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨835675544879,0,false,-301685047104,-301685047040⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1362760217128,0,true,236005891456,236005891520⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨836263038424,0,false,-300912344064,-300912344000⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580474687,0,true,68844736,68844800⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442780865,0,false,-68849088,-68849024⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623465,0,false,-4352,-4288⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1362826056370,0,true,236059011072,236059011136⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨836197199182,0,false,-300998912320,-300998912256⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1363347719269,0,true,236479801856,236479801920⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨835675536283,0,false,-301685058432,-301685058368⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1036202171635,0,false,-65205256512,-65205256448⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1036452278012,0,false,-64939901248,-64939901184⟩
    { al := (61323/256000), au := (491433/2048000), zl := (1999/2000), zu := 1,
      A := ⟨263380279492,263836082897⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨236112137472,236112137536⟩ : DyadicInterval 40),(⟨-301085502784,-301085502720⟩ : DyadicInterval 40),(⟨730269107431,730269126761⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨236479794944,236479795008⟩ : DyadicInterval 40),(⟨-301685047104,-301685047040⟩ : DyadicInterval 40),(⟨730157659333,730157678662⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨236005891456,236005891520⟩ : DyadicInterval 40),(⟨-300912344064,-300912344000⟩ : DyadicInterval 40),(⟨730301269546,730301288876⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨236479794944,236479795008⟩ : DyadicInterval 40),(⟨-301685047104,-301685047040⟩ : DyadicInterval 40),(⟨730157659333,730157678662⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,68846911⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68844736,68844800⟩ : DyadicInterval 40),(⟨-68849088,-68849024⟩ : DyadicInterval 40),(⟨762123381416,762123400746⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4352,0⟩ : DyadicInterval 40),(⟨762123383616,762123405056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨263314428594,263836091493⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨236059011072,236059011136⟩ : DyadicInterval 40),(⟨-300998912320,-300998912256⟩ : DyadicInterval 40),(⟨730285191975,730285211305⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨236479801856,236479801920⟩ : DyadicInterval 40),(⟨-301685058432,-301685058368⟩ : DyadicInterval 40),(⟨730157657249,730157676578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-65205256512,-64939901184⟩ : DyadicInterval 40),(⟨794593334208,794726031136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨236112137472,236479795008⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-301685047104,-301085502720⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e384_ok : ecellOkT e384 = true := by decide +kernel
theorem e384_pos {a z : ℝ} (ha1 : ((61323/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((491433/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e384 e384_ok ha1 ha2 hz1 hz2 hz

-- box ['491433/2048000', '246141/1024000', '1999/2000', '1']  interval_lower 363181453/549755813888
noncomputable def e385 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1363347710672,0,true,236479794944,236479795008⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨835675544880,0,false,-301685047104,-301685047040⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1363803514078,0,true,236847329472,236847329536⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨835219741474,0,false,-302284918528,-302284918464⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1363215792630,0,true,236373400640,236373400704⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨835807462922,0,false,-301511494144,-301511494080⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580604174,0,true,68974208,68974272⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442651378,0,false,-68978624,-68978560⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623448,0,false,-4352,-4288⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1363281745821,0,true,236426594368,236426594432⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨835741509731,0,false,-301598259520,-301598259456⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1363803522668,0,true,236847336384,236847336448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨835219732884,0,false,-302284929792,-302284929728⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1035983235769,0,false,-65437593408,-65437593344⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1036233829329,0,false,-65171665152,-65171665088⟩
    { al := (491433/2048000), au := (246141/1024000), zl := (1999/2000), zu := 1,
      A := ⟨263836082896,264291886302⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨236479794944,236479795008⟩ : DyadicInterval 40),(⟨-301685047104,-301685047040⟩ : DyadicInterval 40),(⟨730157659333,730157678663⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨236847329472,236847329536⟩ : DyadicInterval 40),(⟨-302284918528,-302284918464⟩ : DyadicInterval 40),(⟨730046010767,730046030096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨236373400640,236373400704⟩ : DyadicInterval 40),(⟨-301511494144,-301511494080⟩ : DyadicInterval 40),(⟨730189935112,730189954442⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨236847329472,236847329536⟩ : DyadicInterval 40),(⟨-302284918528,-302284918464⟩ : DyadicInterval 40),(⟨730046010767,730046030096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,68976398⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68974208,68974272⟩ : DyadicInterval 40),(⟨-68978624,-68978560⟩ : DyadicInterval 40),(⟨762123381432,762123400761⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4352,0⟩ : DyadicInterval 40),(⟨762123383616,762123405056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨263770118045,264291894892⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨236426594368,236426594432⟩ : DyadicInterval 40),(⟨-301598259520,-301598259456⟩ : DyadicInterval 40),(⟨730173800750,730173820079⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨236847336384,236847336448⟩ : DyadicInterval 40),(⟨-302284929792,-302284929728⟩ : DyadicInterval 40),(⟨730046008653,730046027982⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-65437593408,-65171665088⟩ : DyadicInterval 40),(⟨794709216160,794842199584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨236479794944,236847329536⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-302284918528,-301685047040⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e385_ok : ecellOkT e385 = true := by decide +kernel
theorem e385_pos {a z : ℝ} (ha1 : ((491433/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((246141/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e385 e385_ok ha1 ha2 hz1 hz2 hz

-- box ['246141/1024000', '493131/2048000', '999/1000', '1999/2000']  interval_lower 5832535/8589934592
noncomputable def e386 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1363803514077,0,true,236847329472,236847329536⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨835219741475,0,false,-302284918528,-302284918464⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1364259317482,0,true,237214741184,237214741248⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨834763938070,0,false,-302885117376,-302885117312⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1363539222190,0,true,236634234112,236634234176⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨835484033362,0,false,-301937050752,-301937050688⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1364126943638,0,true,237108050624,237108050688⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨834896311914,0,false,-302710774592,-302710774528⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580600598,0,true,68970624,68970688⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442654954,0,false,-68975040,-68974976⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099649836327,0,true,138199808,138199872⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099373419225,0,false,-138217280,-138217216⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511610403,0,false,-17408,-17344⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623450,0,false,-4352,-4288⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1363671364391,0,true,236740783936,236740784000⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨835351891161,0,false,-302110965952,-302110965888⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1364193139859,0,true,237161404672,237161404736⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨834830115693,0,false,-302797954816,-302797954752⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1035795791518,0,false,-65636550080,-65636550016⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1036046754204,0,false,-65370181952,-65370181888⟩
    { al := (246141/1024000), au := (493131/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨264291886301,264747689706⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨236847329472,236847329536⟩ : DyadicInterval 40),(⟨-302284918528,-302284918464⟩ : DyadicInterval 40),(⟨730046010767,730046030097⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨237214741184,237214741248⟩ : DyadicInterval 40),(⟨-302885117376,-302885117312⟩ : DyadicInterval 40),(⟨729934161649,729934180979⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨236634234112,236634234176⟩ : DyadicInterval 40),(⟨-301937050752,-301937050688⟩ : DyadicInterval 40),(⟨730110773242,730110792571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨237108050624,237108050688⟩ : DyadicInterval 40),(⟨-302710774592,-302710774528⟩ : DyadicInterval 40),(⟨729966665359,729966684689⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨68972822,138208551⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68970624,68970688⟩ : DyadicInterval 40),(⟨-68975040,-68974976⟩ : DyadicInterval 40),(⟨762123381433,762123400762⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨138199808,138199872⟩ : DyadicInterval 40),(⟨-138217280,-138217216⟩ : DyadicInterval 40),(⟨762123374915,762123394244⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-17408,-4288⟩ : DyadicInterval 40),(⟨762123385760,762123411584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨264159736615,264681512083⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨236740783936,236740784000⟩ : DyadicInterval 40),(⟨-302110965952,-302110965888⟩ : DyadicInterval 40),(⟨730078401348,730078420678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨237161404672,237161404736⟩ : DyadicInterval 40),(⟨-302797954816,-302797954752⟩ : DyadicInterval 40),(⟨729950413364,729950432693⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-65636550080,-65370181888⟩ : DyadicInterval 40),(⟨794808474560,794941677920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨236847329472,237214741248⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-302885117376,-302284918464⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e386_ok : ecellOkT e386 = true := by decide +kernel
theorem e386_pos {a z : ℝ} (ha1 : ((246141/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((493131/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e386 e386_ok ha1 ha2 hz1 hz2 hz

-- box ['493131/2048000', '24699/102400', '999/1000', '1999/2000']  interval_lower 381466705/549755813888
noncomputable def e387 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1364259317481,0,true,237214741184,237214741248⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨834763938071,0,false,-302885117376,-302885117312⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1364715120886,0,true,237582030208,237582030272⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨834308134666,0,false,-303485644032,-303485643968⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1363994569791,0,true,237001349632,237001349696⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨835028685761,0,false,-302536459520,-302536459456⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1364582519140,0,true,237475191616,237475191680⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨834440736412,0,false,-303310905792,-303310905728⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580730127,0,true,69100160,69100224⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442525425,0,false,-69104576,-69104512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099650095519,0,true,138459008,138459072⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099373160033,0,false,-138476480,-138476416⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511610337,0,false,-17472,-17408⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623434,0,false,-4352,-4288⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1364126939899,0,true,237108047616,237108047680⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨834896315653,0,false,-302710769728,-302710769664⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1364648829315,0,true,237528619712,237528619776⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨834374426237,0,false,-303398283712,-303398283648⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1035576209664,0,false,-65869663936,-65869663872⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1035827659694,0,false,-65602722048,-65602721984⟩
    { al := (493131/2048000), au := (24699/102400), zl := (999/1000), zu := (1999/2000),
      A := ⟨264747689705,265203493110⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨237214741184,237214741248⟩ : DyadicInterval 40),(⟨-302885117376,-302885117312⟩ : DyadicInterval 40),(⟨729934161649,729934180979⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨237582030208,237582030272⟩ : DyadicInterval 40),(⟨-303485644032,-303485643968⟩ : DyadicInterval 40),(⟨729822111918,729822131248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨237001349632,237001349696⟩ : DyadicInterval 40),(⟨-302536459520,-302536459456⟩ : DyadicInterval 40),(⟨729999152229,729999171559⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨237475191616,237475191680⟩ : DyadicInterval 40),(⟨-303310905792,-303310905728⟩ : DyadicInterval 40),(⟨729854729985,729854749315⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨69102351,138467743⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69100160,69100224⟩ : DyadicInterval 40),(⟨-69104576,-69104512⟩ : DyadicInterval 40),(⟨762123381416,762123400746⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨138459008,138459072⟩ : DyadicInterval 40),(⟨-138476480,-138476416⟩ : DyadicInterval 40),(⟨762123374849,762123394179⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-17472,-4288⟩ : DyadicInterval 40),(⟨762123385760,762123411616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨264615312123,265137201539⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨237108047616,237108047680⟩ : DyadicInterval 40),(⟨-302710769728,-302710769664⟩ : DyadicInterval 40),(⟨729966666296,729966685626⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨237528619712,237528619776⟩ : DyadicInterval 40),(⟨-303398283712,-303398283648⟩ : DyadicInterval 40),(⟨729838420786,729838440116⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-65869663936,-65602721984⟩ : DyadicInterval 40),(⟨794924744608,795058234848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨237214741184,237582030272⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-303485644032,-302885117312⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e387_ok : ecellOkT e387 = true := by decide +kernel
theorem e387_pos {a z : ℝ} (ha1 : ((493131/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((24699/102400 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e387 e387_ok ha1 ha2 hz1 hz2 hz

-- box ['246141/1024000', '493131/2048000', '1999/2000', '1']  interval_lower 742589385/1099511627776
noncomputable def e388 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1363803514077,0,true,236847329472,236847329536⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨835219741475,0,false,-302284918528,-302284918464⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1364259317482,0,true,237214741184,237214741248⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨834763938070,0,false,-302885117376,-302885117312⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1363671368133,0,true,236740786944,236740787008⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨835351887419,0,false,-302110970880,-302110970816⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580733720,0,true,69103744,69103808⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442521832,0,false,-69108160,-69108096⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623432,0,false,-4352,-4288⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1363737435262,0,true,236794054784,236794054848⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨835285820290,0,false,-302197933568,-302197933504⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1364259326070,0,true,237214748096,237214748160⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨834763929482,0,false,-302885128704,-302885128640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1035763921993,0,false,-65670380544,-65670380480⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1036015002931,0,false,-65403878720,-65403878656⟩
    { al := (246141/1024000), au := (493131/2048000), zl := (1999/2000), zu := 1,
      A := ⟨264291886301,264747689706⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨236847329472,236847329536⟩ : DyadicInterval 40),(⟨-302284918528,-302284918464⟩ : DyadicInterval 40),(⟨730046010767,730046030097⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨237214741184,237214741248⟩ : DyadicInterval 40),(⟨-302885117376,-302885117312⟩ : DyadicInterval 40),(⟨729934161649,729934180979⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨236740786944,236740787008⟩ : DyadicInterval 40),(⟨-302110970880,-302110970816⟩ : DyadicInterval 40),(⟨730078400438,730078419767⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨237214741184,237214741248⟩ : DyadicInterval 40),(⟨-302885117376,-302885117312⟩ : DyadicInterval 40),(⟨729934161649,729934180979⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,69105944⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69103744,69103808⟩ : DyadicInterval 40),(⟨-69108160,-69108096⟩ : DyadicInterval 40),(⟨762123381416,762123400745⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4352,0⟩ : DyadicInterval 40),(⟨762123383616,762123405056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨264225807486,264747698294⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨236794054784,236794054848⟩ : DyadicInterval 40),(⟨-302197933568,-302197933504⟩ : DyadicInterval 40),(⟨730062209142,730062228471⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨237214748096,237214748160⟩ : DyadicInterval 40),(⟨-302885128704,-302885128640⟩ : DyadicInterval 40),(⟨729934159552,729934178881⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-65670380544,-65403878656⟩ : DyadicInterval 40),(⟨794825322944,794958593152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨236847329472,237214741248⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-302885117376,-302284918464⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e388_ok : ecellOkT e388 = true := by decide +kernel
theorem e388_pos {a z : ℝ} (ha1 : ((246141/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((493131/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e388 e388_ok ha1 ha2 hz1 hz2 hz

-- box ['493131/2048000', '24699/102400', '1999/2000', '1']  interval_lower 47433299/68719476736
noncomputable def e389 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1364259317481,0,true,237214741184,237214741248⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨834763938071,0,false,-302885117376,-302885117312⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1364715120886,0,true,237582030208,237582030272⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨834308134666,0,false,-303485644032,-303485643968⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1364126943636,0,true,237108050624,237108050688⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨834896311916,0,false,-302710774592,-302710774528⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580863324,0,true,69233344,69233408⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442392228,0,false,-69237760,-69237696⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623416,0,false,-4416,-4352⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1364193124715,0,true,237161392512,237161392576⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨834830130837,0,false,-302797934848,-302797934784⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1364715129483,0,true,237582037120,237582037184⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨834308126069,0,false,-303485655360,-303485655296⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1035544230305,0,false,-65903618240,-65903618176⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1035795798810,0,false,-65636542336,-65636542272⟩
    { al := (493131/2048000), au := (24699/102400), zl := (1999/2000), zu := 1,
      A := ⟨264747689705,265203493110⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨237214741184,237214741248⟩ : DyadicInterval 40),(⟨-302885117376,-302885117312⟩ : DyadicInterval 40),(⟨729934161649,729934180979⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨237582030208,237582030272⟩ : DyadicInterval 40),(⟨-303485644032,-303485643968⟩ : DyadicInterval 40),(⟨729822111918,729822131248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨237108050624,237108050688⟩ : DyadicInterval 40),(⟨-302710774592,-302710774528⟩ : DyadicInterval 40),(⟨729966665360,729966684689⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨237582030208,237582030272⟩ : DyadicInterval 40),(⟨-303485644032,-303485643968⟩ : DyadicInterval 40),(⟨729822111918,729822131248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,69235548⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69233344,69233408⟩ : DyadicInterval 40),(⟨-69237760,-69237696⟩ : DyadicInterval 40),(⟨762123381400,762123400729⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4416,0⟩ : DyadicInterval 40),(⟨762123383616,762123405088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨264681496939,265203501707⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨237161392512,237161392576⟩ : DyadicInterval 40),(⟨-302797934848,-302797934784⟩ : DyadicInterval 40),(⟨729950417045,729950436375⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨237582037120,237582037184⟩ : DyadicInterval 40),(⟨-303485655360,-303485655296⟩ : DyadicInterval 40),(⟨729822109811,729822129140⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-65903618240,-65636542272⟩ : DyadicInterval 40),(⟨794941654752,795075212000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨237214741184,237582030272⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-303485644032,-302885117312⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e389_ok : ecellOkT e389 = true := by decide +kernel
theorem e389_pos {a z : ℝ} (ha1 : ((493131/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((24699/102400 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e389 e389_ok ha1 ha2 hz1 hz2 hz

-- box ['24699/102400', '494829/2048000', '999/1000', '1999/2000']  interval_lower 389709975/549755813888
noncomputable def e390 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1364715120885,0,true,237582030208,237582030272⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨834308134667,0,false,-303485644032,-303485643968⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1365170924291,0,true,237949196544,237949196608⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨833852331261,0,false,-304086498880,-304086498816⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1364449917391,0,true,237368342656,237368342720⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨834573338161,0,false,-303136195264,-303136195200⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1365038094643,0,true,237842210048,237842210112⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨833985160909,0,false,-303911364672,-303911364608⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580859714,0,true,69229696,69229760⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442395838,0,false,-69234176,-69234112⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099650354827,0,true,138718272,138718336⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099372900725,0,false,-138735808,-138735744⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511610272,0,false,-17536,-17472⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623417,0,false,-4416,-4352⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1364582515414,0,true,237475188608,237475188672⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨834440740138,0,false,-303310900864,-303310900800⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1365104518770,0,true,237895712128,237895712192⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨833918736782,0,false,-303998940544,-303998940480⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1035356250093,0,false,-66103228416,-66103228352⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1035608187651,0,false,-65835712192,-65835712128⟩
    { al := (24699/102400), au := (494829/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨265203493109,265659296515⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨237582030208,237582030272⟩ : DyadicInterval 40),(⟨-303485644032,-303485643968⟩ : DyadicInterval 40),(⟨729822111918,729822131248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨237949196544,237949196608⟩ : DyadicInterval 40),(⟨-304086498880,-304086498816⟩ : DyadicInterval 40),(⟨729709861591,729709880921⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨237368342656,237368342720⟩ : DyadicInterval 40),(⟨-303136195264,-303136195200⟩ : DyadicInterval 40),(⟨729887331045,729887350374⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨237842210048,237842210112⟩ : DyadicInterval 40),(⟨-303911364672,-303911364608⟩ : DyadicInterval 40),(⟨729742594180,729742613509⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨69231938,138727051⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69229696,69229760⟩ : DyadicInterval 40),(⟨-69234176,-69234112⟩ : DyadicInterval 40),(⟨762123381432,762123400761⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨138718272,138718336⟩ : DyadicInterval 40),(⟨-138735808,-138735744⟩ : DyadicInterval 40),(⟨762123374816,762123394145⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-17536,-4352⟩ : DyadicInterval 40),(⟨762123385792,762123411648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨265070887638,265592890994⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨237475188608,237475188672⟩ : DyadicInterval 40),(⟨-303310900864,-303310900800⟩ : DyadicInterval 40),(⟨729854730898,729854750227⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨237895712128,237895712192⟩ : DyadicInterval 40),(⟨-303998940544,-303998940480⟩ : DyadicInterval 40),(⟨729726227695,729726247025⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-66103228416,-65835712128⟩ : DyadicInterval 40),(⟨795041239680,795175017088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨237582030208,237949196608⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-304086498880,-303485643968⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e390_ok : ecellOkT e390 = true := by decide +kernel
theorem e390_pos {a z : ℝ} (ha1 : ((24699/102400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((494829/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e390 e390_ok ha1 ha2 hz1 hz2 hz

-- box ['494829/2048000', '247839/1024000', '999/1000', '1999/2000']  interval_lower 49751519/68719476736
noncomputable def e391 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1365170924290,0,true,237949196544,237949196608⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨833852331262,0,false,-304086498880,-304086498816⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1365626727695,0,true,238316240320,238316240384⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨833396527857,0,false,-304687682304,-304687682240⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1364905264993,0,true,237735213184,237735213248⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨834117990559,0,false,-303736258304,-303736258240⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1365493670146,0,true,238209106048,238209106112⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨833529585406,0,false,-304512151616,-304512151552⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580989360,0,true,69359360,69359424⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442266192,0,false,-69363776,-69363712⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099650614253,0,true,138977664,138977728⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099372641299,0,false,-138995264,-138995200⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511610207,0,false,-17600,-17536⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623401,0,false,-4416,-4352⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1365038090921,0,true,237842207040,237842207104⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨833985164631,0,false,-303911359744,-303911359680⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1365560208229,0,true,238262681984,238262682048⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨833463047323,0,false,-304599925760,-304599925696⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1035135912801,0,false,-66337243712,-66337243648⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1035388338082,0,false,-66069152640,-66069152576⟩
    { al := (494829/2048000), au := (247839/1024000), zl := (999/1000), zu := (1999/2000),
      A := ⟨265659296514,266115099919⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨237949196544,237949196608⟩ : DyadicInterval 40),(⟨-304086498880,-304086498816⟩ : DyadicInterval 40),(⟨729709861592,729709880921⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨238316240320,238316240384⟩ : DyadicInterval 40),(⟨-304687682304,-304687682240⟩ : DyadicInterval 40),(⟨729597410608,729597429937⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨237735213184,237735213248⟩ : DyadicInterval 40),(⟨-303736258304,-303736258240⟩ : DyadicInterval 40),(⟨729775309681,729775329011⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨238209106048,238209106112⟩ : DyadicInterval 40),(⟨-304512151616,-304512151552⟩ : DyadicInterval 40),(⟨729630257882,729630277212⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨69361584,138986477⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69359360,69359424⟩ : DyadicInterval 40),(⟨-69363776,-69363712⟩ : DyadicInterval 40),(⟨762123381384,762123400713⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨138977664,138977728⟩ : DyadicInterval 40),(⟨-138995264,-138995200⟩ : DyadicInterval 40),(⟨762123374782,762123394112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-17600,-4352⟩ : DyadicInterval 40),(⟨762123385792,762123411680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨265526463145,266048580453⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨237842207040,237842207104⟩ : DyadicInterval 40),(⟨-303911359744,-303911359680⟩ : DyadicInterval 40),(⟨729742595095,729742614424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨238262681984,238262682048⟩ : DyadicInterval 40),(⟨-304599925760,-304599925696⟩ : DyadicInterval 40),(⟨729613834094,729613853423⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-66337243712,-66069152576⟩ : DyadicInterval 40),(⟨795157959904,795292024736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨237949196544,238316240384⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-304687682304,-304086498816⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e391_ok : ecellOkT e391 = true := by decide +kernel
theorem e391_pos {a z : ℝ} (ha1 : ((494829/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((247839/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e391 e391_ok ha1 ha2 hz1 hz2 hz

-- box ['24699/102400', '494829/2048000', '1999/2000', '1']  interval_lower 387696665/549755813888
noncomputable def e392 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1364715120885,0,true,237582030208,237582030272⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨834308134667,0,false,-303485644032,-303485643968⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1365170924291,0,true,237949196544,237949196608⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨833852331261,0,false,-304086498880,-304086498816⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1364582519138,0,true,237475191616,237475191680⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨834440736414,0,false,-303310905792,-303310905728⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580992987,0,true,69363008,69363072⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442262565,0,false,-69367424,-69367360⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623399,0,false,-4416,-4352⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1364648814161,0,true,237528607488,237528607552⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨834374441391,0,false,-303398263744,-303398263680⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1365170932887,0,true,237949203456,237949203520⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨833852322665,0,false,-304086510272,-304086510208⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1035324160714,0,false,-66137306752,-66137306688⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1035576216974,0,false,-65869656192,-65869656128⟩
    { al := (24699/102400), au := (494829/2048000), zl := (1999/2000), zu := 1,
      A := ⟨265203493109,265659296515⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨237582030208,237582030272⟩ : DyadicInterval 40),(⟨-303485644032,-303485643968⟩ : DyadicInterval 40),(⟨729822111918,729822131248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨237949196544,237949196608⟩ : DyadicInterval 40),(⟨-304086498880,-304086498816⟩ : DyadicInterval 40),(⟨729709861591,729709880921⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨237475191616,237475191680⟩ : DyadicInterval 40),(⟨-303310905792,-303310905728⟩ : DyadicInterval 40),(⟨729854729986,729854749315⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨237949196544,237949196608⟩ : DyadicInterval 40),(⟨-304086498880,-304086498816⟩ : DyadicInterval 40),(⟨729709861591,729709880921⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,69365211⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69363008,69363072⟩ : DyadicInterval 40),(⟨-69367424,-69367360⟩ : DyadicInterval 40),(⟨762123381383,762123400713⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4416,0⟩ : DyadicInterval 40),(⟨762123383616,762123405088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨265137186385,265659305111⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨237528607488,237528607552⟩ : DyadicInterval 40),(⟨-303398263744,-303398263680⟩ : DyadicInterval 40),(⟨729838424523,729838443852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨237949203456,237949203520⟩ : DyadicInterval 40),(⟨-304086510272,-304086510208⟩ : DyadicInterval 40),(⟨729709859501,729709878831⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-66137306752,-65869656128⟩ : DyadicInterval 40),(⟨795058211680,795192056256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨237582030208,237949196608⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-304086498880,-303485643968⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e392_ok : ecellOkT e392 = true := by decide +kernel
theorem e392_pos {a z : ℝ} (ha1 : ((24699/102400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((494829/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e392 e392_ok ha1 ha2 hz1 hz2 hz

-- box ['494829/2048000', '247839/1024000', '1999/2000', '1']  interval_lower 791972013/1099511627776
noncomputable def e393 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1365170924290,0,true,237949196544,237949196608⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨833852331262,0,false,-304086498880,-304086498816⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1365626727695,0,true,238316240320,238316240384⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨833396527857,0,false,-304687682304,-304687682240⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1365038094641,0,true,237842210048,237842210112⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨833985160911,0,false,-303911364672,-303911364608⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581122708,0,true,69492672,69492736⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442132844,0,false,-69497152,-69497088⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623383,0,false,-4416,-4352⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1365104503606,0,true,237895699904,237895699968⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨833918751946,0,false,-303998920576,-303998920512⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1365626736285,0,true,238316247232,238316247296⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨833396519267,0,false,-304687693632,-304687693568⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1035103713218,0,false,-66371446336,-66371446272⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1035356257420,0,false,-66103220608,-66103220544⟩
    { al := (494829/2048000), au := (247839/1024000), zl := (1999/2000), zu := 1,
      A := ⟨265659296514,266115099919⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨237949196544,237949196608⟩ : DyadicInterval 40),(⟨-304086498880,-304086498816⟩ : DyadicInterval 40),(⟨729709861592,729709880921⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨238316240320,238316240384⟩ : DyadicInterval 40),(⟨-304687682304,-304687682240⟩ : DyadicInterval 40),(⟨729597410608,729597429937⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨237842210048,237842210112⟩ : DyadicInterval 40),(⟨-303911364672,-303911364608⟩ : DyadicInterval 40),(⟨729742594180,729742613509⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨238316240320,238316240384⟩ : DyadicInterval 40),(⟨-304687682304,-304687682240⟩ : DyadicInterval 40),(⟨729597410608,729597429937⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,69494932⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69492672,69492736⟩ : DyadicInterval 40),(⟨-69497152,-69497088⟩ : DyadicInterval 40),(⟨762123381399,762123400728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4416,0⟩ : DyadicInterval 40),(⟨762123383616,762123405088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨265592875830,266115108509⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨237895699904,237895699968⟩ : DyadicInterval 40),(⟨-303998920576,-303998920512⟩ : DyadicInterval 40),(⟨729726231448,729726250778⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨238316247232,238316247296⟩ : DyadicInterval 40),(⟨-304687693632,-304687693568⟩ : DyadicInterval 40),(⟨729597408488,729597427817⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-66371446336,-66103220544⟩ : DyadicInterval 40),(⟨795174993888,795309126048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨237949196544,238316240384⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-304687682304,-304086498816⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e393_ok : ecellOkT e393 = true := by decide +kernel
theorem e393_pos {a z : ℝ} (ha1 : ((494829/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((247839/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e393 e393_ok ha1 ha2 hz1 hz2 hz

-- box ['247839/1024000', '496527/2048000', '999/1000', '1999/2000']  interval_lower 203186813/274877906944
noncomputable def e394 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1365626727694,0,true,238316240320,238316240384⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨833396527858,0,false,-304687682304,-304687682240⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1366082531099,0,true,238683161600,238683161664⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨832940724453,0,false,-305289194560,-305289194496⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1365360612594,0,true,238101961344,238101961408⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨833662642958,0,false,-304336648960,-304336648896⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1365949245648,0,true,238575879616,238575879680⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨833074009904,0,false,-305113267072,-305113267008⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581119063,0,true,69489088,69489152⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442136489,0,false,-69493504,-69493440⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099650873798,0,true,139237184,139237248⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099372381754,0,false,-139254848,-139254784⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511610141,0,false,-17664,-17600⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623385,0,false,-4416,-4352⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1365493666430,0,true,238209103040,238209103104⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨833529589122,0,false,-304512146752,-304512146688⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1366015897682,0,true,238629529408,238629529472⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨833007357870,0,false,-305201239552,-305201239488⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1034915197793,0,false,-66571710144,-66571710080⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1035168110983,0,false,-66303043648,-66303043584⟩
    { al := (247839/1024000), au := (496527/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨266115099918,266570903323⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨238316240320,238316240384⟩ : DyadicInterval 40),(⟨-304687682304,-304687682240⟩ : DyadicInterval 40),(⟨729597410608,729597429938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨238683161600,238683161664⟩ : DyadicInterval 40),(⟨-305289194560,-305289194496⟩ : DyadicInterval 40),(⟨729484758897,729484778226⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨238101961344,238101961408⟩ : DyadicInterval 40),(⟨-304336648960,-304336648896⟩ : DyadicInterval 40),(⟨729663088055,729663107384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨238575879616,238575879680⟩ : DyadicInterval 40),(⟨-305113267072,-305113267008⟩ : DyadicInterval 40),(⟨729517721135,729517740464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨69491287,139246022⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69489088,69489152⟩ : DyadicInterval 40),(⟨-69493504,-69493440⟩ : DyadicInterval 40),(⟨762123381367,762123400697⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨139237184,139237248⟩ : DyadicInterval 40),(⟨-139254848,-139254784⟩ : DyadicInterval 40),(⟨762123374749,762123394078⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-17664,-4352⟩ : DyadicInterval 40),(⟨762123385792,762123411712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨265982038654,266504269906⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨238209103040,238209103104⟩ : DyadicInterval 40),(⟨-304512146752,-304512146688⟩ : DyadicInterval 40),(⟨729630258823,729630278153⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨238629529408,238629529472⟩ : DyadicInterval 40),(⟨-305201239552,-305201239488⟩ : DyadicInterval 40),(⟨729501239848,729501259177⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-66571710144,-66303043584⟩ : DyadicInterval 40),(⟨795274905408,795409257952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨238316240320,238683161664⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-305289194560,-304687682240⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e394_ok : ecellOkT e394 = true := by decide +kernel
theorem e394_pos {a z : ℝ} (ha1 : ((247839/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((496527/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e394 e394_ok ha1 ha2 hz1 hz2 hz

-- box ['496527/2048000', '15543/64000', '999/1000', '1999/2000']  interval_lower 414794643/549755813888
noncomputable def e395 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1366082531098,0,true,238683161600,238683161664⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨832940724454,0,false,-305289194560,-305289194496⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1366538334503,0,true,239049960512,239049960576⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨832484921049,0,false,-305891036096,-305891036032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1365815960194,0,true,238468587200,238468587264⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨833207295358,0,false,-304937367680,-304937367616⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1366404821150,0,true,238942530944,238942531008⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨832618434402,0,false,-305714711296,-305714711232⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581248827,0,true,69618816,69618880⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442006725,0,false,-69623296,-69623232⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099651133462,0,true,139496832,139496896⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099372122090,0,false,-139514560,-139514496⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511610075,0,false,-17728,-17664⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623368,0,false,-4416,-4352⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1365949241936,0,true,238575876672,238575876736⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨833074013616,0,false,-305113262144,-305113262080⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1366471587148,0,true,238996254528,238996254592⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨832551668404,0,false,-305802882496,-305802882432⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1034694105061,0,false,-66806627904,-66806627840⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1034947506356,0,false,-66537385472,-66537385408⟩
    { al := (496527/2048000), au := (15543/64000), zl := (999/1000), zu := (1999/2000),
      A := ⟨266570903322,267026706727⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨238683161600,238683161664⟩ : DyadicInterval 40),(⟨-305289194560,-305289194496⟩ : DyadicInterval 40),(⟨729484758897,729484778227⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨239049960512,239049960576⟩ : DyadicInterval 40),(⟨-305891036096,-305891036032⟩ : DyadicInterval 40),(⟨729371906419,729371925749⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨238468587200,238468587264⟩ : DyadicInterval 40),(⟨-304937367680,-304937367616⟩ : DyadicInterval 40),(⟨729550666167,729550685496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨238942530944,238942531008⟩ : DyadicInterval 40),(⟨-305714711296,-305714711232⟩ : DyadicInterval 40),(⟨729404983787,729405003116⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨69621051,139505686⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69618816,69618880⟩ : DyadicInterval 40),(⟨-69623296,-69623232⟩ : DyadicInterval 40),(⟨762123381383,762123400712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨139496832,139496896⟩ : DyadicInterval 40),(⟨-139514560,-139514496⟩ : DyadicInterval 40),(⟨762123374715,762123394044⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-17728,-4352⟩ : DyadicInterval 40),(⟨762123385792,762123411744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨266437614160,266959959372⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨238575876672,238575876736⟩ : DyadicInterval 40),(⟨-305113262144,-305113262080⟩ : DyadicInterval 40),(⟨729517722014,729517741344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨238996254528,238996254592⟩ : DyadicInterval 40),(⟨-305802882496,-305802882432⟩ : DyadicInterval 40),(⟨729388444964,729388464294⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-66806627904,-66537385408⟩ : DyadicInterval 40),(⟨795392076320,795526716832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨238683161600,239049960576⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-305891036096,-305289194496⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e395_ok : ecellOkT e395 = true := by decide +kernel
theorem e395_pos {a z : ℝ} (ha1 : ((496527/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((15543/64000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e395 e395_ok ha1 ha2 hz1 hz2 hz

-- box ['247839/1024000', '496527/2048000', '1999/2000', '1']  interval_lower 202167223/274877906944
noncomputable def e396 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1365626727694,0,true,238316240320,238316240384⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨833396527858,0,false,-304687682304,-304687682240⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1366082531099,0,true,238683161600,238683161664⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨832940724453,0,false,-305289194560,-305289194496⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1365493670144,0,true,238209106048,238209106112⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨833529585408,0,false,-304512151616,-304512151552⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581252489,0,true,69622464,69622528⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442003063,0,false,-69626944,-69626880⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623367,0,false,-4416,-4352⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1365560193056,0,true,238262669760,238262669824⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨833463062496,0,false,-304599905728,-304599905664⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1366082539689,0,true,238683168576,238683168640⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨832940715863,0,false,-305289205888,-305289205824⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1034882887812,0,false,-66606037312,-66606037248⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1035135920145,0,false,-66337235904,-66337235840⟩
    { al := (247839/1024000), au := (496527/2048000), zl := (1999/2000), zu := 1,
      A := ⟨266115099918,266570903323⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨238316240320,238316240384⟩ : DyadicInterval 40),(⟨-304687682304,-304687682240⟩ : DyadicInterval 40),(⟨729597410608,729597429938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨238683161600,238683161664⟩ : DyadicInterval 40),(⟨-305289194560,-305289194496⟩ : DyadicInterval 40),(⟨729484758897,729484778226⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨238209106048,238209106112⟩ : DyadicInterval 40),(⟨-304512151616,-304512151552⟩ : DyadicInterval 40),(⟨729630257883,729630277212⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨238683161600,238683161664⟩ : DyadicInterval 40),(⟨-305289194560,-305289194496⟩ : DyadicInterval 40),(⟨729484758897,729484778226⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,69624713⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69622464,69622528⟩ : DyadicInterval 40),(⟨-69626944,-69626880⟩ : DyadicInterval 40),(⟨762123381382,762123400712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4416,0⟩ : DyadicInterval 40),(⟨762123383616,762123405088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨266048565280,266570911913⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨238262669760,238262669824⟩ : DyadicInterval 40),(⟨-304599905728,-304599905664⟩ : DyadicInterval 40),(⟨729613837838,729613857167⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨238683168576,238683168640⟩ : DyadicInterval 40),(⟨-305289205888,-305289205824⟩ : DyadicInterval 40),(⟨729484756729,729484776058⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-66606037312,-66337235840⟩ : DyadicInterval 40),(⟨795292001536,795426421536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨238316240320,238683161664⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-305289194560,-304687682240⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e396_ok : ecellOkT e396 = true := by decide +kernel
theorem e396_pos {a z : ℝ} (ha1 : ((247839/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((496527/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e396 e396_ok ha1 ha2 hz1 hz2 hz

-- box ['496527/2048000', '15543/64000', '1999/2000', '1']  interval_lower 103185569/137438953472
noncomputable def e397 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1366082531098,0,true,238683161600,238683161664⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨832940724454,0,false,-305289194560,-305289194496⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1366538334503,0,true,239049960512,239049960576⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨832484921049,0,false,-305891036096,-305891036032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1365949245646,0,true,238575879616,238575879680⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨833074009906,0,false,-305113267072,-305113267008⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581382330,0,true,69752320,69752384⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441873222,0,false,-69756800,-69756736⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623350,0,false,-4480,-4416⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1366015882499,0,true,238629517248,238629517312⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨833007373053,0,false,-305201219520,-305201219456⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1366538343097,0,true,239049967424,239049967488⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨832484912455,0,false,-305891047424,-305891047360⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1034661684497,0,false,-66841080000,-66841079936⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1034915205155,0,false,-66571702272,-66571702208⟩
    { al := (496527/2048000), au := (15543/64000), zl := (1999/2000), zu := 1,
      A := ⟨266570903322,267026706727⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨238683161600,238683161664⟩ : DyadicInterval 40),(⟨-305289194560,-305289194496⟩ : DyadicInterval 40),(⟨729484758897,729484778227⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨239049960512,239049960576⟩ : DyadicInterval 40),(⟨-305891036096,-305891036032⟩ : DyadicInterval 40),(⟨729371906419,729371925749⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨238575879616,238575879680⟩ : DyadicInterval 40),(⟨-305113267072,-305113267008⟩ : DyadicInterval 40),(⟨729517721135,729517740465⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨239049960512,239049960576⟩ : DyadicInterval 40),(⟨-305891036096,-305891036032⟩ : DyadicInterval 40),(⟨729371906419,729371925749⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,69754554⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69752320,69752384⟩ : DyadicInterval 40),(⟨-69756800,-69756736⟩ : DyadicInterval 40),(⟨762123381366,762123400695⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4480,0⟩ : DyadicInterval 40),(⟨762123383616,762123405120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨266504254723,267026715321⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨238629517248,238629517312⟩ : DyadicInterval 40),(⟨-305201219520,-305201219456⟩ : DyadicInterval 40),(⟨729501243568,729501262898⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨239049967424,239049967488⟩ : DyadicInterval 40),(⟨-305891047424,-305891047360⟩ : DyadicInterval 40),(⟨729371904283,729371923612⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-66841080000,-66571702208⟩ : DyadicInterval 40),(⟨795409234720,795543942880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨238683161600,239049960576⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-305891036096,-305289194496⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e397_ok : ecellOkT e397 = true := by decide +kernel
theorem e397_pos {a z : ℝ} (ha1 : ((496527/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((15543/64000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e397 e397_ok ha1 ha2 hz1 hz2 hz

-- box ['15543/64000', '19929/81920', '999/1000', '1999/2000']  interval_lower 846550891/1099511627776
noncomputable def e398 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1366538334502,0,true,239049960512,239049960576⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨832484921050,0,false,-305891036096,-305891036032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1366994137908,0,true,239416637056,239416637120⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨832029117644,0,false,-306493207232,-306493207168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1366271307795,0,true,238835090816,238835090880⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨832751947757,0,false,-305538414848,-305538414784⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1366860396654,0,true,239309059968,239309060032⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨832162858898,0,false,-306316484736,-306316484672⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581378650,0,true,69748608,69748672⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441876902,0,false,-69753088,-69753024⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099651393245,0,true,139756544,139756608⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099371862307,0,false,-139774400,-139774336⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511610009,0,false,-17792,-17728⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623352,0,false,-4480,-4416⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1366404817438,0,true,238942527936,238942528000⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨832618438114,0,false,-305714706432,-305714706368⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1366927276600,0,true,239362857344,239362857408⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨832095978952,0,false,-306404854784,-306404854720⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1034472634618,0,false,-67041997376,-67041997312⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1034726524201,0,false,-66772178432,-66772178368⟩
    { al := (15543/64000), au := (19929/81920), zl := (999/1000), zu := (1999/2000),
      A := ⟨267026706726,267482510132⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨239049960512,239049960576⟩ : DyadicInterval 40),(⟨-305891036096,-305891036032⟩ : DyadicInterval 40),(⟨729371906419,729371925749⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨239416637056,239416637120⟩ : DyadicInterval 40),(⟨-306493207232,-306493207168⟩ : DyadicInterval 40),(⟨729258853168,729258872497⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨238835090816,238835090880⟩ : DyadicInterval 40),(⟨-305538414848,-305538414784⟩ : DyadicInterval 40),(⟨729438043996,729438063326⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨239309059968,239309060032⟩ : DyadicInterval 40),(⟨-306316484736,-306316484672⟩ : DyadicInterval 40),(⟨729292045918,729292065248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨69750874,139765469⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69748608,69748672⟩ : DyadicInterval 40),(⟨-69753088,-69753024⟩ : DyadicInterval 40),(⟨762123381367,762123400696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨139756544,139756608⟩ : DyadicInterval 40),(⟨-139774400,-139774336⟩ : DyadicInterval 40),(⟨762123374713,762123394042⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-17792,-4416⟩ : DyadicInterval 40),(⟨762123385824,762123411776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨266893189662,267415648824⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨238942527936,238942528000⟩ : DyadicInterval 40),(⟨-305714706432,-305714706368⟩ : DyadicInterval 40),(⟨729404984734,729405004063⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨239362857344,239362857408⟩ : DyadicInterval 40),(⟨-306404854784,-306404854720⟩ : DyadicInterval 40),(⟨729275449393,729275468722⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-67041997376,-66772178368⟩ : DyadicInterval 40),(⟨795509472800,795644401568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨239049960512,239416637120⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-306493207232,-305891036032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e398_ok : ecellOkT e398 = true := by decide +kernel
theorem e398_pos {a z : ℝ} (ha1 : ((15543/64000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((19929/81920 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e398 e398_ok ha1 ha2 hz1 hz2 hz

-- box ['19929/81920', '249537/1024000', '999/1000', '1999/2000']  interval_lower 863632405/1099511627776
noncomputable def e399 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1366994137907,0,true,239416637056,239416637120⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨832029117645,0,false,-306493207232,-306493207168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1367449941312,0,true,239783191424,239783191488⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨831573314240,0,false,-307095708352,-307095708288⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1366726655396,0,true,239201472384,239201472448⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨832296600156,0,false,-306139790656,-306139790592⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1367315972156,0,true,239675466880,239675466944⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨831707283396,0,false,-306918587712,-306918587648⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581508533,0,true,69878528,69878592⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441747019,0,false,-69883008,-69882944⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099651653145,0,true,140016448,140016512⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099371602407,0,false,-140034304,-140034240⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511609943,0,false,-17856,-17792⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623335,0,false,-4480,-4416⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1366860392951,0,true,239309057024,239309057088⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨832162862601,0,false,-306316479872,-306316479808⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1367382966060,0,true,239729337984,239729338048⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨831640289492,0,false,-307007156800,-307007156736⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1034250786452,0,false,-67277818816,-67277818752⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1034505164511,0,false,-67007422784,-67007422720⟩
    { al := (19929/81920), au := (249537/1024000), zl := (999/1000), zu := (1999/2000),
      A := ⟨267482510131,267938313536⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨239416637056,239416637120⟩ : DyadicInterval 40),(⟨-306493207232,-306493207168⟩ : DyadicInterval 40),(⟨729258853168,729258872498⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨239783191424,239783191488⟩ : DyadicInterval 40),(⟨-307095708352,-307095708288⟩ : DyadicInterval 40),(⟨729145599040,729145618369⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨239201472384,239201472448⟩ : DyadicInterval 40),(⟨-306139790656,-306139790592⟩ : DyadicInterval 40),(⟨729325221367,729325240697⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨239675466880,239675466944⟩ : DyadicInterval 40),(⟨-306918587712,-306918587648⟩ : DyadicInterval 40),(⟨729178907404,729178926734⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨69880757,140025369⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69878528,69878592⟩ : DyadicInterval 40),(⟨-69883008,-69882944⟩ : DyadicInterval 40),(⟨762123381350,762123400679⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨140016448,140016512⟩ : DyadicInterval 40),(⟨-140034304,-140034240⟩ : DyadicInterval 40),(⟨762123374647,762123393976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-17856,-4416⟩ : DyadicInterval 40),(⟨762123385824,762123411808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨267348765175,267871338284⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨239309057024,239309057088⟩ : DyadicInterval 40),(⟨-306316479872,-306316479808⟩ : DyadicInterval 40),(⟨729292046827,729292066156⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨239729337984,239729338048⟩ : DyadicInterval 40),(⟨-307007156800,-307007156736⟩ : DyadicInterval 40),(⟨729162253066,729162272395⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-67277818816,-67007422720⟩ : DyadicInterval 40),(⟨795627094976,795762312288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨239416637056,239783191488⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-307095708352,-306493207168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e399_ok : ecellOkT e399 = true := by decide +kernel
theorem e399_pos {a z : ℝ} (ha1 : ((19929/81920 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((249537/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e399 e399_ok ha1 ha2 hz1 hz2 hz

-- box ['15543/64000', '19929/81920', '1999/2000', '1']  interval_lower 842420021/1099511627776
noncomputable def e400 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1366538334502,0,true,239049960512,239049960576⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨832484921050,0,false,-305891036096,-305891036032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1366994137908,0,true,239416637056,239416637120⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨832029117644,0,false,-306493207232,-306493207168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1366404821148,0,true,238942530944,238942531008⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨832618434404,0,false,-305714711296,-305714711232⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581512230,0,true,69882176,69882240⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441743322,0,false,-69886720,-69886656⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623334,0,false,-4480,-4416⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1366471571954,0,true,238996242304,238996242368⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨832551683598,0,false,-305802862400,-305802862336⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1366994146499,0,true,239416643968,239416644032⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨832029109053,0,false,-306493218560,-306493218496⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1034440103278,0,false,-67076574528,-67076574464⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1034694112440,0,false,-66806620096,-66806620032⟩
    { al := (15543/64000), au := (19929/81920), zl := (1999/2000), zu := 1,
      A := ⟨267026706726,267482510132⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨239049960512,239049960576⟩ : DyadicInterval 40),(⟨-305891036096,-305891036032⟩ : DyadicInterval 40),(⟨729371906419,729371925749⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨239416637056,239416637120⟩ : DyadicInterval 40),(⟨-306493207232,-306493207168⟩ : DyadicInterval 40),(⟨729258853168,729258872497⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨238942530944,238942531008⟩ : DyadicInterval 40),(⟨-305714711296,-305714711232⟩ : DyadicInterval 40),(⟨729404983787,729405003117⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨239416637056,239416637120⟩ : DyadicInterval 40),(⟨-306493207232,-306493207168⟩ : DyadicInterval 40),(⟨729258853168,729258872497⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,69884454⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69882176,69882240⟩ : DyadicInterval 40),(⟨-69886720,-69886656⟩ : DyadicInterval 40),(⟨762123381382,762123400711⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4480,0⟩ : DyadicInterval 40),(⟨762123383616,762123405120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨266959944178,267482518723⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨238996242304,238996242368⟩ : DyadicInterval 40),(⟨-305802862400,-305802862336⟩ : DyadicInterval 40),(⟨729388448716,729388468045⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨239416643968,239416644032⟩ : DyadicInterval 40),(⟨-306493218560,-306493218496⟩ : DyadicInterval 40),(⟨729258851025,729258870354⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-67076574528,-66806620032⟩ : DyadicInterval 40),(⟨795526693632,795661690144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨239049960512,239416637120⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-306493207232,-305891036032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e400_ok : ecellOkT e400 = true := by decide +kernel
theorem e400_pos {a z : ℝ} (ha1 : ((15543/64000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((19929/81920 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e400 e400_ok ha1 ha2 hz1 hz2 hz

-- box ['19929/81920', '249537/1024000', '1999/2000', '1']  interval_lower 53717183/68719476736
noncomputable def e401 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1366994137907,0,true,239416637056,239416637120⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨832029117645,0,false,-306493207232,-306493207168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1367449941312,0,true,239783191424,239783191488⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨831573314240,0,false,-307095708352,-307095708288⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1366860396651,0,true,239309059968,239309060032⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨832162858901,0,false,-306316484736,-306316484672⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581642189,0,true,70012160,70012224⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441613363,0,false,-70016704,-70016640⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623317,0,false,-4480,-4416⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1366927261395,0,true,239362845120,239362845184⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨832095994157,0,false,-306404834688,-306404834624⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1367449949912,0,true,239783198336,239783198400⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨831573305640,0,false,-307095719680,-307095719616⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1034218144146,0,false,-67312521344,-67312521280⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1034472642015,0,false,-67041989504,-67041989440⟩
    { al := (19929/81920), au := (249537/1024000), zl := (1999/2000), zu := 1,
      A := ⟨267482510131,267938313536⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨239416637056,239416637120⟩ : DyadicInterval 40),(⟨-306493207232,-306493207168⟩ : DyadicInterval 40),(⟨729258853168,729258872498⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨239783191424,239783191488⟩ : DyadicInterval 40),(⟨-307095708352,-307095708288⟩ : DyadicInterval 40),(⟨729145599040,729145618369⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨239309059968,239309060032⟩ : DyadicInterval 40),(⟨-306316484736,-306316484672⟩ : DyadicInterval 40),(⟨729292045919,729292065249⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨239783191424,239783191488⟩ : DyadicInterval 40),(⟨-307095708352,-307095708288⟩ : DyadicInterval 40),(⟨729145599040,729145618369⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,70014413⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70012160,70012224⟩ : DyadicInterval 40),(⟨-70016704,-70016640⟩ : DyadicInterval 40),(⟨762123381365,762123400694⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4480,0⟩ : DyadicInterval 40),(⟨762123383616,762123405120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨267415633619,267938322136⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨239362845120,239362845184⟩ : DyadicInterval 40),(⟨-306404834688,-306404834624⟩ : DyadicInterval 40),(⟨729275453161,729275472490⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨239783198336,239783198400⟩ : DyadicInterval 40),(⟨-307095719680,-307095719616⟩ : DyadicInterval 40),(⟨729145596887,729145616216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-67312521344,-67041989440⟩ : DyadicInterval 40),(⟨795644378336,795779663552⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨239416637056,239783191488⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-307095708352,-306493207168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e401_ok : ecellOkT e401 = true := by decide +kernel
theorem e401_pos {a z : ℝ} (ha1 : ((19929/81920 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((249537/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e401 e401_ok ha1 ha2 hz1 hz2 hz

-- box ['249537/1024000', '499923/2048000', '999/1000', '1999/2000']  interval_lower 880834975/1099511627776
noncomputable def e402 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1367449941311,0,true,239783191424,239783191488⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨831573314241,0,false,-307095708352,-307095708288⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1367905744716,0,true,240149623552,240149623616⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨831117510836,0,false,-307698539776,-307698539712⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1367182002997,0,true,239567731840,239567731904⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨831841252555,0,false,-306741495616,-306741495552⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1367771547658,0,true,240041751744,240041751808⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨831251707894,0,false,-307521020608,-307521020544⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581638475,0,true,70008448,70008512⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441617077,0,false,-70012992,-70012928⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099651913165,0,true,140276416,140276480⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099371342387,0,false,-140294400,-140294336⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511609877,0,false,-17920,-17856⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623319,0,false,-4480,-4416⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1367315968461,0,true,239675463936,239675464000⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨831707287091,0,false,-306918582848,-306918582784⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1367838655514,0,true,240095696512,240095696576⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨831184600038,0,false,-307609788928,-307609788864⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1034028560570,0,false,-67514092416,-67514092352⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1034283427294,0,false,-67243118848,-67243118784⟩
    { al := (249537/1024000), au := (499923/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨267938313535,268394116940⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨239783191424,239783191488⟩ : DyadicInterval 40),(⟨-307095708352,-307095708288⟩ : DyadicInterval 40),(⟨729145599040,729145618369⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨240149623552,240149623616⟩ : DyadicInterval 40),(⟨-307698539776,-307698539712⟩ : DyadicInterval 40),(⟨729032144066,729032163396⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨239567731840,239567731904⟩ : DyadicInterval 40),(⟨-306741495616,-306741495552⟩ : DyadicInterval 40),(⟨729212198386,729212217715⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨240041751744,240041751808⟩ : DyadicInterval 40),(⟨-307521020608,-307521020544⟩ : DyadicInterval 40),(⟨729065568220,729065587549⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨70010699,140285389⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70008448,70008512⟩ : DyadicInterval 40),(⟨-70012992,-70012928⟩ : DyadicInterval 40),(⟨762123381365,762123400695⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨140276416,140276480⟩ : DyadicInterval 40),(⟨-140294400,-140294336⟩ : DyadicInterval 40),(⟨762123374645,762123393974⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-17920,-4416⟩ : DyadicInterval 40),(⟨762123385824,762123411840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨267804340685,268327027738⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨239675463936,239675464000⟩ : DyadicInterval 40),(⟨-306918582848,-306918582784⟩ : DyadicInterval 40),(⟨729178908313,729178927643⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨240095696512,240095696576⟩ : DyadicInterval 40),(⟨-307609788928,-307609788864⟩ : DyadicInterval 40),(⟨729048855963,729048875292⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-67514092416,-67243118784⟩ : DyadicInterval 40),(⟨795744943008,795880449088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨239783191424,240149623616⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-307698539776,-307095708288⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e402_ok : ecellOkT e402 = true := by decide +kernel
theorem e402_pos {a z : ℝ} (ha1 : ((249537/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((499923/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e402 e402_ok ha1 ha2 hz1 hz2 hz

-- box ['499923/2048000', '125193/512000', '999/1000', '1999/2000']  interval_lower 112269831/137438953472
noncomputable def e403 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1367905744715,0,true,240149623552,240149623616⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨831117510837,0,false,-307698539776,-307698539712⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1368361548121,0,true,240515933632,240515933696⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨830661707431,0,false,-308301701952,-308301701888⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1367637350598,0,true,239933869376,239933869440⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨831385904954,0,false,-307343530048,-307343529984⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1368227123162,0,true,240407914624,240407914688⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨830796132390,0,false,-308123783680,-308123783616⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581768477,0,true,70138432,70138496⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441487075,0,false,-70142976,-70142912⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099652173306,0,true,140536512,140536576⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099371082246,0,false,-140554560,-140554496⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511609810,0,false,-17984,-17920⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623302,0,false,-4480,-4416⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1367771543967,0,true,240041748800,240041748864⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨831251711585,0,false,-307521015680,-307521015616⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1368294344976,0,true,240461932992,240461933056⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨830728910576,0,false,-308212751552,-308212751488⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1033805956966,0,false,-67750818560,-67750818496⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1034061312548,0,false,-67479266880,-67479266816⟩
    { al := (499923/2048000), au := (125193/512000), zl := (999/1000), zu := (1999/2000),
      A := ⟨268394116939,268849920345⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨240149623552,240149623616⟩ : DyadicInterval 40),(⟨-307698539776,-307698539712⟩ : DyadicInterval 40),(⟨729032144067,729032163396⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨240515933632,240515933696⟩ : DyadicInterval 40),(⟨-308301701952,-308301701888⟩ : DyadicInterval 40),(⟨728918488168,728918507498⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨239933869376,239933869440⟩ : DyadicInterval 40),(⟨-307343530048,-307343529984⟩ : DyadicInterval 40),(⟨729098974924,729098994254⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨240407914624,240407914688⟩ : DyadicInterval 40),(⟨-308123783680,-308123783616⟩ : DyadicInterval 40),(⟨728952028292,728952047622⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨70140701,140545530⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70138432,70138496⟩ : DyadicInterval 40),(⟨-70142976,-70142912⟩ : DyadicInterval 40),(⟨762123381349,762123400678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨140536512,140536576⟩ : DyadicInterval 40),(⟨-140554560,-140554496⟩ : DyadicInterval 40),(⟨762123374610,762123393939⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-17984,-4416⟩ : DyadicInterval 40),(⟨762123385824,762123411872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨268259916191,268782717200⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨240041748800,240041748864⟩ : DyadicInterval 40),(⟨-307521015680,-307521015616⟩ : DyadicInterval 40),(⟨729065569107,729065588437⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨240461932992,240461933056⟩ : DyadicInterval 40),(⟨-308212751552,-308212751488⟩ : DyadicInterval 40),(⟨728935258056,728935277386⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-67750818560,-67479266816⟩ : DyadicInterval 40),(⟨795863017024,795998812160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨240149623552,240515933696⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-308301701952,-307698539712⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e403_ok : ecellOkT e403 = true := by decide +kernel
theorem e403_pos {a z : ℝ} (ha1 : ((499923/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((125193/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e403 e403_ok ha1 ha2 hz1 hz2 hz

-- box ['249537/1024000', '499923/2048000', '1999/2000', '1']  interval_lower 109581339/137438953472
noncomputable def e404 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1367449941311,0,true,239783191424,239783191488⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨831573314241,0,false,-307095708352,-307095708288⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1367905744716,0,true,240149623552,240149623616⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨831117510836,0,false,-307698539776,-307698539712⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1367315972154,0,true,239675466880,239675466944⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨831707283398,0,false,-306918587712,-306918587648⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581772208,0,true,70142144,70142208⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441483344,0,false,-70146688,-70146624⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623301,0,false,-4480,-4416⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1367382950846,0,true,239729325760,239729325824⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨831640304706,0,false,-307007136704,-307007136640⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1367905753312,0,true,240149630464,240149630528⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨831117502240,0,false,-307698551168,-307698551104⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1033995807113,0,false,-67548920640,-67548920576⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1034250793866,0,false,-67277810880,-67277810816⟩
    { al := (249537/1024000), au := (499923/2048000), zl := (1999/2000), zu := 1,
      A := ⟨267938313535,268394116940⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨239783191424,239783191488⟩ : DyadicInterval 40),(⟨-307095708352,-307095708288⟩ : DyadicInterval 40),(⟨729145599040,729145618369⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨240149623552,240149623616⟩ : DyadicInterval 40),(⟨-307698539776,-307698539712⟩ : DyadicInterval 40),(⟨729032144066,729032163396⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨239675466880,239675466944⟩ : DyadicInterval 40),(⟨-306918587712,-306918587648⟩ : DyadicInterval 40),(⟨729178907405,729178926734⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨240149623552,240149623616⟩ : DyadicInterval 40),(⟨-307698539776,-307698539712⟩ : DyadicInterval 40),(⟨729032144066,729032163396⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,70144432⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70142144,70142208⟩ : DyadicInterval 40),(⟨-70146688,-70146624⟩ : DyadicInterval 40),(⟨762123381348,762123400678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4480,0⟩ : DyadicInterval 40),(⟨762123383616,762123405120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨267871323070,268394125536⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨239729325760,239729325824⟩ : DyadicInterval 40),(⟨-307007136704,-307007136640⟩ : DyadicInterval 40),(⟨729162256849,729162276179⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨240149630464,240149630528⟩ : DyadicInterval 40),(⟨-307698551168,-307698551104⟩ : DyadicInterval 40),(⟨729032141931,729032161260⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-67548920640,-67277810816⟩ : DyadicInterval 40),(⟨795762289024,795897863200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨239783191424,240149623616⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-307698539776,-307095708288⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e404_ok : ecellOkT e404 = true := by decide +kernel
theorem e404_pos {a z : ℝ} (ha1 : ((249537/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((499923/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e404 e404_ok ha1 ha2 hz1 hz2 hz

-- box ['499923/2048000', '125193/512000', '1999/2000', '1']  interval_lower 893947421/1099511627776
noncomputable def e405 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1367905744715,0,true,240149623552,240149623616⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨831117510837,0,false,-307698539776,-307698539712⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1368361548121,0,true,240515933632,240515933696⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨830661707431,0,false,-308301701952,-308301701888⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1367771547656,0,true,240041751744,240041751808⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨831251707896,0,false,-307521020608,-307521020544⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581902287,0,true,70272256,70272320⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441353265,0,false,-70276800,-70276736⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623284,0,false,-4544,-4480⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1367838640290,0,true,240095684224,240095684288⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨831184615262,0,false,-307609768768,-307609768704⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1368361556713,0,true,240515940544,240515940608⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨830661698839,0,false,-308301713280,-308301713216⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1033773092172,0,false,-67785772736,-67785772672⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1034028568002,0,false,-67514084544,-67514084480⟩
    { al := (499923/2048000), au := (125193/512000), zl := (1999/2000), zu := 1,
      A := ⟨268394116939,268849920345⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨240149623552,240149623616⟩ : DyadicInterval 40),(⟨-307698539776,-307698539712⟩ : DyadicInterval 40),(⟨729032144067,729032163396⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨240515933632,240515933696⟩ : DyadicInterval 40),(⟨-308301701952,-308301701888⟩ : DyadicInterval 40),(⟨728918488168,728918507498⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨240041751744,240041751808⟩ : DyadicInterval 40),(⟨-307521020608,-307521020544⟩ : DyadicInterval 40),(⟨729065568220,729065587550⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨240515933632,240515933696⟩ : DyadicInterval 40),(⟨-308301701952,-308301701888⟩ : DyadicInterval 40),(⟨728918488168,728918507498⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,70274511⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70272256,70272320⟩ : DyadicInterval 40),(⟨-70276800,-70276736⟩ : DyadicInterval 40),(⟨762123381332,762123400661⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4544,0⟩ : DyadicInterval 40),(⟨762123383616,762123405152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨268327012514,268849928937⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨240095684224,240095684288⟩ : DyadicInterval 40),(⟨-307609768768,-307609768704⟩ : DyadicInterval 40),(⟨729048859778,729048879107⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨240515940544,240515940608⟩ : DyadicInterval 40),(⟨-308301713280,-308301713216⟩ : DyadicInterval 40),(⟨728918486002,728918505332⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-67785772736,-67514084480⟩ : DyadicInterval 40),(⟨795880425856,796016289248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨240149623552,240515933696⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-308301701952,-307698539712⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e405_ok : ecellOkT e405 = true := by decide +kernel
theorem e405_pos {a z : ℝ} (ha1 : ((499923/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((125193/512000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e405 e405_ok ha1 ha2 hz1 hz2 hz

-- box ['125193/512000', '501621/2048000', '999/1000', '1999/2000']  interval_lower 915604037/1099511627776
noncomputable def e406 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1368361548120,0,true,240515933632,240515933696⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨830661707432,0,false,-308301701952,-308301701888⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1368817351525,0,true,240882121728,240882121792⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨830205904027,0,false,-308905195136,-308905195072⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1368092698199,0,true,240299884992,240299885056⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨830930557353,0,false,-307945894272,-307945894208⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1368682698664,0,true,240773955584,240773955648⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨830340556888,0,false,-308726877440,-308726877376⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581898537,0,true,70268480,70268544⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441357015,0,false,-70273024,-70272960⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099652433565,0,true,140796736,140796800⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099370821987,0,false,-140814848,-140814784⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511609744,0,false,-18048,-17984⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623285,0,false,-4544,-4480⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1368227119472,0,true,240407911680,240407911744⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨830796136080,0,false,-308123778816,-308123778752⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1368750034434,0,true,240828047488,240828047552⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨830273221118,0,false,-308816045056,-308816044992⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1033582975646,0,false,-67987997504,-67987997440⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1033838820274,0,false,-67715867136,-67715867072⟩
    { al := (125193/512000), au := (501621/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨268849920344,269305723749⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨240515933632,240515933696⟩ : DyadicInterval 40),(⟨-308301701952,-308301701888⟩ : DyadicInterval 40),(⟨728918488169,728918507498⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨240882121728,240882121792⟩ : DyadicInterval 40),(⟨-308905195136,-308905195072⟩ : DyadicInterval 40),(⟨728804631272,728804650602⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨240299884992,240299885056⟩ : DyadicInterval 40),(⟨-307945894272,-307945894208⟩ : DyadicInterval 40),(⟨728985550975,728985570305⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨240773955584,240773955648⟩ : DyadicInterval 40),(⟨-308726877440,-308726877376⟩ : DyadicInterval 40),(⟨728838287647,728838306977⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨70270761,140805789⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70268480,70268544⟩ : DyadicInterval 40),(⟨-70273024,-70272960⟩ : DyadicInterval 40),(⟨762123381332,762123400662⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨140796736,140796800⟩ : DyadicInterval 40),(⟨-140814848,-140814784⟩ : DyadicInterval 40),(⟨762123374575,762123393905⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-18048,-4480⟩ : DyadicInterval 40),(⟨762123385856,762123411904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨268715491696,269238406658⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨240407911680,240407911744⟩ : DyadicInterval 40),(⟨-308123778816,-308123778752⟩ : DyadicInterval 40),(⟨728952029207,728952048536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨240828047488,240828047552⟩ : DyadicInterval 40),(⟨-308816045056,-308816044992⟩ : DyadicInterval 40),(⟨728821459324,728821478654⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-67987997504,-67715867072⟩ : DyadicInterval 40),(⟨795981317152,796117401632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨240515933632,240882121792⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-308905195136,-308301701888⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e406_ok : ecellOkT e406 = true := by decide +kernel
theorem e406_pos {a z : ℝ} (ha1 : ((125193/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((501621/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e406 e406_ok ha1 ha2 hz1 hz2 hz

-- box ['501621/2048000', '50247/204800', '999/1000', '1999/2000']  interval_lower 466585805/549755813888
noncomputable def e407 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1368817351524,0,true,240882121728,240882121792⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨830205904028,0,false,-308905195136,-308905195072⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1369273154929,0,true,241248187904,241248187968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨829750100623,0,false,-309509019776,-309509019712⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1368548045800,0,true,240665778816,240665778880⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨830475209752,0,false,-308548588672,-308548588608⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1369138274166,0,true,241139874752,241139874816⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨829884981386,0,false,-309330302208,-309330302144⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582028658,0,true,70398592,70398656⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441226894,0,false,-70403136,-70403072⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099652693946,0,true,141057088,141057152⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099370561606,0,false,-141075264,-141075200⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511609677,0,false,-18112,-18048⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623269,0,false,-4544,-4480⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1368682694984,0,true,240773952640,240773952704⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨830340560568,0,false,-308726872576,-308726872512⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1369205723890,0,true,241194040192,241194040256⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨829817531662,0,false,-309419669696,-309419669632⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1033359616609,0,false,-68225629504,-68225629440⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1033615950467,0,false,-67952919872,-67952919808⟩
    { al := (501621/2048000), au := (50247/204800), zl := (999/1000), zu := (1999/2000),
      A := ⟨269305723748,269761527153⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨240882121728,240882121792⟩ : DyadicInterval 40),(⟨-308905195136,-308905195072⟩ : DyadicInterval 40),(⟨728804631273,728804650602⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨241248187904,241248187968⟩ : DyadicInterval 40),(⟨-309509019776,-309509019712⟩ : DyadicInterval 40),(⟨728690573378,728690592708⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨240665778816,240665778880⟩ : DyadicInterval 40),(⟨-308548588672,-308548588608⟩ : DyadicInterval 40),(⟨728871926474,728871945804⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨241139874752,241139874816⟩ : DyadicInterval 40),(⟨-309330302208,-309330302144⟩ : DyadicInterval 40),(⟨728724346195,728724365524⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨70400882,141066170⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70398592,70398656⟩ : DyadicInterval 40),(⟨-70403136,-70403072⟩ : DyadicInterval 40),(⟨762123381316,762123400645⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨141057088,141057152⟩ : DyadicInterval 40),(⟨-141075264,-141075200⟩ : DyadicInterval 40),(⟨762123374541,762123393870⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-18112,-4480⟩ : DyadicInterval 40),(⟨762123385856,762123411936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨269171067208,269694096114⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨240773952640,240773952704⟩ : DyadicInterval 40),(⟨-308726872576,-308726872512⟩ : DyadicInterval 40),(⟨728838288562,728838307892⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨241194040192,241194040256⟩ : DyadicInterval 40),(⟨-309419669696,-309419669632⟩ : DyadicInterval 40),(⟨728707459614,728707478943⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-68225629504,-67952919808⟩ : DyadicInterval 40),(⟨796099843520,796236217632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨240882121728,241248187968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-309509019776,-308905195072⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e407_ok : ecellOkT e407 = true := by decide +kernel
theorem e407_pos {a z : ℝ} (ha1 : ((501621/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((50247/204800 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e407 e407_ok ha1 ha2 hz1 hz2 hz

-- box ['125193/512000', '501621/2048000', '1999/2000', '1']  interval_lower 14240089/17179869184
noncomputable def e408 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1368361548120,0,true,240515933632,240515933696⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨830661707432,0,false,-308301701952,-308301701888⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1368817351525,0,true,240882121728,240882121792⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨830205904027,0,false,-308905195136,-308905195072⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1368227123159,0,true,240407914624,240407914688⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨830796132393,0,false,-308123783680,-308123783616⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582032426,0,true,70402368,70402432⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441223126,0,false,-70406912,-70406848⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623267,0,false,-4544,-4480⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1368294329740,0,true,240461920704,240461920768⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨830728925812,0,false,-308212731392,-308212731328⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1368817360122,0,true,240882128640,240882128704⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨830205895430,0,false,-308905206528,-308905206464⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1033549999319,0,false,-68023077824,-68023077760⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1033805964416,0,false,-67750810624,-67750810560⟩
    { al := (125193/512000), au := (501621/2048000), zl := (1999/2000), zu := 1,
      A := ⟨268849920344,269305723749⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨240515933632,240515933696⟩ : DyadicInterval 40),(⟨-308301701952,-308301701888⟩ : DyadicInterval 40),(⟨728918488169,728918507498⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨240882121728,240882121792⟩ : DyadicInterval 40),(⟨-308905195136,-308905195072⟩ : DyadicInterval 40),(⟨728804631272,728804650602⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨240407914624,240407914688⟩ : DyadicInterval 40),(⟨-308123783680,-308123783616⟩ : DyadicInterval 40),(⟨728952028293,728952047622⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨240882121728,240882121792⟩ : DyadicInterval 40),(⟨-308905195136,-308905195072⟩ : DyadicInterval 40),(⟨728804631272,728804650602⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,70404650⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70402368,70402432⟩ : DyadicInterval 40),(⟨-70406912,-70406848⟩ : DyadicInterval 40),(⟨762123381315,762123400644⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4544,0⟩ : DyadicInterval 40),(⟨762123383616,762123405152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨268782701964,269305732346⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨240461920704,240461920768⟩ : DyadicInterval 40),(⟨-308212731392,-308212731328⟩ : DyadicInterval 40),(⟨728935261887,728935281217⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨240882128640,240882128704⟩ : DyadicInterval 40),(⟨-308905206528,-308905206464⟩ : DyadicInterval 40),(⟨728804629122,728804648451⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-68023077824,-67750810560⟩ : DyadicInterval 40),(⟨795998788896,796134941792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨240515933632,240882121792⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-308905195136,-308301701888⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e408_ok : ecellOkT e408 = true := by decide +kernel
theorem e408_pos {a z : ℝ} (ha1 : ((125193/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((501621/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e408 e408_ok ha1 ha2 hz1 hz2 hz

-- box ['501621/2048000', '50247/204800', '1999/2000', '1']  interval_lower 928906581/1099511627776
noncomputable def e409 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1368817351524,0,true,240882121728,240882121792⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨830205904028,0,false,-308905195136,-308905195072⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1369273154929,0,true,241248187904,241248187968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨829750100623,0,false,-309509019776,-309509019712⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1368682698662,0,true,240773955584,240773955648⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨830340556890,0,false,-308726877440,-308726877376⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582162624,0,true,70532544,70532608⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441092928,0,false,-70537152,-70537088⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623251,0,false,-4544,-4480⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1368750019188,0,true,240828035264,240828035328⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨830273236364,0,false,-308816024832,-308816024768⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1369273163527,0,true,241248194816,241248194880⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨829750092025,0,false,-309509031168,-309509031104⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1033326528562,0,false,-68260836288,-68260836224⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1033582983114,0,false,-67987989568,-67987989504⟩
    { al := (501621/2048000), au := (50247/204800), zl := (1999/2000), zu := 1,
      A := ⟨269305723748,269761527153⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨240882121728,240882121792⟩ : DyadicInterval 40),(⟨-308905195136,-308905195072⟩ : DyadicInterval 40),(⟨728804631273,728804650602⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨241248187904,241248187968⟩ : DyadicInterval 40),(⟨-309509019776,-309509019712⟩ : DyadicInterval 40),(⟨728690573378,728690592708⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨240773955584,240773955648⟩ : DyadicInterval 40),(⟨-308726877440,-308726877376⟩ : DyadicInterval 40),(⟨728838287647,728838306977⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨241248187904,241248187968⟩ : DyadicInterval 40),(⟨-309509019776,-309509019712⟩ : DyadicInterval 40),(⟨728690573378,728690592708⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,70534848⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70532544,70532608⟩ : DyadicInterval 40),(⟨-70537152,-70537088⟩ : DyadicInterval 40),(⟨762123381330,762123400660⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4544,0⟩ : DyadicInterval 40),(⟨762123383616,762123405152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨269238391412,269761535751⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨240828035264,240828035328⟩ : DyadicInterval 40),(⟨-308816024832,-308816024768⟩ : DyadicInterval 40),(⟨728821463108,728821482437⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨241248194816,241248194880⟩ : DyadicInterval 40),(⟨-309509031168,-309509031104⟩ : DyadicInterval 40),(⟨728690571219,728690590549⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-68260836288,-67987989504⟩ : DyadicInterval 40),(⟨796117378368,796253821024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨240882121728,241248187968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-309509019776,-308905195072⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e409_ok : ecellOkT e409 = true := by decide +kernel
theorem e409_pos {a z : ℝ} (ha1 : ((501621/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((50247/204800 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e409 e409_ok ha1 ha2 hz1 hz2 hz

-- box ['50247/204800', '503319/2048000', '999/1000', '1999/2000']  interval_lower 475431087/549755813888
noncomputable def e410 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1369273154928,0,true,241248187904,241248187968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨829750100624,0,false,-309509019776,-309509019712⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1369728958333,0,true,241614132224,241614132288⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨829294297219,0,false,-310113176128,-310113176064⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1369003393400,0,true,241031550976,241031551040⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨830019862152,0,false,-309151613696,-309151613632⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1369593849668,0,true,241505672192,241505672256⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨829429405884,0,false,-309934058240,-309934058176⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582158840,0,true,70528768,70528832⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441096712,0,false,-70533376,-70533312⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099652954447,0,true,141317568,141317632⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099370301105,0,false,-141335808,-141335744⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511609610,0,false,-18176,-18112⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623252,0,false,-4544,-4480⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1369138270493,0,true,241139871808,241139871872⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨829884985059,0,false,-309330297344,-309330297280⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1369661413356,0,true,241559911040,241559911104⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨829361842196,0,false,-310023625984,-310023625920⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1033135879848,0,false,-68463714880,-68463714816⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1033392703132,0,false,-68190425472,-68190425408⟩
    { al := (50247/204800), au := (503319/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨269761527152,270217330557⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨241248187904,241248187968⟩ : DyadicInterval 40),(⟨-309509019776,-309509019712⟩ : DyadicInterval 40),(⟨728690573378,728690592708⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨241614132224,241614132288⟩ : DyadicInterval 40),(⟨-310113176128,-310113176064⟩ : DyadicInterval 40),(⟨728576314411,728576333741⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨241031550976,241031551040⟩ : DyadicInterval 40),(⟨-309151613696,-309151613632⟩ : DyadicInterval 40),(⟨728758101382,728758120712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨241505672192,241505672256⟩ : DyadicInterval 40),(⟨-309934058240,-309934058176⟩ : DyadicInterval 40),(⟨728610203862,728610223191⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨70531064,141326671⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70528768,70528832⟩ : DyadicInterval 40),(⟨-70533376,-70533312⟩ : DyadicInterval 40),(⟨762123381331,762123400660⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨141317568,141317632⟩ : DyadicInterval 40),(⟨-141335808,-141335744⟩ : DyadicInterval 40),(⟨762123374506,762123393835⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-18176,-4480⟩ : DyadicInterval 40),(⟨762123385856,762123411968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨269626642717,270149785580⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨241139871808,241139871872⟩ : DyadicInterval 40),(⟨-309330297344,-309330297280⟩ : DyadicInterval 40),(⟨728724347111,728724366441⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨241559911040,241559911104⟩ : DyadicInterval 40),(⟨-310023625984,-310023625920⟩ : DyadicInterval 40),(⟨728593259025,728593278354⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-68463714880,-68190425408⟩ : DyadicInterval 40),(⟨796218596320,796355260320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨241248187904,241614132288⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-310113176128,-309509019712⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e410_ok : ecellOkT e410 = true := by decide +kernel
theorem e410_pos {a z : ℝ} (ha1 : ((50247/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((503319/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e410 e410_ok ha1 ha2 hz1 hz2 hz

-- box ['503319/2048000', '63021/256000', '999/1000', '1999/2000']  interval_lower 968676161/1099511627776
noncomputable def e411 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1369728958332,0,true,241614132224,241614132288⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨829294297220,0,false,-310113176128,-310113176064⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1370184761738,0,true,241979954816,241979954880⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨828838493814,0,false,-310717664704,-310717664640⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1369458741001,0,true,241397201408,241397201472⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨829564514551,0,false,-309754969536,-309754969472⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1370049425172,0,true,241871347968,241871348032⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨828973830380,0,false,-310538146048,-310538145984⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582289081,0,true,70659008,70659072⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099440966471,0,false,-70663616,-70663552⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099653215068,0,true,141578176,141578240⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099370040484,0,false,-141596416,-141596352⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511609543,0,false,-18240,-18176⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623235,0,false,-4544,-4480⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1369593846002,0,true,241505669248,241505669312⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨829429409550,0,false,-309934053376,-309934053312⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1370117102816,0,true,241925660224,241925660288⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨828906152736,0,false,-310627914176,-310627914112⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1032911765371,0,false,-68702253888,-68702253824⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1033169078267,0,false,-68428384128,-68428384064⟩
    { al := (503319/2048000), au := (63021/256000), zl := (999/1000), zu := (1999/2000),
      A := ⟨270217330556,270673133962⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨241614132224,241614132288⟩ : DyadicInterval 40),(⟨-310113176128,-310113176064⟩ : DyadicInterval 40),(⟨728576314412,728576333741⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨241979954816,241979954880⟩ : DyadicInterval 40),(⟨-310717664704,-310717664640⟩ : DyadicInterval 40),(⟨728461854355,728461873685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨241397201408,241397201472⟩ : DyadicInterval 40),(⟨-309754969536,-309754969472⟩ : DyadicInterval 40),(⟨728644075680,728644095009⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨241871347968,241871348032⟩ : DyadicInterval 40),(⟨-310538146048,-310538145984⟩ : DyadicInterval 40),(⟨728495860671,728495880000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨70661305,141587292⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70659008,70659072⟩ : DyadicInterval 40),(⟨-70663616,-70663552⟩ : DyadicInterval 40),(⟨762123381314,762123400644⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨141578176,141578240⟩ : DyadicInterval 40),(⟨-141596416,-141596352⟩ : DyadicInterval 40),(⟨762123374439,762123393768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-18240,-4480⟩ : DyadicInterval 40),(⟨762123385856,762123412000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨270082218226,270605475040⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨241505669248,241505669312⟩ : DyadicInterval 40),(⟨-309934053376,-309934053312⟩ : DyadicInterval 40),(⟨728610204780,728610224109⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨241925660224,241925660288⟩ : DyadicInterval 40),(⟨-310627914176,-310627914112⟩ : DyadicInterval 40),(⟨728478857408,728478876738⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-68702253888,-68428384064⟩ : DyadicInterval 40),(⟨796337575648,796474529824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨241614132224,241979954880⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-310717664704,-310113176064⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e411_ok : ecellOkT e411 = true := by decide +kernel
theorem e411_pos {a z : ℝ} (ha1 : ((503319/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((63021/256000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e411 e411_ok ha1 ha2 hz1 hz2 hz

-- box ['50247/204800', '503319/2048000', '1999/2000', '1']  interval_lower 946569863/1099511627776
noncomputable def e412 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1369273154928,0,true,241248187904,241248187968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨829750100624,0,false,-309509019776,-309509019712⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1369728958333,0,true,241614132224,241614132288⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨829294297219,0,false,-310113176128,-310113176064⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1369138274164,0,true,241139874752,241139874816⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨829884981388,0,false,-309330302208,-309330302144⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582292884,0,true,70662784,70662848⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099440962668,0,false,-70667392,-70667328⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623234,0,false,-4544,-4480⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1369205708635,0,true,241194027904,241194027968⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨829817546917,0,false,-309419649472,-309419649408⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1369728966937,0,true,241614139136,241614139200⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨829294288615,0,false,-310113187584,-310113187520⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1033102679895,0,false,-68499048384,-68499048320⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1033359624093,0,false,-68225621568,-68225621504⟩
    { al := (50247/204800), au := (503319/2048000), zl := (1999/2000), zu := 1,
      A := ⟨269761527152,270217330557⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨241248187904,241248187968⟩ : DyadicInterval 40),(⟨-309509019776,-309509019712⟩ : DyadicInterval 40),(⟨728690573378,728690592708⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨241614132224,241614132288⟩ : DyadicInterval 40),(⟨-310113176128,-310113176064⟩ : DyadicInterval 40),(⟨728576314411,728576333741⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨241139874752,241139874816⟩ : DyadicInterval 40),(⟨-309330302208,-309330302144⟩ : DyadicInterval 40),(⟨728724346195,728724365525⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨241614132224,241614132288⟩ : DyadicInterval 40),(⟨-310113176128,-310113176064⟩ : DyadicInterval 40),(⟨728576314411,728576333741⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,70665108⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70662784,70662848⟩ : DyadicInterval 40),(⟨-70667392,-70667328⟩ : DyadicInterval 40),(⟨762123381314,762123400643⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4544,0⟩ : DyadicInterval 40),(⟨762123383616,762123405152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨269694080859,270217339161⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨241194027904,241194027968⟩ : DyadicInterval 40),(⟨-309419649472,-309419649408⟩ : DyadicInterval 40),(⟨728707463453,728707482782⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨241614139136,241614139200⟩ : DyadicInterval 40),(⟨-310113187584,-310113187520⟩ : DyadicInterval 40),(⟨728576312267,728576331597⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-68499048384,-68225621504⟩ : DyadicInterval 40),(⟨796236194368,796372927072⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨241248187904,241614132288⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-310113176128,-309509019712⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e412_ok : ecellOkT e412 = true := by decide +kernel
theorem e412_pos {a z : ℝ} (ha1 : ((50247/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((503319/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e412 e412_ok ha1 ha2 hz1 hz2 hz

-- box ['503319/2048000', '63021/256000', '1999/2000', '1']  interval_lower 964356417/1099511627776
noncomputable def e413 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1369728958332,0,true,241614132224,241614132288⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨829294297220,0,false,-310113176128,-310113176064⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1370184761738,0,true,241979954816,241979954880⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨828838493814,0,false,-310717664704,-310717664640⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1369593849666,0,true,241505672192,241505672256⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨829429405886,0,false,-309934058240,-309934058176⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582423204,0,true,70793088,70793152⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099440832348,0,false,-70797760,-70797696⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623217,0,false,-4608,-4544⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1369661398091,0,true,241559898816,241559898880⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨829361857461,0,false,-310023605760,-310023605696⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1370184770345,0,true,241979961728,241979961792⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨828838485207,0,false,-310717676160,-310717676096⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1032878453321,0,false,-68737714368,-68737714304⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1033135887350,0,false,-68463706880,-68463706816⟩
    { al := (503319/2048000), au := (63021/256000), zl := (1999/2000), zu := 1,
      A := ⟨270217330556,270673133962⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨241614132224,241614132288⟩ : DyadicInterval 40),(⟨-310113176128,-310113176064⟩ : DyadicInterval 40),(⟨728576314412,728576333741⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨241979954816,241979954880⟩ : DyadicInterval 40),(⟨-310717664704,-310717664640⟩ : DyadicInterval 40),(⟨728461854355,728461873685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨241505672192,241505672256⟩ : DyadicInterval 40),(⟨-309934058240,-309934058176⟩ : DyadicInterval 40),(⟨728610203862,728610223191⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨241979954816,241979954880⟩ : DyadicInterval 40),(⟨-310717664704,-310717664640⟩ : DyadicInterval 40),(⟨728461854355,728461873685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,70795428⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70793088,70793152⟩ : DyadicInterval 40),(⟨-70797760,-70797696⟩ : DyadicInterval 40),(⟨762123381329,762123400658⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4608,0⟩ : DyadicInterval 40),(⟨762123383616,762123405184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨270149770315,270673142569⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨241559898816,241559898880⟩ : DyadicInterval 40),(⟨-310023605760,-310023605696⟩ : DyadicInterval 40),(⟨728593262840,728593282169⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨241979961728,241979961792⟩ : DyadicInterval 40),(⟨-310717676160,-310717676096⟩ : DyadicInterval 40),(⟨728461852203,728461871532⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-68737714368,-68463706816⟩ : DyadicInterval 40),(⟨796355237024,796492260064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨241614132224,241979954880⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-310717664704,-310113176064⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e413_ok : ecellOkT e413 = true := by decide +kernel
theorem e413_pos {a z : ℝ} (ha1 : ((503319/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((63021/256000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e413 e413_ok ha1 ha2 hz1 hz2 hz

-- box ['63021/256000', '505017/2048000', '999/1000', '1999/2000']  interval_lower 986614479/1099511627776
noncomputable def e414 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1370184761737,0,true,241979954816,241979954880⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨828838493815,0,false,-310717664704,-310717664640⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1370640565142,0,true,242345655680,242345655744⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨828382690410,0,false,-311322485824,-311322485760⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1369914088602,0,true,241762730304,241762730368⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨829109166950,0,false,-310358656704,-310358656640⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1370505000674,0,true,242236902144,242236902208⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨828518254878,0,false,-311142565952,-311142565888⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582419383,0,true,70789312,70789376⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099440836169,0,false,-70793920,-70793856⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099653475810,0,true,141838848,141838912⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099369779742,0,false,-141857216,-141857152⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511609476,0,false,-18304,-18240⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623219,0,false,-4608,-4544⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1370049421509,0,true,241871345024,241871345088⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨828973834043,0,false,-310538141184,-310538141120⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1370572792264,0,true,242291287744,242291287808⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨828450463288,0,false,-311232534592,-311232534528⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1032687273183,0,false,-68941246784,-68941246720⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1032945075874,0,false,-68666796160,-68666796096⟩
    { al := (63021/256000), au := (505017/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨270673133961,271128937366⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨241979954816,241979954880⟩ : DyadicInterval 40),(⟨-310717664704,-310717664640⟩ : DyadicInterval 40),(⟨728461854355,728461873685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨242345655680,242345655744⟩ : DyadicInterval 40),(⟨-311322485824,-311322485760⟩ : DyadicInterval 40),(⟨728347193199,728347212528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨241762730304,241762730368⟩ : DyadicInterval 40),(⟨-310358656704,-310358656640⟩ : DyadicInterval 40),(⟨728529849313,728529868642⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨242236902144,242236902208⟩ : DyadicInterval 40),(⟨-311142565952,-311142565888⟩ : DyadicInterval 40),(⟨728381316573,728381335902⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨70791607,141848034⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70789312,70789376⟩ : DyadicInterval 40),(⟨-70793920,-70793856⟩ : DyadicInterval 40),(⟨762123381297,762123400627⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨141838848,141838912⟩ : DyadicInterval 40),(⟨-141857216,-141857152⟩ : DyadicInterval 40),(⟨762123374436,762123393765⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-18304,-4544⟩ : DyadicInterval 40),(⟨762123385888,762123412032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨270537793733,271061164488⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨241871345024,241871345088⟩ : DyadicInterval 40),(⟨-310538141184,-310538141120⟩ : DyadicInterval 40),(⟨728495861592,728495880921⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨242291287744,242291287808⟩ : DyadicInterval 40),(⟨-311232534592,-311232534528⟩ : DyadicInterval 40),(⟨728364254754,728364274084⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-68941246784,-68666796096⟩ : DyadicInterval 40),(⟨796456781664,796594026272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨241979954816,242345655744⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-311322485824,-310717664640⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e414_ok : ecellOkT e414 = true := by decide +kernel
theorem e414_pos {a z : ℝ} (ha1 : ((63021/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((505017/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e414 e414_ok ha1 ha2 hz1 hz2 hz

-- box ['505017/2048000', '252933/1024000', '999/1000', '1999/2000']  interval_lower 1004676895/1099511627776
noncomputable def e415 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1370640565141,0,true,242345655680,242345655744⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨828382690411,0,false,-311322485824,-311322485760⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1371096368546,0,true,242711235008,242711235072⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨827926887006,0,false,-311927639744,-311927639680⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1370369436203,0,true,242128137792,242128137856⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨828653819349,0,false,-310962675456,-310962675392⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1370960576176,0,true,242602334784,242602334848⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨828062679376,0,false,-311747318208,-311747318144⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582549745,0,true,70919680,70919744⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099440705807,0,false,-70924288,-70924224⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099653736674,0,true,142099712,142099776⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099369518878,0,false,-142118144,-142118080⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511609408,0,false,-18432,-18368⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623202,0,false,-4608,-4544⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1370504997019,0,true,242236899200,242236899264⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨828518258533,0,false,-311142561088,-311142561024⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1371028481725,0,true,242656793792,242656793856⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨827994773827,0,false,-311837487744,-311837487680⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1032462403269,0,false,-69180693952,-69180693888⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1032720695950,0,false,-68905661888,-68905661824⟩
    { al := (505017/2048000), au := (252933/1024000), zl := (999/1000), zu := (1999/2000),
      A := ⟨271128937365,271584740770⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨242345655680,242345655744⟩ : DyadicInterval 40),(⟨-311322485824,-311322485760⟩ : DyadicInterval 40),(⟨728347193199,728347212529⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨242711235008,242711235072⟩ : DyadicInterval 40),(⟨-311927639744,-311927639680⟩ : DyadicInterval 40),(⟨728232330788,728232350118⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨242128137792,242128137856⟩ : DyadicInterval 40),(⟨-310962675456,-310962675392⟩ : DyadicInterval 40),(⟨728415422166,728415441495⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨242602334784,242602334848⟩ : DyadicInterval 40),(⟨-311747318208,-311747318144⟩ : DyadicInterval 40),(⟨728266571494,728266590823⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨70921969,142108898⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70919680,70919744⟩ : DyadicInterval 40),(⟨-70924288,-70924224⟩ : DyadicInterval 40),(⟨762123381281,762123400610⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨142099712,142099776⟩ : DyadicInterval 40),(⟨-142118144,-142118080⟩ : DyadicInterval 40),(⟨762123374400,762123393729⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-18432,-4544⟩ : DyadicInterval 40),(⟨762123385888,762123412096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨270993369243,271516853949⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨242236899200,242236899264⟩ : DyadicInterval 40),(⟨-311142561088,-311142561024⟩ : DyadicInterval 40),(⟨728381317495,728381336824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨242656793792,242656793856⟩ : DyadicInterval 40),(⟨-311837487744,-311837487680⟩ : DyadicInterval 40),(⟨728249451000,728249470329⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-69180693952,-68905661824⟩ : DyadicInterval 40),(⟨796576214528,796713749856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨242345655680,242711235072⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-311927639744,-311322485760⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e415_ok : ecellOkT e415 = true := by decide +kernel
theorem e415_pos {a z : ℝ} (ha1 : ((505017/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((252933/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e415 e415_ok ha1 ha2 hz1 hz2 hz

-- box ['63021/256000', '505017/2048000', '1999/2000', '1']  interval_lower 982266749/1099511627776
noncomputable def e416 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1370184761737,0,true,241979954816,241979954880⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨828838493815,0,false,-310717664704,-310717664640⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1370640565142,0,true,242345655680,242345655744⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨828382690410,0,false,-311322485824,-311322485760⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1370049425169,0,true,241871347904,241871347968⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨828973830383,0,false,-310538146048,-310538145984⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582553584,0,true,70923520,70923584⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099440701968,0,false,-70928128,-70928064⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623200,0,false,-4608,-4544⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1370117087534,0,true,241925647936,241925648000⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨828906168018,0,false,-310627893888,-310627893824⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1370640573736,0,true,242345662592,242345662656⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨828382681816,0,false,-311322497216,-311322497152⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1032653848849,0,false,-68976834560,-68976834496⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1032911772895,0,false,-68702245888,-68702245824⟩
    { al := (63021/256000), au := (505017/2048000), zl := (1999/2000), zu := 1,
      A := ⟨270673133961,271128937366⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨241979954816,241979954880⟩ : DyadicInterval 40),(⟨-310717664704,-310717664640⟩ : DyadicInterval 40),(⟨728461854355,728461873685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨242345655680,242345655744⟩ : DyadicInterval 40),(⟨-311322485824,-311322485760⟩ : DyadicInterval 40),(⟨728347193199,728347212528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨241871347904,241871347968⟩ : DyadicInterval 40),(⟨-310538146048,-310538145984⟩ : DyadicInterval 40),(⟨728495860712,728495880041⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨242345655680,242345655744⟩ : DyadicInterval 40),(⟨-311322485824,-311322485760⟩ : DyadicInterval 40),(⟨728347193199,728347212528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,70925808⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70923520,70923584⟩ : DyadicInterval 40),(⟨-70928128,-70928064⟩ : DyadicInterval 40),(⟨762123381280,762123400609⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4608,0⟩ : DyadicInterval 40),(⟨762123383616,762123405184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨270605459758,271128945960⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨241925647936,241925648000⟩ : DyadicInterval 40),(⟨-310627893888,-310627893824⟩ : DyadicInterval 40),(⟨728478861257,728478880586⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨242345662592,242345662656⟩ : DyadicInterval 40),(⟨-311322497216,-311322497152⟩ : DyadicInterval 40),(⟨728347191018,728347210348⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-68976834560,-68702245824⟩ : DyadicInterval 40),(⟨796474506528,796611820160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨241979954816,242345655744⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-311322485824,-310717664640⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e416_ok : ecellOkT e416 = true := by decide +kernel
theorem e416_pos {a z : ℝ} (ha1 : ((63021/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((505017/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e416 e416_ok ha1 ha2 hz1 hz2 hz

-- box ['505017/2048000', '252933/1024000', '1999/2000', '1']  interval_lower 1000301629/1099511627776
noncomputable def e417 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1370640565141,0,true,242345655680,242345655744⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨828382690411,0,false,-311322485824,-311322485760⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1371096368546,0,true,242711235008,242711235072⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨827926887006,0,false,-311927639744,-311927639680⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1370505000672,0,true,242236902144,242236902208⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨828518254880,0,false,-311142565952,-311142565888⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582684025,0,true,71053952,71054016⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099440571527,0,false,-71058560,-71058496⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623183,0,false,-4608,-4544⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1370572776979,0,true,242291275520,242291275584⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨828450478573,0,false,-311232514304,-311232514240⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1371096377151,0,true,242711241920,242711241984⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨827926878401,0,false,-311927651200,-311927651136⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1032428866457,0,false,-69216409280,-69216409216⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1032687280720,0,false,-68941238784,-68941238720⟩
    { al := (505017/2048000), au := (252933/1024000), zl := (1999/2000), zu := 1,
      A := ⟨271128937365,271584740770⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨242345655680,242345655744⟩ : DyadicInterval 40),(⟨-311322485824,-311322485760⟩ : DyadicInterval 40),(⟨728347193199,728347212529⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨242711235008,242711235072⟩ : DyadicInterval 40),(⟨-311927639744,-311927639680⟩ : DyadicInterval 40),(⟨728232330788,728232350118⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨242236902144,242236902208⟩ : DyadicInterval 40),(⟨-311142565952,-311142565888⟩ : DyadicInterval 40),(⟨728381316574,728381335903⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨242711235008,242711235072⟩ : DyadicInterval 40),(⟨-311927639744,-311927639680⟩ : DyadicInterval 40),(⟨728232330788,728232350118⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,71056249⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨71053952,71054016⟩ : DyadicInterval 40),(⟨-71058560,-71058496⟩ : DyadicInterval 40),(⟨762123381263,762123400593⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4608,0⟩ : DyadicInterval 40),(⟨762123383616,762123405184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨271061149203,271584749375⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨242291275520,242291275584⟩ : DyadicInterval 40),(⟨-311232514304,-311232514240⟩ : DyadicInterval 40),(⟨728364258577,728364277907⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨242711241920,242711241984⟩ : DyadicInterval 40),(⟨-311927651200,-311927651136⟩ : DyadicInterval 40),(⟨728232328621,728232347951⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-69216409280,-68941238720⟩ : DyadicInterval 40),(⟨796594002976,796731607520⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨242345655680,242711235072⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-311927639744,-311322485760⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e417_ok : ecellOkT e417 = true := by decide +kernel
theorem e417_pos {a z : ℝ} (ha1 : ((505017/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((252933/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e417 e417_ok ha1 ha2 hz1 hz2 hz

-- box ['252933/1024000', '101343/409600', '999/1000', '1999/2000']  interval_lower 255716161/274877906944
noncomputable def e418 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1371096368545,0,true,242711235008,242711235072⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨827926887007,0,false,-311927639744,-311927639680⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1371552171951,0,true,243076692800,243076692864⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨827471083601,0,false,-312533126976,-312533126912⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1370824783804,0,true,242493423808,242493423872⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨828198471748,0,false,-311567026240,-311567026176⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1371416151680,0,true,242967646080,242967646144⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨827607103872,0,false,-312352403392,-312352403328⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582680169,0,true,71050048,71050112⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099440575383,0,false,-71054720,-71054656⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099653997660,0,true,142360640,142360704⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099369257892,0,false,-142379136,-142379072⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511609341,0,false,-18496,-18432⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623185,0,false,-4608,-4544⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1370960572530,0,true,242602331904,242602331968⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨828062683022,0,false,-311747313408,-311747313344⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1371484171182,0,true,243022178304,243022178368⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨827539084370,0,false,-312442773888,-312442773824⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1032237155639,0,false,-69420595584,-69420595520⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1032495938495,0,false,-69144981504,-69144981440⟩
    { al := (252933/1024000), au := (101343/409600), zl := (999/1000), zu := (1999/2000),
      A := ⟨271584740769,272040544175⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨242711235008,242711235072⟩ : DyadicInterval 40),(⟨-311927639744,-311927639680⟩ : DyadicInterval 40),(⟨728232330789,728232350118⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨243076692800,243076692864⟩ : DyadicInterval 40),(⟨-312533126976,-312533126912⟩ : DyadicInterval 40),(⟨728117267185,728117286515⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨242493423808,242493423872⟩ : DyadicInterval 40),(⟨-311567026240,-311567026176⟩ : DyadicInterval 40),(⟨728300794318,728300813648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨242967646080,242967646144⟩ : DyadicInterval 40),(⟨-312352403392,-312352403328⟩ : DyadicInterval 40),(⟨728151625398,728151644727⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨71052393,142369884⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨71050048,71050112⟩ : DyadicInterval 40),(⟨-71054720,-71054656⟩ : DyadicInterval 40),(⟨762123381296,762123400625⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨142360640,142360704⟩ : DyadicInterval 40),(⟨-142379136,-142379072⟩ : DyadicInterval 40),(⟨762123374365,762123393694⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-18496,-4544⟩ : DyadicInterval 40),(⟨762123385888,762123412128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨271448944754,271972543406⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨242602331904,242602331968⟩ : DyadicInterval 40),(⟨-311747313408,-311747313344⟩ : DyadicInterval 40),(⟨728266572401,728266591730⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨243022178304,243022178368⟩ : DyadicInterval 40),(⟨-312442773888,-312442773824⟩ : DyadicInterval 40),(⟨728134446154,728134465483⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-69420595584,-69144981440⟩ : DyadicInterval 40),(⟨796695874336,796833700672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨242711235008,243076692864⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-312533126976,-311927639680⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e418_ok : ecellOkT e418 = true := by decide +kernel
theorem e418_pos {a z : ℝ} (ha1 : ((252933/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((101343/409600 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e418 e418_ok ha1 ha2 hz1 hz2 hz

-- box ['101343/409600', '126891/512000', '999/1000', '1999/2000']  interval_lower 1041177839/1099511627776
noncomputable def e419 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1371552171950,0,true,243076692800,243076692864⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨827471083602,0,false,-312533126976,-312533126912⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1372007975355,0,true,243442029184,243442029248⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨827015280197,0,false,-313138947840,-313138947776⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1371280131405,0,true,242858588544,242858588608⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨827743124147,0,false,-312171709440,-312171709376⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1371871727182,0,true,243332836032,243332836096⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨827151528370,0,false,-312957821632,-312957821568⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582810652,0,true,71180544,71180608⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099440444900,0,false,-71185216,-71185152⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099654258766,0,true,142621696,142621760⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099368996786,0,false,-142640256,-142640192⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511609273,0,false,-18560,-18496⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623168,0,false,-4672,-4608⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1371416148037,0,true,242967643136,242967643200⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨827607107515,0,false,-312352398528,-312352398464⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1371939860644,0,true,243387441472,243387441536⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨827083394908,0,false,-313048393472,-313048393408⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1032011530288,0,false,-69660952000,-69660951936⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1032270803514,0,false,-69384755328,-69384755264⟩
    { al := (101343/409600), au := (126891/512000), zl := (999/1000), zu := (1999/2000),
      A := ⟨272040544174,272496347579⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨243076692800,243076692864⟩ : DyadicInterval 40),(⟨-312533126976,-312533126912⟩ : DyadicInterval 40),(⟨728117267185,728117286515⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨243442029184,243442029248⟩ : DyadicInterval 40),(⟨-313138947840,-313138947776⟩ : DyadicInterval 40),(⟨728002002297,728002021627⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨242858588544,242858588608⟩ : DyadicInterval 40),(⟨-312171709440,-312171709376⟩ : DyadicInterval 40),(⟨728185965663,728185984993⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨243332836032,243332836096⟩ : DyadicInterval 40),(⟨-312957821632,-312957821568⟩ : DyadicInterval 40),(⟨728036478204,728036497533⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨71182876,142630990⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨71180544,71180608⟩ : DyadicInterval 40),(⟨-71185216,-71185152⟩ : DyadicInterval 40),(⟨762123381279,762123400608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨142621696,142621760⟩ : DyadicInterval 40),(⟨-142640256,-142640192⟩ : DyadicInterval 40),(⟨762123374329,762123393658⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-18560,-4608⟩ : DyadicInterval 40),(⟨762123385920,762123412160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨271904520261,272428232868⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨242967643136,242967643200⟩ : DyadicInterval 40),(⟨-312352398528,-312352398464⟩ : DyadicInterval 40),(⟨728151626323,728151645653⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨243387441472,243387441536⟩ : DyadicInterval 40),(⟨-313048393472,-313048393408⟩ : DyadicInterval 40),(⟨728019240131,728019259460⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-69660952000,-69384755264⟩ : DyadicInterval 40),(⟨796815761248,796953878880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨243076692800,243442029248⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-313138947840,-312533126912⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e419_ok : ecellOkT e419 = true := by decide +kernel
theorem e419_pos {a z : ℝ} (ha1 : ((101343/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((126891/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e419 e419_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B006

end


