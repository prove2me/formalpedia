-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B028
-- name    : CK_CKLaneC2R_EpCells_B028
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T15:05:18.453855+00:00
-- url     : https://prove2.me/theorems/556907a7-bc3a-4132-9c8b-4affb16ac53c
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B028` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B028` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B028` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B028 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B028.lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheckT

-- ===== source module CKLaneC2R.EpCells.B028 =====
section

namespace CKLaneC2R.EpCells.B028

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['62289/409600', '1246629/8192000', '3997/4000', '1599/1600']  interval_lower 133246775/1099511627776
noncomputable def e1680 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266717388963,0,true,155649850880,155649850944⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932305866589,0,false,-181375923648,-181375923584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266831339815,0,true,155748755840,155748755904⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932191915737,0,false,-181510319424,-181510319360⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266591984642,0,true,155540994432,155540994496⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932431270910,0,false,-181228038464,-181228038400⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266726764996,0,true,155657989248,155657989312⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932296490556,0,false,-181386981312,-181386981248⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564768595,0,true,53139520,53139584⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458486957,0,false,-53142144,-53142080⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575442408,0,true,63812736,63812800⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447813144,0,false,-63816512,-63816448⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624072,0,false,-3712,-3648⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625208,0,false,-2624,-2560⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266654682778,0,true,155595420480,155595420544⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932368572774,0,false,-181301973824,-181301973760⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266779057039,0,true,155703377472,155703377536⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932244198513,0,false,-181448654080,-181448654016⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074065427676,0,false,-25745276608,-25745276544⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074103255432,0,false,-25706553280,-25706553216⟩
    { al := (62289/409600), au := (1246629/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨167205761187,167319712039⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155649850880,155649850944⟩ : DyadicInterval 40),(⟨-181375923648,-181375923584⟩ : DyadicInterval 40),(⟨749360201100,749360220430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155748755840,155748755904⟩ : DyadicInterval 40),(⟨-181510319424,-181510319360⟩ : DyadicInterval 40),(⟨749342730789,749342750118⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155540994432,155540994496⟩ : DyadicInterval 40),(⟨-181228038464,-181228038400⟩ : DyadicInterval 40),(⟨749379413459,749379432789⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155657989248,155657989312⟩ : DyadicInterval 40),(⟨-181386981312,-181386981248⟩ : DyadicInterval 40),(⟨749358764084,749358783414⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨53140819,63814632⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53139520,53139584⟩ : DyadicInterval 40),(⟨-53142144,-53142080⟩ : DyadicInterval 40),(⟨762123382295,762123401624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63812736,63812800⟩ : DyadicInterval 40),(⟨-63816512,-63816448⟩ : DyadicInterval 40),(⟨762123381736,762123401065⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3712,-2560⟩ : DyadicInterval 40),(⟨762123384896,762123404736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167143055002,167267429263⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155595420480,155595420544⟩ : DyadicInterval 40),(⟨-181301973824,-181301973760⟩ : DyadicInterval 40),(⟨749369809744,749369829073⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155703377472,155703377536⟩ : DyadicInterval 40),(⟨-181448654080,-181448654016⟩ : DyadicInterval 40),(⟨749350748007,749350767336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25745276608,-25706553216⟩ : DyadicInterval 40),(⟨774976660224,774996041184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155649850880,155748755904⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181510319424,-181375923584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1680_ok : ecellOkT e1680 = true := by decide +kernel
theorem e1680_pos {a z : ℝ} (ha1 : ((62289/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1246629/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1680 e1680_ok ha1 ha2 hz1 hz2 hz

-- box ['1246629/8192000', '623739/4096000', '3997/4000', '1599/1600']  interval_lower 33557911/274877906944
noncomputable def e1681 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266831339814,0,true,155748755840,155748755904⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932191915738,0,false,-181510319424,-181510319360⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266945290666,0,true,155847651904,155847651968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932077964886,0,false,-181644731584,-181644731520⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266705850029,0,true,155639835008,155639835072⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932317405523,0,false,-181362315328,-181362315264⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266840644627,0,true,155756831680,155756831744⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932182610925,0,false,-181521294400,-181521294336⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564806048,0,true,53176960,53177024⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458449504,0,false,-53179584,-53179520⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575487357,0,true,63857664,63857728⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447768195,0,false,-63861440,-63861376⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624067,0,false,-3712,-3648⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625205,0,false,-2624,-2560⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266768590893,0,true,155694293248,155694293312⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932254664659,0,false,-181436310144,-181436310080⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266892972280,0,true,155802246720,155802246784⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932130283272,0,false,-181583016704,-181583016640⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074030756287,0,false,-25780769984,-25780769920⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074068611983,0,false,-25742016832,-25742016768⟩
    { al := (1246629/8192000), au := (623739/4096000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨167319712038,167433662890⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155748755840,155748755904⟩ : DyadicInterval 40),(⟨-181510319424,-181510319360⟩ : DyadicInterval 40),(⟨749342730789,749342750118⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155847651904,155847651968⟩ : DyadicInterval 40),(⟨-181644731584,-181644731520⟩ : DyadicInterval 40),(⟨749325248369,749325267698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155639835008,155639835072⟩ : DyadicInterval 40),(⟨-181362315328,-181362315264⟩ : DyadicInterval 40),(⟨749361969525,749361988855⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155756831680,155756831744⟩ : DyadicInterval 40),(⟨-181521294400,-181521294336⟩ : DyadicInterval 40),(⟨749341303677,749341323006⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨53178272,63859581⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53176960,53177024⟩ : DyadicInterval 40),(⟨-53179584,-53179520⟩ : DyadicInterval 40),(⟨762123382291,762123401621⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63857664,63857728⟩ : DyadicInterval 40),(⟨-63861440,-63861376⟩ : DyadicInterval 40),(⟨762123381730,762123401060⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3712,-2560⟩ : DyadicInterval 40),(⟨762123384896,762123404736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167256963117,167381344504⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155694293248,155694293312⟩ : DyadicInterval 40),(⟨-181436310144,-181436310080⟩ : DyadicInterval 40),(⟨749352352628,749352371957⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155802246720,155802246784⟩ : DyadicInterval 40),(⟨-181583016704,-181583016640⟩ : DyadicInterval 40),(⟨749333276595,749333295925⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25780769984,-25742016768⟩ : DyadicInterval 40),(⟨774994392000,775013787872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155748755840,155847651968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181644731584,-181510319360⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1681_ok : ecellOkT e1681 = true := by decide +kernel
theorem e1681_pos {a z : ℝ} (ha1 : ((1246629/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((623739/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1681 e1681_ok ha1 ha2 hz1 hz2 hz

-- box ['62289/409600', '1246629/8192000', '1599/1600', '1999/2000']  interval_lower 33276071/274877906944
noncomputable def e1682 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266717388963,0,true,155649850880,155649850944⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932305866589,0,false,-181375923648,-181375923584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266831339815,0,true,155748755840,155748755904⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932191915737,0,false,-181510319424,-181510319360⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266612885362,0,true,155559137920,155559137984⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932410370190,0,false,-181252684608,-181252684544⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266747679960,0,true,155676143168,155676143232⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932275575592,0,false,-181411647808,-181411647744⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554140471,0,true,42511872,42511936⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469115081,0,false,-42513536,-42513472⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564806793,0,true,53177728,53177792⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458448759,0,false,-53180352,-53180288⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625203,0,false,-2624,-2560⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626133,0,false,-1664,-1600⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266665133017,0,true,155604491712,155604491776⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932358122535,0,false,-181314297536,-181314297472⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266789514423,0,true,155712454016,155712454080⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932233741129,0,false,-181460987840,-181460987776⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074062245837,0,false,-25748533824,-25748533760⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074100078132,0,false,-25709805760,-25709805696⟩
    { al := (62289/409600), au := (1246629/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨167205761187,167319712039⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155649850880,155649850944⟩ : DyadicInterval 40),(⟨-181375923648,-181375923584⟩ : DyadicInterval 40),(⟨749360201100,749360220430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155748755840,155748755904⟩ : DyadicInterval 40),(⟨-181510319424,-181510319360⟩ : DyadicInterval 40),(⟨749342730789,749342750118⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155559137920,155559137984⟩ : DyadicInterval 40),(⟨-181252684608,-181252684544⟩ : DyadicInterval 40),(⟨749376212415,749376231744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155676143168,155676143232⟩ : DyadicInterval 40),(⟨-181411647808,-181411647744⟩ : DyadicInterval 40),(⟨749355558230,749355577559⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨42512695,53179017⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42511872,42511936⟩ : DyadicInterval 40),(⟨-42513536,-42513472⟩ : DyadicInterval 40),(⟨762123382740,762123402069⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53177728,53177792⟩ : DyadicInterval 40),(⟨-53180352,-53180288⟩ : DyadicInterval 40),(⟨762123382291,762123401621⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2624,-1600⟩ : DyadicInterval 40),(⟨762123384416,762123404192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167153505241,167277886647⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155604491712,155604491776⟩ : DyadicInterval 40),(⟨-181314297536,-181314297472⟩ : DyadicInterval 40),(⟨749368208688,749368228018⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155712454016,155712454080⟩ : DyadicInterval 40),(⟨-181460987840,-181460987776⟩ : DyadicInterval 40),(⟨749349144635,749349163964⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25748533824,-25709805696⟩ : DyadicInterval 40),(⟨774978286464,774997669792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155649850880,155748755904⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181510319424,-181375923584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1682_ok : ecellOkT e1682 = true := by decide +kernel
theorem e1682_pos {a z : ℝ} (ha1 : ((62289/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1246629/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1682 e1682_ok ha1 ha2 hz1 hz2 hz

-- box ['1246629/8192000', '623739/4096000', '1599/1600', '1999/2000']  interval_lower 134088981/1099511627776
noncomputable def e1683 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266831339814,0,true,155748755840,155748755904⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932191915738,0,false,-181510319424,-181510319360⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266945290666,0,true,155847651904,155847651968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932077964886,0,false,-181644731584,-181644731520⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266726764993,0,true,155657989248,155657989312⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932296490559,0,false,-181386981312,-181386981248⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266861573835,0,true,155774996288,155774996352⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932161681717,0,false,-181545980736,-181545980672⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554170433,0,true,42541824,42541888⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469085119,0,false,-42543488,-42543424⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564844250,0,true,53215168,53215232⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458411302,0,false,-53217792,-53217728⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625200,0,false,-2624,-2560⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626130,0,false,-1664,-1600⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266779048254,0,true,155703369856,155703369920⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932244207298,0,false,-181448643712,-181448643648⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266903436782,0,true,155811328640,155811328704⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932119818770,0,false,-181595360384,-181595360320⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074027570113,0,false,-25784031744,-25784031680⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074065430350,0,false,-25745273856,-25745273792⟩
    { al := (1246629/8192000), au := (623739/4096000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨167319712038,167433662890⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155748755840,155748755904⟩ : DyadicInterval 40),(⟨-181510319424,-181510319360⟩ : DyadicInterval 40),(⟨749342730789,749342750118⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155847651904,155847651968⟩ : DyadicInterval 40),(⟨-181644731584,-181644731520⟩ : DyadicInterval 40),(⟨749325248369,749325267698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155657989248,155657989312⟩ : DyadicInterval 40),(⟨-181386981312,-181386981248⟩ : DyadicInterval 40),(⟨749358764085,749358783414⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155774996288,155774996352⟩ : DyadicInterval 40),(⟨-181545980736,-181545980672⟩ : DyadicInterval 40),(⟨749338093456,749338112785⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨42542657,53216474⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42541824,42541888⟩ : DyadicInterval 40),(⟨-42543488,-42543424⟩ : DyadicInterval 40),(⟨762123382737,762123402066⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53215168,53215232⟩ : DyadicInterval 40),(⟨-53217792,-53217728⟩ : DyadicInterval 40),(⟨762123382288,762123401617⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2624,-1600⟩ : DyadicInterval 40),(⟨762123384416,762123404192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167267420478,167391809006⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155703369856,155703369920⟩ : DyadicInterval 40),(⟨-181448643712,-181448643648⟩ : DyadicInterval 40),(⟨749350749345,749350768675⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155811328640,155811328704⟩ : DyadicInterval 40),(⟨-181595360384,-181595360320⟩ : DyadicInterval 40),(⟨749331671021,749331690350⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25784031744,-25745273792⟩ : DyadicInterval 40),(⟨774996020512,775015418752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155748755840,155847651968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181644731584,-181510319360⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1683_ok : ecellOkT e1683 = true := by decide +kernel
theorem e1683_pos {a z : ℝ} (ha1 : ((1246629/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((623739/4096000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1683 e1683_ok ha1 ha2 hz1 hz2 hz

-- box ['623739/4096000', '1248327/8192000', '3997/4000', '1599/1600']  interval_lower 135219119/1099511627776
noncomputable def e1684 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266945290665,0,true,155847651904,155847651968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932077964887,0,false,-181644731584,-181644731520⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267059241518,0,true,155946539072,155946539136⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931964014034,0,false,-181779160192,-181779160128⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266819715417,0,true,155738666688,155738666752⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932203540135,0,false,-181496608640,-181496608576⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266954524260,0,true,155855665216,155855665280⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932068731292,0,false,-181655623936,-181655623872⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564843506,0,true,53214400,53214464⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458412046,0,false,-53217024,-53216960⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575532309,0,true,63902656,63902720⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447723243,0,false,-63906432,-63906368⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624061,0,false,-3776,-3712⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625201,0,false,-2624,-2560⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266882499008,0,true,155793157184,155793157248⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932140756544,0,false,-181570662848,-181570662784⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267006887520,0,true,155901107072,155901107136⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932016368032,0,false,-181717395776,-181717395712⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073996061293,0,false,-25816288640,-25816288576⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074033944931,0,false,-25777505664,-25777505600⟩
    { al := (623739/4096000), au := (1248327/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨167433662889,167547613742⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155847651904,155847651968⟩ : DyadicInterval 40),(⟨-181644731584,-181644731520⟩ : DyadicInterval 40),(⟨749325248369,749325267698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155946539072,155946539136⟩ : DyadicInterval 40),(⟨-181779160192,-181779160128⟩ : DyadicInterval 40),(⟨749307753865,749307773195⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155738666688,155738666752⟩ : DyadicInterval 40),(⟨-181496608640,-181496608576⟩ : DyadicInterval 40),(⟨749344513548,749344532877⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155855665216,155855665280⟩ : DyadicInterval 40),(⟨-181655623936,-181655623872⟩ : DyadicInterval 40),(⟨749323831218,749323850547⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨53215730,63904533⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53214400,53214464⟩ : DyadicInterval 40),(⟨-53217024,-53216960⟩ : DyadicInterval 40),(⟨762123382288,762123401617⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63902656,63902720⟩ : DyadicInterval 40),(⟨-63906432,-63906368⟩ : DyadicInterval 40),(⟨762123381725,762123401054⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3776,-2560⟩ : DyadicInterval 40),(⟨762123384896,762123404768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167370871232,167495259744⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155793157184,155793157248⟩ : DyadicInterval 40),(⟨-181570662848,-181570662784⟩ : DyadicInterval 40),(⟨749334883385,749334902715⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155901107072,155901107136⟩ : DyadicInterval 40),(⟨-181717395776,-181717395712⟩ : DyadicInterval 40),(⟨749315793117,749315812446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25816288640,-25777505600⟩ : DyadicInterval 40),(⟨775012136416,775031547200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155847651904,155946539136⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181779160192,-181644731520⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1684_ok : ecellOkT e1684 = true := by decide +kernel
theorem e1684_pos {a z : ℝ} (ha1 : ((623739/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1248327/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1684 e1684_ok ha1 ha2 hz1 hz2 hz

-- box ['1248327/8192000', '156147/1024000', '3997/4000', '1599/1600']  interval_lower 34052345/274877906944
noncomputable def e1685 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267059241517,0,true,155946539072,155946539136⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931964014035,0,false,-181779160192,-181779160128⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267173192369,0,true,156045417408,156045417472⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931850063183,0,false,-181913605248,-181913605184⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266933580806,0,true,155837489536,155837489600⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932089674746,0,false,-181630918336,-181630918272⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267068403892,0,true,155954489856,155954489920⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931954851660,0,false,-181789969856,-181789969792⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564880966,0,true,53251840,53251904⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458374586,0,false,-53254528,-53254464⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575577264,0,true,63947584,63947648⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447678288,0,false,-63951360,-63951296⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624056,0,false,-3776,-3712⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625197,0,false,-2624,-2560⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266996407383,0,true,155892012352,155892012416⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932026848169,0,false,-181705032320,-181705032256⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267120802764,0,true,155999958592,155999958656⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931902452788,0,false,-181851791296,-181851791232⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073961342694,0,false,-25851832640,-25851832576⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073999254200,0,false,-25813019904,-25813019840⟩
    { al := (1248327/8192000), au := (156147/1024000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨167547613741,167661564593⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155946539072,155946539136⟩ : DyadicInterval 40),(⟨-181779160192,-181779160128⟩ : DyadicInterval 40),(⟨749307753865,749307773195⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156045417408,156045417472⟩ : DyadicInterval 40),(⟨-181913605248,-181913605184⟩ : DyadicInterval 40),(⟨749290247241,749290266571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155837489536,155837489600⟩ : DyadicInterval 40),(⟨-181630918336,-181630918272⟩ : DyadicInterval 40),(⟨749327045461,749327064790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155954489856,155954489920⟩ : DyadicInterval 40),(⟨-181789969856,-181789969792⟩ : DyadicInterval 40),(⟨749306346678,749306366008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨53253190,63949488⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53251840,53251904⟩ : DyadicInterval 40),(⟨-53254528,-53254464⟩ : DyadicInterval 40),(⟨762123382316,762123401645⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63947584,63947648⟩ : DyadicInterval 40),(⟨-63951360,-63951296⟩ : DyadicInterval 40),(⟨762123381720,762123401049⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3776,-2560⟩ : DyadicInterval 40),(⟨762123384896,762123404768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167484779607,167609174988⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155892012352,155892012416⟩ : DyadicInterval 40),(⟨-181705032320,-181705032256⟩ : DyadicInterval 40),(⟨749317402101,749317421430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155999958592,155999958656⟩ : DyadicInterval 40),(⟨-181851791296,-181851791232⟩ : DyadicInterval 40),(⟨749298297532,749298316862⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25851832640,-25813019840⟩ : DyadicInterval 40),(⟨775029893536,775049319200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155946539072,156045417472⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181913605248,-181779160128⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1685_ok : ecellOkT e1685 = true := by decide +kernel
theorem e1685_pos {a z : ℝ} (ha1 : ((1248327/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((156147/1024000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1685 e1685_ok ha1 ha2 hz1 hz2 hz

-- box ['623739/4096000', '1248327/8192000', '1599/1600', '1999/2000']  interval_lower 67538049/549755813888
noncomputable def e1686 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266945290665,0,true,155847651904,155847651968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932077964887,0,false,-181644731584,-181644731520⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267059241518,0,true,155946539072,155946539136⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931964014034,0,false,-181779160192,-181779160128⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266840644625,0,true,155756831680,155756831744⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932182610927,0,false,-181521294400,-181521294336⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266975467712,0,true,155873840576,155873840640⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932047787840,0,false,-181680330048,-181680329984⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554200400,0,true,42571776,42571840⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469055152,0,false,-42573504,-42573440⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564881711,0,true,53252608,53252672⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458373841,0,false,-53255232,-53255168⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625196,0,false,-2624,-2560⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626128,0,false,-1664,-1600⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266892963494,0,true,155802239104,155802239168⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932130292058,0,false,-181583006336,-181583006272⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267017359148,0,true,155910194368,155910194432⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932005896404,0,false,-181729749376,-181729749312⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073992870780,0,false,-25819554944,-25819554880⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074030758963,0,false,-25780767232,-25780767168⟩
    { al := (623739/4096000), au := (1248327/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨167433662889,167547613742⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155847651904,155847651968⟩ : DyadicInterval 40),(⟨-181644731584,-181644731520⟩ : DyadicInterval 40),(⟨749325248369,749325267698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155946539072,155946539136⟩ : DyadicInterval 40),(⟨-181779160192,-181779160128⟩ : DyadicInterval 40),(⟨749307753865,749307773195⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155756831680,155756831744⟩ : DyadicInterval 40),(⟨-181521294400,-181521294336⟩ : DyadicInterval 40),(⟨749341303677,749341323007⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155873840576,155873840640⟩ : DyadicInterval 40),(⟨-181680330048,-181680329984⟩ : DyadicInterval 40),(⟨749320616558,749320635888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨42572624,53253935⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42571776,42571840⟩ : DyadicInterval 40),(⟨-42573504,-42573440⟩ : DyadicInterval 40),(⟨762123382767,762123402096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53252608,53252672⟩ : DyadicInterval 40),(⟨-53255232,-53255168⟩ : DyadicInterval 40),(⟨762123382284,762123401613⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2624,-1600⟩ : DyadicInterval 40),(⟨762123384416,762123404192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167381335718,167505731372⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155802239104,155802239168⟩ : DyadicInterval 40),(⟨-181583006336,-181583006272⟩ : DyadicInterval 40),(⟨749333277936,749333297266⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155910194368,155910194432⟩ : DyadicInterval 40),(⟨-181729749376,-181729749312⟩ : DyadicInterval 40),(⟨749314185335,749314204665⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25819554944,-25780767168⟩ : DyadicInterval 40),(⟨775013767200,775033180352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155847651904,155946539136⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181779160192,-181644731520⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1686_ok : ecellOkT e1686 = true := by decide +kernel
theorem e1686_pos {a z : ℝ} (ha1 : ((623739/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1248327/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1686 e1686_ok ha1 ha2 hz1 hz2 hz

-- box ['1248327/8192000', '156147/1024000', '1599/1600', '1999/2000']  interval_lower 2126027/17179869184
noncomputable def e1687 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267059241517,0,true,155946539072,155946539136⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931964014035,0,false,-181779160192,-181779160128⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267173192369,0,true,156045417408,156045417472⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931850063183,0,false,-181913605248,-181913605184⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266954524258,0,true,155855665216,155855665280⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932068731294,0,false,-181655623936,-181655623872⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267089361587,0,true,155972675968,155972676032⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931933893965,0,false,-181814695808,-181814695744⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554230368,0,true,42601728,42601792⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469025184,0,false,-42603456,-42603392⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564919173,0,true,53290048,53290112⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458336379,0,false,-53292736,-53292672⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625193,0,false,-2624,-2560⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626126,0,false,-1664,-1600⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267006878731,0,true,155901099456,155901099520⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932016376821,0,false,-181717385408,-181717385344⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267131281513,0,true,156009051200,156009051264⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931891974039,0,false,-181864154752,-181864154688⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073958147840,0,false,-25855103488,-25855103424⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073996063972,0,false,-25816285888,-25816285824⟩
    { al := (1248327/8192000), au := (156147/1024000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨167547613741,167661564593⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155946539072,155946539136⟩ : DyadicInterval 40),(⟨-181779160192,-181779160128⟩ : DyadicInterval 40),(⟨749307753865,749307773195⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156045417408,156045417472⟩ : DyadicInterval 40),(⟨-181913605248,-181913605184⟩ : DyadicInterval 40),(⟨749290247241,749290266571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155855665216,155855665280⟩ : DyadicInterval 40),(⟨-181655623936,-181655623872⟩ : DyadicInterval 40),(⟨749323831218,749323850547⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155972675968,155972676032⟩ : DyadicInterval 40),(⟨-181814695808,-181814695744⟩ : DyadicInterval 40),(⟨749303127603,749303146932⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨42602592,53291397⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42601728,42601792⟩ : DyadicInterval 40),(⟨-42603456,-42603392⟩ : DyadicInterval 40),(⟨762123382765,762123402094⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53290048,53290112⟩ : DyadicInterval 40),(⟨-53292736,-53292672⟩ : DyadicInterval 40),(⟨762123382312,762123401642⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2624,-1600⟩ : DyadicInterval 40),(⟨762123384416,762123404192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167495250955,167619653737⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155901099456,155901099520⟩ : DyadicInterval 40),(⟨-181717385408,-181717385344⟩ : DyadicInterval 40),(⟨749315794460,749315813790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156009051200,156009051264⟩ : DyadicInterval 40),(⟨-181864154752,-181864154688⟩ : DyadicInterval 40),(⟨749296687551,749296706881⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25855103488,-25816285824⟩ : DyadicInterval 40),(⟨775031526528,775050954624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155946539072,156045417472⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181913605248,-181779160128⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1687_ok : ecellOkT e1687 = true := by decide +kernel
theorem e1687_pos {a z : ℝ} (ha1 : ((1248327/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((156147/1024000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1687 e1687_ok ha1 ha2 hz1 hz2 hz

-- box ['77649/512000', '1243233/8192000', '1999/2000', '7997/8000']  interval_lower 32262815/274877906944
noncomputable def e1688 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266261585559,0,true,155254141952,155254142016⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932761669993,0,false,-180838504896,-180838504832⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266375536411,0,true,155353082560,155353082624⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932647719141,0,false,-180972834944,-180972834880⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266178210580,0,true,155181744000,155181744064⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932845044972,0,false,-180740229376,-180740229312⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266312962446,0,true,155298752256,155298752320⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932710293106,0,false,-180899068096,-180899068032⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543422425,0,true,31794176,31794240⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479833127,0,false,-31795136,-31795072⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554051288,0,true,42422656,42422720⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469204264,0,false,-42424384,-42424320⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626139,0,false,-1664,-1600⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626857,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266219894085,0,true,155217940096,155217940160⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932803361467,0,false,-180789361344,-180789361280⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266344253884,0,true,155325921600,155325921664⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932679001668,0,false,-180935956160,-180935956096⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074197547932,0,false,-25610034496,-25610034432⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074235272935,0,false,-25571421184,-25571421120⟩
    { al := (77649/512000), au := (1243233/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨166749957783,166863908635⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155254141952,155254142016⟩ : DyadicInterval 40),(⟨-180838504896,-180838504832⟩ : DyadicInterval 40),(⟨749429961571,749429980900⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155353082560,155353082624⟩ : DyadicInterval 40),(⟨-180972834944,-180972834880⟩ : DyadicInterval 40),(⟨749412539565,749412558895⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155181744000,155181744064⟩ : DyadicInterval 40),(⟨-180740229376,-180740229312⟩ : DyadicInterval 40),(⟨749442701134,749442720463⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155298752256,155298752320⟩ : DyadicInterval 40),(⟨-180899068096,-180899068032⟩ : DyadicInterval 40),(⟨749422108048,749422127377⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨31794649,42423512⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31794176,31794240⟩ : DyadicInterval 40),(⟨-31795136,-31795072⟩ : DyadicInterval 40),(⟨762123383112,762123402441⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42422656,42422720⟩ : DyadicInterval 40),(⟨-42424384,-42424320⟩ : DyadicInterval 40),(⟨762123382779,762123402108⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1664,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166708266309,166832626108⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155217940096,155217940160⟩ : DyadicInterval 40),(⟨-180789361344,-180789361280⟩ : DyadicInterval 40),(⟨749436332780,749436352110⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155325921600,155325921664⟩ : DyadicInterval 40),(⟨-180935956160,-180935956096⟩ : DyadicInterval 40),(⟨749417323591,749417342920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25610034496,-25571421120⟩ : DyadicInterval 40),(⟨774909094176,774928420128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155254141952,155353082624⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180972834944,-180838504832⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1688_ok : ecellOkT e1688 = true := by decide +kernel
theorem e1688_pos {a z : ℝ} (ha1 : ((77649/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1243233/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1688 e1688_ok ha1 ha2 hz1 hz2 hz

-- box ['1243233/8192000', '622041/4096000', '1999/2000', '7997/8000']  interval_lower 130024997/1099511627776
noncomputable def e1689 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266375536410,0,true,155353082560,155353082624⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932647719142,0,false,-180972834944,-180972834880⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266489487262,0,true,155452014208,155452014272⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932533768290,0,false,-181107181440,-181107181376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266292104455,0,true,155280641600,155280641664⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932731151097,0,false,-180874480256,-180874480192⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266426870565,0,true,155397651776,155397651840⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932596384987,0,false,-181033355200,-181033355136⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543444890,0,true,31816640,31816704⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479810662,0,false,-31817600,-31817536⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554081245,0,true,42452608,42452672⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469174307,0,false,-42454336,-42454272⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626136,0,false,-1664,-1600⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626856,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266333816193,0,true,155316859008,155316859072⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932689439359,0,false,-180923651520,-180923651456⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266458183370,0,true,155424837184,155424837248⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932565072182,0,false,-181070272960,-181070272896⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074162962313,0,false,-25645435712,-25645435648⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074200715327,0,false,-25606792512,-25606792448⟩
    { al := (1243233/8192000), au := (622041/4096000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨166863908634,166977859486⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155353082560,155353082624⟩ : DyadicInterval 40),(⟨-180972834944,-180972834880⟩ : DyadicInterval 40),(⟨749412539565,749412558895⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155452014208,155452014272⟩ : DyadicInterval 40),(⟨-181107181440,-181107181376⟩ : DyadicInterval 40),(⟨749395105519,749395124849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155280641600,155280641664⟩ : DyadicInterval 40),(⟨-180874480256,-180874480192⟩ : DyadicInterval 40),(⟨749425296712,749425316042⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155397651776,155397651840⟩ : DyadicInterval 40),(⟨-181033355200,-181033355136⟩ : DyadicInterval 40),(⟨749404687130,749404706460⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨31817114,42453469⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31816640,31816704⟩ : DyadicInterval 40),(⟨-31817600,-31817536⟩ : DyadicInterval 40),(⟨762123383111,762123402440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42452608,42452672⟩ : DyadicInterval 40),(⟨-42454336,-42454272⟩ : DyadicInterval 40),(⟨762123382776,762123402105⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1664,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166822188417,166946555594⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155316859008,155316859072⟩ : DyadicInterval 40),(⟨-180923651520,-180923651456⟩ : DyadicInterval 40),(⟨749418919597,749418938927⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155424837184,155424837248⟩ : DyadicInterval 40),(⟨-181070272960,-181070272896⟩ : DyadicInterval 40),(⟨749399896109,749399915438⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25645435712,-25606792448⟩ : DyadicInterval 40),(⟨774926779840,774946120736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155353082560,155452014272⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181107181440,-180972834880⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1689_ok : ecellOkT e1689 = true := by decide +kernel
theorem e1689_pos {a z : ℝ} (ha1 : ((1243233/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((622041/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1689 e1689_ok ha1 ha2 hz1 hz2 hz

-- box ['77649/512000', '1243233/8192000', '7997/8000', '3999/4000']  interval_lower 128909579/1099511627776
noncomputable def e1690 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266261585559,0,true,155254141952,155254142016⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932761669993,0,false,-180838504896,-180838504832⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266375536411,0,true,155353082560,155353082624⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932647719141,0,false,-180972834944,-180972834880⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266199054324,0,true,155199843904,155199843968⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932824201228,0,false,-180764797376,-180764797312⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266333820434,0,true,155316862656,155316862720⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932689435118,0,false,-180923656512,-180923656448⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532824167,0,true,21196160,21196224⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490431385,0,false,-21196608,-21196544⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543445541,0,true,31817280,31817344⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479810011,0,false,-31818240,-31818176⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626855,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627368,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266230315625,0,true,155226989504,155226989568⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932792939927,0,false,-180801645440,-180801645376⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266354682823,0,true,155334976576,155334976640⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932668572729,0,false,-180948250624,-180948250560⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074194382997,0,false,-25613274048,-25613273984⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074232112603,0,false,-25574655872,-25574655808⟩
    { al := (77649/512000), au := (1243233/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨166749957783,166863908635⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155254141952,155254142016⟩ : DyadicInterval 40),(⟨-180838504896,-180838504832⟩ : DyadicInterval 40),(⟨749429961571,749429980900⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155353082560,155353082624⟩ : DyadicInterval 40),(⟨-180972834944,-180972834880⟩ : DyadicInterval 40),(⟨749412539565,749412558895⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155199843904,155199843968⟩ : DyadicInterval 40),(⟨-180764797376,-180764797312⟩ : DyadicInterval 40),(⟨749439516844,749439536173⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155316862656,155316862720⟩ : DyadicInterval 40),(⟨-180923656512,-180923656448⟩ : DyadicInterval 40),(⟨749418918966,749418938295⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21196391,31817765⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21196160,21196224⟩ : DyadicInterval 40),(⟨-21196608,-21196544⟩ : DyadicInterval 40),(⟨762123383367,762123402696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31817280,31817344⟩ : DyadicInterval 40),(⟨-31818240,-31818176⟩ : DyadicInterval 40),(⟨762123383111,762123402440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166718687849,166843055047⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155226989504,155226989568⟩ : DyadicInterval 40),(⟨-180801645440,-180801645376⟩ : DyadicInterval 40),(⟨749434740333,749434759662⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155334976576,155334976640⟩ : DyadicInterval 40),(⟨-180948250624,-180948250560⟩ : DyadicInterval 40),(⟨749415728789,749415748118⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25613274048,-25574655808⟩ : DyadicInterval 40),(⟨774910711520,774930039904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155254141952,155353082624⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180972834944,-180838504832⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1690_ok : ecellOkT e1690 = true := by decide +kernel
theorem e1690_pos {a z : ℝ} (ha1 : ((77649/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1243233/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1690 e1690_ok ha1 ha2 hz1 hz2 hz

-- box ['1243233/8192000', '622041/4096000', '7997/8000', '3999/4000']  interval_lower 64941681/549755813888
noncomputable def e1691 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266375536410,0,true,155353082560,155353082624⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932647719142,0,false,-180972834944,-180972834880⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266489487262,0,true,155452014208,155452014272⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932533768290,0,false,-181107181440,-181107181376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266312962444,0,true,155298752256,155298752320⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932710293108,0,false,-180899068096,-180899068032⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266447742798,0,true,155415772864,155415772928⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932575512754,0,false,-181057963392,-181057963328⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532839145,0,true,21211136,21211200⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490416407,0,false,-21211584,-21211520⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543468010,0,true,31839744,31839808⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479787542,0,false,-31840704,-31840640⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626853,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627367,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266344245110,0,true,155325913984,155325914048⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932679010442,0,false,-180935945792,-180935945728⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266468619429,0,true,155433897536,155433897600⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932554636123,0,false,-181082577344,-181082577280⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074159793054,0,false,-25648679808,-25648679744⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074197550596,0,false,-25610031808,-25610031744⟩
    { al := (1243233/8192000), au := (622041/4096000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨166863908634,166977859486⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155353082560,155353082624⟩ : DyadicInterval 40),(⟨-180972834944,-180972834880⟩ : DyadicInterval 40),(⟨749412539565,749412558895⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155452014208,155452014272⟩ : DyadicInterval 40),(⟨-181107181440,-181107181376⟩ : DyadicInterval 40),(⟨749395105519,749395124849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155298752256,155298752320⟩ : DyadicInterval 40),(⟨-180899068096,-180899068032⟩ : DyadicInterval 40),(⟨749422108048,749422127378⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155415772864,155415772928⟩ : DyadicInterval 40),(⟨-181057963392,-181057963328⟩ : DyadicInterval 40),(⟨749401493676,749401513005⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21211369,31840234⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21211136,21211200⟩ : DyadicInterval 40),(⟨-21211584,-21211520⟩ : DyadicInterval 40),(⟨762123383366,762123402695⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31839744,31839808⟩ : DyadicInterval 40),(⟨-31840704,-31840640⟩ : DyadicInterval 40),(⟨762123383109,762123402438⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166832617334,166956991653⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155325913984,155325914048⟩ : DyadicInterval 40),(⟨-180935945792,-180935945728⟩ : DyadicInterval 40),(⟨749417324921,749417344250⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155433897536,155433897600⟩ : DyadicInterval 40),(⟨-181082577344,-181082577280⟩ : DyadicInterval 40),(⟨749398299116,749398318446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25648679808,-25610031744⟩ : DyadicInterval 40),(⟨774928399488,774947742784⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155353082560,155452014272⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181107181440,-180972834880⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1691_ok : ecellOkT e1691 = true := by decide +kernel
theorem e1691_pos {a z : ℝ} (ha1 : ((1243233/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((622041/4096000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1691 e1691_ok ha1 ha2 hz1 hz2 hz

-- box ['622041/4096000', '1244931/8192000', '1999/2000', '7997/8000']  interval_lower 131001341/1099511627776
noncomputable def e1692 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266489487261,0,true,155452014208,155452014272⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932533768291,0,false,-181107181440,-181107181376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266603438113,0,true,155550936960,155550937024⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932419817439,0,false,-181241544320,-181241544256⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266405998331,0,true,155379530304,155379530368⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932617257221,0,false,-181008747520,-181008747456⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266540778685,0,true,155496542336,155496542400⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932482476867,0,false,-181167658688,-181167658624⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543467359,0,true,31839104,31839168⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479788193,0,false,-31840064,-31840000⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554111205,0,true,42482560,42482624⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469144347,0,false,-42484288,-42484224⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626134,0,false,-1664,-1600⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626854,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266447738552,0,true,155415769152,155415769216⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932575517000,0,false,-181057958400,-181057958336⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266572112855,0,true,155523743872,155523743936⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932451142697,0,false,-181204606144,-181204606080⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074128353084,0,false,-25680862272,-25680862208⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074166134035,0,false,-25642189184,-25642189120⟩
    { al := (622041/4096000), au := (1244931/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨166977859485,167091810337⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155452014208,155452014272⟩ : DyadicInterval 40),(⟨-181107181440,-181107181376⟩ : DyadicInterval 40),(⟨749395105519,749395124849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155550936960,155550937024⟩ : DyadicInterval 40),(⟨-181241544320,-181241544256⟩ : DyadicInterval 40),(⟨749377659368,749377678697⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155379530304,155379530368⟩ : DyadicInterval 40),(⟨-181008747520,-181008747456⟩ : DyadicInterval 40),(⟨749407880212,749407899541⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155496542336,155496542400⟩ : DyadicInterval 40),(⟨-181167658688,-181167658624⟩ : DyadicInterval 40),(⟨749387254163,749387273492⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨31839583,42483429⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31839104,31839168⟩ : DyadicInterval 40),(⟨-31840064,-31840000⟩ : DyadicInterval 40),(⟨762123383109,762123402439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42482560,42482624⟩ : DyadicInterval 40),(⟨-42484288,-42484224⟩ : DyadicInterval 40),(⟨762123382774,762123402103⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1664,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166936110776,167060485079⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155415769152,155415769216⟩ : DyadicInterval 40),(⟨-181057958400,-181057958336⟩ : DyadicInterval 40),(⟨749401494346,749401513676⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155523743872,155523743936⟩ : DyadicInterval 40),(⟨-181204606144,-181204606080⟩ : DyadicInterval 40),(⟨749382456531,749382475861⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25680862272,-25642189120⟩ : DyadicInterval 40),(⟨774944478176,774963834016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155452014208,155550937024⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181241544320,-181107181376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1692_ok : ecellOkT e1692 = true := by decide +kernel
theorem e1692_pos {a z : ℝ} (ha1 : ((622041/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1244931/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1692 e1692_ok ha1 ha2 hz1 hz2 hz

-- box ['1244931/8192000', '62289/409600', '1999/2000', '7997/8000']  interval_lower 65990189/549755813888
noncomputable def e1693 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266603438112,0,true,155550936960,155550937024⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932419817440,0,false,-181241544320,-181241544256⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266717388964,0,true,155649850880,155649850944⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932305866588,0,false,-181375923648,-181375923584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266519892206,0,true,155478410176,155478410240⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932503363346,0,false,-181143031232,-181143031168⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266654686804,0,true,155595424000,155595424064⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932368568748,0,false,-181301978560,-181301978496⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543489829,0,true,31861568,31861632⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479765723,0,false,-31862528,-31862464⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554141168,0,true,42512512,42512576⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469114384,0,false,-42514240,-42514176⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626132,0,false,-1664,-1600⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626853,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266561660914,0,true,155514670464,155514670528⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932461594638,0,false,-181192281664,-181192281600⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266686042343,0,true,155622641600,155622641664⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932337213209,0,false,-181338955776,-181338955712⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074093720243,0,false,-25716314112,-25716314048⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074131529134,0,false,-25677611136,-25677611072⟩
    { al := (1244931/8192000), au := (62289/409600), zl := (1999/2000), zu := (7997/8000),
      A := ⟨167091810336,167205761188⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155550936960,155550937024⟩ : DyadicInterval 40),(⟨-181241544320,-181241544256⟩ : DyadicInterval 40),(⟨749377659368,749377678698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155649850880,155649850944⟩ : DyadicInterval 40),(⟨-181375923648,-181375923584⟩ : DyadicInterval 40),(⟨749360201100,749360220430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155478410176,155478410240⟩ : DyadicInterval 40),(⟨-181143031232,-181143031168⟩ : DyadicInterval 40),(⟨749390451621,749390470951⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155595424000,155595424064⟩ : DyadicInterval 40),(⟨-181301978560,-181301978496⟩ : DyadicInterval 40),(⟨749369809107,749369828437⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨31862053,42513392⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31861568,31861632⟩ : DyadicInterval 40),(⟨-31862528,-31862464⟩ : DyadicInterval 40),(⟨762123383108,762123402437⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42512512,42512576⟩ : DyadicInterval 40),(⟨-42514240,-42514176⟩ : DyadicInterval 40),(⟨762123382772,762123402101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1664,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167050033138,167174414567⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155514670464,155514670528⟩ : DyadicInterval 40),(⟨-181192281664,-181192281600⟩ : DyadicInterval 40),(⟨749384056965,749384076295⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155622641600,155622641664⟩ : DyadicInterval 40),(⟨-181338955776,-181338955712⟩ : DyadicInterval 40),(⟨749365004920,749365024250⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25716314112,-25677611072⟩ : DyadicInterval 40),(⟨774962189152,774981559936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155550936960,155649850944⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181375923648,-181241544256⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1693_ok : ecellOkT e1693 = true := by decide +kernel
theorem e1693_pos {a z : ℝ} (ha1 : ((1244931/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((62289/409600 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1693 e1693_ok ha1 ha2 hz1 hz2 hz

-- box ['622041/4096000', '1244931/8192000', '7997/8000', '3999/4000']  interval_lower 65429921/549755813888
noncomputable def e1694 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266489487261,0,true,155452014208,155452014272⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932533768291,0,false,-181107181440,-181107181376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266603438113,0,true,155550936960,155550937024⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932419817439,0,false,-181241544320,-181241544256⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266426870563,0,true,155397651776,155397651840⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932596384989,0,false,-181033355200,-181033355136⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266561665161,0,true,155514674176,155514674240⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932461590391,0,false,-181192286656,-181192286592⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532854124,0,true,21226112,21226176⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490401428,0,false,-21226560,-21226496⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543490481,0,true,31862208,31862272⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479765071,0,false,-31863168,-31863104⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626852,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627367,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266458174849,0,true,155424829760,155424829824⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932565080703,0,false,-181070262912,-181070262848⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266582556038,0,true,155532809536,155532809600⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932440699514,0,false,-181216920448,-181216920384⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074125179497,0,false,-25684110848,-25684110784⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074162964902,0,false,-25645433088,-25645433024⟩
    { al := (622041/4096000), au := (1244931/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨166977859485,167091810337⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155452014208,155452014272⟩ : DyadicInterval 40),(⟨-181107181440,-181107181376⟩ : DyadicInterval 40),(⟨749395105519,749395124849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155550936960,155550937024⟩ : DyadicInterval 40),(⟨-181241544320,-181241544256⟩ : DyadicInterval 40),(⟨749377659368,749377678697⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155397651776,155397651840⟩ : DyadicInterval 40),(⟨-181033355200,-181033355136⟩ : DyadicInterval 40),(⟨749404687131,749404706460⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155514674176,155514674240⟩ : DyadicInterval 40),(⟨-181192286656,-181192286592⟩ : DyadicInterval 40),(⟨749384056294,749384075623⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21226348,31862705⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21226112,21226176⟩ : DyadicInterval 40),(⟨-21226560,-21226496⟩ : DyadicInterval 40),(⟨762123383366,762123402695⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31862208,31862272⟩ : DyadicInterval 40),(⟨-31863168,-31863104⟩ : DyadicInterval 40),(⟨762123383108,762123402437⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166946547073,167070928262⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155424829760,155424829824⟩ : DyadicInterval 40),(⟨-181070262912,-181070262848⟩ : DyadicInterval 40),(⟨749399897427,749399916757⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155532809536,155532809600⟩ : DyadicInterval 40),(⟨-181216920448,-181216920384⟩ : DyadicInterval 40),(⟨749380857381,749380876710⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25684110848,-25645433024⟩ : DyadicInterval 40),(⟨774946100128,774965458304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155452014208,155550937024⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181241544320,-181107181376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1694_ok : ecellOkT e1694 = true := by decide +kernel
theorem e1694_pos {a z : ℝ} (ha1 : ((622041/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1244931/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1694 e1694_ok ha1 ha2 hz1 hz2 hz

-- box ['1244931/8192000', '62289/409600', '7997/8000', '3999/4000']  interval_lower 131838421/1099511627776
noncomputable def e1695 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266603438112,0,true,155550936960,155550937024⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932419817440,0,false,-181241544320,-181241544256⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266717388964,0,true,155649850880,155649850944⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932305866588,0,false,-181375923648,-181375923584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266540778683,0,true,155496542336,155496542400⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932482476869,0,false,-181167658688,-181167658624⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266675587524,0,true,155613566592,155613566656⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932347668028,0,false,-181326626368,-181326626304⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532869104,0,true,21241088,21241152⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490386448,0,false,-21241536,-21241472⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543512953,0,true,31884672,31884736⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479742599,0,false,-31885696,-31885632⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626851,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627366,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266572104076,0,true,155523736256,155523736320⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932451151476,0,false,-181204595776,-181204595712⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266696492649,0,true,155631712704,155631712768⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932326762903,0,false,-181351279936,-181351279872⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074090542326,0,false,-25719567232,-25719567168⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074128355752,0,false,-25680859520,-25680859456⟩
    { al := (1244931/8192000), au := (62289/409600), zl := (7997/8000), zu := (3999/4000),
      A := ⟨167091810336,167205761188⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155550936960,155550937024⟩ : DyadicInterval 40),(⟨-181241544320,-181241544256⟩ : DyadicInterval 40),(⟨749377659368,749377678698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155649850880,155649850944⟩ : DyadicInterval 40),(⟨-181375923648,-181375923584⟩ : DyadicInterval 40),(⟨749360201100,749360220430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155496542336,155496542400⟩ : DyadicInterval 40),(⟨-181167658688,-181167658624⟩ : DyadicInterval 40),(⟨749387254163,749387273492⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155613566592,155613566656⟩ : DyadicInterval 40),(⟨-181326626368,-181326626304⟩ : DyadicInterval 40),(⟨749366606845,749366626174⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21241328,31885177⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21241088,21241152⟩ : DyadicInterval 40),(⟨-21241536,-21241472⟩ : DyadicInterval 40),(⟨762123383365,762123402694⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31884672,31884736⟩ : DyadicInterval 40),(⟨-31885696,-31885632⟩ : DyadicInterval 40),(⟨762123383139,762123402468⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167060476300,167184864873⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155523736256,155523736320⟩ : DyadicInterval 40),(⟨-181204595776,-181204595712⟩ : DyadicInterval 40),(⟨749382457866,749382477195⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155631712704,155631712768⟩ : DyadicInterval 40),(⟨-181351279936,-181351279872⟩ : DyadicInterval 40),(⟨749363403508,749363422837⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25719567232,-25680859456⟩ : DyadicInterval 40),(⟨774963813344,774983186496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155550936960,155649850944⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181375923648,-181241544256⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1695_ok : ecellOkT e1695 = true := by decide +kernel
theorem e1695_pos {a z : ℝ} (ha1 : ((1244931/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((62289/409600 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1695 e1695_ok ha1 ha2 hz1 hz2 hz

-- box ['77649/512000', '1243233/8192000', '3999/4000', '7999/8000']  interval_lower 32192133/274877906944
noncomputable def e1696 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266261585559,0,true,155254141952,155254142016⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932761669993,0,false,-180838504896,-180838504832⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266375536411,0,true,155353082560,155353082624⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932647719141,0,false,-180972834944,-180972834880⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266219898069,0,true,155217943552,155217943616⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932803357483,0,false,-180789366016,-180789365952⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266354678423,0,true,155334972736,155334972800⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932668577129,0,false,-180948245440,-180948245376⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522225865,0,true,10598016,10598080⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099501029687,0,false,-10598144,-10598080⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532839751,0,true,21211712,21211776⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490415801,0,false,-21212224,-21212160⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627366,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627674,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266240737443,0,true,155236039104,155236039168⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932782518109,0,false,-180813930048,-180813929984⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266365111786,0,true,155344031488,155344031552⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932658143766,0,false,-180960545280,-180960545216⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074191217856,0,false,-25616513792,-25616513728⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074228951988,0,false,-25577890880,-25577890816⟩
    { al := (77649/512000), au := (1243233/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨166749957783,166863908635⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155254141952,155254142016⟩ : DyadicInterval 40),(⟨-180838504896,-180838504832⟩ : DyadicInterval 40),(⟨749429961571,749429980900⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155353082560,155353082624⟩ : DyadicInterval 40),(⟨-180972834944,-180972834880⟩ : DyadicInterval 40),(⟨749412539565,749412558895⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155217943552,155217943616⟩ : DyadicInterval 40),(⟨-180789366016,-180789365952⟩ : DyadicInterval 40),(⟨749436332164,749436351493⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155334972736,155334972800⟩ : DyadicInterval 40),(⟨-180948245440,-180948245376⟩ : DyadicInterval 40),(⟨749415729475,749415748804⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10598089,21211975⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10598016,10598080⟩ : DyadicInterval 40),(⟨-10598144,-10598080⟩ : DyadicInterval 40),(⟨762123383513,762123402842⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21211712,21211776⟩ : DyadicInterval 40),(⟨-21212224,-21212160⟩ : DyadicInterval 40),(⟨762123383398,762123402727⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166729109667,166853484010⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155236039104,155236039168⟩ : DyadicInterval 40),(⟨-180813930048,-180813929984⟩ : DyadicInterval 40),(⟨749433147747,749433167076⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155344031488,155344031552⟩ : DyadicInterval 40),(⟨-180960545280,-180960545216⟩ : DyadicInterval 40),(⟨749414133899,749414153229⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25616513792,-25577890816⟩ : DyadicInterval 40),(⟨774912329024,774931659776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155254141952,155353082624⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180972834944,-180838504832⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1696_ok : ecellOkT e1696 = true := by decide +kernel
theorem e1696_pos {a z : ℝ} (ha1 : ((77649/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1243233/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1696 e1696_ok ha1 ha2 hz1 hz2 hz

-- box ['1243233/8192000', '622041/4096000', '3999/4000', '7999/8000']  interval_lower 129741917/1099511627776
noncomputable def e1697 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266375536410,0,true,155353082560,155353082624⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932647719142,0,false,-180972834944,-180972834880⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266489487262,0,true,155452014208,155452014272⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932533768290,0,false,-181107181440,-181107181376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266333820432,0,true,155316862656,155316862720⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932689435120,0,false,-180923656512,-180923656448⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266468615030,0,true,155433893696,155433893760⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932554640522,0,false,-181082572160,-181082572096⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522233355,0,true,10605504,10605568⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099501022197,0,false,-10605632,-10605568⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532854730,0,true,21226688,21226752⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490400822,0,false,-21227200,-21227136⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627366,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627674,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266354674050,0,true,155334968960,155334969024⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932668581502,0,false,-180948240320,-180948240256⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266479055512,0,true,155442957760,155442957824⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932544200040,0,false,-181094881856,-181094881792⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074156623590,0,false,-25651924032,-25651923968⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074194385660,0,false,-25613271296,-25613271232⟩
    { al := (1243233/8192000), au := (622041/4096000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨166863908634,166977859486⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155353082560,155353082624⟩ : DyadicInterval 40),(⟨-180972834944,-180972834880⟩ : DyadicInterval 40),(⟨749412539565,749412558895⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155452014208,155452014272⟩ : DyadicInterval 40),(⟨-181107181440,-181107181376⟩ : DyadicInterval 40),(⟨749395105519,749395124849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155316862656,155316862720⟩ : DyadicInterval 40),(⟨-180923656512,-180923656448⟩ : DyadicInterval 40),(⟨749418918966,749418938295⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155433893696,155433893760⟩ : DyadicInterval 40),(⟨-181082572160,-181082572096⟩ : DyadicInterval 40),(⟨749398299802,749398319132⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10605579,21226954⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10605504,10605568⟩ : DyadicInterval 40),(⟨-10605632,-10605568⟩ : DyadicInterval 40),(⟨762123383513,762123402842⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21226688,21226752⟩ : DyadicInterval 40),(⟨-21227200,-21227136⟩ : DyadicInterval 40),(⟨762123383398,762123402727⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166843046274,166967427736⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155334968960,155334969024⟩ : DyadicInterval 40),(⟨-180948240320,-180948240256⟩ : DyadicInterval 40),(⟨749415730146,749415749476⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155442957760,155442957824⟩ : DyadicInterval 40),(⟨-181094881856,-181094881792⟩ : DyadicInterval 40),(⟨749396702045,749396721374⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25651924032,-25613271232⟩ : DyadicInterval 40),(⟨774930019232,774949364896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155353082560,155452014272⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181107181440,-180972834880⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1697_ok : ecellOkT e1697 = true := by decide +kernel
theorem e1697_pos {a z : ℝ} (ha1 : ((1243233/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((622041/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1697 e1697_ok ha1 ha2 hz1 hz2 hz

-- box ['77649/512000', '1243233/8192000', '7999/8000', '1']  interval_lower 128627329/1099511627776
noncomputable def e1698 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266261585559,0,true,155254141952,155254142016⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932761669993,0,false,-180838504896,-180838504832⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266375536411,0,true,155353082560,155353082624⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932647719141,0,false,-180972834944,-180972834880⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266240741814,0,true,155236042944,155236043008⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932782513738,0,false,-180813935168,-180813935104⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522233915,0,true,10606080,10606144⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099501021637,0,false,-10606208,-10606144⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627673,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1266251159285,0,true,155245088640,155245088704⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨932772096267,0,false,-180826214784,-180826214720⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1266375540771,0,true,155353086336,155353086400⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨932647714781,0,false,-180972840128,-180972840064⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1074188052511,0,false,-25619753728,-25619753664⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1074225791169,0,false,-25581126080,-25581126016⟩
    { al := (77649/512000), au := (1243233/8192000), zl := (7999/8000), zu := 1,
      A := ⟨166749957783,166863908635⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155254141952,155254142016⟩ : DyadicInterval 40),(⟨-180838504896,-180838504832⟩ : DyadicInterval 40),(⟨749429961571,749429980900⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155353082560,155353082624⟩ : DyadicInterval 40),(⟨-180972834944,-180972834880⟩ : DyadicInterval 40),(⟨749412539565,749412558895⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155236042944,155236043008⟩ : DyadicInterval 40),(⟨-180813935168,-180813935104⟩ : DyadicInterval 40),(⟨749433147039,749433166369⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155353082560,155353082624⟩ : DyadicInterval 40),(⟨-180972834944,-180972834880⟩ : DyadicInterval 40),(⟨749412539565,749412558895⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10606139⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10606080,10606144⟩ : DyadicInterval 40),(⟨-10606208,-10606144⟩ : DyadicInterval 40),(⟨762123383513,762123402842⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨166739531509,166863912995⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155245088640,155245088704⟩ : DyadicInterval 40),(⟨-180826214784,-180826214720⟩ : DyadicInterval 40),(⟨749431555045,749431574375⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155353086336,155353086400⟩ : DyadicInterval 40),(⟨-180972840128,-180972840064⟩ : DyadicInterval 40),(⟨749412538922,749412558252⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25619753728,-25581126016⟩ : DyadicInterval 40),(⟨774913946624,774933279744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨155254141952,155353082624⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180972834944,-180838504832⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1698_ok : ecellOkT e1698 = true := by decide +kernel
theorem e1698_pos {a z : ℝ} (ha1 : ((77649/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1243233/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1698 e1698_ok ha1 ha2 hz1 hz2 hz

-- box ['1243233/8192000', '622041/4096000', '7999/8000', '1']  interval_lower 129600321/1099511627776
noncomputable def e1699 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266375536410,0,true,155353082560,155353082624⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932647719142,0,false,-180972834944,-180972834880⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266489487262,0,true,155452014208,155452014272⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932533768290,0,false,-181107181440,-181107181376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266354678421,0,true,155334972736,155334972800⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932668577131,0,false,-180948245440,-180948245376⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522241404,0,true,10613568,10613632⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099501014148,0,false,-10613696,-10613632⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627673,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1266365103012,0,true,155344023872,155344023936⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨932658152540,0,false,-180960534976,-180960534912⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1266489491618,0,true,155452017984,155452018048⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨932533763934,0,false,-181107186560,-181107186496⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1074153453920,0,false,-25655168576,-25655168512⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1074191220520,0,false,-25616511040,-25616510976⟩
    { al := (1243233/8192000), au := (622041/4096000), zl := (7999/8000), zu := 1,
      A := ⟨166863908634,166977859486⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155353082560,155353082624⟩ : DyadicInterval 40),(⟨-180972834944,-180972834880⟩ : DyadicInterval 40),(⟨749412539565,749412558895⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155452014208,155452014272⟩ : DyadicInterval 40),(⟨-181107181440,-181107181376⟩ : DyadicInterval 40),(⟨749395105519,749395124849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155334972736,155334972800⟩ : DyadicInterval 40),(⟨-180948245440,-180948245376⟩ : DyadicInterval 40),(⟨749415729475,749415748804⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155452014208,155452014272⟩ : DyadicInterval 40),(⟨-181107181440,-181107181376⟩ : DyadicInterval 40),(⟨749395105519,749395124849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10613628⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10613568,10613632⟩ : DyadicInterval 40),(⟨-10613696,-10613632⟩ : DyadicInterval 40),(⟨762123383513,762123402842⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨166853475236,166977863842⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155344023872,155344023936⟩ : DyadicInterval 40),(⟨-180960534976,-180960534912⟩ : DyadicInterval 40),(⟨749414135257,749414154586⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155452017984,155452018048⟩ : DyadicInterval 40),(⟨-181107186560,-181107186496⟩ : DyadicInterval 40),(⟨749395104849,749395124178⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25655168576,-25616510976⟩ : DyadicInterval 40),(⟨774931639104,774950987168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨155353082560,155452014272⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181107181440,-180972834880⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1699_ok : ecellOkT e1699 = true := by decide +kernel
theorem e1699_pos {a z : ℝ} (ha1 : ((1243233/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((622041/4096000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1699 e1699_ok ha1 ha2 hz1 hz2 hz

-- box ['622041/4096000', '1244931/8192000', '3999/4000', '7999/8000']  interval_lower 130717741/1099511627776
noncomputable def e1700 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266489487261,0,true,155452014208,155452014272⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932533768291,0,false,-181107181440,-181107181376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266603438113,0,true,155550936960,155550937024⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932419817439,0,false,-181241544320,-181241544256⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266447742796,0,true,155415772864,155415772928⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932575512756,0,false,-181057963392,-181057963328⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266582551637,0,true,155532805696,155532805760⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932440703915,0,false,-181216915264,-181216915200⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522240844,0,true,10612992,10613056⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099501014708,0,false,-10613120,-10613056⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532869710,0,true,21241728,21241792⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490385842,0,false,-21242176,-21242112⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627365,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627674,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266468610653,0,true,155433889920,155433889984⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932554644899,0,false,-181082566976,-181082566912⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266592999239,0,true,155541875200,155541875264⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932430256313,0,false,-181229234880,-181229234816⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074122005706,0,false,-25687359680,-25687359616⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074159795720,0,false,-25648677056,-25648676992⟩
    { al := (622041/4096000), au := (1244931/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨166977859485,167091810337⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155452014208,155452014272⟩ : DyadicInterval 40),(⟨-181107181440,-181107181376⟩ : DyadicInterval 40),(⟨749395105519,749395124849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155550936960,155550937024⟩ : DyadicInterval 40),(⟨-181241544320,-181241544256⟩ : DyadicInterval 40),(⟨749377659368,749377678697⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155415772864,155415772928⟩ : DyadicInterval 40),(⟨-181057963392,-181057963328⟩ : DyadicInterval 40),(⟨749401493676,749401513006⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155532805696,155532805760⟩ : DyadicInterval 40),(⟨-181216915264,-181216915200⟩ : DyadicInterval 40),(⟨749380858068,749380877398⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10613068,21241934⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10612992,10613056⟩ : DyadicInterval 40),(⟨-10613120,-10613056⟩ : DyadicInterval 40),(⟨762123383513,762123402842⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21241728,21241792⟩ : DyadicInterval 40),(⟨-21242176,-21242112⟩ : DyadicInterval 40),(⟨762123383365,762123402694⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166956982877,167081371463⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155433889920,155433889984⟩ : DyadicInterval 40),(⟨-181082566976,-181082566912⟩ : DyadicInterval 40),(⟨749398300448,749398319778⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155541875200,155541875264⟩ : DyadicInterval 40),(⟨-181229234880,-181229234816⟩ : DyadicInterval 40),(⟨749379258078,749379277408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25687359680,-25648676992⟩ : DyadicInterval 40),(⟨774947722112,774967082720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155452014208,155550937024⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181241544320,-181107181376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1700_ok : ecellOkT e1700 = true := by decide +kernel
theorem e1700_pos {a z : ℝ} (ha1 : ((622041/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1244931/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1700 e1700_ok ha1 ha2 hz1 hz2 hz

-- box ['1244931/8192000', '62289/409600', '3999/4000', '7999/8000']  interval_lower 131695979/1099511627776
noncomputable def e1701 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266603438112,0,true,155550936960,155550937024⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932419817440,0,false,-181241544320,-181241544256⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266717388964,0,true,155649850880,155649850944⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932305866588,0,false,-181375923648,-181375923584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266561665159,0,true,155514674176,155514674240⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932461590393,0,false,-181192286656,-181192286592⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266696488244,0,true,155631708864,155631708928⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932326767308,0,false,-181351274752,-181351274688⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522248334,0,true,10620480,10620544⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099501007218,0,false,-10620672,-10620608⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532884692,0,true,21256704,21256768⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490370860,0,false,-21257152,-21257088⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627365,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627674,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266582547259,0,true,155532801920,155532801984⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932440708293,0,false,-181216910080,-181216910016⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266706942974,0,true,155640783680,155640783744⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932316312578,0,false,-181363604288,-181363604224⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074087364204,0,false,-25722820544,-25722820480⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074125182166,0,false,-25684108096,-25684108032⟩
    { al := (1244931/8192000), au := (62289/409600), zl := (3999/4000), zu := (7999/8000),
      A := ⟨167091810336,167205761188⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155550936960,155550937024⟩ : DyadicInterval 40),(⟨-181241544320,-181241544256⟩ : DyadicInterval 40),(⟨749377659368,749377678698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155649850880,155649850944⟩ : DyadicInterval 40),(⟨-181375923648,-181375923584⟩ : DyadicInterval 40),(⟨749360201100,749360220430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155514674176,155514674240⟩ : DyadicInterval 40),(⟨-181192286656,-181192286592⟩ : DyadicInterval 40),(⟨749384056294,749384075623⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155631708864,155631708928⟩ : DyadicInterval 40),(⟨-181351274752,-181351274688⟩ : DyadicInterval 40),(⟨749363404197,749363423526⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10620558,21256916⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10620480,10620544⟩ : DyadicInterval 40),(⟨-10620672,-10620608⟩ : DyadicInterval 40),(⟨762123383545,762123402874⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21256704,21256768⟩ : DyadicInterval 40),(⟨-21257152,-21257088⟩ : DyadicInterval 40),(⟨762123383365,762123402694⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167070919483,167195315198⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155532801920,155532801984⟩ : DyadicInterval 40),(⟨-181216910080,-181216910016⟩ : DyadicInterval 40),(⟨749380858715,749380878045⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155640783680,155640783744⟩ : DyadicInterval 40),(⟨-181363604288,-181363604224⟩ : DyadicInterval 40),(⟨749361802044,749361821374⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25722820544,-25684108032⟩ : DyadicInterval 40),(⟨774965437632,774984813152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155550936960,155649850944⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181375923648,-181241544256⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1701_ok : ecellOkT e1701 = true := by decide +kernel
theorem e1701_pos {a z : ℝ} (ha1 : ((1244931/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((62289/409600 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1701 e1701_ok ha1 ha2 hz1 hz2 hz

-- box ['622041/4096000', '1244931/8192000', '7999/8000', '1']  interval_lower 32643953/274877906944
noncomputable def e1702 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266489487261,0,true,155452014208,155452014272⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932533768291,0,false,-181107181440,-181107181376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266603438113,0,true,155550936960,155550937024⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932419817439,0,false,-181241544320,-181241544256⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266468615028,0,true,155433893696,155433893760⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932554640524,0,false,-181082572160,-181082572096⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522248895,0,true,10621056,10621120⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099501006657,0,false,-10621184,-10621120⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627673,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1266479046736,0,true,155442950144,155442950208⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨932544208816,0,false,-181094871552,-181094871488⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1266603442469,0,true,155550940736,155550940800⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨932419813083,0,false,-181241549504,-181241549440⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1074118831709,0,false,-25690608704,-25690608640⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1074156626256,0,false,-25651921344,-25651921280⟩
    { al := (622041/4096000), au := (1244931/8192000), zl := (7999/8000), zu := 1,
      A := ⟨166977859485,167091810337⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155452014208,155452014272⟩ : DyadicInterval 40),(⟨-181107181440,-181107181376⟩ : DyadicInterval 40),(⟨749395105519,749395124849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155550936960,155550937024⟩ : DyadicInterval 40),(⟨-181241544320,-181241544256⟩ : DyadicInterval 40),(⟨749377659368,749377678697⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155433893696,155433893760⟩ : DyadicInterval 40),(⟨-181082572160,-181082572096⟩ : DyadicInterval 40),(⟨749398299803,749398319132⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155550936960,155550937024⟩ : DyadicInterval 40),(⟨-181241544320,-181241544256⟩ : DyadicInterval 40),(⟨749377659368,749377678697⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10621119⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10621056,10621120⟩ : DyadicInterval 40),(⟨-10621184,-10621120⟩ : DyadicInterval 40),(⟨762123383513,762123402842⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨166967418960,167091814693⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155442950144,155442950208⟩ : DyadicInterval 40),(⟨-181094871552,-181094871488⟩ : DyadicInterval 40),(⟨749396703405,749396722735⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155550940736,155550940800⟩ : DyadicInterval 40),(⟨-181241549504,-181241549440⟩ : DyadicInterval 40),(⟨749377658724,749377678054⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25690608704,-25651921280⟩ : DyadicInterval 40),(⟨774949344256,774968707232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨155452014208,155550937024⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181241544320,-181107181376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1702_ok : ecellOkT e1702 = true := by decide +kernel
theorem e1702_pos {a z : ℝ} (ha1 : ((622041/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1244931/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1702 e1702_ok ha1 ha2 hz1 hz2 hz

-- box ['1244931/8192000', '62289/409600', '7999/8000', '1']  interval_lower 131553961/1099511627776
noncomputable def e1703 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266603438112,0,true,155550936960,155550937024⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932419817440,0,false,-181241544320,-181241544256⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266717388964,0,true,155649850880,155649850944⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932305866588,0,false,-181375923648,-181375923584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266582551635,0,true,155532805696,155532805760⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932440703917,0,false,-181216915264,-181216915200⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522256385,0,true,10628544,10628608⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500999167,0,false,-10628672,-10628608⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627673,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1266592990459,0,true,155541867584,155541867648⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨932430265093,0,false,-181229224512,-181229224448⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1266717393325,0,true,155649854656,155649854720⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨932305862227,0,false,-181375928832,-181375928768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1074084185876,0,false,-25726074112,-25726074048⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1074122008376,0,false,-25687356928,-25687356864⟩
    { al := (1244931/8192000), au := (62289/409600), zl := (7999/8000), zu := 1,
      A := ⟨167091810336,167205761188⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155550936960,155550937024⟩ : DyadicInterval 40),(⟨-181241544320,-181241544256⟩ : DyadicInterval 40),(⟨749377659368,749377678698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155649850880,155649850944⟩ : DyadicInterval 40),(⟨-181375923648,-181375923584⟩ : DyadicInterval 40),(⟨749360201100,749360220430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155532805696,155532805760⟩ : DyadicInterval 40),(⟨-181216915264,-181216915200⟩ : DyadicInterval 40),(⟨749380858068,749380877398⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155649850880,155649850944⟩ : DyadicInterval 40),(⟨-181375923648,-181375923584⟩ : DyadicInterval 40),(⟨749360201100,749360220430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10628609⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10628544,10628608⟩ : DyadicInterval 40),(⟨-10628672,-10628608⟩ : DyadicInterval 40),(⟨762123383513,762123402842⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨167081362683,167205765549⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155541867584,155541867648⟩ : DyadicInterval 40),(⟨-181229224512,-181229224448⟩ : DyadicInterval 40),(⟨749379259413,749379278743⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155649854656,155649854720⟩ : DyadicInterval 40),(⟨-181375928832,-181375928768⟩ : DyadicInterval 40),(⟨749360200455,749360219784⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25726074112,-25687356864⟩ : DyadicInterval 40),(⟨774967062048,774986439936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨155550936960,155649850944⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181375923648,-181241544256⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1703_ok : ecellOkT e1703 = true := by decide +kernel
theorem e1703_pos {a z : ℝ} (ha1 : ((1244931/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((62289/409600 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1703 e1703_ok ha1 ha2 hz1 hz2 hz

-- box ['62289/409600', '1246629/8192000', '1999/2000', '7997/8000']  interval_lower 33240483/274877906944
noncomputable def e1704 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266717388963,0,true,155649850880,155649850944⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932305866589,0,false,-181375923648,-181375923584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266831339815,0,true,155748755840,155748755904⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932191915737,0,false,-181510319424,-181510319360⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266633786082,0,true,155577281088,155577281152⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932389469470,0,false,-181277331328,-181277331264⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266768594924,0,true,155694296768,155694296832⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932254660628,0,false,-181436314880,-181436314816⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543512301,0,true,31884032,31884096⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479743251,0,false,-31884992,-31884928⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554171132,0,true,42542528,42542592⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469084420,0,false,-42544192,-42544128⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626129,0,false,-1664,-1600⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626852,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266675583276,0,true,155613562880,155613562944⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932347672276,0,false,-181326621376,-181326621312⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266799971826,0,true,155721530496,155721530560⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932223283726,0,false,-181473321792,-181473321728⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074059063793,0,false,-25751791232,-25751791168⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074096900626,0,false,-25713058432,-25713058368⟩
    { al := (62289/409600), au := (1246629/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨167205761187,167319712039⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155649850880,155649850944⟩ : DyadicInterval 40),(⟨-181375923648,-181375923584⟩ : DyadicInterval 40),(⟨749360201100,749360220430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155748755840,155748755904⟩ : DyadicInterval 40),(⟨-181510319424,-181510319360⟩ : DyadicInterval 40),(⟨749342730789,749342750118⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155577281088,155577281152⟩ : DyadicInterval 40),(⟨-181277331328,-181277331264⟩ : DyadicInterval 40),(⟨749373010985,749373030315⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155694296768,155694296832⟩ : DyadicInterval 40),(⟨-181436314880,-181436314816⟩ : DyadicInterval 40),(⟨749352351990,749352371320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨31884525,42543356⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31884032,31884096⟩ : DyadicInterval 40),(⟨-31884992,-31884928⟩ : DyadicInterval 40),(⟨762123383107,762123402436⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42542528,42542592⟩ : DyadicInterval 40),(⟨-42544192,-42544128⟩ : DyadicInterval 40),(⟨762123382737,762123402066⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1664,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167163955500,167288344050⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155613562880,155613562944⟩ : DyadicInterval 40),(⟨-181326621376,-181326621312⟩ : DyadicInterval 40),(⟨749366607517,749366626846⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155721530496,155721530560⟩ : DyadicInterval 40),(⟨-181473321792,-181473321728⟩ : DyadicInterval 40),(⟨749347541175,749347560504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25751791232,-25713058368⟩ : DyadicInterval 40),(⟨774979912800,774999298496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155649850880,155748755904⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181510319424,-181375923584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1704_ok : ecellOkT e1704 = true := by decide +kernel
theorem e1704_pos {a z : ℝ} (ha1 : ((62289/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1246629/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1704 e1704_ok ha1 ha2 hz1 hz2 hz

-- box ['1246629/8192000', '623739/4096000', '1999/2000', '7997/8000']  interval_lower 133946423/1099511627776
noncomputable def e1705 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266831339814,0,true,155748755840,155748755904⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932191915738,0,false,-181510319424,-181510319360⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266945290666,0,true,155847651904,155847651968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932077964886,0,false,-181644731584,-181644731520⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266747679957,0,true,155676143168,155676143232⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932275575595,0,false,-181411647808,-181411647744⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266882503043,0,true,155793160640,155793160704⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932140752509,0,false,-181570667584,-181570667520⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543534773,0,true,31906496,31906560⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479720779,0,false,-31907520,-31907456⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554201098,0,true,42572480,42572544⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469054454,0,false,-42574208,-42574144⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626127,0,false,-1664,-1600⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626851,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266789505638,0,true,155712446400,155712446464⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932233749914,0,false,-181460977472,-181460977408⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266913901311,0,true,155820410496,155820410560⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932109354241,0,false,-181607704256,-181607704192⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074024383733,0,false,-25787293696,-25787293632⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074062248511,0,false,-25748531072,-25748531008⟩
    { al := (1246629/8192000), au := (623739/4096000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨167319712038,167433662890⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155748755840,155748755904⟩ : DyadicInterval 40),(⟨-181510319424,-181510319360⟩ : DyadicInterval 40),(⟨749342730789,749342750118⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155847651904,155847651968⟩ : DyadicInterval 40),(⟨-181644731584,-181644731520⟩ : DyadicInterval 40),(⟨749325248369,749325267698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155676143168,155676143232⟩ : DyadicInterval 40),(⟨-181411647808,-181411647744⟩ : DyadicInterval 40),(⟨749355558231,749355577560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155793160640,155793160704⟩ : DyadicInterval 40),(⟨-181570667584,-181570667520⟩ : DyadicInterval 40),(⟨749334882783,749334902112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨31906997,42573322⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31906496,31906560⟩ : DyadicInterval 40),(⟨-31907520,-31907456⟩ : DyadicInterval 40),(⟨762123383138,762123402467⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42572480,42572544⟩ : DyadicInterval 40),(⟨-42574208,-42574144⟩ : DyadicInterval 40),(⟨762123382767,762123402096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1664,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167277877862,167402273535⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155712446400,155712446464⟩ : DyadicInterval 40),(⟨-181460977472,-181460977408⟩ : DyadicInterval 40),(⟨749349145973,749349165303⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155820410496,155820410560⟩ : DyadicInterval 40),(⟨-181607704256,-181607704192⟩ : DyadicInterval 40),(⟨749330065356,749330084686⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25787293696,-25748531008⟩ : DyadicInterval 40),(⟨774997649120,775017049728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155748755840,155847651968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181644731584,-181510319360⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1705_ok : ecellOkT e1705 = true := by decide +kernel
theorem e1705_pos {a z : ℝ} (ha1 : ((1246629/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((623739/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1705 e1705_ok ha1 ha2 hz1 hz2 hz

-- box ['62289/409600', '1246629/8192000', '7997/8000', '3999/4000']  interval_lower 33204909/274877906944
noncomputable def e1706 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266717388963,0,true,155649850880,155649850944⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932305866589,0,false,-181375923648,-181375923584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266831339815,0,true,155748755840,155748755904⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932191915737,0,false,-181510319424,-181510319360⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266654686802,0,true,155595424000,155595424064⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932368568750,0,false,-181301978560,-181301978496⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266789509888,0,true,155712450112,155712450176⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932233745664,0,false,-181460982528,-181460982464⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532884086,0,true,21256064,21256128⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490371466,0,false,-21256576,-21256512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543535426,0,true,31907136,31907200⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479720126,0,false,-31908160,-31908096⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626850,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627366,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266686033562,0,true,155622633984,155622634048⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932337221990,0,false,-181338945408,-181338945344⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266810429253,0,true,155730606912,155730606976⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932212826299,0,false,-181485655872,-181485655808⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074055881544,0,false,-25755048896,-25755048832⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074093722914,0,false,-25716311360,-25716311296⟩
    { al := (62289/409600), au := (1246629/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨167205761187,167319712039⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155649850880,155649850944⟩ : DyadicInterval 40),(⟨-181375923648,-181375923584⟩ : DyadicInterval 40),(⟨749360201100,749360220430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155748755840,155748755904⟩ : DyadicInterval 40),(⟨-181510319424,-181510319360⟩ : DyadicInterval 40),(⟨749342730789,749342750118⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155595424000,155595424064⟩ : DyadicInterval 40),(⟨-181301978560,-181301978496⟩ : DyadicInterval 40),(⟨749369809107,749369828437⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155712450112,155712450176⟩ : DyadicInterval 40),(⟨-181460982528,-181460982464⟩ : DyadicInterval 40),(⟨749349145327,749349164657⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21256310,31907650⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21256064,21256128⟩ : DyadicInterval 40),(⟨-21256576,-21256512⟩ : DyadicInterval 40),(⟨762123383397,762123402726⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31907136,31907200⟩ : DyadicInterval 40),(⟨-31908160,-31908096⟩ : DyadicInterval 40),(⟨762123383138,762123402467⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167174405786,167298801477⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155622633984,155622634048⟩ : DyadicInterval 40),(⟨-181338945408,-181338945344⟩ : DyadicInterval 40),(⟨749365006257,749365025586⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155730606912,155730606976⟩ : DyadicInterval 40),(⟨-181485655872,-181485655808⟩ : DyadicInterval 40),(⟨749345937599,749345956928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25755048896,-25716311296⟩ : DyadicInterval 40),(⟨774981539264,775000927328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155649850880,155748755904⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181510319424,-181375923584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1706_ok : ecellOkT e1706 = true := by decide +kernel
theorem e1706_pos {a z : ℝ} (ha1 : ((62289/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1246629/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1706 e1706_ok ha1 ha2 hz1 hz2 hz

-- box ['1246629/8192000', '623739/4096000', '7997/8000', '3999/4000']  interval_lower 133803879/1099511627776
noncomputable def e1707 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266831339814,0,true,155748755840,155748755904⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932191915738,0,false,-181510319424,-181510319360⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266945290666,0,true,155847651904,155847651968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932077964886,0,false,-181644731584,-181644731520⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266768594921,0,true,155694296768,155694296832⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932254660631,0,false,-181436314880,-181436314816⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266903432251,0,true,155811324736,155811324800⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932119823301,0,false,-181595355072,-181595355008⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532899067,0,true,21271040,21271104⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490356485,0,false,-21271552,-21271488⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543557900,0,true,31929600,31929664⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479697652,0,false,-31930624,-31930560⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626848,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627365,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266799963297,0,true,155721523072,155721523136⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932223292255,0,false,-181473311744,-181473311680⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266924365861,0,true,155829492288,155829492352⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932098889691,0,false,-181620048256,-181620048192⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074021197147,0,false,-25790555904,-25790555840⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074059066390,0,false,-25751788608,-25751788544⟩
    { al := (1246629/8192000), au := (623739/4096000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨167319712038,167433662890⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155748755840,155748755904⟩ : DyadicInterval 40),(⟨-181510319424,-181510319360⟩ : DyadicInterval 40),(⟨749342730789,749342750118⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155847651904,155847651968⟩ : DyadicInterval 40),(⟨-181644731584,-181644731520⟩ : DyadicInterval 40),(⟨749325248369,749325267698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155694296768,155694296832⟩ : DyadicInterval 40),(⟨-181436314880,-181436314816⟩ : DyadicInterval 40),(⟨749352351991,749352371320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155811324736,155811324800⟩ : DyadicInterval 40),(⟨-181595355072,-181595355008⟩ : DyadicInterval 40),(⟨749331671713,749331691043⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21271291,31930124⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21271040,21271104⟩ : DyadicInterval 40),(⟨-21271552,-21271488⟩ : DyadicInterval 40),(⟨762123383396,762123402725⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31929600,31929664⟩ : DyadicInterval 40),(⟨-31930624,-31930560⟩ : DyadicInterval 40),(⟨762123383136,762123402465⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167288335521,167412738085⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155721523072,155721523136⟩ : DyadicInterval 40),(⟨-181473311744,-181473311680⟩ : DyadicInterval 40),(⟨749347542499,749347561829⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155829492288,155829492352⟩ : DyadicInterval 40),(⟨-181620048256,-181620048192⟩ : DyadicInterval 40),(⟨749328459576,749328478906⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25790555904,-25751788544⟩ : DyadicInterval 40),(⟨774999277888,775018680832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155748755840,155847651968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181644731584,-181510319360⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1707_ok : ecellOkT e1707 = true := by decide +kernel
theorem e1707_pos {a z : ℝ} (ha1 : ((1246629/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((623739/4096000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1707 e1707_ok ha1 ha2 hz1 hz2 hz

-- box ['623739/4096000', '1248327/8192000', '1999/2000', '7997/8000']  interval_lower 67466565/549755813888
noncomputable def e1708 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266945290665,0,true,155847651904,155847651968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932077964887,0,false,-181644731584,-181644731520⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267059241518,0,true,155946539072,155946539136⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931964014034,0,false,-181779160192,-181779160128⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266861573833,0,true,155774996288,155774996352⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932161681719,0,false,-181545980736,-181545980672⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266996411163,0,true,155892015680,155892015744⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932026844389,0,false,-181705036736,-181705036672⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543557248,0,true,31928960,31929024⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479698304,0,false,-31929984,-31929920⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554231067,0,true,42602432,42602496⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469024485,0,false,-42604160,-42604096⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626125,0,false,-1664,-1600⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626849,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266903427996,0,true,155811321024,155811321088⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932119827556,0,false,-181595350016,-181595349952⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267027830799,0,true,155919281600,155919281664⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931995424753,0,false,-181742103104,-181742103040⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073989680061,0,false,-25822821504,-25822821440⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074027572790,0,false,-25784028992,-25784028928⟩
    { al := (623739/4096000), au := (1248327/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨167433662889,167547613742⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155847651904,155847651968⟩ : DyadicInterval 40),(⟨-181644731584,-181644731520⟩ : DyadicInterval 40),(⟨749325248369,749325267698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155946539072,155946539136⟩ : DyadicInterval 40),(⟨-181779160192,-181779160128⟩ : DyadicInterval 40),(⟨749307753865,749307773195⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155774996288,155774996352⟩ : DyadicInterval 40),(⟨-181545980736,-181545980672⟩ : DyadicInterval 40),(⟨749338093456,749338112785⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155892015680,155892015744⟩ : DyadicInterval 40),(⟨-181705036736,-181705036672⟩ : DyadicInterval 40),(⟨749317401474,749317420804⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨31929472,42603291⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31928960,31929024⟩ : DyadicInterval 40),(⟨-31929984,-31929920⟩ : DyadicInterval 40),(⟨762123383136,762123402465⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42602432,42602496⟩ : DyadicInterval 40),(⟨-42604160,-42604096⟩ : DyadicInterval 40),(⟨762123382765,762123402094⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1664,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167391800220,167516203023⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155811321024,155811321088⟩ : DyadicInterval 40),(⟨-181595350016,-181595349952⟩ : DyadicInterval 40),(⟨749331672362,749331691691⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155919281600,155919281664⟩ : DyadicInterval 40),(⟨-181742103104,-181742103040⟩ : DyadicInterval 40),(⟨749312577437,749312596767⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25822821504,-25784028928⟩ : DyadicInterval 40),(⟨775015398080,775034813632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155847651904,155946539136⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181779160192,-181644731520⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1708_ok : ecellOkT e1708 = true := by decide +kernel
theorem e1708_pos {a z : ℝ} (ha1 : ((623739/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1248327/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1708 e1708_ok ha1 ha2 hz1 hz2 hz

-- box ['1248327/8192000', '156147/1024000', '1999/2000', '7997/8000']  interval_lower 67961369/549755813888
noncomputable def e1709 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267059241517,0,true,155946539072,155946539136⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931964014035,0,false,-181779160192,-181779160128⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267173192369,0,true,156045417408,156045417472⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931850063183,0,false,-181913605248,-181913605184⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266975467710,0,true,155873840576,155873840640⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932047787842,0,false,-181680330048,-181680329984⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267110319283,0,true,155990861760,155990861824⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931912936269,0,false,-181839422336,-181839422272⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543579724,0,true,31951424,31951488⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479675828,0,false,-31952448,-31952384⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554261038,0,true,42632384,42632448⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468994514,0,false,-42634112,-42634048⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626122,0,false,-1664,-1600⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626848,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267017350614,0,true,155910186944,155910187008⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932005904938,0,false,-181729739328,-181729739264⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267141760283,0,true,156018143808,156018143872⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931881495269,0,false,-181876518400,-181876518336⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073954952780,0,false,-25858374592,-25858374528⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073992873382,0,false,-25819552320,-25819552256⟩
    { al := (1248327/8192000), au := (156147/1024000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨167547613741,167661564593⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155946539072,155946539136⟩ : DyadicInterval 40),(⟨-181779160192,-181779160128⟩ : DyadicInterval 40),(⟨749307753865,749307773195⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156045417408,156045417472⟩ : DyadicInterval 40),(⟨-181913605248,-181913605184⟩ : DyadicInterval 40),(⟨749290247241,749290266571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155873840576,155873840640⟩ : DyadicInterval 40),(⟨-181680330048,-181680329984⟩ : DyadicInterval 40),(⟨749320616559,749320635888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155990861760,155990861824⟩ : DyadicInterval 40),(⟨-181839422336,-181839422272⟩ : DyadicInterval 40),(⟨749299908138,749299927467⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨31951948,42633262⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31951424,31951488⟩ : DyadicInterval 40),(⟨-31952448,-31952384⟩ : DyadicInterval 40),(⟨762123383135,762123402464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42632384,42632448⟩ : DyadicInterval 40),(⟨-42634112,-42634048⟩ : DyadicInterval 40),(⟨762123382762,762123402091⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1664,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167505722838,167630132507⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155910186944,155910187008⟩ : DyadicInterval 40),(⟨-181729739328,-181729739264⟩ : DyadicInterval 40),(⟨749314186664,749314205994⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156018143808,156018143872⟩ : DyadicInterval 40),(⟨-181876518400,-181876518336⟩ : DyadicInterval 40),(⟨749295077444,749295096773⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25858374592,-25819552256⟩ : DyadicInterval 40),(⟨775033159744,775052590176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155946539072,156045417472⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181913605248,-181779160128⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1709_ok : ecellOkT e1709 = true := by decide +kernel
theorem e1709_pos {a z : ℝ} (ha1 : ((1248327/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((156147/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1709 e1709_ok ha1 ha2 hz1 hz2 hz

-- box ['623739/4096000', '1248327/8192000', '7997/8000', '3999/4000']  interval_lower 134789737/1099511627776
noncomputable def e1710 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266945290665,0,true,155847651904,155847651968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932077964887,0,false,-181644731584,-181644731520⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267059241518,0,true,155946539072,155946539136⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931964014034,0,false,-181779160192,-181779160128⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266882503041,0,true,155793160640,155793160704⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932140752511,0,false,-181570667584,-181570667520⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267017354615,0,true,155910190464,155910190528⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932005900937,0,false,-181729744000,-181729743936⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532914050,0,true,21286016,21286080⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490341502,0,false,-21286528,-21286464⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543580377,0,true,31952128,31952192⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479675175,0,false,-31953088,-31953024⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626847,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627364,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266913892524,0,true,155820402880,155820402944⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932109363028,0,false,-181607693888,-181607693824⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267038302470,0,true,155928368704,155928368768⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931984953082,0,false,-181754457024,-181754456960⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073986489137,0,false,-25826088256,-25826088192⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074024386410,0,false,-25787290944,-25787290880⟩
    { al := (623739/4096000), au := (1248327/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨167433662889,167547613742⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155847651904,155847651968⟩ : DyadicInterval 40),(⟨-181644731584,-181644731520⟩ : DyadicInterval 40),(⟨749325248369,749325267698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155946539072,155946539136⟩ : DyadicInterval 40),(⟨-181779160192,-181779160128⟩ : DyadicInterval 40),(⟨749307753865,749307773195⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155793160640,155793160704⟩ : DyadicInterval 40),(⟨-181570667584,-181570667520⟩ : DyadicInterval 40),(⟨749334882783,749334902113⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155910190464,155910190528⟩ : DyadicInterval 40),(⟨-181729744000,-181729743936⟩ : DyadicInterval 40),(⟨749314186002,749314205332⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21286274,31952601⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21286016,21286080⟩ : DyadicInterval 40),(⟨-21286528,-21286464⟩ : DyadicInterval 40),(⟨762123383395,762123402724⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31952128,31952192⟩ : DyadicInterval 40),(⟨-31953088,-31953024⟩ : DyadicInterval 40),(⟨762123383103,762123402432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167402264748,167526674694⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155820402880,155820402944⟩ : DyadicInterval 40),(⟨-181607693888,-181607693824⟩ : DyadicInterval 40),(⟨749330066698,749330086027⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155928368704,155928368768⟩ : DyadicInterval 40),(⟨-181754457024,-181754456960⟩ : DyadicInterval 40),(⟨749310969487,749310988816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25826088256,-25787290880⟩ : DyadicInterval 40),(⟨775017029056,775036447008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155847651904,155946539136⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181779160192,-181644731520⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1710_ok : ecellOkT e1710 = true := by decide +kernel
theorem e1710_pos {a z : ℝ} (ha1 : ((623739/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1248327/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1710 e1710_ok ha1 ha2 hz1 hz2 hz

-- box ['1248327/8192000', '156147/1024000', '7997/8000', '3999/4000']  interval_lower 33944719/274877906944
noncomputable def e1711 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267059241517,0,true,155946539072,155946539136⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931964014035,0,false,-181779160192,-181779160128⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267173192369,0,true,156045417408,156045417472⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931850063183,0,false,-181913605248,-181913605184⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266996411161,0,true,155892015680,155892015744⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932026844391,0,false,-181705036736,-181705036672⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267131276978,0,true,156009047296,156009047360⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931891978574,0,false,-181864149440,-181864149376⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532929034,0,true,21300992,21301056⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490326518,0,false,-21301504,-21301440⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543602855,0,true,31974592,31974656⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479652697,0,false,-31975552,-31975488⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626846,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627364,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267027822009,0,true,155919273984,155919274048⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931995433543,0,false,-181742092736,-181742092672⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267152239077,0,true,156027236288,156027236352⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931871016475,0,false,-181888882240,-181888882176⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073951757514,0,false,-25861645888,-25861645824⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073989682741,0,false,-25822818752,-25822818688⟩
    { al := (1248327/8192000), au := (156147/1024000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨167547613741,167661564593⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155946539072,155946539136⟩ : DyadicInterval 40),(⟨-181779160192,-181779160128⟩ : DyadicInterval 40),(⟨749307753865,749307773195⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156045417408,156045417472⟩ : DyadicInterval 40),(⟨-181913605248,-181913605184⟩ : DyadicInterval 40),(⟨749290247241,749290266571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155892015680,155892015744⟩ : DyadicInterval 40),(⟨-181705036736,-181705036672⟩ : DyadicInterval 40),(⟨749317401475,749317420804⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156009047296,156009047360⟩ : DyadicInterval 40),(⟨-181864149440,-181864149376⟩ : DyadicInterval 40),(⟨749296688246,749296707576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21301258,31975079⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21300992,21301056⟩ : DyadicInterval 40),(⟨-21301504,-21301440⟩ : DyadicInterval 40),(⟨762123383395,762123402724⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31974592,31974656⟩ : DyadicInterval 40),(⟨-31975552,-31975488⟩ : DyadicInterval 40),(⟨762123383102,762123402431⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167516194233,167640611301⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155919273984,155919274048⟩ : DyadicInterval 40),(⟨-181742092736,-181742092672⟩ : DyadicInterval 40),(⟨749312578781,749312598110⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156027236288,156027236352⟩ : DyadicInterval 40),(⟨-181888882240,-181888882176⟩ : DyadicInterval 40),(⟨749293467283,749293486613⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25861645888,-25822818688⟩ : DyadicInterval 40),(⟨775034792960,775054225824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155946539072,156045417472⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181913605248,-181779160128⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1711_ok : ecellOkT e1711 = true := by decide +kernel
theorem e1711_pos {a z : ℝ} (ha1 : ((1248327/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((156147/1024000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1711 e1711_ok ha1 ha2 hz1 hz2 hz

-- box ['62289/409600', '1246629/8192000', '3999/4000', '7999/8000']  interval_lower 33169269/274877906944
noncomputable def e1712 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266717388963,0,true,155649850880,155649850944⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932305866589,0,false,-181375923648,-181375923584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266831339815,0,true,155748755840,155748755904⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932191915737,0,false,-181510319424,-181510319360⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266675587522,0,true,155613566592,155613566656⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932347668030,0,false,-181326626368,-181326626304⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266810424852,0,true,155730603136,155730603200⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932212830700,0,false,-181485650688,-181485650624⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522255825,0,true,10627968,10628032⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500999727,0,false,-10628160,-10628096⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532899674,0,true,21271680,21271744⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490355878,0,false,-21272128,-21272064⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627364,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627674,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266696483867,0,true,155631705088,155631705152⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932326771685,0,false,-181351269568,-181351269504⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266820886703,0,true,155739683328,155739683392⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932202368849,0,false,-181497990144,-181497990080⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074052699088,0,false,-25758306816,-25758306752⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074090544997,0,false,-25719564480,-25719564416⟩
    { al := (62289/409600), au := (1246629/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨167205761187,167319712039⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155649850880,155649850944⟩ : DyadicInterval 40),(⟨-181375923648,-181375923584⟩ : DyadicInterval 40),(⟨749360201100,749360220430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155748755840,155748755904⟩ : DyadicInterval 40),(⟨-181510319424,-181510319360⟩ : DyadicInterval 40),(⟨749342730789,749342750118⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155613566592,155613566656⟩ : DyadicInterval 40),(⟨-181326626368,-181326626304⟩ : DyadicInterval 40),(⟨749366606845,749366626174⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155730603136,155730603200⟩ : DyadicInterval 40),(⟨-181485650688,-181485650624⟩ : DyadicInterval 40),(⟨749345938251,749345957580⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10628049,21271898⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10627968,10628032⟩ : DyadicInterval 40),(⟨-10628160,-10628096⟩ : DyadicInterval 40),(⟨762123383545,762123402874⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21271680,21271744⟩ : DyadicInterval 40),(⟨-21272128,-21272064⟩ : DyadicInterval 40),(⟨762123383364,762123402693⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167184856091,167309258927⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155631705088,155631705152⟩ : DyadicInterval 40),(⟨-181351269568,-181351269504⟩ : DyadicInterval 40),(⟨749363404845,749363424174⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155739683328,155739683392⟩ : DyadicInterval 40),(⟨-181497990144,-181497990080⟩ : DyadicInterval 40),(⟨749344333897,749344353226⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25758306816,-25719564416⟩ : DyadicInterval 40),(⟨774983165824,775002556288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155649850880,155748755904⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181510319424,-181375923584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1712_ok : ecellOkT e1712 = true := by decide +kernel
theorem e1712_pos {a z : ℝ} (ha1 : ((62289/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1246629/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1712 e1712_ok ha1 ha2 hz1 hz2 hz

-- box ['1246629/8192000', '623739/4096000', '3999/4000', '7999/8000']  interval_lower 4176893/34359738368
noncomputable def e1713 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266831339814,0,true,155748755840,155748755904⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932191915738,0,false,-181510319424,-181510319360⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266945290666,0,true,155847651904,155847651968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932077964886,0,false,-181644731584,-181644731520⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266789509885,0,true,155712450112,155712450176⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932233745667,0,false,-181460982528,-181460982464⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266924361459,0,true,155829488448,155829488512⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932098894093,0,false,-181620043072,-181620043008⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522263315,0,true,10635456,10635520⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500992237,0,false,-10635648,-10635584⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532914657,0,true,21286656,21286720⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490340895,0,false,-21287104,-21287040⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627363,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627674,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266810420468,0,true,155730599296,155730599360⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932212835084,0,false,-181485645504,-181485645440⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266934830429,0,true,155838574016,155838574080⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932088425123,0,false,-181632392384,-181632392320⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074018010356,0,false,-25793818368,-25793818304⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074055884218,0,false,-25755046208,-25755046144⟩
    { al := (1246629/8192000), au := (623739/4096000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨167319712038,167433662890⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155748755840,155748755904⟩ : DyadicInterval 40),(⟨-181510319424,-181510319360⟩ : DyadicInterval 40),(⟨749342730789,749342750118⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155847651904,155847651968⟩ : DyadicInterval 40),(⟨-181644731584,-181644731520⟩ : DyadicInterval 40),(⟨749325248369,749325267698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155712450112,155712450176⟩ : DyadicInterval 40),(⟨-181460982528,-181460982464⟩ : DyadicInterval 40),(⟨749349145327,749349164657⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155829488448,155829488512⟩ : DyadicInterval 40),(⟨-181620043072,-181620043008⟩ : DyadicInterval 40),(⟨749328460266,749328479596⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10635539,21286881⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10635456,10635520⟩ : DyadicInterval 40),(⟨-10635648,-10635584⟩ : DyadicInterval 40),(⟨762123383545,762123402874⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21286656,21286720⟩ : DyadicInterval 40),(⟨-21287104,-21287040⟩ : DyadicInterval 40),(⟨762123383363,762123402692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167298792692,167423202653⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155730599296,155730599360⟩ : DyadicInterval 40),(⟨-181485645504,-181485645440⟩ : DyadicInterval 40),(⟨749345938938,749345958267⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155838574016,155838574080⟩ : DyadicInterval 40),(⟨-181632392384,-181632392320⟩ : DyadicInterval 40),(⟨749326853680,749326873010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25793818368,-25755046144⟩ : DyadicInterval 40),(⟨775000906688,775020312064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155748755840,155847651968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181644731584,-181510319360⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1713_ok : ecellOkT e1713 = true := by decide +kernel
theorem e1713_pos {a z : ℝ} (ha1 : ((1246629/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((623739/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1713 e1713_ok ha1 ha2 hz1 hz2 hz

-- box ['62289/409600', '1246629/8192000', '7999/8000', '1']  interval_lower 66267307/549755813888
noncomputable def e1714 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266717388963,0,true,155649850880,155649850944⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932305866589,0,false,-181375923648,-181375923584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266831339815,0,true,155748755840,155748755904⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932191915737,0,false,-181510319424,-181510319360⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266696488242,0,true,155631708864,155631708928⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932326767310,0,false,-181351274752,-181351274688⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522263877,0,true,10636032,10636096⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500991675,0,false,-10636160,-10636096⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627673,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1266706934192,0,true,155640776064,155640776128⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨932316321360,0,false,-181363593920,-181363593856⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1266831344172,0,true,155748759616,155748759680⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨932191911380,0,false,-181510324544,-181510324480⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1074049516428,0,false,-25761564928,-25761564864⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1074087366876,0,false,-25722817856,-25722817792⟩
    { al := (62289/409600), au := (1246629/8192000), zl := (7999/8000), zu := 1,
      A := ⟨167205761187,167319712039⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155649850880,155649850944⟩ : DyadicInterval 40),(⟨-181375923648,-181375923584⟩ : DyadicInterval 40),(⟨749360201100,749360220430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155748755840,155748755904⟩ : DyadicInterval 40),(⟨-181510319424,-181510319360⟩ : DyadicInterval 40),(⟨749342730789,749342750118⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155631708864,155631708928⟩ : DyadicInterval 40),(⟨-181351274752,-181351274688⟩ : DyadicInterval 40),(⟨749363404197,749363423526⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155748755840,155748755904⟩ : DyadicInterval 40),(⟨-181510319424,-181510319360⟩ : DyadicInterval 40),(⟨749342730789,749342750118⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10636101⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10636032,10636096⟩ : DyadicInterval 40),(⟨-10636160,-10636096⟩ : DyadicInterval 40),(⟨762123383513,762123402842⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨167195306416,167319716396⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155640776064,155640776128⟩ : DyadicInterval 40),(⟨-181363593920,-181363593856⟩ : DyadicInterval 40),(⟨749361803381,749361822711⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155748759616,155748759680⟩ : DyadicInterval 40),(⟨-181510324544,-181510324480⟩ : DyadicInterval 40),(⟨749342730116,749342749446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25761564928,-25722817792⟩ : DyadicInterval 40),(⟨774984792512,775004185344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨155649850880,155748755904⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181510319424,-181375923584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1714_ok : ecellOkT e1714 = true := by decide +kernel
theorem e1714_pos {a z : ℝ} (ha1 : ((62289/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1246629/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1714 e1714_ok ha1 ha2 hz1 hz2 hz

-- box ['1246629/8192000', '623739/4096000', '7999/8000', '1']  interval_lower 33379411/274877906944
noncomputable def e1715 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266831339814,0,true,155748755840,155748755904⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932191915738,0,false,-181510319424,-181510319360⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266945290666,0,true,155847651904,155847651968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932077964886,0,false,-181644731584,-181644731520⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266810424849,0,true,155730603136,155730603200⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932212830703,0,false,-181485650688,-181485650624⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522271368,0,true,10643520,10643584⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500984184,0,false,-10643648,-10643584⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627672,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1266820877918,0,true,155739675648,155739675712⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨932202377634,0,false,-181497979776,-181497979712⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1266945295023,0,true,155847655680,155847655744⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨932077960529,0,false,-181644736704,-181644736640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1074014823358,0,false,-25797081024,-25797080960⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1074052701763,0,false,-25758304064,-25758304000⟩
    { al := (1246629/8192000), au := (623739/4096000), zl := (7999/8000), zu := 1,
      A := ⟨167319712038,167433662890⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155748755840,155748755904⟩ : DyadicInterval 40),(⟨-181510319424,-181510319360⟩ : DyadicInterval 40),(⟨749342730789,749342750118⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155847651904,155847651968⟩ : DyadicInterval 40),(⟨-181644731584,-181644731520⟩ : DyadicInterval 40),(⟨749325248369,749325267698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155730603136,155730603200⟩ : DyadicInterval 40),(⟨-181485650688,-181485650624⟩ : DyadicInterval 40),(⟨749345938251,749345957581⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155847651904,155847651968⟩ : DyadicInterval 40),(⟨-181644731584,-181644731520⟩ : DyadicInterval 40),(⟨749325248369,749325267698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10643592⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10643520,10643584⟩ : DyadicInterval 40),(⟨-10643648,-10643584⟩ : DyadicInterval 40),(⟨762123383512,762123402841⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨167309250142,167433667247⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155739675648,155739675712⟩ : DyadicInterval 40),(⟨-181497979776,-181497979712⟩ : DyadicInterval 40),(⟨749344335273,749344354602⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155847655680,155847655744⟩ : DyadicInterval 40),(⟨-181644736704,-181644736640⟩ : DyadicInterval 40),(⟨749325247695,749325267024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25797081024,-25758304000⟩ : DyadicInterval 40),(⟨775002535616,775021943392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨155748755840,155847651968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181644731584,-181510319360⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1715_ok : ecellOkT e1715 = true := by decide +kernel
theorem e1715_pos {a z : ℝ} (ha1 : ((1246629/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((623739/4096000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1715 e1715_ok ha1 ha2 hz1 hz2 hz

-- box ['623739/4096000', '1248327/8192000', '3999/4000', '7999/8000']  interval_lower 134646657/1099511627776
noncomputable def e1716 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266945290665,0,true,155847651904,155847651968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932077964887,0,false,-181644731584,-181644731520⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267059241518,0,true,155946539072,155946539136⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931964014034,0,false,-181779160192,-181779160128⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266903432249,0,true,155811324736,155811324800⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932119823303,0,false,-181595355072,-181595355008⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267038298067,0,true,155928364928,155928364992⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931984957485,0,false,-181754451840,-181754451776⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522270807,0,true,10642944,10643008⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500984745,0,false,-10643136,-10643072⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532929641,0,true,21301632,21301696⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490325911,0,false,-21302080,-21302016⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627363,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627673,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266924357073,0,true,155829484672,155829484736⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932098898479,0,false,-181620037888,-181620037824⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267048774161,0,true,155937455808,155937455872⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931974481391,0,false,-181766811072,-181766811008⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073983298006,0,false,-25829355264,-25829355200⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074021199824,0,false,-25790553216,-25790553152⟩
    { al := (623739/4096000), au := (1248327/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨167433662889,167547613742⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155847651904,155847651968⟩ : DyadicInterval 40),(⟨-181644731584,-181644731520⟩ : DyadicInterval 40),(⟨749325248369,749325267698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155946539072,155946539136⟩ : DyadicInterval 40),(⟨-181779160192,-181779160128⟩ : DyadicInterval 40),(⟨749307753865,749307773195⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155811324736,155811324800⟩ : DyadicInterval 40),(⟨-181595355072,-181595355008⟩ : DyadicInterval 40),(⟨749331671714,749331691043⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155928364928,155928364992⟩ : DyadicInterval 40),(⟨-181754451840,-181754451776⟩ : DyadicInterval 40),(⟨749310970142,749310989471⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10643031,21301865⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10642944,10643008⟩ : DyadicInterval 40),(⟨-10643136,-10643072⟩ : DyadicInterval 40),(⟨762123383544,762123402873⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21301632,21301696⟩ : DyadicInterval 40),(⟨-21302080,-21302016⟩ : DyadicInterval 40),(⟨762123383363,762123402692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167412729297,167537146385⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155829484672,155829484736⟩ : DyadicInterval 40),(⟨-181620037888,-181620037824⟩ : DyadicInterval 40),(⟨749328460918,749328480247⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155937455808,155937455872⟩ : DyadicInterval 40),(⟨-181766811072,-181766811008⟩ : DyadicInterval 40),(⟨749309361384,749309380713⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25829355264,-25790553152⟩ : DyadicInterval 40),(⟨775018660192,775038080512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155847651904,155946539136⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181779160192,-181644731520⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1716_ok : ecellOkT e1716 = true := by decide +kernel
theorem e1716_pos {a z : ℝ} (ha1 : ((623739/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1248327/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1716 e1716_ok ha1 ha2 hz1 hz2 hz

-- box ['1248327/8192000', '156147/1024000', '3999/4000', '7999/8000']  interval_lower 135635295/1099511627776
noncomputable def e1717 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267059241517,0,true,155946539072,155946539136⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931964014035,0,false,-181779160192,-181779160128⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267173192369,0,true,156045417408,156045417472⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931850063183,0,false,-181913605248,-181913605184⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267017354613,0,true,155910190464,155910190528⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932005900939,0,false,-181729744000,-181729743936⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267152234674,0,true,156027232448,156027232512⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931871020878,0,false,-181888877056,-181888876992⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522278299,0,true,10650432,10650496⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500977253,0,false,-10650624,-10650560⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532944627,0,true,21316608,21316672⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490310925,0,false,-21317120,-21317056⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627362,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627673,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267038293679,0,true,155928361088,155928361152⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931984961873,0,false,-181754446656,-181754446592⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267162717889,0,true,156036328768,156036328832⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931860537663,0,false,-181901246208,-181901246144⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073948562042,0,false,-25864917440,-25864917376⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073986491817,0,false,-25826085504,-25826085440⟩
    { al := (1248327/8192000), au := (156147/1024000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨167547613741,167661564593⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155946539072,155946539136⟩ : DyadicInterval 40),(⟨-181779160192,-181779160128⟩ : DyadicInterval 40),(⟨749307753865,749307773195⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156045417408,156045417472⟩ : DyadicInterval 40),(⟨-181913605248,-181913605184⟩ : DyadicInterval 40),(⟨749290247241,749290266571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155910190464,155910190528⟩ : DyadicInterval 40),(⟨-181729744000,-181729743936⟩ : DyadicInterval 40),(⟨749314186002,749314205332⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156027232448,156027232512⟩ : DyadicInterval 40),(⟨-181888877056,-181888876992⟩ : DyadicInterval 40),(⟨749293467975,749293487305⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10650523,21316851⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10650432,10650496⟩ : DyadicInterval 40),(⟨-10650624,-10650560⟩ : DyadicInterval 40),(⟨762123383544,762123402873⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21316608,21316672⟩ : DyadicInterval 40),(⟨-21317120,-21317056⟩ : DyadicInterval 40),(⟨762123383394,762123402723⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167526665903,167651090113⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155928361088,155928361152⟩ : DyadicInterval 40),(⟨-181754446656,-181754446592⟩ : DyadicInterval 40),(⟨749310970831,749310990160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156036328768,156036328832⟩ : DyadicInterval 40),(⟨-181901246208,-181901246144⟩ : DyadicInterval 40),(⟨749291856969,749291876299⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25864917440,-25826085440⟩ : DyadicInterval 40),(⟨775036426336,775055861600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155946539072,156045417472⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181913605248,-181779160128⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1717_ok : ecellOkT e1717 = true := by decide +kernel
theorem e1717_pos {a z : ℝ} (ha1 : ((1248327/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((156147/1024000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1717 e1717_ok ha1 ha2 hz1 hz2 hz

-- box ['623739/4096000', '1248327/8192000', '7999/8000', '1']  interval_lower 134503523/1099511627776
noncomputable def e1718 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266945290665,0,true,155847651904,155847651968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932077964887,0,false,-181644731584,-181644731520⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267059241518,0,true,155946539072,155946539136⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931964014034,0,false,-181779160192,-181779160128⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266924361457,0,true,155829488448,155829488512⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932098894095,0,false,-181620043008,-181620042944⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522278860,0,true,10651008,10651072⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500976692,0,false,-10651136,-10651072⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627672,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1266934821644,0,true,155838566400,155838566464⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨932088433908,0,false,-181632382016,-181632381952⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1267059245873,0,true,155946542848,155946542912⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨931964009679,0,false,-181779165312,-181779165248⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1073980106670,0,false,-25832622464,-25832622400⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1074018013033,0,false,-25793815616,-25793815552⟩
    { al := (623739/4096000), au := (1248327/8192000), zl := (7999/8000), zu := 1,
      A := ⟨167433662889,167547613742⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155847651904,155847651968⟩ : DyadicInterval 40),(⟨-181644731584,-181644731520⟩ : DyadicInterval 40),(⟨749325248369,749325267698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155946539072,155946539136⟩ : DyadicInterval 40),(⟨-181779160192,-181779160128⟩ : DyadicInterval 40),(⟨749307753865,749307773195⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155829488448,155829488512⟩ : DyadicInterval 40),(⟨-181620043008,-181620042944⟩ : DyadicInterval 40),(⟨749328460240,749328479569⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155946539072,155946539136⟩ : DyadicInterval 40),(⟨-181779160192,-181779160128⟩ : DyadicInterval 40),(⟨749307753865,749307773195⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10651084⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10651008,10651072⟩ : DyadicInterval 40),(⟨-10651136,-10651072⟩ : DyadicInterval 40),(⟨762123383512,762123402841⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨167423193868,167547618097⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155838566400,155838566464⟩ : DyadicInterval 40),(⟨-181632382016,-181632381952⟩ : DyadicInterval 40),(⟨749326855022,749326874351⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155946542848,155946542912⟩ : DyadicInterval 40),(⟨-181779165312,-181779165248⟩ : DyadicInterval 40),(⟨749307753191,749307772520⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25832622464,-25793815552⟩ : DyadicInterval 40),(⟨775020291392,775039714112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨155847651904,155946539136⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181779160192,-181644731520⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1718_ok : ecellOkT e1718 = true := by decide +kernel
theorem e1718_pos {a z : ℝ} (ha1 : ((623739/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1248327/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1718 e1718_ok ha1 ha2 hz1 hz2 hz

-- box ['1248327/8192000', '156147/1024000', '7999/8000', '1']  interval_lower 8468245/68719476736
noncomputable def e1719 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267059241517,0,true,155946539072,155946539136⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931964014035,0,false,-181779160192,-181779160128⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267173192369,0,true,156045417408,156045417472⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931850063183,0,false,-181913605248,-181913605184⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267038298065,0,true,155928364928,155928364992⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931984957487,0,false,-181754451840,-181754451776⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522286353,0,true,10658496,10658560⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500969199,0,false,-10658688,-10658624⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627672,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1267048765370,0,true,155937448192,155937448256⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨931974490182,0,false,-181766800704,-181766800640⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1267173196729,0,true,156045421184,156045421248⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨931850058823,0,false,-181913610368,-181913610304⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1073945366361,0,false,-25868189184,-25868189120⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1073983300686,0,false,-25829352512,-25829352448⟩
    { al := (1248327/8192000), au := (156147/1024000), zl := (7999/8000), zu := 1,
      A := ⟨167547613741,167661564593⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155946539072,155946539136⟩ : DyadicInterval 40),(⟨-181779160192,-181779160128⟩ : DyadicInterval 40),(⟨749307753865,749307773195⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156045417408,156045417472⟩ : DyadicInterval 40),(⟨-181913605248,-181913605184⟩ : DyadicInterval 40),(⟨749290247241,749290266571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155928364928,155928364992⟩ : DyadicInterval 40),(⟨-181754451840,-181754451776⟩ : DyadicInterval 40),(⟨749310970142,749310989471⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156045417408,156045417472⟩ : DyadicInterval 40),(⟨-181913605248,-181913605184⟩ : DyadicInterval 40),(⟨749290247241,749290266571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10658577⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10658496,10658560⟩ : DyadicInterval 40),(⟨-10658688,-10658624⟩ : DyadicInterval 40),(⟨762123383544,762123402873⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨167537137594,167661568953⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155937448192,155937448256⟩ : DyadicInterval 40),(⟨-181766800704,-181766800640⟩ : DyadicInterval 40),(⟨749309362728,749309382057⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156045421184,156045421248⟩ : DyadicInterval 40),(⟨-181913610368,-181913610304⟩ : DyadicInterval 40),(⟨749290246565,749290265894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25868189184,-25829352448⟩ : DyadicInterval 40),(⟨775038059840,775057497472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨155946539072,156045417472⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181913605248,-181779160128⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1719_ok : ecellOkT e1719 = true := by decide +kernel
theorem e1719_pos {a z : ℝ} (ha1 : ((1248327/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((156147/1024000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1719 e1719_ok ha1 ha2 hz1 hz2 hz

-- box ['156147/1024000', '50001/327680', '999/1000', '7993/8000']  interval_lower 68744447/549755813888
noncomputable def e1720 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267173192368,0,true,156045417408,156045417472⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931850063184,0,false,-181913605248,-181913605184⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267287143220,0,true,156144286784,156144286848⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931736112332,0,false,-182048066752,-182048066688⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267005530803,0,true,155899929728,155899929792⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932017724749,0,false,-181715795264,-181715795200⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267140339645,0,true,156016911104,156016911168⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931882915907,0,false,-181874842240,-181874842176⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586234471,0,true,74604160,74604224⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437021081,0,false,-74609280,-74609216⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099596953251,0,true,85322112,85322176⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099426302301,0,false,-85328832,-85328768⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621154,0,false,-6656,-6592⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622714,0,false,-5120,-5056⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267089357860,0,true,155972672704,155972672768⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931933897692,0,false,-181814691392,-181814691328⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267213746333,0,true,156080605056,156080605120⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931809509219,0,false,-181961456832,-181961456768⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073932998266,0,false,-25880851776,-25880851712⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073970928696,0,false,-25842018624,-25842018560⟩
    { al := (156147/1024000), au := (50001/327680), zl := (999/1000), zu := (7993/8000),
      A := ⟨167661564592,167775515444⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156045417408,156045417472⟩ : DyadicInterval 40),(⟨-181913605248,-181913605184⟩ : DyadicInterval 40),(⟨749290247241,749290266571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156144286784,156144286848⟩ : DyadicInterval 40),(⟨-182048066752,-182048066688⟩ : DyadicInterval 40),(⟨749272728569,749272747898⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155899929728,155899929792⟩ : DyadicInterval 40),(⟨-181715795264,-181715795200⟩ : DyadicInterval 40),(⟨749316001413,749316020742⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156016911104,156016911168⟩ : DyadicInterval 40),(⟨-181874842240,-181874842176⟩ : DyadicInterval 40),(⟨749295295745,749295315075⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨74606695,85325475⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74604160,74604224⟩ : DyadicInterval 40),(⟨-74609280,-74609216⟩ : DyadicInterval 40),(⟨762123381049,762123400378⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨85322112,85322176⟩ : DyadicInterval 40),(⟨-85328832,-85328768⟩ : DyadicInterval 40),(⟨762123380290,762123399619⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6656,-5056⟩ : DyadicInterval 40),(⟨762123386144,762123406208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167577730084,167702118557⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155972672704,155972672768⟩ : DyadicInterval 40),(⟨-181814691392,-181814691328⟩ : DyadicInterval 40),(⟨749303128185,749303147514⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156080605056,156080605120⟩ : DyadicInterval 40),(⟨-181961456832,-181961456768⟩ : DyadicInterval 40),(⟨749284013888,749284033218⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25880851776,-25842018560⟩ : DyadicInterval 40),(⟨775044392896,775063828768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156045417408,156144286848⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182048066752,-181913605184⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1720_ok : ecellOkT e1720 = true := by decide +kernel
theorem e1720_pos {a z : ℝ} (ha1 : ((156147/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((50001/327680 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1720 e1720_ok ha1 ha2 hz1 hz2 hz

-- box ['50001/327680', '625437/4096000', '999/1000', '7993/8000']  interval_lower 138484899/1099511627776
noncomputable def e1721 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267287143219,0,true,156144286784,156144286848⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931736112333,0,false,-182048066752,-182048066688⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267401094071,0,true,156243147264,156243147328⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931622161481,0,false,-182182544640,-182182544576⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267119367703,0,true,155998713344,155998713408⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931903887849,0,false,-181850098112,-181850098048⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267254190789,0,true,156115696512,156115696576⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931769064763,0,false,-182009181312,-182009181248⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586286921,0,true,74656576,74656640⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436968631,0,false,-74661696,-74661632⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099597013199,0,true,85382080,85382144⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099426242353,0,false,-85388800,-85388736⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621145,0,false,-6656,-6592⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622707,0,false,-5120,-5056⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267203251734,0,true,156071499264,156071499328⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931820003818,0,false,-181949073536,-181949073472⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267327647330,0,true,156179428032,156179428096⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931695608222,0,false,-182095865344,-182095865280⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073898241152,0,false,-25916437312,-25916437248⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073936199527,0,false,-25877574272,-25877574208⟩
    { al := (50001/327680), au := (625437/4096000), zl := (999/1000), zu := (7993/8000),
      A := ⟨167775515443,167889466295⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156144286784,156144286848⟩ : DyadicInterval 40),(⟨-182048066752,-182048066688⟩ : DyadicInterval 40),(⟨749272728569,749272747898⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156243147264,156243147328⟩ : DyadicInterval 40),(⟨-182182544640,-182182544576⟩ : DyadicInterval 40),(⟨749255197783,749255217112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155998713344,155998713408⟩ : DyadicInterval 40),(⟨-181850098112,-181850098048⟩ : DyadicInterval 40),(⟨749298518008,749298537338⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156115696512,156115696576⟩ : DyadicInterval 40),(⟨-182009181312,-182009181248⟩ : DyadicInterval 40),(⟨749277795888,749277815217⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨74659145,85385423⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74656576,74656640⟩ : DyadicInterval 40),(⟨-74661696,-74661632⟩ : DyadicInterval 40),(⟨762123381042,762123400371⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨85382080,85382144⟩ : DyadicInterval 40),(⟨-85388800,-85388736⟩ : DyadicInterval 40),(⟨762123380280,762123399610⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6656,-5056⟩ : DyadicInterval 40),(⟨762123386144,762123406208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167691623958,167816019554⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156071499264,156071499328⟩ : DyadicInterval 40),(⟨-181949073536,-181949073472⟩ : DyadicInterval 40),(⟨749285627106,749285646435⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156179428032,156179428096⟩ : DyadicInterval 40),(⟨-182095865344,-182095865280⟩ : DyadicInterval 40),(⟨749266498568,749266517897⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25916437312,-25877574208⟩ : DyadicInterval 40),(⟨775062170720,775081621536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156144286784,156243147328⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182182544640,-182048066688⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1721_ok : ecellOkT e1721 = true := by decide +kernel
theorem e1721_pos {a z : ℝ} (ha1 : ((50001/327680 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((625437/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1721 e1721_ok ha1 ha2 hz1 hz2 hz

-- box ['156147/1024000', '50001/327680', '7993/8000', '3997/4000']  interval_lower 137345181/1099511627776
noncomputable def e1722 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267173192368,0,true,156045417408,156045417472⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931850063184,0,false,-181913605248,-181913605184⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267287143220,0,true,156144286784,156144286848⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931736112332,0,false,-182048066752,-182048066688⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267026488498,0,true,155918116736,155918116800⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931996767054,0,false,-181740519552,-181740519488⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267161311584,0,true,156035108544,156035108608⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931861943968,0,false,-181899586944,-181899586880⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575576473,0,true,63946816,63946880⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447679079,0,false,-63950592,-63950528⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586287760,0,true,74657408,74657472⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436967792,0,false,-74662528,-74662464⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622706,0,false,-5120,-5056⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624057,0,false,-3776,-3712⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267099836543,0,true,155981765504,155981765568⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931923419009,0,false,-181827054400,-181827054336⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267224232158,0,true,156089703104,156089703168⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931799023394,0,false,-181973829952,-181973829888⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073929799482,0,false,-25884126784,-25884126720⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073967734462,0,false,-25845288832,-25845288768⟩
    { al := (156147/1024000), au := (50001/327680), zl := (7993/8000), zu := (3997/4000),
      A := ⟨167661564592,167775515444⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156045417408,156045417472⟩ : DyadicInterval 40),(⟨-181913605248,-181913605184⟩ : DyadicInterval 40),(⟨749290247241,749290266571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156144286784,156144286848⟩ : DyadicInterval 40),(⟨-182048066752,-182048066688⟩ : DyadicInterval 40),(⟨749272728569,749272747898⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155918116736,155918116800⟩ : DyadicInterval 40),(⟨-181740519552,-181740519488⟩ : DyadicInterval 40),(⟨749312783570,749312802899⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156035108544,156035108608⟩ : DyadicInterval 40),(⟨-181899586944,-181899586880⟩ : DyadicInterval 40),(⟨749292073092,749292092421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨63948697,74659984⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63946816,63946880⟩ : DyadicInterval 40),(⟨-63950592,-63950528⟩ : DyadicInterval 40),(⟨762123381720,762123401049⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74657408,74657472⟩ : DyadicInterval 40),(⟨-74662528,-74662464⟩ : DyadicInterval 40),(⟨762123381042,762123400371⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5120,-3712⟩ : DyadicInterval 40),(⟨762123385472,762123405440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167588208767,167712604382⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155981765504,155981765568⟩ : DyadicInterval 40),(⟨-181827054400,-181827054336⟩ : DyadicInterval 40),(⟨749301518527,749301537856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156089703104,156089703168⟩ : DyadicInterval 40),(⟨-181973829952,-181973829888⟩ : DyadicInterval 40),(⟨749282401966,749282421295⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25884126784,-25845288768⟩ : DyadicInterval 40),(⟨775046028000,775065466272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156045417408,156144286848⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182048066752,-181913605184⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1722_ok : ecellOkT e1722 = true := by decide +kernel
theorem e1722_pos {a z : ℝ} (ha1 : ((156147/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((50001/327680 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1722 e1722_ok ha1 ha2 hz1 hz2 hz

-- box ['50001/327680', '625437/4096000', '7993/8000', '3997/4000']  interval_lower 138340699/1099511627776
noncomputable def e1723 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267287143219,0,true,156144286784,156144286848⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931736112333,0,false,-182048066752,-182048066688⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267401094071,0,true,156243147264,156243147328⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931622161481,0,false,-182182544640,-182182544576⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267140339642,0,true,156016911104,156016911168⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931882915910,0,false,-181874842240,-181874842176⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267275176972,0,true,156133904704,156133904768⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931748078580,0,false,-182033945856,-182033945792⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575621431,0,true,63991744,63991808⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447634121,0,false,-63995520,-63995456⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586340214,0,true,74709888,74709952⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436915338,0,false,-74715008,-74714944⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622699,0,false,-5120,-5056⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624052,0,false,-3776,-3712⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267213737538,0,true,156080597376,156080597440⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931809518014,0,false,-181961446464,-181961446400⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267338140279,0,true,156188531456,156188531520⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931685115273,0,false,-182108248384,-182108248320⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073895038021,0,false,-25919716864,-25919716800⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073933000950,0,false,-25880849024,-25880848960⟩
    { al := (50001/327680), au := (625437/4096000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨167775515443,167889466295⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156144286784,156144286848⟩ : DyadicInterval 40),(⟨-182048066752,-182048066688⟩ : DyadicInterval 40),(⟨749272728569,749272747898⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156243147264,156243147328⟩ : DyadicInterval 40),(⟨-182182544640,-182182544576⟩ : DyadicInterval 40),(⟨749255197783,749255217112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156016911104,156016911168⟩ : DyadicInterval 40),(⟨-181874842240,-181874842176⟩ : DyadicInterval 40),(⟨749295295745,749295315075⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156133904704,156133904768⟩ : DyadicInterval 40),(⟨-182033945856,-182033945792⟩ : DyadicInterval 40),(⟨749274568808,749274588137⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨63993655,74712438⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63991744,63991808⟩ : DyadicInterval 40),(⟨-63995520,-63995456⟩ : DyadicInterval 40),(⟨762123381715,762123401044⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74709888,74709952⟩ : DyadicInterval 40),(⟨-74715008,-74714944⟩ : DyadicInterval 40),(⟨762123381035,762123400364⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5120,-3712⟩ : DyadicInterval 40),(⟨762123385472,762123405440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167702109762,167826512503⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156080597376,156080597440⟩ : DyadicInterval 40),(⟨-181961446464,-181961446400⟩ : DyadicInterval 40),(⟨749284015272,749284034602⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156188531456,156188531520⟩ : DyadicInterval 40),(⟨-182108248384,-182108248320⟩ : DyadicInterval 40),(⟨749264884429,749264903759⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25919716864,-25880848960⟩ : DyadicInterval 40),(⟨775063808096,775083261312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156144286784,156243147328⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182182544640,-182048066688⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1723_ok : ecellOkT e1723 = true := by decide +kernel
theorem e1723_pos {a z : ℝ} (ha1 : ((50001/327680 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((625437/4096000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1723 e1723_ok ha1 ha2 hz1 hz2 hz

-- box ['625437/4096000', '1251723/8192000', '999/1000', '7993/8000']  interval_lower 139483199/1099511627776
noncomputable def e1724 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267401094070,0,true,156243147264,156243147328⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931622161482,0,false,-182182544640,-182182544576⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267515044922,0,true,156341998912,156341998976⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931508210630,0,false,-182317039040,-182317038976⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267233204603,0,true,156097488064,156097488128⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931790050949,0,false,-181984417344,-181984417280⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267368041933,0,true,156214473088,156214473152⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931655213619,0,false,-182143536832,-182143536768⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586339376,0,true,74709056,74709120⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436916176,0,false,-74714176,-74714112⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099597073151,0,true,85442048,85442112⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099426182401,0,false,-85448704,-85448640⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621135,0,false,-6656,-6592⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622700,0,false,-5120,-5056⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267317145608,0,true,156170316864,156170316928⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931706109944,0,false,-182083472128,-182083472064⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267441548329,0,true,156278242112,156278242176⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931581707223,0,false,-182230290304,-182230290240⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073863460440,0,false,-25952048128,-25952048064⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073901446762,0,false,-25913155264,-25913155200⟩
    { al := (625437/4096000), au := (1251723/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨167889466294,168003417146⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156243147264,156243147328⟩ : DyadicInterval 40),(⟨-182182544640,-182182544576⟩ : DyadicInterval 40),(⟨749255197783,749255217112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156341998912,156341998976⟩ : DyadicInterval 40),(⟨-182317039040,-182317038976⟩ : DyadicInterval 40),(⟨749237654899,749237674229⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156097488064,156097488128⟩ : DyadicInterval 40),(⟨-181984417344,-181984417280⟩ : DyadicInterval 40),(⟨749281022540,749281041869⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156214473088,156214473152⟩ : DyadicInterval 40),(⟨-182143536832,-182143536768⟩ : DyadicInterval 40),(⟨749260283950,749260303279⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨74711600,85445375⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74709056,74709120⟩ : DyadicInterval 40),(⟨-74714176,-74714112⟩ : DyadicInterval 40),(⟨762123381035,762123400364⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨85442048,85442112⟩ : DyadicInterval 40),(⟨-85448704,-85448640⟩ : DyadicInterval 40),(⟨762123380239,762123399569⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6656,-5056⟩ : DyadicInterval 40),(⟨762123386144,762123406208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167805517832,167929920553⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156170316864,156170316928⟩ : DyadicInterval 40),(⟨-182083472128,-182083472064⟩ : DyadicInterval 40),(⟨749268114002,749268133331⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156278242112,156278242176⟩ : DyadicInterval 40),(⟨-182230290304,-182230290240⟩ : DyadicInterval 40),(⟨749248971181,749248990511⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25952048128,-25913155200⟩ : DyadicInterval 40),(⟨775079961216,775099426944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156243147264,156341998976⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182317039040,-182182544576⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1724_ok : ecellOkT e1724 = true := by decide +kernel
theorem e1724_pos {a z : ℝ} (ha1 : ((625437/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1251723/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1724 e1724_ok ha1 ha2 hz1 hz2 hz

-- box ['1251723/8192000', '313143/2048000', '999/1000', '7993/8000']  interval_lower 140484343/1099511627776
noncomputable def e1725 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267515044921,0,true,156341998912,156341998976⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931508210631,0,false,-182317039040,-182317038976⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267628995773,0,true,156440841664,156440841728⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931394259779,0,false,-182451549888,-182451549824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267347041503,0,true,156196253952,156196254016⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931676214049,0,false,-182118753024,-182118752960⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267481893077,0,true,156313240832,156313240896⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931541362475,0,false,-182277908736,-182277908672⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586391833,0,true,74761472,74761536⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436863719,0,false,-74766656,-74766592⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099597133107,0,true,85501952,85502016⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099426122445,0,false,-85508672,-85508608⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621126,0,false,-6656,-6592⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622693,0,false,-5120,-5056⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267431039486,0,true,156269125632,156269125696⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931592216066,0,false,-182217887168,-182217887104⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267555449332,0,true,156377047360,156377047424⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931467806220,0,false,-182364731712,-182364731648⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073828656127,0,false,-25987684288,-25987684224⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073866670400,0,false,-25948761536,-25948761472⟩
    { al := (1251723/8192000), au := (313143/2048000), zl := (999/1000), zu := (7993/8000),
      A := ⟨168003417145,168117367997⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156341998912,156341998976⟩ : DyadicInterval 40),(⟨-182317039040,-182317038976⟩ : DyadicInterval 40),(⟨749237654899,749237674229⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156440841664,156440841728⟩ : DyadicInterval 40),(⟨-182451549888,-182451549824⟩ : DyadicInterval 40),(⟨749220099927,749220119256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156196253952,156196254016⟩ : DyadicInterval 40),(⟨-182118753024,-182118752960⟩ : DyadicInterval 40),(⟨749263514996,749263534326⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156313240832,156313240896⟩ : DyadicInterval 40),(⟨-182277908736,-182277908672⟩ : DyadicInterval 40),(⟨749242759902,749242779232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨74764057,85505331⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74761472,74761536⟩ : DyadicInterval 40),(⟨-74766656,-74766592⟩ : DyadicInterval 40),(⟨762123381060,762123400389⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨85501952,85502016⟩ : DyadicInterval 40),(⟨-85508672,-85508608⟩ : DyadicInterval 40),(⟨762123380262,762123399591⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6656,-5056⟩ : DyadicInterval 40),(⟨762123386144,762123406208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167919411710,168043821556⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156269125632,156269125696⟩ : DyadicInterval 40),(⟨-182217887168,-182217887104⟩ : DyadicInterval 40),(⟨749250588798,749250608128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156377047360,156377047424⟩ : DyadicInterval 40),(⟨-182364731712,-182364731648⟩ : DyadicInterval 40),(⟨749231431690,749231451019⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25987684288,-25948761472⟩ : DyadicInterval 40),(⟨775097764352,775117245024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156341998912,156440841728⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182451549888,-182317038976⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1725_ok : ecellOkT e1725 = true := by decide +kernel
theorem e1725_pos {a z : ℝ} (ha1 : ((1251723/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((313143/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1725 e1725_ok ha1 ha2 hz1 hz2 hz

-- box ['625437/4096000', '1251723/8192000', '7993/8000', '3997/4000']  interval_lower 69669473/549755813888
noncomputable def e1726 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267401094070,0,true,156243147264,156243147328⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931622161482,0,false,-182182544640,-182182544576⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267515044922,0,true,156341998912,156341998976⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931508210630,0,false,-182317039040,-182317038976⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267254190786,0,true,156115696512,156115696576⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931769064766,0,false,-182009181312,-182009181248⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267389042360,0,true,156232691968,156232692032⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931634213192,0,false,-182168321216,-182168321152⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575666391,0,true,64036736,64036800⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447589161,0,false,-64040512,-64040448⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586392673,0,true,74762304,74762368⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436862879,0,false,-74767488,-74767424⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622692,0,false,-5120,-5056⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624047,0,false,-3776,-3712⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267327638533,0,true,156179420352,156179420416⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931695617019,0,false,-182095854976,-182095854912⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267452048397,0,true,156287350912,156287350976⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931571207155,0,false,-182242683200,-182242683136⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073860252960,0,false,-25955332224,-25955332160⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073898243839,0,false,-25916434560,-25916434496⟩
    { al := (625437/4096000), au := (1251723/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨167889466294,168003417146⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156243147264,156243147328⟩ : DyadicInterval 40),(⟨-182182544640,-182182544576⟩ : DyadicInterval 40),(⟨749255197783,749255217112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156341998912,156341998976⟩ : DyadicInterval 40),(⟨-182317039040,-182317038976⟩ : DyadicInterval 40),(⟨749237654899,749237674229⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156115696512,156115696576⟩ : DyadicInterval 40),(⟨-182009181312,-182009181248⟩ : DyadicInterval 40),(⟨749277795888,749277815217⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156232691968,156232692032⟩ : DyadicInterval 40),(⟨-182168321216,-182168321152⟩ : DyadicInterval 40),(⟨749257052474,749257071803⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨64038615,74764897⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64036736,64036800⟩ : DyadicInterval 40),(⟨-64040512,-64040448⟩ : DyadicInterval 40),(⟨762123381710,762123401039⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74762304,74762368⟩ : DyadicInterval 40),(⟨-74767488,-74767424⟩ : DyadicInterval 40),(⟨762123381059,762123400389⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5120,-3712⟩ : DyadicInterval 40),(⟨762123385472,762123405440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167816010757,167940420621⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156179420352,156179420416⟩ : DyadicInterval 40),(⟨-182095854976,-182095854912⟩ : DyadicInterval 40),(⟨749266499954,749266519284⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156287350912,156287350976⟩ : DyadicInterval 40),(⟨-182242683200,-182242683136⟩ : DyadicInterval 40),(⟨749247354798,749247374127⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25955332224,-25916434496⟩ : DyadicInterval 40),(⟨775081600864,775101068992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156243147264,156341998976⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182317039040,-182182544576⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1726_ok : ecellOkT e1726 = true := by decide +kernel
theorem e1726_pos {a z : ℝ} (ha1 : ((625437/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1251723/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1726 e1726_ok ha1 ha2 hz1 hz2 hz

-- box ['1251723/8192000', '313143/2048000', '7993/8000', '3997/4000']  interval_lower 140339439/1099511627776
noncomputable def e1727 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267515044921,0,true,156341998912,156341998976⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931508210631,0,false,-182317039040,-182317038976⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267628995773,0,true,156440841664,156440841728⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931394259779,0,false,-182451549888,-182451549824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267368041930,0,true,156214473088,156214473152⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931655213622,0,false,-182143536832,-182143536768⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267502907748,0,true,156331470400,156331470464⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931520347804,0,false,-182302712960,-182302712896⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575711355,0,true,64081664,64081728⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447544197,0,false,-64085504,-64085440⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586445134,0,true,74814784,74814848⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436810418,0,false,-74819904,-74819840⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622684,0,false,-5120,-5056⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624041,0,false,-3776,-3712⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267441539528,0,true,156278234496,156278234560⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931581716024,0,false,-182230279936,-182230279872⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267565956519,0,true,156386161536,156386161600⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931457299033,0,false,-182377134528,-182377134464⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073825444296,0,false,-25990972992,-25990972928⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073863463129,0,false,-25952045376,-25952045312⟩
    { al := (1251723/8192000), au := (313143/2048000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨168003417145,168117367997⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156341998912,156341998976⟩ : DyadicInterval 40),(⟨-182317039040,-182317038976⟩ : DyadicInterval 40),(⟨749237654899,749237674229⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156440841664,156440841728⟩ : DyadicInterval 40),(⟨-182451549888,-182451549824⟩ : DyadicInterval 40),(⟨749220099927,749220119256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156214473088,156214473152⟩ : DyadicInterval 40),(⟨-182143536832,-182143536768⟩ : DyadicInterval 40),(⟨749260283950,749260303280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156331470400,156331470464⟩ : DyadicInterval 40),(⟨-182302712960,-182302712896⟩ : DyadicInterval 40),(⟨749239524024,749239543353⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨64083579,74817358⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64081664,64081728⟩ : DyadicInterval 40),(⟨-64085504,-64085440⟩ : DyadicInterval 40),(⟨762123381736,762123401066⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74814784,74814848⟩ : DyadicInterval 40),(⟨-74819904,-74819840⟩ : DyadicInterval 40),(⟨762123381020,762123400350⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5120,-3712⟩ : DyadicInterval 40),(⟨762123385472,762123405440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167929911752,168054328743⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156278234496,156278234560⟩ : DyadicInterval 40),(⟨-182230279936,-182230279872⟩ : DyadicInterval 40),(⟨749248972533,749248991863⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156386161536,156386161600⟩ : DyadicInterval 40),(⟨-182377134528,-182377134464⟩ : DyadicInterval 40),(⟨749229813086,749229832415⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25990972992,-25952045312⟩ : DyadicInterval 40),(⟨775099406272,775118889376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156341998912,156440841728⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182451549888,-182317038976⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1727_ok : ecellOkT e1727 = true := by decide +kernel
theorem e1727_pos {a z : ℝ} (ha1 : ((1251723/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((313143/2048000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1727 e1727_ok ha1 ha2 hz1 hz2 hz

-- box ['156147/1024000', '50001/327680', '3997/4000', '1599/1600']  interval_lower 137201513/1099511627776
noncomputable def e1728 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267173192368,0,true,156045417408,156045417472⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931850063184,0,false,-181913605248,-181913605184⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267287143220,0,true,156144286784,156144286848⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931736112332,0,false,-182048066752,-182048066688⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267047446194,0,true,155936303424,155936303488⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931975809358,0,false,-181765244416,-181765244352⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267182283523,0,true,156053305664,156053305728⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931840972029,0,false,-181924332160,-181924332096⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564918428,0,true,53289344,53289408⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458337124,0,false,-53291968,-53291904⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575622223,0,true,63992576,63992640⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447633329,0,false,-63996352,-63996288⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624051,0,false,-3776,-3712⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625194,0,false,-2624,-2560⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267110315246,0,true,155990858240,155990858304⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931912940306,0,false,-181839417536,-181839417472⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267234718006,0,true,156098801152,156098801216⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931788537546,0,false,-181986203200,-181986203136⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073926600491,0,false,-25887401984,-25887401920⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073964540022,0,false,-25848559232,-25848559168⟩
    { al := (156147/1024000), au := (50001/327680), zl := (3997/4000), zu := (1599/1600),
      A := ⟨167661564592,167775515444⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156045417408,156045417472⟩ : DyadicInterval 40),(⟨-181913605248,-181913605184⟩ : DyadicInterval 40),(⟨749290247241,749290266571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156144286784,156144286848⟩ : DyadicInterval 40),(⟨-182048066752,-182048066688⟩ : DyadicInterval 40),(⟨749272728569,749272747898⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155936303424,155936303488⟩ : DyadicInterval 40),(⟨-181765244416,-181765244352⟩ : DyadicInterval 40),(⟨749309565338,749309584667⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156053305664,156053305728⟩ : DyadicInterval 40),(⟨-181924332160,-181924332096⟩ : DyadicInterval 40),(⟨749288850021,749288869351⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨53290652,63994447⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53289344,53289408⟩ : DyadicInterval 40),(⟨-53291968,-53291904⟩ : DyadicInterval 40),(⟨762123382281,762123401610⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63992576,63992640⟩ : DyadicInterval 40),(⟨-63996352,-63996288⟩ : DyadicInterval 40),(⟨762123381715,762123401044⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3776,-2560⟩ : DyadicInterval 40),(⟨762123384896,762123404768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167598687470,167723090230⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155990858240,155990858304⟩ : DyadicInterval 40),(⟨-181839417536,-181839417472⟩ : DyadicInterval 40),(⟨749299908752,749299928082⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156098801152,156098801216⟩ : DyadicInterval 40),(⟨-181986203200,-181986203136⟩ : DyadicInterval 40),(⟨749280789889,749280809218⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25887401984,-25848559168⟩ : DyadicInterval 40),(⟨775047663200,775067103872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156045417408,156144286848⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182048066752,-181913605184⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1728_ok : ecellOkT e1728 = true := by decide +kernel
theorem e1728_pos {a z : ℝ} (ha1 : ((156147/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((50001/327680 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1728 e1728_ok ha1 ha2 hz1 hz2 hz

-- box ['50001/327680', '625437/4096000', '3997/4000', '1599/1600']  interval_lower 138196847/1099511627776
noncomputable def e1729 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267287143219,0,true,156144286784,156144286848⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931736112333,0,false,-182048066752,-182048066688⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267401094071,0,true,156243147264,156243147328⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931622161481,0,false,-182182544640,-182182544576⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267161311582,0,true,156035108480,156035108544⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931861943970,0,false,-181899586944,-181899586880⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267296163155,0,true,156152112512,156152112576⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931727092397,0,false,-182058710912,-182058710848⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564955893,0,true,53326784,53326848⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458299659,0,false,-53329472,-53329408⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575667183,0,true,64037504,64037568⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447588369,0,false,-64041280,-64041216⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624046,0,false,-3776,-3712⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625190,0,false,-2624,-2560⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267224223360,0,true,156089695488,156089695552⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931799032192,0,false,-181973819520,-181973819456⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267348633246,0,true,156197634880,156197634944⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931674622306,0,false,-182120631488,-182120631424⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073891834684,0,false,-25922996608,-25922996544⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073929802167,0,false,-25884124032,-25884123968⟩
    { al := (50001/327680), au := (625437/4096000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨167775515443,167889466295⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156144286784,156144286848⟩ : DyadicInterval 40),(⟨-182048066752,-182048066688⟩ : DyadicInterval 40),(⟨749272728569,749272747898⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156243147264,156243147328⟩ : DyadicInterval 40),(⟨-182182544640,-182182544576⟩ : DyadicInterval 40),(⟨749255197783,749255217112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156035108480,156035108544⟩ : DyadicInterval 40),(⟨-181899586944,-181899586880⟩ : DyadicInterval 40),(⟨749292073129,749292092459⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156152112512,156152112576⟩ : DyadicInterval 40),(⟨-182058710912,-182058710848⟩ : DyadicInterval 40),(⟨749271341346,749271360675⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨53328117,64039407⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53326784,53326848⟩ : DyadicInterval 40),(⟨-53329472,-53329408⟩ : DyadicInterval 40),(⟨762123382309,762123401638⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64037504,64037568⟩ : DyadicInterval 40),(⟨-64041280,-64041216⟩ : DyadicInterval 40),(⟨762123381710,762123401039⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3776,-2560⟩ : DyadicInterval 40),(⟨762123384896,762123404768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167712595584,167837005470⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156089695488,156089695552⟩ : DyadicInterval 40),(⟨-181973819520,-181973819456⟩ : DyadicInterval 40),(⟨749282403286,749282422616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156197634880,156197634944⟩ : DyadicInterval 40),(⟨-182120631488,-182120631424⟩ : DyadicInterval 40),(⟨749263270111,749263289440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25922996608,-25884123968⟩ : DyadicInterval 40),(⟨775065445600,775084901184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156144286784,156243147328⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182182544640,-182048066688⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1729_ok : ecellOkT e1729 = true := by decide +kernel
theorem e1729_pos {a z : ℝ} (ha1 : ((50001/327680 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((625437/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1729 e1729_ok ha1 ha2 hz1 hz2 hz

-- box ['156147/1024000', '50001/327680', '1599/1600', '1999/2000']  interval_lower 137057997/1099511627776
noncomputable def e1730 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267173192368,0,true,156045417408,156045417472⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931850063184,0,false,-181913605248,-181913605184⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267287143220,0,true,156144286784,156144286848⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931736112332,0,false,-182048066752,-182048066688⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267068403890,0,true,155954489856,155954489920⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931954851662,0,false,-181789969856,-181789969792⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267203255463,0,true,156071502464,156071502528⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931820000089,0,false,-181949077952,-181949077888⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554260338,0,true,42631680,42631744⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468995214,0,false,-42633408,-42633344⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564956639,0,true,53327552,53327616⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458298913,0,false,-53330176,-53330112⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625189,0,false,-2624,-2560⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626123,0,false,-1664,-1600⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267120793972,0,true,155999950976,155999951040⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931902461580,0,false,-181851780864,-181851780800⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267245203876,0,true,156107899136,156107899200⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931778051676,0,false,-181998576576,-181998576512⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073923401293,0,false,-25890677376,-25890677312⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073961345375,0,false,-25851829888,-25851829824⟩
    { al := (156147/1024000), au := (50001/327680), zl := (1599/1600), zu := (1999/2000),
      A := ⟨167661564592,167775515444⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156045417408,156045417472⟩ : DyadicInterval 40),(⟨-181913605248,-181913605184⟩ : DyadicInterval 40),(⟨749290247241,749290266571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156144286784,156144286848⟩ : DyadicInterval 40),(⟨-182048066752,-182048066688⟩ : DyadicInterval 40),(⟨749272728569,749272747898⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155954489856,155954489920⟩ : DyadicInterval 40),(⟨-181789969856,-181789969792⟩ : DyadicInterval 40),(⟨749306346679,749306366008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156071502464,156071502528⟩ : DyadicInterval 40),(⟨-181949077952,-181949077888⟩ : DyadicInterval 40),(⟨749285626559,749285645889⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨42632562,53328863⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42631680,42631744⟩ : DyadicInterval 40),(⟨-42633408,-42633344⟩ : DyadicInterval 40),(⟨762123382762,762123402091⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53327552,53327616⟩ : DyadicInterval 40),(⟨-53330176,-53330112⟩ : DyadicInterval 40),(⟨762123382277,762123401606⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2624,-1600⟩ : DyadicInterval 40),(⟨762123384416,762123404192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167609166196,167733576100⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155999950976,155999951040⟩ : DyadicInterval 40),(⟨-181851780864,-181851780800⟩ : DyadicInterval 40),(⟨749298298851,749298318180⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156107899136,156107899200⟩ : DyadicInterval 40),(⟨-181998576576,-181998576512⟩ : DyadicInterval 40),(⟨749279177695,749279197024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25890677376,-25851829824⟩ : DyadicInterval 40),(⟨775049298528,775068741568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156045417408,156144286848⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182048066752,-181913605184⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1730_ok : ecellOkT e1730 = true := by decide +kernel
theorem e1730_pos {a z : ℝ} (ha1 : ((156147/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((50001/327680 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1730 e1730_ok ha1 ha2 hz1 hz2 hz

-- box ['50001/327680', '625437/4096000', '1599/1600', '1999/2000']  interval_lower 138052943/1099511627776
noncomputable def e1731 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267287143219,0,true,156144286784,156144286848⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931736112333,0,false,-182048066752,-182048066688⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267401094071,0,true,156243147264,156243147328⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931622161481,0,false,-182182544640,-182182544576⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267182283521,0,true,156053305664,156053305728⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931840972031,0,false,-181924332160,-181924332096⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267317149338,0,true,156170320064,156170320128⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931706106214,0,false,-182083476544,-182083476480⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554290310,0,true,42661696,42661760⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468965242,0,false,-42663424,-42663360⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564994107,0,true,53364992,53365056⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458261445,0,false,-53367680,-53367616⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625185,0,false,-2624,-2560⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626121,0,false,-1664,-1600⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267234709212,0,true,156098793536,156098793600⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931788546340,0,false,-181986192768,-181986192704⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267359126238,0,true,156206738240,156206738304⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931664129314,0,false,-182133014848,-182133014784⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073888631139,0,false,-25926276608,-25926276544⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073926603175,0,false,-25887399232,-25887399168⟩
    { al := (50001/327680), au := (625437/4096000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨167775515443,167889466295⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156144286784,156144286848⟩ : DyadicInterval 40),(⟨-182048066752,-182048066688⟩ : DyadicInterval 40),(⟨749272728569,749272747898⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156243147264,156243147328⟩ : DyadicInterval 40),(⟨-182182544640,-182182544576⟩ : DyadicInterval 40),(⟨749255197783,749255217112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156053305664,156053305728⟩ : DyadicInterval 40),(⟨-181924332160,-181924332096⟩ : DyadicInterval 40),(⟨749288850021,749288869351⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156170320064,156170320128⟩ : DyadicInterval 40),(⟨-182083476544,-182083476480⟩ : DyadicInterval 40),(⟨749268113455,749268132784⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨42662534,53366331⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42661696,42661760⟩ : DyadicInterval 40),(⟨-42663424,-42663360⟩ : DyadicInterval 40),(⟨762123382760,762123402089⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53364992,53365056⟩ : DyadicInterval 40),(⟨-53367680,-53367616⟩ : DyadicInterval 40),(⟨762123382305,762123401634⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2624,-1600⟩ : DyadicInterval 40),(⟨762123384416,762123404192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167723081436,167847498462⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156098793536,156098793600⟩ : DyadicInterval 40),(⟨-181986192768,-181986192704⟩ : DyadicInterval 40),(⟨749280791209,749280810539⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156206738240,156206738304⟩ : DyadicInterval 40),(⟨-182133014848,-182133014784⟩ : DyadicInterval 40),(⟨749261655728,749261675057⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25926276608,-25887399168⟩ : DyadicInterval 40),(⟨775067083200,775086541184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156144286784,156243147328⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182182544640,-182048066688⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1731_ok : ecellOkT e1731 = true := by decide +kernel
theorem e1731_pos {a z : ℝ} (ha1 : ((50001/327680 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((625437/4096000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1731 e1731_ok ha1 ha2 hz1 hz2 hz

-- box ['625437/4096000', '1251723/8192000', '3997/4000', '1599/1600']  interval_lower 139194575/1099511627776
noncomputable def e1732 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267401094070,0,true,156243147264,156243147328⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931622161482,0,false,-182182544640,-182182544576⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267515044922,0,true,156341998912,156341998976⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931508210630,0,false,-182317039040,-182317038976⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267275176970,0,true,156133904704,156133904768⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931748078582,0,false,-182033945856,-182033945792⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267410042787,0,true,156250910592,156250910656⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931613212765,0,false,-182193106112,-182193106048⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564993361,0,true,53364288,53364352⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458262191,0,false,-53366912,-53366848⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575712148,0,true,64082496,64082560⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447543404,0,false,-64086272,-64086208⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624040,0,false,-3776,-3712⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625186,0,false,-2624,-2560⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267338131482,0,true,156188523840,156188523904⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931685124070,0,false,-182108237952,-182108237888⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267462548493,0,true,156296459712,156296459776⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931560707059,0,false,-182255076288,-182255076224⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073857045271,0,false,-25958616576,-25958616512⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073895040708,0,false,-25919714112,-25919714048⟩
    { al := (625437/4096000), au := (1251723/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨167889466294,168003417146⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156243147264,156243147328⟩ : DyadicInterval 40),(⟨-182182544640,-182182544576⟩ : DyadicInterval 40),(⟨749255197783,749255217112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156341998912,156341998976⟩ : DyadicInterval 40),(⟨-182317039040,-182317038976⟩ : DyadicInterval 40),(⟨749237654899,749237674229⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156133904704,156133904768⟩ : DyadicInterval 40),(⟨-182033945856,-182033945792⟩ : DyadicInterval 40),(⟨749274568808,749274588138⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156250910592,156250910656⟩ : DyadicInterval 40),(⟨-182193106112,-182193106048⟩ : DyadicInterval 40),(⟨749253820540,749253839869⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨53365585,64084372⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53364288,53364352⟩ : DyadicInterval 40),(⟨-53366912,-53366848⟩ : DyadicInterval 40),(⟨762123382273,762123401602⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64082496,64082560⟩ : DyadicInterval 40),(⟨-64086272,-64086208⟩ : DyadicInterval 40),(⟨762123381704,762123401033⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3776,-2560⟩ : DyadicInterval 40),(⟨762123384896,762123404768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167826503706,167950920717⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156188523840,156188523904⟩ : DyadicInterval 40),(⟨-182108237952,-182108237888⟩ : DyadicInterval 40),(⟨749264885752,749264905081⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156296459712,156296459776⟩ : DyadicInterval 40),(⟨-182255076288,-182255076224⟩ : DyadicInterval 40),(⟨749245738286,749245757616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25958616576,-25919714048⟩ : DyadicInterval 40),(⟨775083240640,775102711168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156243147264,156341998976⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182317039040,-182182544576⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1732_ok : ecellOkT e1732 = true := by decide +kernel
theorem e1732_pos {a z : ℝ} (ha1 : ((625437/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1251723/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1732 e1732_ok ha1 ha2 hz1 hz2 hz

-- box ['1251723/8192000', '313143/2048000', '3997/4000', '1599/1600']  interval_lower 140194933/1099511627776
noncomputable def e1733 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267515044921,0,true,156341998912,156341998976⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931508210631,0,false,-182317039040,-182317038976⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267628995773,0,true,156440841664,156440841728⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931394259779,0,false,-182451549888,-182451549824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267389042358,0,true,156232691968,156232692032⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931634213194,0,false,-182168321152,-182168321088⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267523922419,0,true,156349699712,156349699776⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931499333133,0,false,-182327517696,-182327517632⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565030830,0,true,53401728,53401792⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458224722,0,false,-53404352,-53404288⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575757116,0,true,64127424,64127488⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447498436,0,false,-64131264,-64131200⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624035,0,false,-3776,-3712⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625183,0,false,-2624,-2560⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267452039600,0,true,156287343296,156287343360⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931571215952,0,false,-182242672832,-182242672768⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267576463734,0,true,156395275648,156395275712⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931446791818,0,false,-182389537536,-182389537472⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073822232255,0,false,-25994261824,-25994261760⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073860255648,0,false,-25955329472,-25955329408⟩
    { al := (1251723/8192000), au := (313143/2048000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨168003417145,168117367997⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156341998912,156341998976⟩ : DyadicInterval 40),(⟨-182317039040,-182317038976⟩ : DyadicInterval 40),(⟨749237654899,749237674229⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156440841664,156440841728⟩ : DyadicInterval 40),(⟨-182451549888,-182451549824⟩ : DyadicInterval 40),(⟨749220099927,749220119256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156232691968,156232692032⟩ : DyadicInterval 40),(⟨-182168321152,-182168321088⟩ : DyadicInterval 40),(⟨749257052447,749257071776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156349699712,156349699776⟩ : DyadicInterval 40),(⟨-182327517696,-182327517632⟩ : DyadicInterval 40),(⟨749236287687,749236307016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨53403054,64129340⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53401728,53401792⟩ : DyadicInterval 40),(⟨-53404352,-53404288⟩ : DyadicInterval 40),(⟨762123382270,762123401599⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64127424,64127488⟩ : DyadicInterval 40),(⟨-64131264,-64131200⟩ : DyadicInterval 40),(⟨762123381731,762123401060⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3776,-2560⟩ : DyadicInterval 40),(⟨762123384896,762123404768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167940411824,168064835958⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156287343296,156287343360⟩ : DyadicInterval 40),(⟨-182242672832,-182242672768⟩ : DyadicInterval 40),(⟨749247356149,749247375479⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156395275648,156395275712⟩ : DyadicInterval 40),(⟨-182389537536,-182389537472⟩ : DyadicInterval 40),(⟨749228194389,749228213719⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25994261824,-25955329408⟩ : DyadicInterval 40),(⟨775101048320,775120533792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156341998912,156440841728⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182451549888,-182317038976⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1733_ok : ecellOkT e1733 = true := by decide +kernel
theorem e1733_pos {a z : ℝ} (ha1 : ((1251723/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((313143/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1733 e1733_ok ha1 ha2 hz1 hz2 hz

-- box ['625437/4096000', '1251723/8192000', '1599/1600', '1999/2000']  interval_lower 34762545/274877906944
noncomputable def e1734 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267401094070,0,true,156243147264,156243147328⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931622161482,0,false,-182182544640,-182182544576⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267515044922,0,true,156341998912,156341998976⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931508210630,0,false,-182317039040,-182317038976⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267296163153,0,true,156152112512,156152112576⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931727092399,0,false,-182058710912,-182058710848⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267431043214,0,true,156269128832,156269128896⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931592212338,0,false,-182217891584,-182217891520⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554320284,0,true,42691648,42691712⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468935268,0,false,-42693376,-42693312⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565031577,0,true,53402496,53402560⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458223975,0,false,-53405120,-53405056⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625182,0,false,-2624,-2560⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626119,0,false,-1664,-1600⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267348624448,0,true,156197627264,156197627328⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931674631104,0,false,-182120621120,-182120621056⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267473048603,0,true,156305568384,156305568448⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931550206949,0,false,-182267469568,-182267469504⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073853837377,0,false,-25961901120,-25961901056⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073891837371,0,false,-25922993856,-25922993792⟩
    { al := (625437/4096000), au := (1251723/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨167889466294,168003417146⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156243147264,156243147328⟩ : DyadicInterval 40),(⟨-182182544640,-182182544576⟩ : DyadicInterval 40),(⟨749255197783,749255217112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156341998912,156341998976⟩ : DyadicInterval 40),(⟨-182317039040,-182317038976⟩ : DyadicInterval 40),(⟨749237654899,749237674229⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156152112512,156152112576⟩ : DyadicInterval 40),(⟨-182058710912,-182058710848⟩ : DyadicInterval 40),(⟨749271341346,749271360676⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156269128832,156269128896⟩ : DyadicInterval 40),(⟨-182217891584,-182217891520⟩ : DyadicInterval 40),(⟨749250588251,749250607580⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨42692508,53403801⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42691648,42691712⟩ : DyadicInterval 40),(⟨-42693376,-42693312⟩ : DyadicInterval 40),(⟨762123382758,762123402087⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53402496,53402560⟩ : DyadicInterval 40),(⟨-53405120,-53405056⟩ : DyadicInterval 40),(⟨762123382270,762123401599⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2624,-1600⟩ : DyadicInterval 40),(⟨762123384416,762123404192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167836996672,167961420827⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156197627264,156197627328⟩ : DyadicInterval 40),(⟨-182120621120,-182120621056⟩ : DyadicInterval 40),(⟨749263271460,749263290790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156305568384,156305568448⟩ : DyadicInterval 40),(⟨-182267469568,-182267469504⟩ : DyadicInterval 40),(⟨749244121722,749244141052⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25961901120,-25922993792⟩ : DyadicInterval 40),(⟨775084880512,775104353440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156243147264,156341998976⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182317039040,-182182544576⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1734_ok : ecellOkT e1734 = true := by decide +kernel
theorem e1734_pos {a z : ℝ} (ha1 : ((625437/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1251723/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1734 e1734_ok ha1 ha2 hz1 hz2 hz

-- box ['1251723/8192000', '313143/2048000', '1599/1600', '1999/2000']  interval_lower 140050311/1099511627776
noncomputable def e1735 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267515044921,0,true,156341998912,156341998976⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931508210631,0,false,-182317039040,-182317038976⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267628995773,0,true,156440841664,156440841728⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931394259779,0,false,-182451549888,-182451549824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267410042785,0,true,156250910592,156250910656⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931613212767,0,false,-182193106112,-182193106048⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267544937090,0,true,156367928704,156367928768⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931478318462,0,false,-182352323008,-182352322944⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554350261,0,true,42721600,42721664⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468905291,0,false,-42723328,-42723264⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565069051,0,true,53439936,53440000⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458186501,0,false,-53442624,-53442560⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625178,0,false,-2624,-2560⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626116,0,false,-1664,-1600⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267462539692,0,true,156296452096,156296452160⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931560715860,0,false,-182255065920,-182255065856⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267586970970,0,true,156404389696,156404389760⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931436284582,0,false,-182401940672,-182401940608⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073819020007,0,false,-25997550976,-25997550912⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073857047960,0,false,-25958613824,-25958613760⟩
    { al := (1251723/8192000), au := (313143/2048000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨168003417145,168117367997⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156341998912,156341998976⟩ : DyadicInterval 40),(⟨-182317039040,-182317038976⟩ : DyadicInterval 40),(⟨749237654899,749237674229⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156440841664,156440841728⟩ : DyadicInterval 40),(⟨-182451549888,-182451549824⟩ : DyadicInterval 40),(⟨749220099927,749220119256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156250910592,156250910656⟩ : DyadicInterval 40),(⟨-182193106112,-182193106048⟩ : DyadicInterval 40),(⟨749253820541,749253839870⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156367928704,156367928768⟩ : DyadicInterval 40),(⟨-182352323008,-182352322944⟩ : DyadicInterval 40),(⟨749233050956,749233070286⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨42722485,53441275⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42721600,42721664⟩ : DyadicInterval 40),(⟨-42723328,-42723264⟩ : DyadicInterval 40),(⟨762123382755,762123402085⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53439936,53440000⟩ : DyadicInterval 40),(⟨-53442624,-53442560⟩ : DyadicInterval 40),(⟨762123382298,762123401627⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2624,-1600⟩ : DyadicInterval 40),(⟨762123384416,762123404192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167950911916,168075343194⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156296452096,156296452160⟩ : DyadicInterval 40),(⟨-182255065920,-182255065856⟩ : DyadicInterval 40),(⟨749245739638,749245758968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156404389696,156404389760⟩ : DyadicInterval 40),(⟨-182401940672,-182401940608⟩ : DyadicInterval 40),(⟨749226575575,749226594905⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25997550976,-25958613760⟩ : DyadicInterval 40),(⟨775102690496,775122178368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156341998912,156440841728⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182451549888,-182317038976⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1735_ok : ecellOkT e1735 = true := by decide +kernel
theorem e1735_pos {a z : ℝ} (ha1 : ((1251723/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((313143/2048000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1735 e1735_ok ha1 ha2 hz1 hz2 hz

-- box ['313143/2048000', '1253421/8192000', '999/1000', '7993/8000']  interval_lower 70743817/549755813888
noncomputable def e1736 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267628995772,0,true,156440841664,156440841728⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931394259780,0,false,-182451549888,-182451549824⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267742946624,0,true,156539675520,156539675584⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931280308928,0,false,-182586077184,-182586077120⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267460878403,0,true,156295010944,156295011008⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931562377149,0,false,-182253105088,-182253105024⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267595744221,0,true,156411999680,156411999744⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931427511331,0,false,-182412297088,-182412297024⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586444295,0,true,74813952,74814016⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436811257,0,false,-74819072,-74819008⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099597193067,0,true,85561920,85561984⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099426062485,0,false,-85568640,-85568576⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621117,0,false,-6720,-6656⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622686,0,false,-5120,-5056⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267544933362,0,true,156367925440,156367925504⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931478322190,0,false,-182352318656,-182352318592⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267669350332,0,true,156475843712,156475843776⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931353905220,0,false,-182499189504,-182499189440⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073793828217,0,false,-26023345792,-26023345728⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073831870443,0,false,-25984393152,-25984393088⟩
    { al := (313143/2048000), au := (1253421/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨168117367996,168231318848⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156440841664,156440841728⟩ : DyadicInterval 40),(⟨-182451549888,-182451549824⟩ : DyadicInterval 40),(⟨749220099927,749220119257⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156539675520,156539675584⟩ : DyadicInterval 40),(⟨-182586077184,-182586077120⟩ : DyadicInterval 40),(⟨749202532865,749202552194⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156295010944,156295011008⟩ : DyadicInterval 40),(⟨-182253105088,-182253105024⟩ : DyadicInterval 40),(⟨749245995388,749246014717⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156411999680,156411999744⟩ : DyadicInterval 40),(⟨-182412297088,-182412297024⟩ : DyadicInterval 40),(⟨749225223809,749225243139⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨74816519,85565291⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74813952,74814016⟩ : DyadicInterval 40),(⟨-74819072,-74819008⟩ : DyadicInterval 40),(⟨762123381020,762123400350⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨85561920,85561984⟩ : DyadicInterval 40),(⟨-85568640,-85568576⟩ : DyadicInterval 40),(⟨762123380252,762123399582⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6720,-5056⟩ : DyadicInterval 40),(⟨762123386144,762123406240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168033305586,168157722556⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156367925440,156367925504⟩ : DyadicInterval 40),(⟨-182352318656,-182352318592⟩ : DyadicInterval 40),(⟨749233051568,749233070898⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156475843712,156475843776⟩ : DyadicInterval 40),(⟨-182499189504,-182499189440⟩ : DyadicInterval 40),(⟨749213880104,749213899434⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26023345792,-25984393088⟩ : DyadicInterval 40),(⟨775115580160,775135075776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156440841664,156539675584⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182586077184,-182451549824⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1736_ok : ecellOkT e1736 = true := by decide +kernel
theorem e1736_pos {a z : ℝ} (ha1 : ((313143/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1253421/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1736 e1736_ok ha1 ha2 hz1 hz2 hz

-- box ['1253421/8192000', '125427/819200', '999/1000', '7993/8000']  interval_lower 71247007/549755813888
noncomputable def e1737 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267742946623,0,true,156539675520,156539675584⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931280308929,0,false,-182586077184,-182586077120⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267856897475,0,true,156638500480,156638500544⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931166358077,0,false,-182720620928,-182720620864⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267574715304,0,true,156393759040,156393759104⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931448540248,0,false,-182387473600,-182387473536⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267709595365,0,true,156510749632,156510749696⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931313660187,0,false,-182546701888,-182546701824⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586496759,0,true,74866432,74866496⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436758793,0,false,-74871552,-74871488⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099597253032,0,true,85621888,85621952⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099426002520,0,false,-85628608,-85628544⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621107,0,false,-6720,-6656⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622678,0,false,-5120,-5056⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267658827235,0,true,156466716480,156466716544⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931364428317,0,false,-182486766528,-182486766464⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267783251329,0,true,156574631168,156574631232⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931240004223,0,false,-182633663744,-182633663680⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073758976709,0,false,-26059032576,-26059032512⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073797046892,0,false,-26020050048,-26020049984⟩
    { al := (1253421/8192000), au := (125427/819200), zl := (999/1000), zu := (7993/8000),
      A := ⟨168231318847,168345269699⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156539675520,156539675584⟩ : DyadicInterval 40),(⟨-182586077184,-182586077120⟩ : DyadicInterval 40),(⟨749202532865,749202552194⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156638500480,156638500544⟩ : DyadicInterval 40),(⟨-182720620928,-182720620864⟩ : DyadicInterval 40),(⟨749184953711,749184973041⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156393759040,156393759104⟩ : DyadicInterval 40),(⟨-182387473600,-182387473536⟩ : DyadicInterval 40),(⟨749228463739,749228483068⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156510749632,156510749696⟩ : DyadicInterval 40),(⟨-182546701888,-182546701824⟩ : DyadicInterval 40),(⟨749207675669,749207694998⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨74868983,85625256⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74866432,74866496⟩ : DyadicInterval 40),(⟨-74871552,-74871488⟩ : DyadicInterval 40),(⟨762123381013,762123400343⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨85621888,85621952⟩ : DyadicInterval 40),(⟨-85628608,-85628544⟩ : DyadicInterval 40),(⟨762123380243,762123399573⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6720,-5056⟩ : DyadicInterval 40),(⟨762123386144,762123406240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168147199459,168271623553⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156466716480,156466716544⟩ : DyadicInterval 40),(⟨-182486766528,-182486766464⟩ : DyadicInterval 40),(⟨749215502173,749215521502⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156574631168,156574631232⟩ : DyadicInterval 40),(⟨-182633663744,-182633663680⟩ : DyadicInterval 40),(⟨749196316450,749196335780⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26059032576,-26020049984⟩ : DyadicInterval 40),(⟨775133408608,775152919168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156539675520,156638500544⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182720620928,-182586077120⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1737_ok : ecellOkT e1737 = true := by decide +kernel
theorem e1737_pos {a z : ℝ} (ha1 : ((1253421/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((125427/819200 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1737 e1737_ok ha1 ha2 hz1 hz2 hz

-- box ['313143/2048000', '1253421/8192000', '7993/8000', '3997/4000']  interval_lower 141342699/1099511627776
noncomputable def e1738 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267628995772,0,true,156440841664,156440841728⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931394259780,0,false,-182451549888,-182451549824⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267742946624,0,true,156539675520,156539675584⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931280308928,0,false,-182586077184,-182586077120⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267481893074,0,true,156313240832,156313240896⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931541362478,0,false,-182277908736,-182277908672⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267616773135,0,true,156430239936,156430240000⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931406482417,0,false,-182437121152,-182437121088⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575756322,0,true,64126656,64126720⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447499230,0,false,-64130432,-64130368⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586497601,0,true,74867264,74867328⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436757951,0,false,-74872384,-74872320⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622677,0,false,-5120,-5056⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624036,0,false,-3776,-3712⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267555440529,0,true,156377039680,156377039744⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931467815023,0,false,-182364721280,-182364721216⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267679864640,0,true,156484963200,156484963264⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931343390912,0,false,-182511602240,-182511602176⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073790612030,0,false,-26026639040,-26026638976⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073828658819,0,false,-25987681536,-25987681472⟩
    { al := (313143/2048000), au := (1253421/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨168117367996,168231318848⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156440841664,156440841728⟩ : DyadicInterval 40),(⟨-182451549888,-182451549824⟩ : DyadicInterval 40),(⟨749220099927,749220119257⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156539675520,156539675584⟩ : DyadicInterval 40),(⟨-182586077184,-182586077120⟩ : DyadicInterval 40),(⟨749202532865,749202552194⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156313240832,156313240896⟩ : DyadicInterval 40),(⟨-182277908736,-182277908672⟩ : DyadicInterval 40),(⟨749242759903,749242779233⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156430239936,156430240000⟩ : DyadicInterval 40),(⟨-182437121152,-182437121088⟩ : DyadicInterval 40),(⟨749221983522,749222002851⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨64128546,74869825⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64126656,64126720⟩ : DyadicInterval 40),(⟨-64130432,-64130368⟩ : DyadicInterval 40),(⟨762123381699,762123401028⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74867264,74867328⟩ : DyadicInterval 40),(⟨-74872384,-74872320⟩ : DyadicInterval 40),(⟨762123381013,762123400343⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5120,-3712⟩ : DyadicInterval 40),(⟨762123385472,762123405440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168043812753,168168236864⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156377039680,156377039744⟩ : DyadicInterval 40),(⟨-182364721280,-182364721216⟩ : DyadicInterval 40),(⟨749231433054,749231452384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156484963200,156484963264⟩ : DyadicInterval 40),(⟨-182511602240,-182511602176⟩ : DyadicInterval 40),(⟨749212259312,749212278642⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26026639040,-25987681472⟩ : DyadicInterval 40),(⟨775117224352,775136722400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156440841664,156539675584⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182586077184,-182451549824⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1738_ok : ecellOkT e1738 = true := by decide +kernel
theorem e1738_pos {a z : ℝ} (ha1 : ((313143/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1253421/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1738 e1738_ok ha1 ha2 hz1 hz2 hz

-- box ['1253421/8192000', '125427/819200', '7993/8000', '3997/4000']  interval_lower 35587185/274877906944
noncomputable def e1739 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267742946623,0,true,156539675520,156539675584⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931280308929,0,false,-182586077184,-182586077120⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267856897475,0,true,156638500480,156638500544⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931166358077,0,false,-182720620928,-182720620864⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1267595744218,0,true,156411999680,156411999744⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931427511334,0,false,-182412297088,-182412297024⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267730638523,0,true,156529000640,156529000704⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931292617029,0,false,-182571545792,-182571545728⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575801292,0,true,64171584,64171648⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447454260,0,false,-64175424,-64175360⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586550069,0,true,74919680,74919744⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436705483,0,false,-74924864,-74924800⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622670,0,false,-5120,-5056⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624031,0,false,-3776,-3712⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1267669341526,0,true,156475836032,156475836096⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨931353914026,0,false,-182499179136,-182499179072⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267793772761,0,true,156583756032,156583756096⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931229482791,0,false,-182646086464,-182646086400⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073755756164,0,false,-26062330368,-26062330304⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073793830912,0,false,-26023343040,-26023342976⟩
    { al := (1253421/8192000), au := (125427/819200), zl := (7993/8000), zu := (3997/4000),
      A := ⟨168231318847,168345269699⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156539675520,156539675584⟩ : DyadicInterval 40),(⟨-182586077184,-182586077120⟩ : DyadicInterval 40),(⟨749202532865,749202552194⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156638500480,156638500544⟩ : DyadicInterval 40),(⟨-182720620928,-182720620864⟩ : DyadicInterval 40),(⟨749184953711,749184973041⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156411999680,156411999744⟩ : DyadicInterval 40),(⟨-182412297088,-182412297024⟩ : DyadicInterval 40),(⟨749225223809,749225243139⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156529000640,156529000704⟩ : DyadicInterval 40),(⟨-182571545792,-182571545728⟩ : DyadicInterval 40),(⟨749204430929,749204450259⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨64173516,74922293⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64171584,64171648⟩ : DyadicInterval 40),(⟨-64175424,-64175360⟩ : DyadicInterval 40),(⟨762123381726,762123401055⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74919680,74919744⟩ : DyadicInterval 40),(⟨-74924864,-74924800⟩ : DyadicInterval 40),(⟨762123381038,762123400367⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5120,-3712⟩ : DyadicInterval 40),(⟨762123385472,762123405440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168157713750,168282144985⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156475836032,156475836096⟩ : DyadicInterval 40),(⟨-182499179136,-182499179072⟩ : DyadicInterval 40),(⟨749213881498,749213900828⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156583756032,156583756096⟩ : DyadicInterval 40),(⟨-182646086464,-182646086400⟩ : DyadicInterval 40),(⟨749194693457,749194712787⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26062330368,-26023342976⟩ : DyadicInterval 40),(⟨775135055104,775154568064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156539675520,156638500544⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-182720620928,-182586077120⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1739_ok : ecellOkT e1739 = true := by decide +kernel
theorem e1739_pos {a z : ℝ} (ha1 : ((1253421/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((125427/819200 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1739 e1739_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B028

end


