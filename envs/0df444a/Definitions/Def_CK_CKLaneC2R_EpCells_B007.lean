-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B007
-- name    : CK_CKLaneC2R_EpCells_B007
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:21:45.627951+00:00
-- url     : https://prove2.me/theorems/2ac6bd5d-d3e2-4b51-ab44-b2c214cd9b5c
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B007` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B007` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B007` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B007 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B007.lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheckT

-- ===== source module CKLaneC2R.EpCells.B007 =====
section

namespace CKLaneC2R.EpCells.B007

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['252933/1024000', '101343/409600', '1999/2000', '1']  interval_lower 254615351/274877906944
noncomputable def e420 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1371096368545,0,true,242711235008,242711235072⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨827926887007,0,false,-311927639744,-311927639680⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1371552171951,0,true,243076692800,243076692864⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨827471083601,0,false,-312533126976,-312533126912⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1370960576174,0,true,242602334784,242602334848⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨828062679378,0,false,-311747318208,-311747318144⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582814527,0,true,71184384,71184448⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099440441025,0,false,-71189056,-71188992⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623167,0,false,-4672,-4608⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1371028466430,0,true,242656781504,242656781568⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨827994789122,0,false,-311837467456,-311837467392⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1371552180553,0,true,243076699712,243076699776⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨827471074999,0,false,-312533138432,-312533138368⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1032203506164,0,false,-69456438656,-69456438592⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1032462410824,0,false,-69180685888,-69180685824⟩
    { al := (252933/1024000), au := (101343/409600), zl := (1999/2000), zu := 1,
      A := ⟨271584740769,272040544175⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨242711235008,242711235072⟩ : DyadicInterval 40),(⟨-311927639744,-311927639680⟩ : DyadicInterval 40),(⟨728232330789,728232350118⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨243076692800,243076692864⟩ : DyadicInterval 40),(⟨-312533126976,-312533126912⟩ : DyadicInterval 40),(⟨728117267185,728117286515⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨242602334784,242602334848⟩ : DyadicInterval 40),(⟨-311747318208,-311747318144⟩ : DyadicInterval 40),(⟨728266571494,728266590824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨243076692800,243076692864⟩ : DyadicInterval 40),(⟨-312533126976,-312533126912⟩ : DyadicInterval 40),(⟨728117267185,728117286515⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,71186751⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨71184384,71184448⟩ : DyadicInterval 40),(⟨-71189056,-71188992⟩ : DyadicInterval 40),(⟨762123381278,762123400608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4672,0⟩ : DyadicInterval 40),(⟨762123383616,762123405216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨271516838654,272040552777⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨242656781504,242656781568⟩ : DyadicInterval 40),(⟨-311837467456,-311837467392⟩ : DyadicInterval 40),(⟨728249454879,728249474208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨243076699712,243076699776⟩ : DyadicInterval 40),(⟨-312533138432,-312533138368⟩ : DyadicInterval 40),(⟨728117265011,728117284341⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-69456438656,-69180685824⟩ : DyadicInterval 40),(⟨796713726528,796851622208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨242711235008,243076692864⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-312533126976,-311927639680⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e420_ok : ecellOkT e420 = true := by decide +kernel
theorem e420_pos {a z : ℝ} (ha1 : ((252933/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((101343/409600 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e420 e420_ok ha1 ha2 hz1 hz2 hz

-- box ['101343/409600', '126891/512000', '1999/2000', '1']  interval_lower 518373437/549755813888
noncomputable def e421 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1371552171950,0,true,243076692800,243076692864⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨827471083602,0,false,-312533126976,-312533126912⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1372007975355,0,true,243442029184,243442029248⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨827015280197,0,false,-313138947840,-313138947776⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1371416151677,0,true,242967646080,242967646144⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨827607103875,0,false,-312352403328,-312352403264⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582945089,0,true,71314944,71315008⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099440310463,0,false,-71319680,-71319616⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623150,0,false,-4672,-4608⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1371484155879,0,true,243022166016,243022166080⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨827539099673,0,false,-312442753600,-312442753536⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1372007983959,0,true,243442036096,243442036160⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨827015271593,0,false,-313138959296,-313138959232⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1031977767962,0,false,-69696923136,-69696923072⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1032237163210,0,false,-69420587520,-69420587456⟩
    { al := (101343/409600), au := (126891/512000), zl := (1999/2000), zu := 1,
      A := ⟨272040544174,272496347579⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨243076692800,243076692864⟩ : DyadicInterval 40),(⟨-312533126976,-312533126912⟩ : DyadicInterval 40),(⟨728117267185,728117286515⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨243442029184,243442029248⟩ : DyadicInterval 40),(⟨-313138947840,-313138947776⟩ : DyadicInterval 40),(⟨728002002297,728002021627⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨242967646080,242967646144⟩ : DyadicInterval 40),(⟨-312352403328,-312352403264⟩ : DyadicInterval 40),(⟨728151625375,728151644704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨243442029184,243442029248⟩ : DyadicInterval 40),(⟨-313138947840,-313138947776⟩ : DyadicInterval 40),(⟨728002002297,728002021627⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,71317313⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨71314944,71315008⟩ : DyadicInterval 40),(⟨-71319680,-71319616⟩ : DyadicInterval 40),(⟨762123381294,762123400623⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4672,0⟩ : DyadicInterval 40),(⟨762123383616,762123405216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨271972528103,272496356183⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨243022166016,243022166080⟩ : DyadicInterval 40),(⟨-312442753600,-312442753536⟩ : DyadicInterval 40),(⟨728134450048,728134469378⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨243442036096,243442036160⟩ : DyadicInterval 40),(⟨-313138959296,-313138959232⟩ : DyadicInterval 40),(⟨728002000115,728002019445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-69696923136,-69420587456⟩ : DyadicInterval 40),(⟨796833677344,796971864448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨243076692800,243442029248⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-313138947840,-312533126912⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e421_ok : ecellOkT e421 = true := by decide +kernel
theorem e421_pos {a z : ℝ} (ha1 : ((101343/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((126891/512000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e421 e421_ok ha1 ha2 hz1 hz2 hz

-- box ['126891/512000', '508413/2048000', '999/1000', '1999/2000']  interval_lower 1059617647/1099511627776
noncomputable def e422 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1372007975354,0,true,243442029184,243442029248⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨827015280198,0,false,-313138947840,-313138947776⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1372463778759,0,true,243807244224,243807244288⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨826559476793,0,false,-313745102656,-313745102592⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1371735479006,0,true,243223632000,243223632064⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨827287776546,0,false,-312776725312,-312776725248⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1372327302684,0,true,243697904704,243697904768⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨826695952868,0,false,-313563573504,-313563573440⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582941196,0,true,71311104,71311168⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099440314356,0,false,-71315776,-71315712⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099654519996,0,true,142882880,142882944⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099368735556,0,false,-142901568,-142901504⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511609205,0,false,-18624,-18560⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623151,0,false,-4672,-4608⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1371871723544,0,true,243332833088,243332833152⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨827151532008,0,false,-312957816832,-312957816768⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1372395550101,0,true,243752583296,243752583360⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨826627705451,0,false,-313654346816,-313654346752⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1031785527221,0,false,-69901763456,-69901763392⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1032045291002,0,false,-69624983680,-69624983616⟩
    { al := (126891/512000), au := (508413/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨272496347578,272952150983⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨243442029184,243442029248⟩ : DyadicInterval 40),(⟨-313138947840,-313138947776⟩ : DyadicInterval 40),(⟨728002002298,728002021627⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨243807244224,243807244288⟩ : DyadicInterval 40),(⟨-313745102656,-313745102592⟩ : DyadicInterval 40),(⟨727886536074,727886555404⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨243223632000,243223632064⟩ : DyadicInterval 40),(⟨-312776725312,-312776725248⟩ : DyadicInterval 40),(⟨728070936166,728070955496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨243697904704,243697904768⟩ : DyadicInterval 40),(⟨-313563573504,-313563573440⟩ : DyadicInterval 40),(⟨727921129955,727921149285⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨71313420,142892220⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨71311104,71311168⟩ : DyadicInterval 40),(⟨-71315776,-71315712⟩ : DyadicInterval 40),(⟨762123381262,762123400591⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨142882880,142882944⟩ : DyadicInterval 40),(⟨-142901568,-142901504⟩ : DyadicInterval 40),(⟨762123374325,762123393654⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-18624,-4608⟩ : DyadicInterval 40),(⟨762123385920,762123412192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨272360095768,272883922325⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨243332833088,243332833152⟩ : DyadicInterval 40),(⟨-312957816832,-312957816768⟩ : DyadicInterval 40),(⟨728036479155,728036498485⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨243752583296,243752583360⟩ : DyadicInterval 40),(⟨-313654346816,-313654346752⟩ : DyadicInterval 40),(⟨727903832922,727903852252⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-69901763456,-69624983616⟩ : DyadicInterval 40),(⟨796935875424,797074284608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨243442029184,243807244288⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-313745102656,-313138947776⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e422_ok : ecellOkT e422 = true := by decide +kernel
theorem e422_pos {a z : ℝ} (ha1 : ((126891/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((508413/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e422 e422_ok ha1 ha2 hz1 hz2 hz

-- box ['508413/2048000', '254631/1024000', '999/1000', '1999/2000']  interval_lower 539092143/549755813888
noncomputable def e423 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1372463778758,0,true,243807244224,243807244288⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨826559476794,0,false,-313745102656,-313745102592⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1372919582163,0,true,244172337920,244172337984⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨826103673389,0,false,-314351591808,-314351591744⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1372190826606,0,true,243588554368,243588554432⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨826832428946,0,false,-313382074304,-313382074240⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1372782878187,0,true,244062852224,244062852288⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨826240377365,0,false,-314169659264,-314169659200⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099583071802,0,true,71441664,71441728⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099440183750,0,false,-71446400,-71446336⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099654781348,0,true,143144192,143144256⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099368474204,0,false,-143162944,-143162880⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511609137,0,false,-18688,-18624⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623134,0,false,-4672,-4608⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1372327299060,0,true,243697901824,243697901888⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨826695956492,0,false,-313563568704,-313563568640⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1372851239554,0,true,244117603968,244117604032⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨826172015998,0,false,-314260634240,-314260634176⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1031559146438,0,false,-70143030272,-70143030208⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1031819400957,0,false,-69865666816,-69865666752⟩
    { al := (508413/2048000), au := (254631/1024000), zl := (999/1000), zu := (1999/2000),
      A := ⟨272952150982,273407954387⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨243807244224,243807244288⟩ : DyadicInterval 40),(⟨-313745102656,-313745102592⟩ : DyadicInterval 40),(⟨727886536075,727886555404⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨244172337920,244172337984⟩ : DyadicInterval 40),(⟨-314351591808,-314351591744⟩ : DyadicInterval 40),(⟨727770868527,727770887857⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨243588554368,243588554432⟩ : DyadicInterval 40),(⟨-313382074304,-313382074240⟩ : DyadicInterval 40),(⟨727955705745,727955725074⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨244062852224,244062852288⟩ : DyadicInterval 40),(⟨-314169659264,-314169659200⟩ : DyadicInterval 40),(⟨727805580537,727805599866⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨71444026,143153572⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨71441664,71441728⟩ : DyadicInterval 40),(⟨-71446400,-71446336⟩ : DyadicInterval 40),(⟨762123381277,762123400606⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨143144192,143144256⟩ : DyadicInterval 40),(⟨-143162944,-143162880⟩ : DyadicInterval 40),(⟨762123374289,762123393618⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-18688,-4608⟩ : DyadicInterval 40),(⟨762123385920,762123412224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨272815671284,273339611778⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨243697901824,243697901888⟩ : DyadicInterval 40),(⟨-313563568704,-313563568640⟩ : DyadicInterval 40),(⟨727921130867,727921150196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨244117603968,244117604032⟩ : DyadicInterval 40),(⟨-314260634240,-314260634176⟩ : DyadicInterval 40),(⟨727788224396,727788243726⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-70143030272,-69865666752⟩ : DyadicInterval 40),(⟨797056216992,797194918016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨243807244224,244172337984⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-314351591808,-313745102592⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e423_ok : ecellOkT e423 = true := by decide +kernel
theorem e423_pos {a z : ℝ} (ha1 : ((508413/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((254631/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e423 e423_ok ha1 ha2 hz1 hz2 hz

-- box ['126891/512000', '508413/2048000', '1999/2000', '1']  interval_lower 1055158259/1099511627776
noncomputable def e424 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1372007975354,0,true,243442029184,243442029248⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨827015280198,0,false,-313138947840,-313138947776⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1372463778759,0,true,243807244224,243807244288⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨826559476793,0,false,-313745102656,-313745102592⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1371871727180,0,true,243332836032,243332836096⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨827151528372,0,false,-312957821632,-312957821568⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099583075713,0,true,71445568,71445632⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099440179839,0,false,-71450304,-71450240⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623133,0,false,-4672,-4608⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1371939845329,0,true,243387429184,243387429248⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨827083410223,0,false,-313048373120,-313048373056⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1372463787369,0,true,243807251072,243807251136⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨826559468183,0,false,-313745114112,-313745114048⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1031751651851,0,false,-69937862976,-69937862912⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1032011537878,0,false,-69660943872,-69660943808⟩
    { al := (126891/512000), au := (508413/2048000), zl := (1999/2000), zu := 1,
      A := ⟨272496347578,272952150983⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨243442029184,243442029248⟩ : DyadicInterval 40),(⟨-313138947840,-313138947776⟩ : DyadicInterval 40),(⟨728002002298,728002021627⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨243807244224,243807244288⟩ : DyadicInterval 40),(⟨-313745102656,-313745102592⟩ : DyadicInterval 40),(⟨727886536074,727886555404⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨243332836032,243332836096⟩ : DyadicInterval 40),(⟨-312957821632,-312957821568⟩ : DyadicInterval 40),(⟨728036478204,728036497534⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨243807244224,243807244288⟩ : DyadicInterval 40),(⟨-313745102656,-313745102592⟩ : DyadicInterval 40),(⟨727886536074,727886555404⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,71447937⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨71445568,71445632⟩ : DyadicInterval 40),(⟨-71450304,-71450240⟩ : DyadicInterval 40),(⟨762123381277,762123400606⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4672,0⟩ : DyadicInterval 40),(⟨762123383616,762123405216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨272428217553,272952159593⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨243387429184,243387429248⟩ : DyadicInterval 40),(⟨-313048373120,-313048373056⟩ : DyadicInterval 40),(⟨728019244018,728019263347⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨243807251072,243807251136⟩ : DyadicInterval 40),(⟨-313745114112,-313745114048⟩ : DyadicInterval 40),(⟨727886533923,727886553253⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-69937862976,-69660943808⟩ : DyadicInterval 40),(⟨796953855520,797092334368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨243442029184,243807244288⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-313745102656,-313138947776⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e424_ok : ecellOkT e424 = true := by decide +kernel
theorem e424_pos {a z : ℝ} (ha1 : ((126891/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((508413/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e424 e424_ok ha1 ha2 hz1 hz2 hz

-- box ['508413/2048000', '254631/1024000', '1999/2000', '1']  interval_lower 134212075/137438953472
noncomputable def e425 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1372463778758,0,true,243807244224,243807244288⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨826559476794,0,false,-313745102656,-313745102592⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1372919582163,0,true,244172337920,244172337984⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨826103673389,0,false,-314351591808,-314351591744⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1372327302682,0,true,243697904704,243697904768⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨826695952870,0,false,-313563573504,-313563573440⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099583206398,0,true,71576256,71576320⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099440049154,0,false,-71580992,-71580928⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623116,0,false,-4672,-4608⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1372395534775,0,true,243752571072,243752571136⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨826627720777,0,false,-313654326400,-313654326336⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1372919590766,0,true,244172344832,244172344896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨826103664786,0,false,-314351603264,-314351603200⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1031525157839,0,false,-70179258432,-70179258368⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1031785534830,0,false,-69901755328,-69901755264⟩
    { al := (508413/2048000), au := (254631/1024000), zl := (1999/2000), zu := 1,
      A := ⟨272952150982,273407954387⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨243807244224,243807244288⟩ : DyadicInterval 40),(⟨-313745102656,-313745102592⟩ : DyadicInterval 40),(⟨727886536075,727886555404⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨244172337920,244172337984⟩ : DyadicInterval 40),(⟨-314351591808,-314351591744⟩ : DyadicInterval 40),(⟨727770868527,727770887857⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨243697904704,243697904768⟩ : DyadicInterval 40),(⟨-313563573504,-313563573440⟩ : DyadicInterval 40),(⟨727921129956,727921149285⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨244172337920,244172337984⟩ : DyadicInterval 40),(⟨-314351591808,-314351591744⟩ : DyadicInterval 40),(⟨727770868527,727770887857⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,71578622⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨71576256,71576320⟩ : DyadicInterval 40),(⟨-71580992,-71580928⟩ : DyadicInterval 40),(⟨762123381260,762123400589⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4672,0⟩ : DyadicInterval 40),(⟨762123383616,762123405216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨272883906999,273407962990⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨243752571072,243752571136⟩ : DyadicInterval 40),(⟨-313654326400,-313654326336⟩ : DyadicInterval 40),(⟨727903836761,727903856091⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨244172344832,244172344896⟩ : DyadicInterval 40),(⟨-314351603264,-314351603200⟩ : DyadicInterval 40),(⟨727770866331,727770885660⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-70179258432,-69901755264⟩ : DyadicInterval 40),(⟨797074261248,797213032096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨243807244224,244172337984⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-314351591808,-313745102592⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e425_ok : ecellOkT e425 = true := by decide +kernel
theorem e425_pos {a z : ℝ} (ha1 : ((508413/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((254631/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e425 e425_ok ha1 ha2 hz1 hz2 hz

-- box ['254631/1024000', '510111/2048000', '999/1000', '1999/2000']  interval_lower 548439097/549755813888
noncomputable def e426 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1372919582162,0,true,244172337920,244172337984⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨826103673390,0,false,-314351591808,-314351591744⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1373375385568,0,true,244537310528,244537310592⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨825647869984,0,false,-314958415744,-314958415680⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1372646174207,0,true,243953355584,243953355648⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨826377081345,0,false,-313987756736,-313987756672⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1373238453690,0,true,244427678656,244427678720⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨825784801862,0,false,-314776079296,-314776079232⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099583202468,0,true,71572352,71572416⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099440053084,0,false,-71577024,-71576960⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099655042822,0,true,143405632,143405696⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099368212730,0,false,-143424448,-143424384⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511609069,0,false,-18752,-18688⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623117,0,false,-4672,-4608⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1372782874561,0,true,244062849344,244062849408⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨826240380991,0,false,-314169654400,-314169654336⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1373306929017,0,true,244482503424,244482503488⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨825716326535,0,false,-314867256192,-314867256128⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1031332387931,0,false,-70384752704,-70384752640⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1031593133390,0,false,-70106805056,-70106804992⟩
    { al := (254631/1024000), au := (510111/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨273407954386,273863757792⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨244172337920,244172337984⟩ : DyadicInterval 40),(⟨-314351591808,-314351591744⟩ : DyadicInterval 40),(⟨727770868527,727770887857⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨244537310528,244537310592⟩ : DyadicInterval 40),(⟨-314958415744,-314958415680⟩ : DyadicInterval 40),(⟨727654999532,727655018861⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨243953355584,243953355648⟩ : DyadicInterval 40),(⟨-313987756736,-313987756672⟩ : DyadicInterval 40),(⟨727840274427,727840293756⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨244427678656,244427678720⟩ : DyadicInterval 40),(⟨-314776079296,-314776079232⟩ : DyadicInterval 40),(⟨727689829921,727689849250⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨71574692,143415046⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨71572352,71572416⟩ : DyadicInterval 40),(⟨-71577024,-71576960⟩ : DyadicInterval 40),(⟨762123381228,762123400557⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨143405632,143405696⟩ : DyadicInterval 40),(⟨-143424448,-143424384⟩ : DyadicInterval 40),(⟨762123374253,762123393582⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-18752,-4608⟩ : DyadicInterval 40),(⟨762123385920,762123412256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨273271246785,273795301241⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨244062849344,244062849408⟩ : DyadicInterval 40),(⟨-314169654400,-314169654336⟩ : DyadicInterval 40),(⟨727805581428,727805600757⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨244482503424,244482503488⟩ : DyadicInterval 40),(⟨-314867256192,-314867256128⟩ : DyadicInterval 40),(⟨727672414624,727672433954⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-70384752704,-70106804992⟩ : DyadicInterval 40),(⟨797176786112,797315779232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨244172337920,244537310592⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-314958415744,-314351591744⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e426_ok : ecellOkT e426 = true := by decide +kernel
theorem e426_pos {a z : ℝ} (ha1 : ((254631/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((510111/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e426 e426_ok ha1 ha2 hz1 hz2 hz

-- box ['510111/2048000', '6387/25600', '999/1000', '1999/2000']  interval_lower 1115699937/1099511627776
noncomputable def e427 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1373375385567,0,true,244537310528,244537310592⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨825647869985,0,false,-314958415744,-314958415680⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1373831188972,0,true,244902161920,244902161984⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨825192066580,0,false,-315565574720,-315565574656⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1373101521809,0,true,244318035840,244318035904⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨825921733743,0,false,-314593773056,-314593772992⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1373694029192,0,true,244792384064,244792384128⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨825329226360,0,false,-315382833920,-315382833856⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099583333197,0,true,71703040,71703104⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099439922355,0,false,-71707776,-71707712⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099655304420,0,true,143667200,143667264⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099367951132,0,false,-143686080,-143686016⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511609001,0,false,-18816,-18752⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623100,0,false,-4736,-4672⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1373238450072,0,true,244427675712,244427675776⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨825784805480,0,false,-314776074432,-314776074368⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1373762618472,0,true,244847281856,244847281920⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨825260637080,0,false,-315474213056,-315474212992⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1031105251710,0,false,-70626931136,-70626931072⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1031366488288,0,false,-70348398656,-70348398592⟩
    { al := (510111/2048000), au := (6387/25600), zl := (999/1000), zu := (1999/2000),
      A := ⟨273863757791,274319561196⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨244537310528,244537310592⟩ : DyadicInterval 40),(⟨-314958415744,-314958415680⟩ : DyadicInterval 40),(⟨727654999532,727655018862⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨244902161920,244902161984⟩ : DyadicInterval 40),(⟨-315565574720,-315565574656⟩ : DyadicInterval 40),(⟨727538929133,727538948462⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨244318035840,244318035904⟩ : DyadicInterval 40),(⟨-314593773056,-314593772992⟩ : DyadicInterval 40),(⟨727724642129,727724661458⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨244792384064,244792384128⟩ : DyadicInterval 40),(⟨-315382833920,-315382833856⟩ : DyadicInterval 40),(⟨727573878055,727573897384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨71705421,143676644⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨71703040,71703104⟩ : DyadicInterval 40),(⟨-71707776,-71707712⟩ : DyadicInterval 40),(⟨762123381243,762123400572⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨143667200,143667264⟩ : DyadicInterval 40),(⟨-143686080,-143686016⟩ : DyadicInterval 40),(⟨762123374217,762123393546⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-18816,-4672⟩ : DyadicInterval 40),(⟨762123385952,762123412288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨273726822296,274250990696⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨244427675712,244427675776⟩ : DyadicInterval 40),(⟨-314776074432,-314776074368⟩ : DyadicInterval 40),(⟨727689830853,727689850182⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨244847281856,244847281920⟩ : DyadicInterval 40),(⟨-315474213056,-315474212992⟩ : DyadicInterval 40),(⟨727556403504,727556422833⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-70626931136,-70348398592⟩ : DyadicInterval 40),(⟨797297582912,797436868448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨244537310528,244902161984⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-315565574720,-314958415680⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e427_ok : ecellOkT e427 = true := by decide +kernel
theorem e427_pos {a z : ℝ} (ha1 : ((510111/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((6387/25600 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e427 e427_ok ha1 ha2 hz1 hz2 hz

-- box ['254631/1024000', '510111/2048000', '1999/2000', '1']  interval_lower 1092361707/1099511627776
noncomputable def e428 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1372919582162,0,true,244172337920,244172337984⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨826103673390,0,false,-314351591808,-314351591744⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1373375385568,0,true,244537310528,244537310592⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨825647869984,0,false,-314958415744,-314958415680⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1372782878184,0,true,244062852224,244062852288⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨826240377368,0,false,-314169659264,-314169659200⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099583337145,0,true,71707008,71707072⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099439918407,0,false,-71711744,-71711680⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623099,0,false,-4736,-4672⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1372851224219,0,true,244117591680,244117591744⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨826172031333,0,false,-314260613824,-314260613760⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1373375394177,0,true,244537317376,244537317440⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨825647861375,0,false,-314958427200,-314958427136⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1031298285913,0,false,-70421109760,-70421109696⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1031559154063,0,false,-70143022144,-70143022080⟩
    { al := (254631/1024000), au := (510111/2048000), zl := (1999/2000), zu := 1,
      A := ⟨273407954386,273863757792⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨244172337920,244172337984⟩ : DyadicInterval 40),(⟨-314351591808,-314351591744⟩ : DyadicInterval 40),(⟨727770868527,727770887857⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨244537310528,244537310592⟩ : DyadicInterval 40),(⟨-314958415744,-314958415680⟩ : DyadicInterval 40),(⟨727654999532,727655018861⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨244062852224,244062852288⟩ : DyadicInterval 40),(⟨-314169659264,-314169659200⟩ : DyadicInterval 40),(⟨727805580538,727805599867⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨244537310528,244537310592⟩ : DyadicInterval 40),(⟨-314958415744,-314958415680⟩ : DyadicInterval 40),(⟨727654999532,727655018861⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,71709369⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨71707008,71707072⟩ : DyadicInterval 40),(⟨-71711744,-71711680⟩ : DyadicInterval 40),(⟨762123381243,762123400572⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4736,0⟩ : DyadicInterval 40),(⟨762123383616,762123405248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨273339596443,273863766401⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨244117591680,244117591744⟩ : DyadicInterval 40),(⟨-314260613824,-314260613760⟩ : DyadicInterval 40),(⟨727788228291,727788247620⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨244537317376,244537317440⟩ : DyadicInterval 40),(⟨-314958427200,-314958427136⟩ : DyadicInterval 40),(⟨727654997366,727655016696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-70421109760,-70143022080⟩ : DyadicInterval 40),(⟨797194894656,797333957760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨244172337920,244537310592⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-314958415744,-314351591744⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e428_ok : ecellOkT e428 = true := by decide +kernel
theorem e428_pos {a z : ℝ} (ha1 : ((254631/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((510111/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e428 e428_ok ha1 ha2 hz1 hz2 hz

-- box ['510111/2048000', '6387/25600', '1999/2000', '1']  interval_lower 277788753/274877906944
noncomputable def e429 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1373375385567,0,true,244537310528,244537310592⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨825647869985,0,false,-314958415744,-314958415680⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1373831188972,0,true,244902161920,244902161984⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨825192066580,0,false,-315565574720,-315565574656⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1373238453688,0,true,244427678656,244427678720⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨825784801864,0,false,-314776079232,-314776079168⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099583467953,0,true,71837824,71837888⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099439787599,0,false,-71842560,-71842496⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623082,0,false,-4736,-4672⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1373306913675,0,true,244482491200,244482491264⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨825716341877,0,false,-314867235776,-314867235712⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1373831197572,0,true,244902168832,244902168896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨825192057980,0,false,-315565586176,-315565586112⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1031071036087,0,false,-70663417344,-70663417280⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1031332395573,0,false,-70384744576,-70384744512⟩
    { al := (510111/2048000), au := (6387/25600), zl := (1999/2000), zu := 1,
      A := ⟨273863757791,274319561196⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨244537310528,244537310592⟩ : DyadicInterval 40),(⟨-314958415744,-314958415680⟩ : DyadicInterval 40),(⟨727654999532,727655018862⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨244902161920,244902161984⟩ : DyadicInterval 40),(⟨-315565574720,-315565574656⟩ : DyadicInterval 40),(⟨727538929133,727538948462⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨244427678656,244427678720⟩ : DyadicInterval 40),(⟨-314776079232,-314776079168⟩ : DyadicInterval 40),(⟨727689829898,727689849227⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨244902161920,244902161984⟩ : DyadicInterval 40),(⟨-315565574720,-315565574656⟩ : DyadicInterval 40),(⟨727538929133,727538948462⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,71840177⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨71837824,71837888⟩ : DyadicInterval 40),(⟨-71842560,-71842496⟩ : DyadicInterval 40),(⟨762123381225,762123400555⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4736,0⟩ : DyadicInterval 40),(⟨762123383616,762123405248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨273795285899,274319569796⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨244482491200,244482491264⟩ : DyadicInterval 40),(⟨-314867235776,-314867235712⟩ : DyadicInterval 40),(⟨727672418495,727672437824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨244902168832,244902168896⟩ : DyadicInterval 40),(⟨-315565586176,-315565586112⟩ : DyadicInterval 40),(⟨727538926921,727538946250⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-70663417344,-70384744512⟩ : DyadicInterval 40),(⟨797315755872,797455111552⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨244537310528,244902161984⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-315565574720,-314958415680⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e429_ok : ecellOkT e429 = true := by decide +kernel
theorem e429_pos {a z : ℝ} (ha1 : ((510111/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((6387/25600 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e429 e429_ok ha1 ha2 hz1 hz2 hz

-- box ['6387/25600', '511809/2048000', '999/1000', '1999/2000']  interval_lower 1134650521/1099511627776
noncomputable def e430 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1373831188971,0,true,244902161920,244902161984⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨825192066581,0,false,-315565574720,-315565574656⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1374286992376,0,true,245266892352,245266892416⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨824736263176,0,false,-316173069184,-316173069120⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1373556869409,0,true,244682595200,244682595264⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨825466386143,0,false,-315200123520,-315200123456⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1374149604694,0,true,245156968512,245156968576⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨824873650858,0,false,-315989923648,-315989923584⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099583463986,0,true,71833856,71833920⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099439791566,0,false,-71838592,-71838528⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099655566141,0,true,143928896,143928960⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099367689411,0,false,-143947840,-143947776⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511608932,0,false,-18880,-18816⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623083,0,false,-4736,-4672⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1373694025579,0,true,244792381184,244792381248⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨825329229973,0,false,-315382829120,-315382829056⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1374218307925,0,true,245211939328,245211939392⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨824804947627,0,false,-316081505088,-316081505024⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1030877737772,0,false,-70869565760,-70869565696⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1031139465658,0,false,-70590447936,-70590447872⟩
    { al := (6387/25600), au := (511809/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨274319561195,274775364600⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨244902161920,244902161984⟩ : DyadicInterval 40),(⟨-315565574720,-315565574656⟩ : DyadicInterval 40),(⟨727538929133,727538948462⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨245266892352,245266892416⟩ : DyadicInterval 40),(⟨-316173069184,-316173069120⟩ : DyadicInterval 40),(⟨727422657203,727422676532⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨244682595200,244682595264⟩ : DyadicInterval 40),(⟨-315200123520,-315200123456⟩ : DyadicInterval 40),(⟨727608808775,727608828105⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨245156968512,245156968576⟩ : DyadicInterval 40),(⟨-315989923648,-315989923584⟩ : DyadicInterval 40),(⟨727457724958,727457744288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨71836210,143938365⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨71833856,71833920⟩ : DyadicInterval 40),(⟨-71838592,-71838528⟩ : DyadicInterval 40),(⟨762123381226,762123400555⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨143928896,143928960⟩ : DyadicInterval 40),(⟨-143947840,-143947776⟩ : DyadicInterval 40),(⟨762123374180,762123393510⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-18880,-4672⟩ : DyadicInterval 40),(⟨762123385952,762123412320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨274182397803,274706680149⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨244792381184,244792381248⟩ : DyadicInterval 40),(⟨-315382829120,-315382829056⟩ : DyadicInterval 40),(⟨727573878973,727573898302⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨245211939328,245211939392⟩ : DyadicInterval 40),(⟨-316081505088,-316081505024⟩ : DyadicInterval 40),(⟨727440190955,727440210284⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-70869565760,-70590447872⟩ : DyadicInterval 40),(⟨797418607552,797558185760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨244902161920,245266892416⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-316173069184,-315565574656⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e430_ok : ecellOkT e430 = true := by decide +kernel
theorem e430_pos {a z : ℝ} (ha1 : ((6387/25600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((511809/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e430 e430_ok ha1 ha2 hz1 hz2 hz

-- box ['511809/2048000', '256329/1024000', '999/1000', '1999/2000']  interval_lower 288432483/274877906944
noncomputable def e431 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1374286992375,0,true,245266892352,245266892416⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨824736263177,0,false,-316173069184,-316173069120⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1374742795781,0,true,245631501824,245631501888⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨824280459771,0,false,-316780899456,-316780899392⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1374012217010,0,true,245047033664,245047033728⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨825011038542,0,false,-315806808576,-315806808512⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1374605180198,0,true,245521432128,245521432192⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨824418075354,0,false,-316597348672,-316597348608⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099583594837,0,true,71964672,71964736⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099439660715,0,false,-71969472,-71969408⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099655827986,0,true,144190720,144190784⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099367427566,0,false,-144209728,-144209664⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511608864,0,false,-18944,-18880⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623066,0,false,-4736,-4672⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1374149601084,0,true,245156965632,245156965696⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨824873654468,0,false,-315989918784,-315989918720⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1374673997388,0,true,245576475904,245576475968⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨824349258164,0,false,-316689132800,-316689132736⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1030649846110,0,false,-71112656896,-71112656832⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1030912065501,0,false,-70832953152,-70832953088⟩
    { al := (511809/2048000), au := (256329/1024000), zl := (999/1000), zu := (1999/2000),
      A := ⟨274775364599,275231168005⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨245266892352,245266892416⟩ : DyadicInterval 40),(⟨-316173069184,-316173069120⟩ : DyadicInterval 40),(⟨727422657204,727422676533⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨245631501824,245631501888⟩ : DyadicInterval 40),(⟨-316780899456,-316780899392⟩ : DyadicInterval 40),(⟨727306183730,727306203060⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨245047033664,245047033728⟩ : DyadicInterval 40),(⟨-315806808576,-315806808512⟩ : DyadicInterval 40),(⟨727492774401,727492793731⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨245521432128,245521432192⟩ : DyadicInterval 40),(⟨-316597348672,-316597348608⟩ : DyadicInterval 40),(⟨727341370489,727341389819⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨71967061,144200210⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨71964672,71964736⟩ : DyadicInterval 40),(⟨-71969472,-71969408⟩ : DyadicInterval 40),(⟨762123381241,762123400570⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨144190720,144190784⟩ : DyadicInterval 40),(⟨-144209728,-144209664⟩ : DyadicInterval 40),(⟨762123374143,762123393473⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-18944,-4672⟩ : DyadicInterval 40),(⟨762123385952,762123412352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨274637973308,275162369612⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨245156965632,245156965696⟩ : DyadicInterval 40),(⟨-315989918784,-315989918720⟩ : DyadicInterval 40),(⟨727457725855,727457745184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨245576475904,245576475968⟩ : DyadicInterval 40),(⟨-316689132800,-316689132736⟩ : DyadicInterval 40),(⟨727323776994,727323796323⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-71112656896,-70832953088⟩ : DyadicInterval 40),(⟨797539860160,797679731328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨245266892352,245631501888⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-316780899456,-316173069120⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e431_ok : ecellOkT e431 = true := by decide +kernel
theorem e431_pos {a z : ℝ} (ha1 : ((511809/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((256329/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e431 e431_ok ha1 ha2 hz1 hz2 hz

-- box ['6387/25600', '511809/2048000', '1999/2000', '1']  interval_lower 1130076459/1099511627776
noncomputable def e432 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1373831188971,0,true,244902161920,244902161984⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨825192066581,0,false,-315565574720,-315565574656⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1374286992376,0,true,245266892352,245266892416⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨824736263176,0,false,-316173069184,-316173069120⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1373694029190,0,true,244792384064,244792384128⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨825329226362,0,false,-315382833920,-315382833856⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099583598822,0,true,71968640,71968704⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099439656730,0,false,-71973440,-71973376⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623064,0,false,-4736,-4672⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1373762603117,0,true,244847269568,244847269632⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨825260652435,0,false,-315474192576,-315474192512⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1374287000978,0,true,245266899264,245266899328⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨824736254574,0,false,-316173080640,-316173080576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1030843408349,0,false,-70906181376,-70906181312⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1031105259371,0,false,-70626922944,-70626922880⟩
    { al := (6387/25600), au := (511809/2048000), zl := (1999/2000), zu := 1,
      A := ⟨274319561195,274775364600⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨244902161920,244902161984⟩ : DyadicInterval 40),(⟨-315565574720,-315565574656⟩ : DyadicInterval 40),(⟨727538929133,727538948462⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨245266892352,245266892416⟩ : DyadicInterval 40),(⟨-316173069184,-316173069120⟩ : DyadicInterval 40),(⟨727422657203,727422676532⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨244792384064,244792384128⟩ : DyadicInterval 40),(⟨-315382833920,-315382833856⟩ : DyadicInterval 40),(⟨727573878056,727573897385⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨245266892352,245266892416⟩ : DyadicInterval 40),(⟨-316173069184,-316173069120⟩ : DyadicInterval 40),(⟨727422657203,727422676532⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,71971046⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨71968640,71968704⟩ : DyadicInterval 40),(⟨-71973440,-71973376⟩ : DyadicInterval 40),(⟨762123381240,762123400570⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4736,0⟩ : DyadicInterval 40),(⟨762123383616,762123405248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨274250975341,274775373202⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨244847269568,244847269632⟩ : DyadicInterval 40),(⟨-315474192576,-315474192512⟩ : DyadicInterval 40),(⟨727556407407,727556426736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨245266899264,245266899328⟩ : DyadicInterval 40),(⟨-316173080640,-316173080576⟩ : DyadicInterval 40),(⟨727422654984,727422674313⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-70906181376,-70626922880⟩ : DyadicInterval 40),(⟨797436845056,797576493568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨244902161920,245266892416⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-316173069184,-315565574656⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e432_ok : ecellOkT e432 = true := by decide +kernel
theorem e432_pos {a z : ℝ} (ha1 : ((6387/25600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((511809/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e432 e432_ok ha1 ha2 hz1 hz2 hz

-- box ['511809/2048000', '256329/1024000', '1999/2000', '1']  interval_lower 1149127077/1099511627776
noncomputable def e433 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1374286992375,0,true,245266892352,245266892416⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨824736263177,0,false,-316173069184,-316173069120⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1374742795781,0,true,245631501824,245631501888⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨824280459771,0,false,-316780899456,-316780899392⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1374149604692,0,true,245156968512,245156968576⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨824873650860,0,false,-315989923648,-315989923584⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099583729754,0,true,72099584,72099648⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099439525798,0,false,-72104384,-72104320⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623047,0,false,-4736,-4672⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1374218292560,0,true,245211927040,245211927104⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨824804962992,0,false,-316081484608,-316081484544⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1374742804387,0,true,245631508736,245631508800⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨824280451165,0,false,-316780910912,-316780910848⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1030615402702,0,false,-71149402176,-71149402112⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1030877745451,0,false,-70869557568,-70869557504⟩
    { al := (511809/2048000), au := (256329/1024000), zl := (1999/2000), zu := 1,
      A := ⟨274775364599,275231168005⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨245266892352,245266892416⟩ : DyadicInterval 40),(⟨-316173069184,-316173069120⟩ : DyadicInterval 40),(⟨727422657204,727422676533⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨245631501824,245631501888⟩ : DyadicInterval 40),(⟨-316780899456,-316780899392⟩ : DyadicInterval 40),(⟨727306183730,727306203060⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨245156968512,245156968576⟩ : DyadicInterval 40),(⟨-315989923648,-315989923584⟩ : DyadicInterval 40),(⟨727457724959,727457744288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨245631501824,245631501888⟩ : DyadicInterval 40),(⟨-316780899456,-316780899392⟩ : DyadicInterval 40),(⟨727306183730,727306203060⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,72101978⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨72099584,72099648⟩ : DyadicInterval 40),(⟨-72104384,-72104320⟩ : DyadicInterval 40),(⟨762123381223,762123400552⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4736,0⟩ : DyadicInterval 40),(⟨762123383616,762123405248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨274706664784,275231176611⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨245211927040,245211927104⟩ : DyadicInterval 40),(⟨-316081484608,-316081484544⟩ : DyadicInterval 40),(⟨727440194874,727440214204⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨245631508736,245631508800⟩ : DyadicInterval 40),(⟨-316780910912,-316780910848⟩ : DyadicInterval 40),(⟨727306181503,727306200832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-71149402176,-70869557504⟩ : DyadicInterval 40),(⟨797558162368,797698103968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨245266892352,245631501888⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-316780899456,-316173069120⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e433_ok : ecellOkT e433 = true := by decide +kernel
theorem e433_pos {a z : ℝ} (ha1 : ((511809/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((256329/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e433 e433_ok ha1 ha2 hz1 hz2 hz

-- box ['256329/1024000', '513507/2048000', '999/1000', '1999/2000']  interval_lower 1172938995/1099511627776
noncomputable def e434 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1374742795780,0,true,245631501824,245631501888⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨824280459772,0,false,-316780899456,-316780899392⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1375198599185,0,true,245995990464,245995990528⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨823824656367,0,false,-317389065984,-317389065920⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1374467564611,0,true,245411351424,245411351488⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨824555690941,0,false,-316413828544,-316413828480⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1375060755700,0,true,245885774976,245885775040⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨823962499852,0,false,-317205109504,-317205109440⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099583725749,0,true,72095552,72095616⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099439529803,0,false,-72100352,-72100288⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099656089953,0,true,144452672,144452736⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099367165599,0,false,-144471680,-144471616⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511608795,0,false,-19008,-18944⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623049,0,false,-4736,-4672⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1374605176598,0,true,245521429248,245521429312⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨824418078954,0,false,-316597343872,-316597343808⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1375129686847,0,true,245940891648,245940891712⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨823893568705,0,false,-317297096448,-317297096384⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1030421576732,0,false,-71356204800,-71356204736⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1030684287809,0,false,-71075914624,-71075914560⟩
    { al := (256329/1024000), au := (513507/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨275231168004,275686971409⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨245631501824,245631501888⟩ : DyadicInterval 40),(⟨-316780899456,-316780899392⟩ : DyadicInterval 40),(⟨727306183731,727306203060⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨245995990464,245995990528⟩ : DyadicInterval 40),(⟨-317389065984,-317389065920⟩ : DyadicInterval 40),(⟨727189508669,727189527999⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨245411351424,245411351488⟩ : DyadicInterval 40),(⟨-316413828544,-316413828480⟩ : DyadicInterval 40),(⟨727376538875,727376558204⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨245885774976,245885775040⟩ : DyadicInterval 40),(⟨-317205109504,-317205109440⟩ : DyadicInterval 40),(⟨727224814667,727224833997⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨72097973,144462177⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨72095552,72095616⟩ : DyadicInterval 40),(⟨-72100352,-72100288⟩ : DyadicInterval 40),(⟨762123381224,762123400553⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨144452672,144452736⟩ : DyadicInterval 40),(⟨-144471680,-144471616⟩ : DyadicInterval 40),(⟨762123374075,762123393404⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-19008,-4672⟩ : DyadicInterval 40),(⟨762123385952,762123412384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨275093548822,275618059071⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨245521429248,245521429312⟩ : DyadicInterval 40),(⟨-316597343872,-316597343808⟩ : DyadicInterval 40),(⟨727341371410,727341390739⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨245940891648,245940891712⟩ : DyadicInterval 40),(⟨-317297096448,-317297096384⟩ : DyadicInterval 40),(⟨727207161547,727207180877⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-71356204800,-71075914560⟩ : DyadicInterval 40),(⟨797661340896,797801505280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨245631501824,245995990528⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-317389065984,-316780899392⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e434_ok : ecellOkT e434 = true := by decide +kernel
theorem e434_pos {a z : ℝ} (ha1 : ((256329/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((513507/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e434 e434_ok ha1 ha2 hz1 hz2 hz

-- box ['513507/2048000', '128589/512000', '999/1000', '1999/2000']  interval_lower 1192278755/1099511627776
noncomputable def e435 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1375198599184,0,true,245995990464,245995990528⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨823824656368,0,false,-317389065984,-317389065920⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1375654402589,0,true,246360358272,246360358336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨823368852963,0,false,-317997569024,-317997568960⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1374922912212,0,true,245775548544,245775548608⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨824100343340,0,false,-317021183872,-317021183808⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1375516331202,0,true,246249997184,246249997248⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨823506924350,0,false,-317813206464,-317813206400⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099583856724,0,true,72226560,72226624⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099439398828,0,false,-72231360,-72231296⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099656352045,0,true,144714688,144714752⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099366903507,0,false,-144733824,-144733760⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511608726,0,false,-19072,-19008⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623032,0,false,-4800,-4736⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1375060752113,0,true,245885772160,245885772224⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨823962503439,0,false,-317205104768,-317205104704⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1375585376312,0,true,246305186624,246305186688⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨823437879240,0,false,-317905396480,-317905396416⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1030192929632,0,false,-71600209792,-71600209728⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1030456132587,0,false,-71319332608,-71319332544⟩
    { al := (513507/2048000), au := (128589/512000), zl := (999/1000), zu := (1999/2000),
      A := ⟨275686971408,276142774813⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨245995990464,245995990528⟩ : DyadicInterval 40),(⟨-317389065984,-317389065920⟩ : DyadicInterval 40),(⟨727189508669,727189527999⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨246360358272,246360358336⟩ : DyadicInterval 40),(⟨-317997569024,-317997568960⟩ : DyadicInterval 40),(⟨727072631981,727072651310⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨245775548544,245775548608⟩ : DyadicInterval 40),(⟨-317021183872,-317021183808⟩ : DyadicInterval 40),(⟨727260102189,727260121519⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨246249997184,246249997248⟩ : DyadicInterval 40),(⟨-317813206464,-317813206400⟩ : DyadicInterval 40),(⟨727108057398,727108076728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨72228948,144724269⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨72226560,72226624⟩ : DyadicInterval 40),(⟨-72231360,-72231296⟩ : DyadicInterval 40),(⟨762123381206,762123400536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨144714688,144714752⟩ : DyadicInterval 40),(⟨-144733824,-144733760⟩ : DyadicInterval 40),(⟨762123374070,762123393399⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-19072,-4736⟩ : DyadicInterval 40),(⟨762123385984,762123412416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨275549124337,276073748536⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨245885772160,245885772224⟩ : DyadicInterval 40),(⟨-317205104768,-317205104704⟩ : DyadicInterval 40),(⟨727224815572,727224834901⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨246305186624,246305186688⟩ : DyadicInterval 40),(⟨-317905396480,-317905396416⟩ : DyadicInterval 40),(⟨727090344606,727090363935⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-71600209792,-71319332544⟩ : DyadicInterval 40),(⟨797783049888,797923507776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨245995990464,246360358336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-317997569024,-317389065920⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e435_ok : ecellOkT e435 = true := by decide +kernel
theorem e435_pos {a z : ℝ} (ha1 : ((513507/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((128589/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e435 e435_ok ha1 ha2 hz1 hz2 hz

-- box ['256329/1024000', '513507/2048000', '1999/2000', '1']  interval_lower 584153475/549755813888
noncomputable def e436 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1374742795780,0,true,245631501824,245631501888⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨824280459772,0,false,-316780899456,-316780899392⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1375198599185,0,true,245995990464,245995990528⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨823824656367,0,false,-317389065984,-317389065920⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1374605180195,0,true,245521432128,245521432192⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨824418075357,0,false,-316597348672,-316597348608⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099583860747,0,true,72230592,72230656⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099439394805,0,false,-72235392,-72235328⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623030,0,false,-4800,-4736⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1374673982012,0,true,245576463616,245576463680⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨824349273540,0,false,-316689112256,-316689112192⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1375198607795,0,true,245995997312,245995997376⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨823824647757,0,false,-317389077440,-317389077376⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1030387019147,0,false,-71393080064,-71393080000⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1030649853807,0,false,-71112648640,-71112648576⟩
    { al := (256329/1024000), au := (513507/2048000), zl := (1999/2000), zu := 1,
      A := ⟨275231168004,275686971409⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨245631501824,245631501888⟩ : DyadicInterval 40),(⟨-316780899456,-316780899392⟩ : DyadicInterval 40),(⟨727306183731,727306203060⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨245995990464,245995990528⟩ : DyadicInterval 40),(⟨-317389065984,-317389065920⟩ : DyadicInterval 40),(⟨727189508669,727189527999⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨245521432128,245521432192⟩ : DyadicInterval 40),(⟨-316597348672,-316597348608⟩ : DyadicInterval 40),(⟨727341370490,727341389820⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨245995990464,245995990528⟩ : DyadicInterval 40),(⟨-317389065984,-317389065920⟩ : DyadicInterval 40),(⟨727189508669,727189527999⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,72232971⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨72230592,72230656⟩ : DyadicInterval 40),(⟨-72235392,-72235328⟩ : DyadicInterval 40),(⟨762123381206,762123400535⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4800,0⟩ : DyadicInterval 40),(⟨762123383616,762123405280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨275162354236,275686980019⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨245576463616,245576463680⟩ : DyadicInterval 40),(⟨-316689112256,-316689112192⟩ : DyadicInterval 40),(⟨727323780906,727323800235⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨245995997312,245995997376⟩ : DyadicInterval 40),(⟨-317389077440,-317389077376⟩ : DyadicInterval 40),(⟨727189506473,727189525802⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-71393080064,-71112648576⟩ : DyadicInterval 40),(⟨797679707904,797819942912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨245631501824,245995990528⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-317389065984,-316780899392⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e436_ok : ecellOkT e436 = true := by decide +kernel
theorem e436_pos {a z : ℝ} (ha1 : ((256329/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((513507/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e436 e436_ok ha1 ha2 hz1 hz2 hz

-- box ['513507/2048000', '128589/512000', '1999/2000', '1']  interval_lower 593808529/549755813888
noncomputable def e437 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1375198599184,0,true,245995990464,245995990528⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨823824656368,0,false,-317389065984,-317389065920⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1375654402589,0,true,246360358272,246360358336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨823368852963,0,false,-317997569024,-317997568960⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1375060755698,0,true,245885774976,245885775040⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨823962499854,0,false,-317205109504,-317205109440⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099583991803,0,true,72361600,72361664⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099439263749,0,false,-72366464,-72366400⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623013,0,false,-4800,-4736⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1375129671462,0,true,245940879296,245940879360⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨823893584090,0,false,-317297075904,-317297075840⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1375654411202,0,true,246360365120,246360365184⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨823368844350,0,false,-317997580544,-317997580480⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1030158257687,0,false,-71637215360,-71637215296⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1030421584446,0,false,-71356196544,-71356196480⟩
    { al := (513507/2048000), au := (128589/512000), zl := (1999/2000), zu := 1,
      A := ⟨275686971408,276142774813⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨245995990464,245995990528⟩ : DyadicInterval 40),(⟨-317389065984,-317389065920⟩ : DyadicInterval 40),(⟨727189508669,727189527999⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨246360358272,246360358336⟩ : DyadicInterval 40),(⟨-317997569024,-317997568960⟩ : DyadicInterval 40),(⟨727072631981,727072651310⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨245885774976,245885775040⟩ : DyadicInterval 40),(⟨-317205109504,-317205109440⟩ : DyadicInterval 40),(⟨727224814668,727224833997⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨246360358272,246360358336⟩ : DyadicInterval 40),(⟨-317997569024,-317997568960⟩ : DyadicInterval 40),(⟨727072631981,727072651310⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,72364027⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨72361600,72361664⟩ : DyadicInterval 40),(⟨-72366464,-72366400⟩ : DyadicInterval 40),(⟨762123381221,762123400550⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4800,0⟩ : DyadicInterval 40),(⟨762123383616,762123405280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨275618043686,276142783426⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨245940879296,245940879360⟩ : DyadicInterval 40),(⟨-317297075904,-317297075840⟩ : DyadicInterval 40),(⟨727207165515,727207184845⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨246360365120,246360365184⟩ : DyadicInterval 40),(⟨-317997580544,-317997580480⟩ : DyadicInterval 40),(⟨727072629800,727072649129⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-71637215360,-71356196480⟩ : DyadicInterval 40),(⟨797801481856,797942010560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨245995990464,246360358336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-317997569024,-317389065920⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e437_ok : ecellOkT e437 = true := by decide +kernel
theorem e437_pos {a z : ℝ} (ha1 : ((513507/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((128589/512000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e437 e437_ok ha1 ha2 hz1 hz2 hz

-- box ['128589/512000', '103041/409600', '999/1000', '1999/2000']  interval_lower 1211748979/1099511627776
noncomputable def e438 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1375654402588,0,true,246360358272,246360358336⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨823368852964,0,false,-317997569024,-317997568960⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1376110205993,0,true,246724605376,246724605440⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨822913049559,0,false,-318606409024,-318606408960⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1375378259813,0,true,246139625024,246139625088⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨823644995739,0,false,-317628874880,-317628874816⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1375971906705,0,true,246614098688,246614098752⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨823051348847,0,false,-318421639936,-318421639872⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099583987761,0,true,72357568,72357632⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099439267791,0,false,-72362368,-72362304⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099656614263,0,true,144976896,144976960⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099366641289,0,false,-144996096,-144996032⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511608657,0,false,-19136,-19072⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623014,0,false,-4800,-4736⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1375516327621,0,true,246249994304,246249994368⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨823506927931,0,false,-317813201728,-317813201664⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1376041065765,0,true,246669360960,246669361024⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨822982189787,0,false,-318514033216,-318514033152⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1029963904820,0,false,-71844672192,-71844672128⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1030227599839,0,false,-71563207360,-71563207296⟩
    { al := (128589/512000), au := (103041/409600), zl := (999/1000), zu := (1999/2000),
      A := ⟨276142774812,276598578217⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨246360358272,246360358336⟩ : DyadicInterval 40),(⟨-317997569024,-317997568960⟩ : DyadicInterval 40),(⟨727072631981,727072651311⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨246724605376,246724605440⟩ : DyadicInterval 40),(⟨-318606409024,-318606408960⟩ : DyadicInterval 40),(⟨726955553619,726955572949⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨246139625024,246139625088⟩ : DyadicInterval 40),(⟨-317628874880,-317628874816⟩ : DyadicInterval 40),(⟨727143464333,727143483662⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨246614098688,246614098752⟩ : DyadicInterval 40),(⟨-318421639936,-318421639872⟩ : DyadicInterval 40),(⟨726991098731,726991118060⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨72359985,144986487⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨72357568,72357632⟩ : DyadicInterval 40),(⟨-72362368,-72362304⟩ : DyadicInterval 40),(⟨762123381189,762123400519⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨144976896,144976960⟩ : DyadicInterval 40),(⟨-144996096,-144996032⟩ : DyadicInterval 40),(⟨762123374033,762123393362⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-19136,-4736⟩ : DyadicInterval 40),(⟨762123385984,762123412448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨276004699845,276529437989⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨246249994304,246249994368⟩ : DyadicInterval 40),(⟨-317813201728,-317813201664⟩ : DyadicInterval 40),(⟨727108058345,727108077674⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨246669360960,246669361024⟩ : DyadicInterval 40),(⟨-318514033216,-318514033152⟩ : DyadicInterval 40),(⟨726973326080,726973345410⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-71844672192,-71563207296⟩ : DyadicInterval 40),(⟨797904987264,798045738976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨246360358272,246724605440⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-318606409024,-317997568960⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e438_ok : ecellOkT e438 = true := by decide +kernel
theorem e438_pos {a z : ℝ} (ha1 : ((128589/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((103041/409600 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e438 e438_ok ha1 ha2 hz1 hz2 hz

-- box ['103041/409600', '258027/1024000', '999/1000', '1999/2000']  interval_lower 1231350617/1099511627776
noncomputable def e439 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1376110205992,0,true,246724605376,246724605440⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨822913049560,0,false,-318606409024,-318606408960⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1376566009398,0,true,247088731840,247088731904⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨822457246154,0,false,-319215586368,-319215586304⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1375833607413,0,true,246503580992,246503581056⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨823189648139,0,false,-318236901888,-318236901824⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1376427482208,0,true,246978079744,246978079808⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨822595773344,0,false,-319030410304,-319030410240⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099584118860,0,true,72488640,72488704⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099439136692,0,false,-72493504,-72493440⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099656876603,0,true,145239232,145239296⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099366378949,0,false,-145258432,-145258368⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511608588,0,false,-19200,-19136⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622997,0,false,-4800,-4736⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1375971903133,0,true,246614095872,246614095936⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨823051352419,0,false,-318421635200,-318421635136⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1376496755224,0,true,247033414720,247033414784⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨822526500328,0,false,-319123007040,-319123006976⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1029734502287,0,false,-72089592320,-72089592256⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1029998689559,0,false,-71807539264,-71807539200⟩
    { al := (103041/409600), au := (258027/1024000), zl := (999/1000), zu := (1999/2000),
      A := ⟨276598578216,277054381622⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨246724605376,246724605440⟩ : DyadicInterval 40),(⟨-318606409024,-318606408960⟩ : DyadicInterval 40),(⟨726955553619,726955572949⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨247088731840,247088731904⟩ : DyadicInterval 40),(⟨-319215586368,-319215586304⟩ : DyadicInterval 40),(⟨726838273552,726838292882⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨246503580992,246503581056⟩ : DyadicInterval 40),(⟨-318236901888,-318236901824⟩ : DyadicInterval 40),(⟨727026625210,727026644540⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨246978079744,246978079808⟩ : DyadicInterval 40),(⟨-319030410304,-319030410240⟩ : DyadicInterval 40),(⟨726873938516,726873957845⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨72491084,145248827⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨72488640,72488704⟩ : DyadicInterval 40),(⟨-72493504,-72493440⟩ : DyadicInterval 40),(⟨762123381204,762123400533⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨145239232,145239296⟩ : DyadicInterval 40),(⟨-145258432,-145258368⟩ : DyadicInterval 40),(⟨762123373963,762123393293⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-19200,-4736⟩ : DyadicInterval 40),(⟨762123385984,762123412480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨276460275357,276985127448⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨246614095872,246614095936⟩ : DyadicInterval 40),(⟨-318421635200,-318421635136⟩ : DyadicInterval 40),(⟨726991099638,726991118968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨247033414720,247033414784⟩ : DyadicInterval 40),(⟨-319123007040,-319123006976⟩ : DyadicInterval 40),(⟨726856105935,726856125264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-72089592320,-71807539200⟩ : DyadicInterval 40),(⟨798027153216,798168199040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨246724605376,247088731904⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-319215586368,-318606408960⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e439_ok : ecellOkT e439 = true := by decide +kernel
theorem e439_pos {a z : ℝ} (ha1 : ((103041/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((258027/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e439 e439_ok ha1 ha2 hz1 hz2 hz

-- box ['128589/512000', '103041/409600', '1999/2000', '1']  interval_lower 1207057795/1099511627776
noncomputable def e440 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1375654402588,0,true,246360358272,246360358336⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨823368852964,0,false,-317997569024,-317997568960⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1376110205993,0,true,246724605376,246724605440⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨822913049559,0,false,-318606409024,-318606408960⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1375516331200,0,true,246249997184,246249997248⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨823506924352,0,false,-317813206464,-317813206400⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099584122921,0,true,72492736,72492800⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099439132631,0,false,-72497536,-72497472⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622996,0,false,-4800,-4736⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1375585360916,0,true,246305174336,246305174400⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨823437894636,0,false,-317905375936,-317905375872⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1376110214610,0,true,246724612224,246724612288⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨822913040942,0,false,-318606420544,-318606420480⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1029929118318,0,false,-71881808320,-71881808256⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1030192937365,0,false,-71600201536,-71600201472⟩
    { al := (128589/512000), au := (103041/409600), zl := (1999/2000), zu := 1,
      A := ⟨276142774812,276598578217⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨246360358272,246360358336⟩ : DyadicInterval 40),(⟨-317997569024,-317997568960⟩ : DyadicInterval 40),(⟨727072631981,727072651311⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨246724605376,246724605440⟩ : DyadicInterval 40),(⟨-318606409024,-318606408960⟩ : DyadicInterval 40),(⟨726955553619,726955572949⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨246249997184,246249997248⟩ : DyadicInterval 40),(⟨-317813206464,-317813206400⟩ : DyadicInterval 40),(⟨727108057398,727108076728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨246724605376,246724605440⟩ : DyadicInterval 40),(⟨-318606409024,-318606408960⟩ : DyadicInterval 40),(⟨726955553619,726955572949⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,72495145⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨72492736,72492800⟩ : DyadicInterval 40),(⟨-72497536,-72497472⟩ : DyadicInterval 40),(⟨762123381171,762123400501⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4800,0⟩ : DyadicInterval 40),(⟨762123383616,762123405280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨276073733140,276598586834⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨246305174336,246305174400⟩ : DyadicInterval 40),(⟨-317905375936,-317905375872⟩ : DyadicInterval 40),(⟨727090348550,727090367880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨246724612224,246724612288⟩ : DyadicInterval 40),(⟨-318606420544,-318606420480⟩ : DyadicInterval 40),(⟨726955551429,726955570759⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-71881808320,-71600201472⟩ : DyadicInterval 40),(⟨797923484352,798064307040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨246360358272,246724605440⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-318606409024,-317997568960⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e440_ok : ecellOkT e440 = true := by decide +kernel
theorem e440_pos {a z : ℝ} (ha1 : ((128589/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((103041/409600 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e440 e440_ok ha1 ha2 hz1 hz2 hz

-- box ['103041/409600', '258027/1024000', '1999/2000', '1']  interval_lower 1226630045/1099511627776
noncomputable def e441 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1376110205992,0,true,246724605376,246724605440⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨822913049560,0,false,-318606409024,-318606408960⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1376566009398,0,true,247088731840,247088731904⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨822457246154,0,false,-319215586368,-319215586304⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1375971906702,0,true,246614098688,246614098752⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨823051348850,0,false,-318421639936,-318421639872⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099584254101,0,true,72623872,72623936⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099439001451,0,false,-72628736,-72628672⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622978,0,false,-4800,-4736⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1376041050359,0,true,246669348608,246669348672⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨822982205193,0,false,-318514012608,-318514012544⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1376566018013,0,true,247088738688,247088738752⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨822457237539,0,false,-319215597888,-319215597824⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1029699601044,0,false,-72126859136,-72126859072⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1029963912571,0,false,-71844663936,-71844663872⟩
    { al := (103041/409600), au := (258027/1024000), zl := (1999/2000), zu := 1,
      A := ⟨276598578216,277054381622⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨246724605376,246724605440⟩ : DyadicInterval 40),(⟨-318606409024,-318606408960⟩ : DyadicInterval 40),(⟨726955553619,726955572949⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨247088731840,247088731904⟩ : DyadicInterval 40),(⟨-319215586368,-319215586304⟩ : DyadicInterval 40),(⟨726838273552,726838292882⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨246614098688,246614098752⟩ : DyadicInterval 40),(⟨-318421639936,-318421639872⟩ : DyadicInterval 40),(⟨726991098732,726991118061⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨247088731840,247088731904⟩ : DyadicInterval 40),(⟨-319215586368,-319215586304⟩ : DyadicInterval 40),(⟨726838273552,726838292882⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,72626325⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨72623872,72623936⟩ : DyadicInterval 40),(⟨-72628736,-72628672⟩ : DyadicInterval 40),(⟨762123381186,762123400515⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4800,0⟩ : DyadicInterval 40),(⟨762123383616,762123405280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨276529422583,277054390237⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨246669348608,246669348672⟩ : DyadicInterval 40),(⟨-318514012608,-318514012544⟩ : DyadicInterval 40),(⟨726973330057,726973349386⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨247088738688,247088738752⟩ : DyadicInterval 40),(⟨-319215597888,-319215597824⟩ : DyadicInterval 40),(⟨726838271355,726838290685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-72126859136,-71844663872⟩ : DyadicInterval 40),(⟨798045715552,798186832448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨246724605376,247088731904⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-319215586368,-318606408960⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e441_ok : ecellOkT e441 = true := by decide +kernel
theorem e441_pos {a z : ℝ} (ha1 : ((103041/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((258027/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e441 e441_ok ha1 ha2 hz1 hz2 hz

-- box ['258027/1024000', '516903/2048000', '999/1000', '1999/2000']  interval_lower 312771137/274877906944
noncomputable def e442 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1376566009397,0,true,247088731840,247088731904⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨822457246155,0,false,-319215586368,-319215586304⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1377021812802,0,true,247452737792,247452737856⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨822001442750,0,false,-319825101440,-319825101376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1376288955015,0,true,246867416512,246867416576⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨822734300537,0,false,-318845265344,-318845265280⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1376883057710,0,true,247341940288,247341940352⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨822140197842,0,false,-319639517888,-319639517824⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099584250022,0,true,72619840,72619904⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099439005530,0,false,-72624704,-72624640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099657139070,0,true,145501632,145501696⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099366116482,0,false,-145520960,-145520896⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511608518,0,false,-19264,-19200⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622980,0,false,-4800,-4736⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1376427478642,0,true,246978076864,246978076928⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨822595776910,0,false,-319030405504,-319030405440⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1376952444680,0,true,247397347968,247397348032⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨822070810872,0,false,-319732318336,-319732318272⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1029504722037,0,false,-72334970368,-72334970304⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1029769401752,0,false,-72052328576,-72052328512⟩
    { al := (258027/1024000), au := (516903/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨277054381621,277510185026⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨247088731840,247088731904⟩ : DyadicInterval 40),(⟨-319215586368,-319215586304⟩ : DyadicInterval 40),(⟨726838273552,726838292882⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨247452737792,247452737856⟩ : DyadicInterval 40),(⟨-319825101440,-319825101376⟩ : DyadicInterval 40),(⟨726720791710,726720811039⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨246867416512,246867416576⟩ : DyadicInterval 40),(⟨-318845265344,-318845265280⟩ : DyadicInterval 40),(⟨726909584815,726909604145⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨247341940288,247341940352⟩ : DyadicInterval 40),(⟨-319639517888,-319639517824⟩ : DyadicInterval 40),(⟨726756576778,726756596107⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨72622246,145511294⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨72619840,72619904⟩ : DyadicInterval 40),(⟨-72624704,-72624640⟩ : DyadicInterval 40),(⟨762123381187,762123400516⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨145501632,145501696⟩ : DyadicInterval 40),(⟨-145520960,-145520896⟩ : DyadicInterval 40),(⟨762123373958,762123393288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-19264,-4736⟩ : DyadicInterval 40),(⟨762123385984,762123412512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨276915850866,277440816904⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨246978076864,246978076928⟩ : DyadicInterval 40),(⟨-319030405504,-319030405440⟩ : DyadicInterval 40),(⟨726873939441,726873958770⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨247397347968,247397348032⟩ : DyadicInterval 40),(⟨-319732318336,-319732318272⟩ : DyadicInterval 40),(⟨726738684141,726738703470⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-72334970368,-72052328512⟩ : DyadicInterval 40),(⟨798149547872,798290888064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨247088731840,247452737856⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-319825101440,-319215586304⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e442_ok : ecellOkT e442 = true := by decide +kernel
theorem e442_pos {a z : ℝ} (ha1 : ((258027/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((516903/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e442 e442_ok ha1 ha2 hz1 hz2 hz

-- box ['516903/2048000', '64719/256000', '999/1000', '1999/2000']  interval_lower 635475597/549755813888
noncomputable def e443 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1377021812801,0,true,247452737792,247452737856⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨822001442751,0,false,-319825101440,-319825101376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1377477616206,0,true,247816623232,247816623296⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨821545639346,0,false,-320434954560,-320434954496⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1376744302615,0,true,247231131648,247231131712⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨822278952937,0,false,-319453965632,-319453965568⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1377338633213,0,true,247705680512,247705680576⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨821684622339,0,false,-320248963072,-320248963008⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099584381245,0,true,72751040,72751104⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438874307,0,false,-72755904,-72755840⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099657401662,0,true,145764160,145764224⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099365853890,0,false,-145783552,-145783488⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511608449,0,false,-19328,-19264⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622962,0,false,-4864,-4800⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1376883054145,0,true,247341937472,247341937536⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨822140201407,0,false,-319639513088,-319639513024⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1377408134140,0,true,247761160768,247761160832⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨821615121412,0,false,-320341967488,-320341967424⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1029274564066,0,false,-72580806656,-72580806592⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1029539736418,0,false,-72297575616,-72297575552⟩
    { al := (516903/2048000), au := (64719/256000), zl := (999/1000), zu := (1999/2000),
      A := ⟨277510185025,277965988430⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨247452737792,247452737856⟩ : DyadicInterval 40),(⟨-319825101440,-319825101376⟩ : DyadicInterval 40),(⟨726720791710,726720811040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨247816623232,247816623296⟩ : DyadicInterval 40),(⟨-320434954560,-320434954496⟩ : DyadicInterval 40),(⟨726603108076,726603127406⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨247231131648,247231131712⟩ : DyadicInterval 40),(⟨-319453965632,-319453965568⟩ : DyadicInterval 40),(⟨726792343119,726792362448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨247705680512,247705680576⟩ : DyadicInterval 40),(⟨-320248963072,-320248963008⟩ : DyadicInterval 40),(⟨726639013405,726639032735⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨72753469,145773886⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨72751040,72751104⟩ : DyadicInterval 40),(⟨-72755904,-72755840⟩ : DyadicInterval 40),(⟨762123381169,762123400499⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨145764160,145764224⟩ : DyadicInterval 40),(⟨-145783552,-145783488⟩ : DyadicInterval 40),(⟨762123373920,762123393250⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-19328,-4800⟩ : DyadicInterval 40),(⟨762123386016,762123412544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨277371426369,277896506364⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨247341937472,247341937536⟩ : DyadicInterval 40),(⟨-319639513088,-319639513024⟩ : DyadicInterval 40),(⟨726756577666,726756596995⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨247761160768,247761160832⟩ : DyadicInterval 40),(⟨-320341967488,-320341967424⟩ : DyadicInterval 40),(⟨726621060664,726621079994⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-72580806656,-72297575552⟩ : DyadicInterval 40),(⟨798272171392,798413806208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨247452737792,247816623296⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-320434954560,-319825101376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e443_ok : ecellOkT e443 = true := by decide +kernel
theorem e443_pos {a z : ℝ} (ha1 : ((516903/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((64719/256000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e443 e443_ok ha1 ha2 hz1 hz2 hz

-- box ['258027/1024000', '516903/2048000', '1999/2000', '1']  interval_lower 311583459/274877906944
noncomputable def e444 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1376566009397,0,true,247088731840,247088731904⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨822457246155,0,false,-319215586368,-319215586304⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1377021812802,0,true,247452737792,247452737856⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨822001442750,0,false,-319825101440,-319825101376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1376427482206,0,true,246978079744,246978079808⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨822595773346,0,false,-319030410304,-319030410240⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099584385344,0,true,72755136,72755200⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438870208,0,false,-72760000,-72759936⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622961,0,false,-4864,-4800⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1376496739808,0,true,247033402368,247033402432⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨822526515744,0,false,-319122986432,-319122986368⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1377021821419,0,true,247452744640,247452744704⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨822001434133,0,false,-319825112960,-319825112896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1029469705862,0,false,-72372368320,-72372368256⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1029734510055,0,false,-72089584000,-72089583936⟩
    { al := (258027/1024000), au := (516903/2048000), zl := (1999/2000), zu := 1,
      A := ⟨277054381621,277510185026⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨247088731840,247088731904⟩ : DyadicInterval 40),(⟨-319215586368,-319215586304⟩ : DyadicInterval 40),(⟨726838273552,726838292882⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨247452737792,247452737856⟩ : DyadicInterval 40),(⟨-319825101440,-319825101376⟩ : DyadicInterval 40),(⟨726720791710,726720811039⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨246978079744,246978079808⟩ : DyadicInterval 40),(⟨-319030410304,-319030410240⟩ : DyadicInterval 40),(⟨726873938516,726873957846⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨247452737792,247452737856⟩ : DyadicInterval 40),(⟨-319825101440,-319825101376⟩ : DyadicInterval 40),(⟨726720791710,726720811039⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,72757568⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨72755136,72755200⟩ : DyadicInterval 40),(⟨-72760000,-72759936⟩ : DyadicInterval 40),(⟨762123381169,762123400498⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4864,0⟩ : DyadicInterval 40),(⟨762123383616,762123405312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨276985112032,277510193643⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨247033402368,247033402432⟩ : DyadicInterval 40),(⟨-319122986432,-319122986368⟩ : DyadicInterval 40),(⟨726856109927,726856129257⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨247452744640,247452744704⟩ : DyadicInterval 40),(⟨-319825112960,-319825112896⟩ : DyadicInterval 40),(⟨726720789505,726720808835⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-72372368320,-72089583936⟩ : DyadicInterval 40),(⟨798168175584,798309587040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨247088731840,247452737856⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-319825101440,-319215586304⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e444_ok : ecellOkT e444 = true := by decide +kernel
theorem e444_pos {a z : ℝ} (ha1 : ((258027/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((516903/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e444 e444_ok ha1 ha2 hz1 hz2 hz

-- box ['516903/2048000', '64719/256000', '1999/2000', '1']  interval_lower 633085247/549755813888
noncomputable def e445 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1377021812801,0,true,247452737792,247452737856⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨822001442751,0,false,-319825101440,-319825101376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1377477616206,0,true,247816623232,247816623296⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨821545639346,0,false,-320434954560,-320434954496⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1376883057708,0,true,247341940288,247341940352⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨822140197844,0,false,-319639517888,-319639517824⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099584516650,0,true,72886400,72886464⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438738902,0,false,-72891328,-72891264⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622944,0,false,-4864,-4800⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1376952429254,0,true,247397335616,247397335680⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨822070826298,0,false,-319732297728,-319732297664⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1377477624818,0,true,247816630080,247816630144⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨821545630734,0,false,-320434966080,-320434966016⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1029239432776,0,false,-72618335936,-72618335872⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1029504729823,0,false,-72334962048,-72334961984⟩
    { al := (516903/2048000), au := (64719/256000), zl := (1999/2000), zu := 1,
      A := ⟨277510185025,277965988430⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨247452737792,247452737856⟩ : DyadicInterval 40),(⟨-319825101440,-319825101376⟩ : DyadicInterval 40),(⟨726720791710,726720811040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨247816623232,247816623296⟩ : DyadicInterval 40),(⟨-320434954560,-320434954496⟩ : DyadicInterval 40),(⟨726603108076,726603127406⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨247341940288,247341940352⟩ : DyadicInterval 40),(⟨-319639517888,-319639517824⟩ : DyadicInterval 40),(⟨726756576779,726756596108⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨247816623232,247816623296⟩ : DyadicInterval 40),(⟨-320434954560,-320434954496⟩ : DyadicInterval 40),(⟨726603108076,726603127406⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,72888874⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨72886400,72886464⟩ : DyadicInterval 40),(⟨-72891328,-72891264⟩ : DyadicInterval 40),(⟨762123381183,762123400513⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4864,0⟩ : DyadicInterval 40),(⟨762123383616,762123405312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨277440801478,277965997042⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨247397335616,247397335680⟩ : DyadicInterval 40),(⟨-319732297728,-319732297664⟩ : DyadicInterval 40),(⟨726738688149,726738707478⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨247816630080,247816630144⟩ : DyadicInterval 40),(⟨-320434966080,-320434966016⟩ : DyadicInterval 40),(⟨726603105865,726603125195⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-72618335936,-72334961984⟩ : DyadicInterval 40),(⟨798290864608,798432570848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨247452737792,247816623296⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-320434954560,-319825101376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e445_ok : ecellOkT e445 = true := by decide +kernel
theorem e445_pos {a z : ℝ} (ha1 : ((516903/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((64719/256000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e445 e445_ok ha1 ha2 hz1 hz2 hz

-- box ['64719/256000', '518601/2048000', '999/1000', '1999/2000']  interval_lower 161368823/137438953472
noncomputable def e446 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1377477616205,0,true,247816623232,247816623296⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨821545639347,0,false,-320434954560,-320434954496⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1377933419611,0,true,248180388288,248180388352⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨821089835941,0,false,-321045146112,-321045146048⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1377199650216,0,true,247594726592,247594726656⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨821823605336,0,false,-320063003072,-320063003008⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1377794208716,0,true,248069300416,248069300480⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨821229046836,0,false,-320858746304,-320858746240⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099584512531,0,true,72882304,72882368⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438743021,0,false,-72887232,-72887168⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099657664379,0,true,146026880,146026944⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099365591173,0,false,-146046336,-146046272⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511608379,0,false,-19456,-19392⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622945,0,false,-4864,-4800⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1377338629656,0,true,247705677632,247705677696⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨821684625896,0,false,-320248958336,-320248958272⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1377863823596,0,true,248124853248,248124853312⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨821159431956,0,false,-320951954880,-320951954816⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1029044028379,0,false,-72827101568,-72827101504⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1029309693551,0,false,-72543280640,-72543280576⟩
    { al := (64719/256000), au := (518601/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨277965988429,278421791835⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨247816623232,247816623296⟩ : DyadicInterval 40),(⟨-320434954560,-320434954496⟩ : DyadicInterval 40),(⟨726603108076,726603127406⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨248180388288,248180388352⟩ : DyadicInterval 40),(⟨-321045146112,-321045146048⟩ : DyadicInterval 40),(⟨726485222579,726485241908⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨247594726592,247594726656⟩ : DyadicInterval 40),(⟨-320063003072,-320063003008⟩ : DyadicInterval 40),(⟨726674899984,726674919314⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨248069300416,248069300480⟩ : DyadicInterval 40),(⟨-320858746304,-320858746240⟩ : DyadicInterval 40),(⟨726521248431,726521267760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨72884755,146036603⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨72882304,72882368⟩ : DyadicInterval 40),(⟨-72887232,-72887168⟩ : DyadicInterval 40),(⟨762123381184,762123400513⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨146026880,146026944⟩ : DyadicInterval 40),(⟨-146046336,-146046272⟩ : DyadicInterval 40),(⟨762123373883,762123393212⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-19456,-4800⟩ : DyadicInterval 40),(⟨762123386016,762123412608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨277827001880,278352195820⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨247705677632,247705677696⟩ : DyadicInterval 40),(⟨-320248958336,-320248958272⟩ : DyadicInterval 40),(⟨726639014358,726639033688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨248124853248,248124853312⟩ : DyadicInterval 40),(⟨-320951954880,-320951954816⟩ : DyadicInterval 40),(⟨726503235436,726503254766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-72827101568,-72543280576⟩ : DyadicInterval 40),(⟨798395023904,798536953664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨247816623232,248180388352⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-321045146112,-320434954496⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e446_ok : ecellOkT e446 = true := by decide +kernel
theorem e446_pos {a z : ℝ} (ha1 : ((64719/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((518601/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e446 e446_ok ha1 ha2 hz1 hz2 hz

-- box ['518601/2048000', '10389/40960', '999/1000', '1999/2000']  interval_lower 1311084029/1099511627776
noncomputable def e447 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1377933419610,0,true,248180388288,248180388352⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨821089835942,0,false,-321045146112,-321045146048⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1378389223015,0,true,248544033088,248544033152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨820634032537,0,false,-321655676544,-321655676480⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1377654997818,0,true,247958201280,247958201344⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨821368257734,0,false,-320672377984,-320672377920⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1378249784218,0,true,248432800064,248432800128⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨820773471334,0,false,-321468867840,-321468867776⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099584643880,0,true,73013632,73013696⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438611672,0,false,-73018560,-73018496⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099657927223,0,true,146289664,146289728⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099365328329,0,false,-146309184,-146309120⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511608309,0,false,-19520,-19456⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622928,0,false,-4864,-4800⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1377794205167,0,true,248069297536,248069297600⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨821229050385,0,false,-320858741504,-320858741440⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1378319513053,0,true,248488425536,248488425600⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨820703742499,0,false,-321562280832,-321562280768⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1028813114973,0,false,-73073855296,-73073855232⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1029079273154,0,false,-72789443904,-72789443840⟩
    { al := (518601/2048000), au := (10389/40960), zl := (999/1000), zu := (1999/2000),
      A := ⟨278421791834,278877595239⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨248180388288,248180388352⟩ : DyadicInterval 40),(⟨-321045146112,-321045146048⟩ : DyadicInterval 40),(⟨726485222579,726485241909⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨248544033088,248544033152⟩ : DyadicInterval 40),(⟨-321655676544,-321655676480⟩ : DyadicInterval 40),(⟨726367135170,726367154499⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨247958201280,247958201344⟩ : DyadicInterval 40),(⟨-320672377984,-320672377920⟩ : DyadicInterval 40),(⟨726557255436,726557274766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨248432800064,248432800128⟩ : DyadicInterval 40),(⟨-321468867840,-321468867776⟩ : DyadicInterval 40),(⟨726403281774,726403301104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨73016104,146299447⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73013632,73013696⟩ : DyadicInterval 40),(⟨-73018560,-73018496⟩ : DyadicInterval 40),(⟨762123381167,762123400496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨146289664,146289728⟩ : DyadicInterval 40),(⟨-146309184,-146309120⟩ : DyadicInterval 40),(⟨762123373845,762123393174⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-19520,-4800⟩ : DyadicInterval 40),(⟨762123386016,762123412640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨278282577391,278807885277⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨248069297536,248069297600⟩ : DyadicInterval 40),(⟨-320858741504,-320858741440⟩ : DyadicInterval 40),(⟨726521249361,726521268690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨248488425536,248488425600⟩ : DyadicInterval 40),(⟨-321562280832,-321562280768⟩ : DyadicInterval 40),(⟨726385208359,726385227689⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-73073855296,-72789443840⟩ : DyadicInterval 40),(⟨798518105536,798660330528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨248180388288,248544033152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-321655676544,-321045146048⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e447_ok : ecellOkT e447 = true := by decide +kernel
theorem e447_pos {a z : ℝ} (ha1 : ((518601/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((10389/40960 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e447 e447_ok ha1 ha2 hz1 hz2 hz

-- box ['64719/256000', '518601/2048000', '1999/2000', '1']  interval_lower 1286140165/1099511627776
noncomputable def e448 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1377477616205,0,true,247816623232,247816623296⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨821545639347,0,false,-320434954560,-320434954496⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1377933419611,0,true,248180388288,248180388352⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨821089835941,0,false,-321045146112,-321045146048⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1377338633210,0,true,247705680512,247705680576⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨821684622342,0,false,-320248963072,-320248963008⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099584648017,0,true,73017792,73017856⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438607535,0,false,-73022720,-73022656⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622926,0,false,-4864,-4800⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1377408118704,0,true,247761148480,247761148544⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨821615136848,0,false,-320341946816,-320341946752⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1377933428222,0,true,248180395200,248180395264⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨821089827330,0,false,-321045157632,-321045157568⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1029008781780,0,false,-72864762432,-72864762368⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1029274571870,0,false,-72580798336,-72580798272⟩
    { al := (64719/256000), au := (518601/2048000), zl := (1999/2000), zu := 1,
      A := ⟨277965988429,278421791835⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨247816623232,247816623296⟩ : DyadicInterval 40),(⟨-320434954560,-320434954496⟩ : DyadicInterval 40),(⟨726603108076,726603127406⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨248180388288,248180388352⟩ : DyadicInterval 40),(⟨-321045146112,-321045146048⟩ : DyadicInterval 40),(⟨726485222579,726485241908⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨247705680512,247705680576⟩ : DyadicInterval 40),(⟨-320248963072,-320248963008⟩ : DyadicInterval 40),(⟨726639013406,726639032736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨248180388288,248180388352⟩ : DyadicInterval 40),(⟨-321045146112,-321045146048⟩ : DyadicInterval 40),(⟨726485222579,726485241908⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,73020241⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73017792,73017856⟩ : DyadicInterval 40),(⟨-73022720,-73022656⟩ : DyadicInterval 40),(⟨762123381166,762123400495⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4864,0⟩ : DyadicInterval 40),(⟨762123383616,762123405312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨277896490928,278421800446⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨247761148480,247761148544⟩ : DyadicInterval 40),(⟨-320341946816,-320341946752⟩ : DyadicInterval 40),(⟨726621064625,726621083955⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨248180395200,248180395264⟩ : DyadicInterval 40),(⟨-321045157632,-321045157568⟩ : DyadicInterval 40),(⟨726485220320,726485239650⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-72864762432,-72580798272⟩ : DyadicInterval 40),(⟨798413782752,798555784096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨247816623232,248180388352⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-321045146112,-320434954496⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e448_ok : ecellOkT e448 = true := by decide +kernel
theorem e448_pos {a z : ℝ} (ha1 : ((64719/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((518601/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e448 e448_ok ha1 ha2 hz1 hz2 hz

-- box ['518601/2048000', '10389/40960', '1999/2000', '1']  interval_lower 1306242977/1099511627776
noncomputable def e449 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1377933419610,0,true,248180388288,248180388352⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨821089835942,0,false,-321045146112,-321045146048⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1378389223015,0,true,248544033088,248544033152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨820634032537,0,false,-321655676544,-321655676480⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1377794208714,0,true,248069300416,248069300480⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨821229046838,0,false,-320858746240,-320858746176⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099584779448,0,true,73149184,73149248⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438476104,0,false,-73154112,-73154048⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622909,0,false,-4928,-4864⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1377863808154,0,true,248124840960,248124841024⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨821159447398,0,false,-320951934208,-320951934144⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1378389231629,0,true,248544039936,248544040000⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨820634023923,0,false,-321655688064,-321655688000⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1028777752875,0,false,-73111648064,-73111648000⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1029044036199,0,false,-72827093184,-72827093120⟩
    { al := (518601/2048000), au := (10389/40960), zl := (1999/2000), zu := 1,
      A := ⟨278421791834,278877595239⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨248180388288,248180388352⟩ : DyadicInterval 40),(⟨-321045146112,-321045146048⟩ : DyadicInterval 40),(⟨726485222579,726485241909⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨248544033088,248544033152⟩ : DyadicInterval 40),(⟨-321655676544,-321655676480⟩ : DyadicInterval 40),(⟨726367135170,726367154499⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨248069300416,248069300480⟩ : DyadicInterval 40),(⟨-320858746240,-320858746176⟩ : DyadicInterval 40),(⟨726521248407,726521267737⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨248544033088,248544033152⟩ : DyadicInterval 40),(⟨-321655676544,-321655676480⟩ : DyadicInterval 40),(⟨726367135170,726367154499⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,73151672⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73149184,73149248⟩ : DyadicInterval 40),(⟨-73154112,-73154048⟩ : DyadicInterval 40),(⟨762123381148,762123400478⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4928,0⟩ : DyadicInterval 40),(⟨762123383616,762123405344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨278352180378,278877603853⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨248124840960,248124841024⟩ : DyadicInterval 40),(⟨-320951934208,-320951934144⟩ : DyadicInterval 40),(⟨726503239412,726503258742⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨248544039936,248544040000⟩ : DyadicInterval 40),(⟨-321655688064,-321655688000⟩ : DyadicInterval 40),(⟨726367132943,726367152272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-73111648064,-72827093120⟩ : DyadicInterval 40),(⟨798536930176,798679226912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨248180388288,248544033152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-321655676544,-321045146048⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e449_ok : ecellOkT e449 = true := by decide +kernel
theorem e449_pos {a z : ℝ} (ha1 : ((518601/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((10389/40960 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e449 e449_ok ha1 ha2 hz1 hz2 hz

-- box ['10389/40960', '520299/2048000', '999/1000', '1999/2000']  interval_lower 665675985/549755813888
noncomputable def e450 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1378389223014,0,true,248544033088,248544033152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨820634032538,0,false,-321655676544,-321655676480⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1378845026419,0,true,248907557568,248907557632⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨820178229133,0,false,-322266546112,-322266546048⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1378110345418,0,true,248321555840,248321555904⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨820912910134,0,false,-321282090880,-321282090816⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1378705359720,0,true,248796179648,248796179712⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨820317895832,0,false,-322079328128,-322079328064⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099584775293,0,true,73145024,73145088⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438480259,0,false,-73149952,-73149888⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099658190192,0,true,146552640,146552704⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099365065360,0,false,-146572224,-146572160⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511608239,0,false,-19584,-19520⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622910,0,false,-4928,-4864⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1378249780674,0,true,248432797248,248432797312⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨820773474878,0,false,-321468863104,-321468863040⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1378775202511,0,true,248851877568,248851877632⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨820248053041,0,false,-322172945792,-322172945728⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1028581823848,0,false,-73321068224,-73321068160⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1028848475229,0,false,-73036065792,-73036065728⟩
    { al := (10389/40960), au := (520299/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨278877595238,279333398643⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨248544033088,248544033152⟩ : DyadicInterval 40),(⟨-321655676544,-321655676480⟩ : DyadicInterval 40),(⟨726367135170,726367154499⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨248907557568,248907557632⟩ : DyadicInterval 40),(⟨-322266546112,-322266546048⟩ : DyadicInterval 40),(⟨726248845848,726248865178⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨248321555840,248321555904⟩ : DyadicInterval 40),(⟨-321282090880,-321282090816⟩ : DyadicInterval 40),(⟨726439409452,726439428781⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨248796179648,248796179712⟩ : DyadicInterval 40),(⟨-322079328128,-322079328064⟩ : DyadicInterval 40),(⟨726285113347,726285132676⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨73147517,146562416⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73145024,73145088⟩ : DyadicInterval 40),(⟨-73149952,-73149888⟩ : DyadicInterval 40),(⟨762123381149,762123400478⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨146552640,146552704⟩ : DyadicInterval 40),(⟨-146572224,-146572160⟩ : DyadicInterval 40),(⟨762123373807,762123393136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-19584,-4864⟩ : DyadicInterval 40),(⟨762123386048,762123412672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨278738152898,279263574735⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨248432797248,248432797312⟩ : DyadicInterval 40),(⟨-321468863104,-321468863040⟩ : DyadicInterval 40),(⟨726403282690,726403302020⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨248851877568,248851877632⟩ : DyadicInterval 40),(⟨-322172945792,-322172945728⟩ : DyadicInterval 40),(⟨726266979504,726266998833⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-73321068224,-73036065728⟩ : DyadicInterval 40),(⟨798641416480,798783936992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨248544033088,248907557632⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-322266546112,-321655676480⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e450_ok : ecellOkT e450 = true := by decide +kernel
theorem e450_pos {a z : ℝ} (ha1 : ((10389/40960 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((520299/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e450 e450_ok ha1 ha2 hz1 hz2 hz

-- box ['520299/2048000', '130287/512000', '999/1000', '1999/2000']  interval_lower 675877477/549755813888
noncomputable def e451 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1378845026418,0,true,248907557568,248907557632⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨820178229134,0,false,-322266546112,-322266546048⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1379300829823,0,true,249270961984,249270962048⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨819722425729,0,false,-322877755264,-322877755200⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1378565693019,0,true,248684790400,248684790464⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨820457562533,0,false,-321892142080,-321892142016⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1379160935223,0,true,249159439168,249159439232⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨819862320329,0,false,-322690127616,-322690127552⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099584906767,0,true,73276544,73276608⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438348785,0,false,-73281472,-73281408⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099658453288,0,true,146815680,146815744⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099364802264,0,false,-146835328,-146835264⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511608169,0,false,-19648,-19584⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622893,0,false,-4928,-4864⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1378705356179,0,true,248796176832,248796176896⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨820317899373,0,false,-322079323392,-322079323328⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1379230891972,0,true,249215209536,249215209600⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨819792363580,0,false,-322783950080,-322783950016⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1028350155004,0,false,-73568740544,-73568740480⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1028617299776,0,false,-73283146560,-73283146496⟩
    { al := (520299/2048000), au := (130287/512000), zl := (999/1000), zu := (1999/2000),
      A := ⟨279333398642,279789202047⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨248907557568,248907557632⟩ : DyadicInterval 40),(⟨-322266546112,-322266546048⟩ : DyadicInterval 40),(⟨726248845848,726248865178⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨249270961984,249270962048⟩ : DyadicInterval 40),(⟨-322877755264,-322877755200⟩ : DyadicInterval 40),(⟨726130354484,726130373813⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨248684790400,248684790464⟩ : DyadicInterval 40),(⟨-321892142080,-321892142016⟩ : DyadicInterval 40),(⟨726321361934,726321381264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨249159439168,249159439232⟩ : DyadicInterval 40),(⟨-322690127616,-322690127552⟩ : DyadicInterval 40),(⟨726166743180,726166762509⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨73278991,146825512⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73276544,73276608⟩ : DyadicInterval 40),(⟨-73281472,-73281408⟩ : DyadicInterval 40),(⟨762123381132,762123400461⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨146815680,146815744⟩ : DyadicInterval 40),(⟨-146835328,-146835264⟩ : DyadicInterval 40),(⟨762123373769,762123393098⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-19648,-4864⟩ : DyadicInterval 40),(⟨762123386048,762123412704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨279193728403,279719264196⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨248796176832,248796176896⟩ : DyadicInterval 40),(⟨-322079323392,-322079323328⟩ : DyadicInterval 40),(⟨726285114265,726285133595⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨249215209536,249215209600⟩ : DyadicInterval 40),(⟨-322783950080,-322783950016⟩ : DyadicInterval 40),(⟨726148548733,726148568063⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-73568740544,-73283146496⟩ : DyadicInterval 40),(⟨798764956864,798907773152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨248907557568,249270962048⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-322877755264,-322266546048⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e451_ok : ecellOkT e451 = true := by decide +kernel
theorem e451_pos {a z : ℝ} (ha1 : ((520299/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((130287/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e451 e451_ok ha1 ha2 hz1 hz2 hz

-- box ['10389/40960', '520299/2048000', '1999/2000', '1']  interval_lower 1326480379/1099511627776
noncomputable def e452 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1378389223014,0,true,248544033088,248544033152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨820634032538,0,false,-321655676544,-321655676480⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1378845026419,0,true,248907557568,248907557632⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨820178229133,0,false,-322266546112,-322266546048⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1378249784216,0,true,248432800064,248432800128⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨820773471336,0,false,-321468867840,-321468867776⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099584910943,0,true,73280704,73280768⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438344609,0,false,-73285632,-73285568⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622891,0,false,-4928,-4864⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1378319497597,0,true,248488413184,248488413248⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨820703757955,0,false,-321562260160,-321562260096⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1378845035025,0,true,248907564480,248907564544⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨820178220527,0,false,-322266557632,-322266557568⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1028546346068,0,false,-73358993152,-73358993088⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1028813122813,0,false,-73073846912,-73073846848⟩
    { al := (10389/40960), au := (520299/2048000), zl := (1999/2000), zu := 1,
      A := ⟨278877595238,279333398643⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨248544033088,248544033152⟩ : DyadicInterval 40),(⟨-321655676544,-321655676480⟩ : DyadicInterval 40),(⟨726367135170,726367154499⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨248907557568,248907557632⟩ : DyadicInterval 40),(⟨-322266546112,-322266546048⟩ : DyadicInterval 40),(⟨726248845848,726248865178⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨248432800064,248432800128⟩ : DyadicInterval 40),(⟨-321468867840,-321468867776⟩ : DyadicInterval 40),(⟨726403281775,726403301104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨248907557568,248907557632⟩ : DyadicInterval 40),(⟨-322266546112,-322266546048⟩ : DyadicInterval 40),(⟨726248845848,726248865178⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,73283167⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73280704,73280768⟩ : DyadicInterval 40),(⟨-73285632,-73285568⟩ : DyadicInterval 40),(⟨762123381131,762123400460⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4928,0⟩ : DyadicInterval 40),(⟨762123383616,762123405344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨278807869821,279333407249⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨248488413184,248488413248⟩ : DyadicInterval 40),(⟨-321562260160,-321562260096⟩ : DyadicInterval 40),(⟨726385212393,726385231722⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨248907564480,248907564544⟩ : DyadicInterval 40),(⟨-322266557632,-322266557568⟩ : DyadicInterval 40),(⟨726248843575,726248862905⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-73358993152,-73073846848⟩ : DyadicInterval 40),(⟨798660307040,798802899456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨248544033088,248907557632⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-322266546112,-321655676480⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e452_ok : ecellOkT e452 = true := by decide +kernel
theorem e452_pos {a z : ℝ} (ha1 : ((10389/40960 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((520299/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e452 e452_ok ha1 ha2 hz1 hz2 hz

-- box ['520299/2048000', '130287/512000', '1999/2000', '1']  interval_lower 1346852751/1099511627776
noncomputable def e453 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1378845026418,0,true,248907557568,248907557632⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨820178229134,0,false,-322266546112,-322266546048⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1379300829823,0,true,249270961984,249270962048⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨819722425729,0,false,-322877755264,-322877755200⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1378705359718,0,true,248796179648,248796179712⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨820317895834,0,false,-322079328128,-322079328064⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585042501,0,true,73412224,73412288⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438213051,0,false,-73417216,-73417152⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622874,0,false,-4928,-4864⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1378775187045,0,true,248851865216,248851865280⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨820248068507,0,false,-322172925056,-322172924992⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1379300838439,0,true,249270968832,249270968896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨819722417113,0,false,-322877766848,-322877766784⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1028314561345,0,false,-73606797952,-73606797888⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1028581831706,0,false,-73321059840,-73321059776⟩
    { al := (520299/2048000), au := (130287/512000), zl := (1999/2000), zu := 1,
      A := ⟨279333398642,279789202047⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨248907557568,248907557632⟩ : DyadicInterval 40),(⟨-322266546112,-322266546048⟩ : DyadicInterval 40),(⟨726248845848,726248865178⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨249270961984,249270962048⟩ : DyadicInterval 40),(⟨-322877755264,-322877755200⟩ : DyadicInterval 40),(⟨726130354484,726130373813⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨248796179648,248796179712⟩ : DyadicInterval 40),(⟨-322079328128,-322079328064⟩ : DyadicInterval 40),(⟨726285113348,726285132677⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨249270961984,249270962048⟩ : DyadicInterval 40),(⟨-322877755264,-322877755200⟩ : DyadicInterval 40),(⟨726130354484,726130373813⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,73414725⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73412224,73412288⟩ : DyadicInterval 40),(⟨-73417216,-73417152⟩ : DyadicInterval 40),(⟨762123381145,762123400475⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4928,0⟩ : DyadicInterval 40),(⟨762123383616,762123405344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨279263559269,279789210663⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨248851865216,248851865280⟩ : DyadicInterval 40),(⟨-322172925056,-322172924992⟩ : DyadicInterval 40),(⟨726266983530,726267002859⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨249270968832,249270968896⟩ : DyadicInterval 40),(⟨-322877766848,-322877766784⟩ : DyadicInterval 40),(⟨726130352265,726130371595⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-73606797952,-73321059776⟩ : DyadicInterval 40),(⟨798783913504,798926801856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨248907557568,249270962048⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-322877755264,-322266546048⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e453_ok : ecellOkT e453 = true := by decide +kernel
theorem e453_pos {a z : ℝ} (ha1 : ((520299/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((130287/512000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e453 e453_ok ha1 ha2 hz1 hz2 hz

-- box ['130287/512000', '521997/2048000', '999/1000', '1999/2000']  interval_lower 1372293533/1099511627776
noncomputable def e454 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1379300829822,0,true,249270961984,249270962048⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨819722425730,0,false,-322877755264,-322877755200⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1379756633228,0,true,249634246272,249634246336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨819266622324,0,false,-323489304384,-323489304320⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1379021040619,0,true,249047905024,249047905088⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨820002214933,0,false,-322502531904,-322502531840⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1379616510726,0,true,249522578688,249522578752⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨819406744826,0,false,-323301266496,-323301266432⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585038306,0,true,73408064,73408128⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438217246,0,false,-73412992,-73412928⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099658716510,0,true,147078848,147078912⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099364539042,0,false,-147098624,-147098560⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511608098,0,false,-19712,-19648⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622875,0,false,-4928,-4864⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1379160931697,0,true,249159436352,249159436416⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨819862323855,0,false,-322690122880,-322690122816⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1379686581430,0,true,249578421440,249578421504⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨819336674122,0,false,-323395294144,-323395294080⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1028118108442,0,false,-73816872640,-73816872576⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1028385746787,0,false,-73530686464,-73530686400⟩
    { al := (130287/512000), au := (521997/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨279789202046,280245005452⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨249270961984,249270962048⟩ : DyadicInterval 40),(⟨-322877755264,-322877755200⟩ : DyadicInterval 40),(⟨726130354484,726130373814⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨249634246272,249634246336⟩ : DyadicInterval 40),(⟨-323489304384,-323489304320⟩ : DyadicInterval 40),(⟨726011661125,726011680454⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨249047905024,249047905088⟩ : DyadicInterval 40),(⟨-322502531904,-322502531840⟩ : DyadicInterval 40),(⟨726203112827,726203132157⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨249522578688,249522578752⟩ : DyadicInterval 40),(⟨-323301266496,-323301266432⟩ : DyadicInterval 40),(⟨726048171168,726048190498⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨73410530,147088734⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73408064,73408128⟩ : DyadicInterval 40),(⟨-73412992,-73412928⟩ : DyadicInterval 40),(⟨762123381114,762123400443⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨147078848,147078912⟩ : DyadicInterval 40),(⟨-147098624,-147098560⟩ : DyadicInterval 40),(⟨762123373762,762123393092⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-19712,-4864⟩ : DyadicInterval 40),(⟨762123386048,762123412736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨279649303921,280174953654⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨249159436352,249159436416⟩ : DyadicInterval 40),(⟨-322690122880,-322690122816⟩ : DyadicInterval 40),(⟨726166744097,726166763427⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨249578421440,249578421504⟩ : DyadicInterval 40),(⟨-323395294144,-323395294080⟩ : DyadicInterval 40),(⟨726029916079,726029935409⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-73816872640,-73530686400⟩ : DyadicInterval 40),(⟨798888726816,799031839200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨249270961984,249634246336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-323489304384,-322877755200⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e454_ok : ecellOkT e454 = true := by decide +kernel
theorem e454_pos {a z : ℝ} (ha1 : ((130287/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((521997/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e454 e454_ok ha1 ha2 hz1 hz2 hz

-- box ['521997/2048000', '261423/1024000', '999/1000', '1999/2000']  interval_lower 696484011/549755813888
noncomputable def e455 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1379756633227,0,true,249634246272,249634246336⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨819266622325,0,false,-323489304384,-323489304320⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1380212436632,0,true,249997410624,249997410688⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨818810818920,0,false,-324101193856,-324101193792⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1379476388221,0,true,249410899712,249410899776⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨819546867331,0,false,-323113260800,-323113260736⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1380072086228,0,true,249885598272,249885598336⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨818951169324,0,false,-323912745344,-323912745280⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585169908,0,true,73539648,73539712⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438085644,0,false,-73544640,-73544576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099658979860,0,true,147342208,147342272⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099364275692,0,false,-147361984,-147361920⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511608028,0,false,-19776,-19712⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622858,0,false,-4928,-4864⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1379616507203,0,true,249522575872,249522575936⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨819406748349,0,false,-323301261824,-323301261760⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1380142270883,0,true,249941513408,249941513472⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨818880984669,0,false,-324006978240,-324006978176⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1027885684165,0,false,-74065464832,-74065464768⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1028153816275,0,false,-73778685888,-73778685824⟩
    { al := (521997/2048000), au := (261423/1024000), zl := (999/1000), zu := (1999/2000),
      A := ⟨280245005451,280700808856⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨249634246272,249634246336⟩ : DyadicInterval 40),(⟨-323489304384,-323489304320⟩ : DyadicInterval 40),(⟨726011661125,726011680455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨249997410624,249997410688⟩ : DyadicInterval 40),(⟨-324101193856,-324101193792⟩ : DyadicInterval 40),(⟨725892765656,725892784985⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨249410899712,249410899776⟩ : DyadicInterval 40),(⟨-323113260800,-323113260736⟩ : DyadicInterval 40),(⟨726084662162,726084681491⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨249885598272,249885598336⟩ : DyadicInterval 40),(⟨-323912745344,-323912745280⟩ : DyadicInterval 40),(⟨725929397350,725929416680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨73542132,147352084⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73539648,73539712⟩ : DyadicInterval 40),(⟨-73544640,-73544576⟩ : DyadicInterval 40),(⟨762123381128,762123400458⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨147342208,147342272⟩ : DyadicInterval 40),(⟨-147361984,-147361920⟩ : DyadicInterval 40),(⟨762123373692,762123393021⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-19776,-4864⟩ : DyadicInterval 40),(⟨762123386048,762123412768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨280104879427,280630643107⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨249522575872,249522575936⟩ : DyadicInterval 40),(⟨-323301261824,-323301261760⟩ : DyadicInterval 40),(⟨726048172112,726048191441⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨249941513408,249941513472⟩ : DyadicInterval 40),(⟨-324006978240,-324006978176⟩ : DyadicInterval 40),(⟨725911081421,725911100750⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-74065464832,-73778685824⟩ : DyadicInterval 40),(⟨799012726528,799156135296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨249634246272,249997410688⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-324101193856,-323489304320⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e455_ok : ecellOkT e455 = true := by decide +kernel
theorem e455_pos {a z : ℝ} (ha1 : ((521997/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((261423/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e455 e455_ok ha1 ha2 hz1 hz2 hz

-- box ['130287/512000', '521997/2048000', '1999/2000', '1']  interval_lower 341840113/274877906944
noncomputable def e456 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1379300829822,0,true,249270961984,249270962048⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨819722425730,0,false,-322877755264,-322877755200⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1379756633228,0,true,249634246272,249634246336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨819266622324,0,false,-323489304384,-323489304320⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1379160935220,0,true,249159439168,249159439232⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨819862320332,0,false,-322690127616,-322690127552⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585174122,0,true,73543872,73543936⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438081430,0,false,-73548864,-73548800⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622856,0,false,-4928,-4864⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1379230876496,0,true,249215197184,249215197248⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨819792379056,0,false,-322783929344,-322783929280⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1379756641839,0,true,249634253184,249634253248⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨819266613713,0,false,-323489315968,-323489315904⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1028082398722,0,false,-73855062784,-73855062720⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1028350162879,0,false,-73568732160,-73568732096⟩
    { al := (130287/512000), au := (521997/2048000), zl := (1999/2000), zu := 1,
      A := ⟨279789202046,280245005452⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨249270961984,249270962048⟩ : DyadicInterval 40),(⟨-322877755264,-322877755200⟩ : DyadicInterval 40),(⟨726130354484,726130373814⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨249634246272,249634246336⟩ : DyadicInterval 40),(⟨-323489304384,-323489304320⟩ : DyadicInterval 40),(⟨726011661125,726011680454⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨249159439168,249159439232⟩ : DyadicInterval 40),(⟨-322690127616,-322690127552⟩ : DyadicInterval 40),(⟨726166743181,726166762510⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨249634246272,249634246336⟩ : DyadicInterval 40),(⟨-323489304384,-323489304320⟩ : DyadicInterval 40),(⟨726011661125,726011680454⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,73546346⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73543872,73543936⟩ : DyadicInterval 40),(⟨-73548864,-73548800⟩ : DyadicInterval 40),(⟨762123381128,762123400457⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4928,0⟩ : DyadicInterval 40),(⟨762123383616,762123405344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨279719248720,280245014063⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨249215197184,249215197248⟩ : DyadicInterval 40),(⟨-322783929344,-322783929280⟩ : DyadicInterval 40),(⟨726148552775,726148572105⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨249634253184,249634253248⟩ : DyadicInterval 40),(⟨-323489315968,-323489315904⟩ : DyadicInterval 40),(⟨726011658859,726011678189⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-73855062784,-73568732096⟩ : DyadicInterval 40),(⟨798907749664,799050934272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨249270961984,249634246336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-323489304384,-322877755200⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e456_ok : ecellOkT e456 = true := by decide +kernel
theorem e456_pos {a z : ℝ} (ha1 : ((130287/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((521997/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e456 e456_ok ha1 ha2 hz1 hz2 hz

-- box ['521997/2048000', '261423/1024000', '1999/2000', '1']  interval_lower 1388003763/1099511627776
noncomputable def e457 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1379756633227,0,true,249634246272,249634246336⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨819266622325,0,false,-323489304384,-323489304320⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1380212436632,0,true,249997410624,249997410688⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨818810818920,0,false,-324101193856,-324101193792⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1379616510724,0,true,249522578688,249522578752⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨819406744828,0,false,-323301266496,-323301266432⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585305807,0,true,73675520,73675584⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437949745,0,false,-73680512,-73680448⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622838,0,false,-4992,-4928⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1379686565945,0,true,249578409088,249578409152⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨819336689607,0,false,-323395273344,-323395273280⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1380212445248,0,true,249997417472,249997417536⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨818810810304,0,false,-324101205440,-324101205376⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1027849858187,0,false,-74103787904,-74103787840⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1028118116335,0,false,-73816864192,-73816864128⟩
    { al := (521997/2048000), au := (261423/1024000), zl := (1999/2000), zu := 1,
      A := ⟨280245005451,280700808856⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨249634246272,249634246336⟩ : DyadicInterval 40),(⟨-323489304384,-323489304320⟩ : DyadicInterval 40),(⟨726011661125,726011680455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨249997410624,249997410688⟩ : DyadicInterval 40),(⟨-324101193856,-324101193792⟩ : DyadicInterval 40),(⟨725892765656,725892784985⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨249522578688,249522578752⟩ : DyadicInterval 40),(⟨-323301266496,-323301266432⟩ : DyadicInterval 40),(⟨726048171169,726048190498⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨249997410624,249997410688⟩ : DyadicInterval 40),(⟨-324101193856,-324101193792⟩ : DyadicInterval 40),(⟨725892765656,725892784985⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,73678031⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73675520,73675584⟩ : DyadicInterval 40),(⟨-73680512,-73680448⟩ : DyadicInterval 40),(⟨762123381110,762123400440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4992,0⟩ : DyadicInterval 40),(⟨762123383616,762123405376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨280174938169,280700817472⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨249578409088,249578409152⟩ : DyadicInterval 40),(⟨-323395273344,-323395273280⟩ : DyadicInterval 40),(⟨726029920114,726029939444⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨249997417472,249997417536⟩ : DyadicInterval 40),(⟨-324101205440,-324101205376⟩ : DyadicInterval 40),(⟨725892763422,725892782751⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-74103787904,-73816864128⟩ : DyadicInterval 40),(⟨799031815680,799175296832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨249634246272,249997410688⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-324101193856,-323489304320⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e457_ok : ecellOkT e457 = true := by decide +kernel
theorem e457_pos {a z : ℝ} (ha1 : ((521997/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((261423/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e457 e457_ok ha1 ha2 hz1 hz2 hz

-- box ['261423/1024000', '104739/409600', '999/1000', '1999/2000']  interval_lower 1413779679/1099511627776
noncomputable def e458 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1380212436631,0,true,249997410624,249997410688⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨818810818921,0,false,-324101193856,-324101193792⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1380668240036,0,true,250360455040,250360455104⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨818355015516,0,false,-324713424000,-324713423936⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1379931735822,0,true,249773774592,249773774656⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨819091519730,0,false,-323724329088,-323724329024⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1380527661731,0,true,250248498112,250248498176⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨818495593821,0,false,-324524564416,-324524564352⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585301573,0,true,73671296,73671360⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437953979,0,false,-73676288,-73676224⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099659243337,0,true,147605632,147605696⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099364012215,0,false,-147625472,-147625408⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511607957,0,false,-19840,-19776⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622840,0,false,-4992,-4928⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1380072082713,0,true,249885595520,249885595584⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨818951172839,0,false,-323912740608,-323912740544⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1380597960346,0,true,250304485504,250304485568⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨818425295206,0,false,-324619002880,-324619002816⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1027652882164,0,false,-74314517312,-74314517248⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1027921508231,0,false,-74027145088,-74027145024⟩
    { al := (261423/1024000), au := (104739/409600), zl := (999/1000), zu := (1999/2000),
      A := ⟨280700808855,281156612260⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨249997410624,249997410688⟩ : DyadicInterval 40),(⟨-324101193856,-324101193792⟩ : DyadicInterval 40),(⟨725892765656,725892784986⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨250360455040,250360455104⟩ : DyadicInterval 40),(⟨-324713424000,-324713423936⟩ : DyadicInterval 40),(⟨725773668059,725773687389⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨249773774592,249773774656⟩ : DyadicInterval 40),(⟨-323724329088,-323724329024⟩ : DyadicInterval 40),(⟨725966009841,725966029170⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨250248498112,250248498176⟩ : DyadicInterval 40),(⟨-324524564416,-324524564352⟩ : DyadicInterval 40),(⟨725810421563,725810440893⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨73673797,147615561⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73671296,73671360⟩ : DyadicInterval 40),(⟨-73676288,-73676224⟩ : DyadicInterval 40),(⟨762123381111,762123400440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨147605632,147605696⟩ : DyadicInterval 40),(⟨-147625472,-147625408⟩ : DyadicInterval 40),(⟨762123373653,762123392983⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-19840,-4928⟩ : DyadicInterval 40),(⟨762123386080,762123412800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨280560454937,281086332570⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨249885595520,249885595584⟩ : DyadicInterval 40),(⟨-323912740608,-323912740544⟩ : DyadicInterval 40),(⟨725929398231,725929417560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨250304485504,250304485568⟩ : DyadicInterval 40),(⟨-324619002880,-324619002816⟩ : DyadicInterval 40),(⟨725792044767,725792064097⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-74314517312,-74027145024⟩ : DyadicInterval 40),(⟨799136956128,799280661536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨249997410624,250360455104⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-324713424000,-324101193792⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e458_ok : ecellOkT e458 = true := by decide +kernel
theorem e458_pos {a z : ℝ} (ha1 : ((261423/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((104739/409600 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e458 e458_ok ha1 ha2 hz1 hz2 hz

-- box ['104739/409600', '2049/8000', '999/1000', '1999/2000']  interval_lower 717364281/549755813888
noncomputable def e459 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1380668240035,0,true,250360455040,250360455104⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨818355015517,0,false,-324713424000,-324713423936⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1381124043441,0,true,250723379584,250723379648⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨817899212111,0,false,-325325995264,-325325995200⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1380387083422,0,true,250136529792,250136529856⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨818636172130,0,false,-324335737216,-324335737152⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1380983237234,0,true,250611278208,250611278272⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨818040018318,0,false,-325136724096,-325136724032⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585433301,0,true,73803008,73803072⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437822251,0,false,-73808064,-73808000⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099659506941,0,true,147869184,147869248⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099363748611,0,false,-147889152,-147889088⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511607886,0,false,-19904,-19840⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622822,0,false,-4992,-4928⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1380527658224,0,true,250248495296,250248495360⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨818495597328,0,false,-324524559680,-324524559616⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1381053649805,0,true,250667337856,250667337920⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨817969605747,0,false,-325231368320,-325231368256⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1027419702446,0,false,-74564030464,-74564030400⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1027688822657,0,false,-74276064320,-74276064256⟩
    { al := (104739/409600), au := (2049/8000), zl := (999/1000), zu := (1999/2000),
      A := ⟨281156612259,281612415665⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨250360455040,250360455104⟩ : DyadicInterval 40),(⟨-324713424000,-324713423936⟩ : DyadicInterval 40),(⟨725773668060,725773687389⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨250723379584,250723379648⟩ : DyadicInterval 40),(⟨-325325995264,-325325995200⟩ : DyadicInterval 40),(⟨725654368325,725654387654⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨250136529792,250136529856⟩ : DyadicInterval 40),(⟨-324335737216,-324335737152⟩ : DyadicInterval 40),(⟨725847155814,725847175144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨250611278208,250611278272⟩ : DyadicInterval 40),(⟨-325136724096,-325136724032⟩ : DyadicInterval 40),(⟨725691243814,725691263144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨73805525,147879165⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73803008,73803072⟩ : DyadicInterval 40),(⟨-73808064,-73808000⟩ : DyadicInterval 40),(⟨762123381125,762123400454⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨147869184,147869248⟩ : DyadicInterval 40),(⟨-147889152,-147889088⟩ : DyadicInterval 40),(⟨762123373646,762123392976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-19904,-4928⟩ : DyadicInterval 40),(⟨762123386080,762123412832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨281016030448,281542022029⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨250248495296,250248495360⟩ : DyadicInterval 40),(⟨-324524559680,-324524559616⟩ : DyadicInterval 40),(⟨725810422485,725810441815⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨250667337856,250667337920⟩ : DyadicInterval 40),(⟨-325231368320,-325231368256⟩ : DyadicInterval 40),(⟨725672806001,725672825330⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-74564030464,-74276064256⟩ : DyadicInterval 40),(⟨799261415744,799405418112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨250360455040,250723379648⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-325325995264,-324713423936⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e459_ok : ecellOkT e459 = true := by decide +kernel
theorem e459_pos {a z : ℝ} (ha1 : ((104739/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((2049/8000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e459 e459_ok ha1 ha2 hz1 hz2 hz

-- box ['261423/1024000', '104739/409600', '1999/2000', '1']  interval_lower 176097995/137438953472
noncomputable def e460 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1380212436631,0,true,249997410624,249997410688⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨818810818921,0,false,-324101193856,-324101193792⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1380668240036,0,true,250360455040,250360455104⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨818355015516,0,false,-324713424000,-324713423936⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1380072086226,0,true,249885598272,249885598336⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨818951169326,0,false,-323912745344,-323912745280⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585437555,0,true,73807296,73807360⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437817997,0,false,-73812288,-73812224⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622821,0,false,-4992,-4928⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1380142255388,0,true,249941501056,249941501120⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨818881000164,0,false,-324006957440,-324006957376⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1380668248657,0,true,250360461888,250360461952⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨818355006895,0,false,-324713435584,-324713435520⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1027616939745,0,false,-74352973696,-74352973632⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1027885692075,0,false,-74065456320,-74065456256⟩
    { al := (261423/1024000), au := (104739/409600), zl := (1999/2000), zu := 1,
      A := ⟨280700808855,281156612260⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨249997410624,249997410688⟩ : DyadicInterval 40),(⟨-324101193856,-324101193792⟩ : DyadicInterval 40),(⟨725892765656,725892784986⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨250360455040,250360455104⟩ : DyadicInterval 40),(⟨-324713424000,-324713423936⟩ : DyadicInterval 40),(⟨725773668059,725773687389⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨249885598272,249885598336⟩ : DyadicInterval 40),(⟨-323912745344,-323912745280⟩ : DyadicInterval 40),(⟨725929397351,725929416680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨250360455040,250360455104⟩ : DyadicInterval 40),(⟨-324713424000,-324713423936⟩ : DyadicInterval 40),(⟨725773668059,725773687389⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,73809779⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73807296,73807360⟩ : DyadicInterval 40),(⟨-73812288,-73812224⟩ : DyadicInterval 40),(⟨762123381093,762123400422⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4992,0⟩ : DyadicInterval 40),(⟨762123383616,762123405376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨280630627612,281156620881⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨249941501056,249941501120⟩ : DyadicInterval 40),(⟨-324006957440,-324006957376⟩ : DyadicInterval 40),(⟨725911085472,725911104801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨250360461888,250360461952⟩ : DyadicInterval 40),(⟨-324713435584,-324713435520⟩ : DyadicInterval 40),(⟨725773665816,725773685146⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-74352973696,-74065456256⟩ : DyadicInterval 40),(⟨799156111744,799299889728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨249997410624,250360455104⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-324713424000,-324101193792⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e460_ok : ecellOkT e460 = true := by decide +kernel
theorem e460_pos {a z : ℝ} (ha1 : ((261423/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((104739/409600 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e460 e460_ok ha1 ha2 hz1 hz2 hz

-- box ['104739/409600', '2049/8000', '1999/2000', '1']  interval_lower 1429701729/1099511627776
noncomputable def e461 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1380668240035,0,true,250360455040,250360455104⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨818355015517,0,false,-324713424000,-324713423936⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1381124043441,0,true,250723379584,250723379648⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨817899212111,0,false,-325325995264,-325325995200⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1380527661728,0,true,250248498112,250248498176⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨818495593824,0,false,-324524564416,-324524564352⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585569366,0,true,73939072,73939136⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437686186,0,false,-73944128,-73944064⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622803,0,false,-4992,-4928⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1380597944840,0,true,250304473152,250304473216⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨818425310712,0,false,-324618982016,-324618981952⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1381124052054,0,true,250723386432,250723386496⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨817899203498,0,false,-325326006848,-325326006784⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1027383643401,0,false,-74602620352,-74602620288⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1027652890093,0,false,-74314508800,-74314508736⟩
    { al := (104739/409600), au := (2049/8000), zl := (1999/2000), zu := 1,
      A := ⟨281156612259,281612415665⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨250360455040,250360455104⟩ : DyadicInterval 40),(⟨-324713424000,-324713423936⟩ : DyadicInterval 40),(⟨725773668060,725773687389⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨250723379584,250723379648⟩ : DyadicInterval 40),(⟨-325325995264,-325325995200⟩ : DyadicInterval 40),(⟨725654368325,725654387654⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨250248498112,250248498176⟩ : DyadicInterval 40),(⟨-324524564416,-324524564352⟩ : DyadicInterval 40),(⟨725810421564,725810440894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨250723379584,250723379648⟩ : DyadicInterval 40),(⟨-325325995264,-325325995200⟩ : DyadicInterval 40),(⟨725654368325,725654387654⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,73941590⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73939072,73939136⟩ : DyadicInterval 40),(⟨-73944128,-73944064⟩ : DyadicInterval 40),(⟨762123381107,762123400436⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4992,0⟩ : DyadicInterval 40),(⟨762123383616,762123405376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨281086317064,281612424278⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨250304473152,250304473216⟩ : DyadicInterval 40),(⟨-324618982016,-324618981952⟩ : DyadicInterval 40),(⟨725792048811,725792068141⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨250723386432,250723386496⟩ : DyadicInterval 40),(⟨-325326006848,-325326006784⟩ : DyadicInterval 40),(⟨725654366076,725654385405⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-74602620352,-74314508736⟩ : DyadicInterval 40),(⟨799280637984,799424713056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨250360455040,250723379648⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-325325995264,-324713423936⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e461_ok : ecellOkT e461 = true := by decide +kernel
theorem e461_pos {a z : ℝ} (ha1 : ((104739/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((2049/8000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e461 e461_ok ha1 ha2 hz1 hz2 hz

-- box ['2049/8000', '525393/2048000', '999/1000', '1999/2000']  interval_lower 1455815499/1099511627776
noncomputable def e462 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1381124043440,0,true,250723379584,250723379648⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨817899212112,0,false,-325325995264,-325325995200⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1381579846845,0,true,251086184448,251086184512⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨817443408707,0,false,-325938908032,-325938907968⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1380842431024,0,true,250499165376,250499165440⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨818180824528,0,false,-324947485504,-324947485440⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1381438812736,0,true,250973938624,250973938688⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨817584442816,0,false,-325749224832,-325749224768⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585565094,0,true,73934784,73934848⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437690458,0,false,-73939840,-73939776⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099659770674,0,true,148132864,148132928⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099363484878,0,false,-148152896,-148152832⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511607815,0,false,-19968,-19904⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622805,0,false,-4992,-4928⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1380983233736,0,true,250611275392,250611275456⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨818040021816,0,false,-325136719424,-325136719360⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1381509339264,0,true,251030070464,251030070528⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨817513916288,0,false,-325844075072,-325844075008⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1027186145011,0,false,-74814004544,-74814004480⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1027455759553,0,false,-74525443968,-74525443904⟩
    { al := (2049/8000), au := (525393/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨281612415664,282068219069⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨250723379584,250723379648⟩ : DyadicInterval 40),(⟨-325325995264,-325325995200⟩ : DyadicInterval 40),(⟨725654368325,725654387655⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨251086184448,251086184512⟩ : DyadicInterval 40),(⟨-325938908032,-325938907968⟩ : DyadicInterval 40),(⟨725534866336,725534885666⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨250499165376,250499165440⟩ : DyadicInterval 40),(⟨-324947485504,-324947485440⟩ : DyadicInterval 40),(⟨725728100024,725728119353⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨250973938624,250973938688⟩ : DyadicInterval 40),(⟨-325749224832,-325749224768⟩ : DyadicInterval 40),(⟨725571864091,725571883421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨73937318,148142898⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73934784,73934848⟩ : DyadicInterval 40),(⟨-73939840,-73939776⟩ : DyadicInterval 40),(⟨762123381107,762123400437⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨148132864,148132928⟩ : DyadicInterval 40),(⟨-148152896,-148152832⟩ : DyadicInterval 40),(⟨762123373607,762123392937⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-19968,-4928⟩ : DyadicInterval 40),(⟨762123386080,762123412864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨281471605960,281997711488⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨250611275392,250611275456⟩ : DyadicInterval 40),(⟨-325136719424,-325136719360⟩ : DyadicInterval 40),(⟨725691244760,725691264090⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨251030070464,251030070528⟩ : DyadicInterval 40),(⟨-325844075072,-325844075008⟩ : DyadicInterval 40),(⟨725553365173,725553384502⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-74814004544,-74525443904⟩ : DyadicInterval 40),(⟨799386105568,799530405152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨250723379584,251086184512⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-325938908032,-325325995200⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e462_ok : ecellOkT e462 = true := by decide +kernel
theorem e462_pos {a z : ℝ} (ha1 : ((2049/8000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((525393/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e462 e462_ok ha1 ha2 hz1 hz2 hz

-- box ['525393/2048000', '263121/1024000', '999/1000', '1999/2000']  interval_lower 738520511/549755813888
noncomputable def e463 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1381579846844,0,true,251086184448,251086184512⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨817443408708,0,false,-325938907968,-325938907904⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1382035650249,0,true,251448869568,251448869632⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨816987605303,0,false,-326552162560,-326552162496⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1381297778624,0,true,250861681344,250861681408⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨817725476928,0,false,-325559574336,-325559574272⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1381894388238,0,true,251336479424,251336479488⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨817128867314,0,false,-326362066944,-326362066880⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585696950,0,true,74066624,74066688⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437558602,0,false,-74071680,-74071616⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099660034535,0,true,148396736,148396800⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099363221017,0,false,-148416832,-148416768⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511607744,0,false,-20096,-20032⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622787,0,false,-4992,-4928⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1381438809250,0,true,250973935808,250973935872⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨817584446302,0,false,-325749220160,-325749220096⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1381965028717,0,true,251392683456,251392683520⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨817058226835,0,false,-326457123392,-326457123328⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1026952209860,0,false,-75064439872,-75064439808⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1027222318918,0,false,-74775284288,-74775284224⟩
    { al := (525393/2048000), au := (263121/1024000), zl := (999/1000), zu := (1999/2000),
      A := ⟨282068219068,282524022473⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨251086184448,251086184512⟩ : DyadicInterval 40),(⟨-325938907968,-325938907904⟩ : DyadicInterval 40),(⟨725534866313,725534885642⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨251448869568,251448869632⟩ : DyadicInterval 40),(⟨-326552162560,-326552162496⟩ : DyadicInterval 40),(⟨725415162091,725415181421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨250861681344,250861681408⟩ : DyadicInterval 40),(⟨-325559574336,-325559574272⟩ : DyadicInterval 40),(⟨725608842476,725608861806⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨251336479424,251336479488⟩ : DyadicInterval 40),(⟨-326362066944,-326362066880⟩ : DyadicInterval 40),(⟨725452282336,725452301666⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨74069174,148406759⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74066624,74066688⟩ : DyadicInterval 40),(⟨-74071680,-74071616⟩ : DyadicInterval 40),(⟨762123381090,762123400419⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨148396736,148396800⟩ : DyadicInterval 40),(⟨-148416832,-148416768⟩ : DyadicInterval 40),(⟨762123373568,762123392898⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-20096,-4928⟩ : DyadicInterval 40),(⟨762123386080,762123412928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨281927181474,282453400941⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨250973935808,250973935872⟩ : DyadicInterval 40),(⟨-325749220160,-325749220096⟩ : DyadicInterval 40),(⟨725571865037,725571884367⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨251392683456,251392683520⟩ : DyadicInterval 40),(⟨-326457123392,-326457123328⟩ : DyadicInterval 40),(⟨725433722161,725433741491⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-75064439872,-74775284224⟩ : DyadicInterval 40),(⟨799511025728,799655622816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨251086184448,251448869632⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-326552162560,-325938907904⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e463_ok : ecellOkT e463 = true := by decide +kernel
theorem e463_pos {a z : ℝ} (ha1 : ((525393/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((263121/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e463 e463_ok ha1 ha2 hz1 hz2 hz

-- box ['2049/8000', '525393/2048000', '1999/2000', '1']  interval_lower 90672325/68719476736
noncomputable def e464 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1381124043440,0,true,250723379584,250723379648⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨817899212112,0,false,-325325995264,-325325995200⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1381579846845,0,true,251086184448,251086184512⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨817443408707,0,false,-325938908032,-325938907968⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1380983237232,0,true,250611278208,250611278272⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨818040018320,0,false,-325136724096,-325136724032⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585701242,0,true,74070912,74070976⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437554310,0,false,-74075968,-74075904⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622785,0,false,-4992,-4928⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1381053634289,0,true,250667325504,250667325568⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨817969621263,0,false,-325231347456,-325231347392⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1381579855463,0,true,251086191296,251086191360⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨817443400089,0,false,-325938919616,-325938919552⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1027149969144,0,false,-74852728256,-74852728192⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1027419710393,0,false,-74564021952,-74564021888⟩
    { al := (2049/8000), au := (525393/2048000), zl := (1999/2000), zu := 1,
      A := ⟨281612415664,282068219069⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨250723379584,250723379648⟩ : DyadicInterval 40),(⟨-325325995264,-325325995200⟩ : DyadicInterval 40),(⟨725654368325,725654387655⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨251086184448,251086184512⟩ : DyadicInterval 40),(⟨-325938908032,-325938907968⟩ : DyadicInterval 40),(⟨725534866336,725534885666⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨250611278208,250611278272⟩ : DyadicInterval 40),(⟨-325136724096,-325136724032⟩ : DyadicInterval 40),(⟨725691243815,725691263144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨251086184448,251086184512⟩ : DyadicInterval 40),(⟨-325938908032,-325938907968⟩ : DyadicInterval 40),(⟨725534866336,725534885666⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,74073466⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74070912,74070976⟩ : DyadicInterval 40),(⟨-74075968,-74075904⟩ : DyadicInterval 40),(⟨762123381089,762123400418⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4992,0⟩ : DyadicInterval 40),(⟨762123383616,762123405376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨281542006513,282068227687⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨250667325504,250667325568⟩ : DyadicInterval 40),(⟨-325231347456,-325231347392⟩ : DyadicInterval 40),(⟨725672810061,725672829391⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨251086191296,251086191360⟩ : DyadicInterval 40),(⟨-325938919616,-325938919552⟩ : DyadicInterval 40),(⟨725534864078,725534883408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-74852728256,-74564021888⟩ : DyadicInterval 40),(⟨799405394560,799549767008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨250723379584,251086184512⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-325938908032,-325325995200⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e464_ok : ecellOkT e464 = true := by decide +kernel
theorem e464_pos {a z : ℝ} (ha1 : ((2049/8000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((525393/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e464 e464_ok ha1 ha2 hz1 hz2 hz

-- box ['525393/2048000', '263121/1024000', '1999/2000', '1']  interval_lower 735975397/549755813888
noncomputable def e465 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1381579846844,0,true,251086184448,251086184512⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨817443408708,0,false,-325938907968,-325938907904⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1382035650249,0,true,251448869568,251448869632⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨816987605303,0,false,-326552162560,-326552162496⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1381438812734,0,true,250973938624,250973938688⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨817584442818,0,false,-325749224832,-325749224768⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585833183,0,true,74202880,74202944⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437422369,0,false,-74207936,-74207872⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622767,0,false,-5056,-4992⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1381509323742,0,true,251030058112,251030058176⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨817513931810,0,false,-325844054208,-325844054144⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1382035658869,0,true,251448876416,251448876480⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨816987596683,0,false,-326552174208,-326552174144⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1026915916981,0,false,-75103297728,-75103297664⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1027186152974,0,false,-74813996032,-74813995968⟩
    { al := (525393/2048000), au := (263121/1024000), zl := (1999/2000), zu := 1,
      A := ⟨282068219068,282524022473⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨251086184448,251086184512⟩ : DyadicInterval 40),(⟨-325938907968,-325938907904⟩ : DyadicInterval 40),(⟨725534866313,725534885642⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨251448869568,251448869632⟩ : DyadicInterval 40),(⟨-326552162560,-326552162496⟩ : DyadicInterval 40),(⟨725415162091,725415181421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨250973938624,250973938688⟩ : DyadicInterval 40),(⟨-325749224832,-325749224768⟩ : DyadicInterval 40),(⟨725571864092,725571883421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨251448869568,251448869632⟩ : DyadicInterval 40),(⟨-326552162560,-326552162496⟩ : DyadicInterval 40),(⟨725415162091,725415181421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,74205407⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74202880,74202944⟩ : DyadicInterval 40),(⟨-74207936,-74207872⟩ : DyadicInterval 40),(⟨762123381071,762123400401⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5056,0⟩ : DyadicInterval 40),(⟨762123383616,762123405408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨281997695966,282524031093⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨251030058112,251030058176⟩ : DyadicInterval 40),(⟨-325844054208,-325844054144⟩ : DyadicInterval 40),(⟨725553369248,725553388577⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨251448876416,251448876480⟩ : DyadicInterval 40),(⟨-326552174208,-326552174144⟩ : DyadicInterval 40),(⟨725415159849,725415179178⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-75103297728,-74813995968⟩ : DyadicInterval 40),(⟨799530381600,799675051744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨251086184448,251448869632⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-326552162560,-325938907904⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e465_ok : ecellOkT e465 = true := by decide +kernel
theorem e465_pos {a z : ℝ} (ha1 : ((525393/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((263121/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e465 e465_ok ha1 ha2 hz1 hz2 hz

-- box ['263121/1024000', '527091/2048000', '999/1000', '1999/2000']  interval_lower 1498405919/1099511627776
noncomputable def e466 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1382035650248,0,true,251448869568,251448869632⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨816987605304,0,false,-326552162560,-326552162496⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1382491453653,0,true,251811435136,251811435200⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨816531801899,0,false,-327165759424,-327165759360⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1381753126225,0,true,251224077824,251224077888⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨817270129327,0,false,-326172004096,-326172004032⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1382349963741,0,true,251698900800,251698900864⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨816673291811,0,false,-326975250816,-326975250752⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585828871,0,true,74198528,74198592⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437426681,0,false,-74203648,-74203584⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099660298524,0,true,148660672,148660736⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099362957028,0,false,-148680832,-148680768⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511607673,0,false,-20160,-20096⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622769,0,false,-5056,-4992⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1381894384755,0,true,251336476672,251336476736⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨817128870797,0,false,-326362062208,-326362062144⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1382420718179,0,true,251755176960,251755177024⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨816602537373,0,false,-327070513728,-327070513664⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1026717896986,0,false,-75315336768,-75315336704⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1026988500758,0,false,-75025585536,-75025585472⟩
    { al := (263121/1024000), au := (527091/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨282524022472,282979825877⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨251448869568,251448869632⟩ : DyadicInterval 40),(⟨-326552162560,-326552162496⟩ : DyadicInterval 40),(⟨725415162091,725415181421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨251811435136,251811435200⟩ : DyadicInterval 40),(⟨-327165759424,-327165759360⟩ : DyadicInterval 40),(⟨725295255544,725295274874⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨251224077824,251224077888⟩ : DyadicInterval 40),(⟨-326172004096,-326172004032⟩ : DyadicInterval 40),(⟨725489383095,725489402425⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨251698900800,251698900864⟩ : DyadicInterval 40),(⟨-326975250816,-326975250752⟩ : DyadicInterval 40),(⟨725332498432,725332517761⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨74201095,148670748⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74198528,74198592⟩ : DyadicInterval 40),(⟨-74203648,-74203584⟩ : DyadicInterval 40),(⟨762123381104,762123400433⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨148660672,148660736⟩ : DyadicInterval 40),(⟨-148680832,-148680768⟩ : DyadicInterval 40),(⟨762123373529,762123392858⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-20160,-4992⟩ : DyadicInterval 40),(⟨762123386112,762123412960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨282382756979,282909090403⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨251336476672,251336476736⟩ : DyadicInterval 40),(⟨-326362062208,-326362062144⟩ : DyadicInterval 40),(⟨725452283220,725452302550⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨251755176960,251755177024⟩ : DyadicInterval 40),(⟨-327070513728,-327070513664⟩ : DyadicInterval 40),(⟨725313876911,725313896240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-75315336768,-75025585472⟩ : DyadicInterval 40),(⟨799636176352,799781071264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨251448869568,251811435200⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-327165759424,-326552162496⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e466_ok : ecellOkT e466 = true := by decide +kernel
theorem e466_pos {a z : ℝ} (ha1 : ((263121/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((527091/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e466 e466_ok ha1 ha2 hz1 hz2 hz

-- box ['527091/2048000', '26397/102400', '999/1000', '1999/2000']  interval_lower 759955311/549755813888
noncomputable def e467 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1382491453652,0,true,251811435136,251811435200⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨816531801900,0,false,-327165759424,-327165759360⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1382947257058,0,true,252173881152,252173881216⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨816075998494,0,false,-327779698816,-327779698752⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1382208473826,0,true,251586354944,251586355008⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨816814781726,0,false,-326784775232,-326784775168⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1382805539244,0,true,252061202688,252061202752⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨816217716308,0,false,-327588776832,-327588776768⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585960855,0,true,74330560,74330624⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437294697,0,false,-74335616,-74335552⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099660562642,0,true,148924736,148924800⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099362692910,0,false,-148944960,-148944896⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511607601,0,false,-20224,-20160⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622751,0,false,-5056,-4992⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1382349960265,0,true,251698898048,251698898112⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨816673295287,0,false,-326975246144,-326975246080⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1382876407637,0,true,252117550912,252117550976⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨816146847915,0,false,-327684246464,-327684246400⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1026483206395,0,false,-75566695552,-75566695488⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1026754305067,0,false,-75276348096,-75276348032⟩
    { al := (527091/2048000), au := (26397/102400), zl := (999/1000), zu := (1999/2000),
      A := ⟨282979825876,283435629282⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨251811435136,251811435200⟩ : DyadicInterval 40),(⟨-327165759424,-327165759360⟩ : DyadicInterval 40),(⟨725295255545,725295274874⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨252173881152,252173881216⟩ : DyadicInterval 40),(⟨-327779698816,-327779698752⟩ : DyadicInterval 40),(⟨725175146629,725175165959⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨251586354944,251586355008⟩ : DyadicInterval 40),(⟨-326784775232,-326784775168⟩ : DyadicInterval 40),(⟨725369721831,725369741160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨252061202688,252061202752⟩ : DyadicInterval 40),(⟨-327588776832,-327588776768⟩ : DyadicInterval 40),(⟨725212512424,725212531754⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨74333079,148934866⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74330560,74330624⟩ : DyadicInterval 40),(⟨-74335616,-74335552⟩ : DyadicInterval 40),(⟨762123381054,762123400383⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨148924736,148924800⟩ : DyadicInterval 40),(⟨-148944960,-148944896⟩ : DyadicInterval 40),(⟨762123373489,762123392819⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-20224,-4992⟩ : DyadicInterval 40),(⟨762123386112,762123412992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨282838332489,283364779861⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨251698898048,251698898112⟩ : DyadicInterval 40),(⟨-326975246144,-326975246080⟩ : DyadicInterval 40),(⟨725332499342,725332518671⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨252117550912,252117550976⟩ : DyadicInterval 40),(⟨-327684246464,-327684246400⟩ : DyadicInterval 40),(⟨725193829469,725193848798⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-75566695552,-75276348032⟩ : DyadicInterval 40),(⟨799761557632,799906750656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨251811435136,252173881216⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-327779698816,-327165759360⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e467_ok : ecellOkT e467 = true := by decide +kernel
theorem e467_pos {a z : ℝ} (ha1 : ((527091/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((26397/102400 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e467 e467_ok ha1 ha2 hz1 hz2 hz

-- box ['263121/1024000', '527091/2048000', '1999/2000', '1']  interval_lower 746641933/549755813888
noncomputable def e468 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1382035650248,0,true,251448869568,251448869632⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨816987605304,0,false,-326552162560,-326552162496⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1382491453653,0,true,251811435136,251811435200⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨816531801899,0,false,-327165759424,-327165759360⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1381894388236,0,true,251336479424,251336479488⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨817128867316,0,false,-326362066944,-326362066880⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585965188,0,true,74334848,74334912⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437290364,0,false,-74339968,-74339904⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622750,0,false,-5056,-4992⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1381965013182,0,true,251392671104,251392671168⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨817058242370,0,false,-326457102464,-326457102400⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1382491462271,0,true,251811441984,251811442048⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨816531793281,0,false,-327165771008,-327165770944⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1026681486913,0,false,-75354329024,-75354328960⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1026952217842,0,false,-75064431360,-75064431296⟩
    { al := (263121/1024000), au := (527091/2048000), zl := (1999/2000), zu := 1,
      A := ⟨282524022472,282979825877⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨251448869568,251448869632⟩ : DyadicInterval 40),(⟨-326552162560,-326552162496⟩ : DyadicInterval 40),(⟨725415162091,725415181421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨251811435136,251811435200⟩ : DyadicInterval 40),(⟨-327165759424,-327165759360⟩ : DyadicInterval 40),(⟨725295255544,725295274874⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨251336479424,251336479488⟩ : DyadicInterval 40),(⟨-326362066944,-326362066880⟩ : DyadicInterval 40),(⟨725452282337,725452301666⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨251811435136,251811435200⟩ : DyadicInterval 40),(⟨-327165759424,-327165759360⟩ : DyadicInterval 40),(⟨725295255544,725295274874⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,74337412⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74334848,74334912⟩ : DyadicInterval 40),(⟨-74339968,-74339904⟩ : DyadicInterval 40),(⟨762123381085,762123400415⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5056,0⟩ : DyadicInterval 40),(⟨762123383616,762123405408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨282453385406,282979834495⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨251392671104,251392671168⟩ : DyadicInterval 40),(⟨-326457102464,-326457102400⟩ : DyadicInterval 40),(⟨725433726230,725433745560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨251811441984,251811442048⟩ : DyadicInterval 40),(⟨-327165771008,-327165770944⟩ : DyadicInterval 40),(⟨725295253271,725295272601⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-75354329024,-75064431296⟩ : DyadicInterval 40),(⟨799655599264,799800567392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨251448869568,251811435200⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-327165759424,-326552162496⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e468_ok : ecellOkT e468 = true := by decide +kernel
theorem e468_pos {a z : ℝ} (ha1 : ((263121/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((527091/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e468 e468_ok ha1 ha2 hz1 hz2 hz

-- box ['527091/2048000', '26397/102400', '1999/2000', '1']  interval_lower 1514756363/1099511627776
noncomputable def e469 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1382491453652,0,true,251811435136,251811435200⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨816531801900,0,false,-327165759424,-327165759360⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1382947257058,0,true,252173881152,252173881216⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨816075998494,0,false,-327779698816,-327779698752⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1382349963739,0,true,251698900800,251698900864⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨816673291813,0,false,-326975250816,-326975250752⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586097257,0,true,74466944,74467008⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437158295,0,false,-74472064,-74472000⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622732,0,false,-5056,-4992⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1382420702634,0,true,251755164544,251755164608⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨816602552918,0,false,-327070492800,-327070492736⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1382947265678,0,true,252173888000,252173888064⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨816075989874,0,false,-327779710464,-327779710400⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1026446678935,0,false,-75605822400,-75605822336⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1026717904986,0,false,-75315328192,-75315328128⟩
    { al := (527091/2048000), au := (26397/102400), zl := (1999/2000), zu := 1,
      A := ⟨282979825876,283435629282⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨251811435136,251811435200⟩ : DyadicInterval 40),(⟨-327165759424,-327165759360⟩ : DyadicInterval 40),(⟨725295255545,725295274874⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨252173881152,252173881216⟩ : DyadicInterval 40),(⟨-327779698816,-327779698752⟩ : DyadicInterval 40),(⟨725175146629,725175165959⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨251698900800,251698900864⟩ : DyadicInterval 40),(⟨-326975250816,-326975250752⟩ : DyadicInterval 40),(⟨725332498432,725332517762⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨252173881152,252173881216⟩ : DyadicInterval 40),(⟨-327779698816,-327779698752⟩ : DyadicInterval 40),(⟨725175146629,725175165959⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,74469481⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74466944,74467008⟩ : DyadicInterval 40),(⟨-74472064,-74472000⟩ : DyadicInterval 40),(⟨762123381068,762123400397⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5056,0⟩ : DyadicInterval 40),(⟨762123383616,762123405408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨282909074858,283435637902⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨251755164544,251755164608⟩ : DyadicInterval 40),(⟨-327070492800,-327070492736⟩ : DyadicInterval 40),(⟨725313881036,725313900366⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨252173888000,252173888064⟩ : DyadicInterval 40),(⟨-327779710464,-327779710400⟩ : DyadicInterval 40),(⟨725175144372,725175163701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-75605822400,-75315328128⟩ : DyadicInterval 40),(⟨799781047680,799926314080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨251811435136,252173881216⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-327779698816,-327165759360⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e469_ok : ecellOkT e469 = true := by decide +kernel
theorem e469_pos {a z : ℝ} (ha1 : ((527091/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((26397/102400 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e469 e469_ok ha1 ha2 hz1 hz2 hz

-- box ['26397/102400', '528789/2048000', '999/1000', '1999/2000']  interval_lower 1541555925/1099511627776
noncomputable def e470 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1382947257057,0,true,252173881152,252173881216⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨816075998495,0,false,-327779698816,-327779698752⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1383403060462,0,true,252536207744,252536207808⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨815620195090,0,false,-328393981248,-328393981184⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1382663821427,0,true,251948512704,251948512768⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨816359434125,0,false,-327397888000,-327397887936⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1383261114746,0,true,252423385280,252423385344⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨815762140806,0,false,-328202645440,-328202645376⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586092904,0,true,74462592,74462656⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437162648,0,false,-74467712,-74467648⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099660826889,0,true,149188928,149188992⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099362428663,0,false,-149209280,-149209216⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511607530,0,false,-20288,-20224⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622733,0,false,-5056,-4992⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1382805535777,0,true,252061199936,252061200000⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨816217719775,0,false,-327588772160,-327588772096⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1383332097094,0,true,252479805504,252479805568⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨815691158458,0,false,-328298321984,-328298321920⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1026248138087,0,false,-75818516416,-75818516352⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1026519731845,0,false,-75527572224,-75527572160⟩
    { al := (26397/102400), au := (528789/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨283435629281,283891432686⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨252173881152,252173881216⟩ : DyadicInterval 40),(⟨-327779698816,-327779698752⟩ : DyadicInterval 40),(⟨725175146629,725175165959⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨252536207744,252536207808⟩ : DyadicInterval 40),(⟨-328393981248,-328393981184⟩ : DyadicInterval 40),(⟨725054835316,725054854646⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨251948512704,251948512768⟩ : DyadicInterval 40),(⟨-327397888000,-327397887936⟩ : DyadicInterval 40),(⟨725249858639,725249877968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨252423385280,252423385344⟩ : DyadicInterval 40),(⟨-328202645440,-328202645376⟩ : DyadicInterval 40),(⟨725092324220,725092343549⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨74465128,149199113⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74462592,74462656⟩ : DyadicInterval 40),(⟨-74467712,-74467648⟩ : DyadicInterval 40),(⟨762123381068,762123400397⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨149188928,149188992⟩ : DyadicInterval 40),(⟨-149209280,-149209216⟩ : DyadicInterval 40),(⟨762123373481,762123392811⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-20288,-4992⟩ : DyadicInterval 40),(⟨762123386112,762123413024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨283293908001,283820469318⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨252061199936,252061200000⟩ : DyadicInterval 40),(⟨-327588772160,-327588772096⟩ : DyadicInterval 40),(⟨725212513334,725212532664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨252479805504,252479805568⟩ : DyadicInterval 40),(⟨-328298321984,-328298321920⟩ : DyadicInterval 40),(⟨725073579718,725073599048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-75818516416,-75527572160⟩ : DyadicInterval 40),(⟨799887169696,800032661088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨252173881152,252536207808⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-328393981248,-327779698752⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e470_ok : ecellOkT e470 = true := by decide +kernel
theorem e470_pos {a z : ℝ} (ha1 : ((26397/102400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((528789/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e470 e470_ok ha1 ha2 hz1 hz2 hz

-- box ['528789/2048000', '264819/1024000', '999/1000', '1999/2000']  interval_lower 781671041/549755813888
noncomputable def e471 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1383403060461,0,true,252536207744,252536207808⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨815620195091,0,false,-328393981248,-328393981184⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1383858863866,0,true,252898414976,252898415040⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨815164391686,0,false,-329008607104,-329008607040⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1383119169028,0,true,252310551232,252310551296⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨815904086524,0,false,-328011342848,-328011342784⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1383716690249,0,true,252785448576,252785448640⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨815306565303,0,false,-328816856896,-328816856832⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586225018,0,true,74594688,74594752⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437030534,0,false,-74599808,-74599744⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099661091266,0,true,149453312,149453376⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099362164286,0,false,-149473664,-149473600⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511607458,0,false,-20352,-20288⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622715,0,false,-5120,-5056⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1383261111287,0,true,252423382528,252423382592⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨815762144265,0,false,-328202640768,-328202640704⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1383787786552,0,true,252841940800,252841940864⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨815235469000,0,false,-328912740608,-328912740544⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1026012692060,0,false,-76070799808,-76070799744⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1026284781094,0,false,-75779258240,-75779258176⟩
    { al := (528789/2048000), au := (264819/1024000), zl := (999/1000), zu := (1999/2000),
      A := ⟨283891432685,284347236090⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨252536207744,252536207808⟩ : DyadicInterval 40),(⟨-328393981248,-328393981184⟩ : DyadicInterval 40),(⟨725054835317,725054854646⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨252898414976,252898415040⟩ : DyadicInterval 40),(⟨-329008607104,-329008607040⟩ : DyadicInterval 40),(⟨724934321568,724934340898⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨252310551232,252310551296⟩ : DyadicInterval 40),(⟨-328011342848,-328011342784⟩ : DyadicInterval 40),(⟨725129793467,725129812797⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨252785448576,252785448640⟩ : DyadicInterval 40),(⟨-328816856896,-328816856832⟩ : DyadicInterval 40),(⟨724971933774,724971953104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨74597242,149463490⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74594688,74594752⟩ : DyadicInterval 40),(⟨-74599808,-74599744⟩ : DyadicInterval 40),(⟨762123381050,762123400380⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨149453312,149453376⟩ : DyadicInterval 40),(⟨-149473664,-149473600⟩ : DyadicInterval 40),(⟨762123373410,762123392739⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-20352,-5056⟩ : DyadicInterval 40),(⟨762123386144,762123413056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨283749483511,284276158776⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨252423382528,252423382592⟩ : DyadicInterval 40),(⟨-328202640768,-328202640704⟩ : DyadicInterval 40),(⟨725092325131,725092344460⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨252841940800,252841940864⟩ : DyadicInterval 40),(⟨-328912740608,-328912740544⟩ : DyadicInterval 40),(⟨724953127597,724953146927⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-76070799808,-75779258176⟩ : DyadicInterval 40),(⟨800013012704,800158802784⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨252536207744,252898415040⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-329008607104,-328393981184⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e471_ok : ecellOkT e471 = true := by decide +kernel
theorem e471_pos {a z : ℝ} (ha1 : ((528789/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((264819/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e471 e471_ok ha1 ha2 hz1 hz2 hz

-- box ['26397/102400', '528789/2048000', '1999/2000', '1']  interval_lower 1536369299/1099511627776
noncomputable def e472 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1382947257057,0,true,252173881152,252173881216⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨816075998495,0,false,-327779698816,-327779698752⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1383403060462,0,true,252536207744,252536207808⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨815620195090,0,false,-328393981248,-328393981184⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1382805539242,0,true,252061202688,252061202752⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨816217716310,0,false,-327588776832,-327588776768⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586229391,0,true,74599040,74599104⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437026161,0,false,-74604160,-74604096⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622714,0,false,-5120,-5056⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1382876392082,0,true,252117538560,252117538624⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨816146863470,0,false,-327684225536,-327684225472⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1383403069083,0,true,252536214592,252536214656⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨815620186469,0,false,-328393992896,-328393992832⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1026211493051,0,false,-75857778240,-75857778176⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1026483214414,0,false,-75566686976,-75566686912⟩
    { al := (26397/102400), au := (528789/2048000), zl := (1999/2000), zu := 1,
      A := ⟨283435629281,283891432686⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨252173881152,252173881216⟩ : DyadicInterval 40),(⟨-327779698816,-327779698752⟩ : DyadicInterval 40),(⟨725175146629,725175165959⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨252536207744,252536207808⟩ : DyadicInterval 40),(⟨-328393981248,-328393981184⟩ : DyadicInterval 40),(⟨725054835316,725054854646⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨252061202688,252061202752⟩ : DyadicInterval 40),(⟨-327588776832,-327588776768⟩ : DyadicInterval 40),(⟨725212512425,725212531754⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨252536207744,252536207808⟩ : DyadicInterval 40),(⟨-328393981248,-328393981184⟩ : DyadicInterval 40),(⟨725054835316,725054854646⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,74601615⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74599040,74599104⟩ : DyadicInterval 40),(⟨-74604160,-74604096⟩ : DyadicInterval 40),(⟨762123381050,762123400379⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5120,0⟩ : DyadicInterval 40),(⟨762123383616,762123405440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨283364764306,283891441307⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨252117538560,252117538624⟩ : DyadicInterval 40),(⟨-327684225536,-327684225472⟩ : DyadicInterval 40),(⟨725193833571,725193852900⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨252536214592,252536214656⟩ : DyadicInterval 40),(⟨-328393992896,-328393992832⟩ : DyadicInterval 40),(⟨725054833051,725054852380⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-75857778240,-75566686912⟩ : DyadicInterval 40),(⟨799906727072,800052292000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨252173881152,252536207808⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-328393981248,-327779698752⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e472_ok : ecellOkT e472 = true := by decide +kernel
theorem e472_pos {a z : ℝ} (ha1 : ((26397/102400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((528789/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e472 e472_ok ha1 ha2 hz1 hz2 hz

-- box ['528789/2048000', '264819/1024000', '1999/2000', '1']  interval_lower 1558123077/1099511627776
noncomputable def e473 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1383403060461,0,true,252536207744,252536207808⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨815620195091,0,false,-328393981248,-328393981184⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1383858863866,0,true,252898414976,252898415040⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨815164391686,0,false,-329008607104,-329008607040⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1383261114744,0,true,252423385280,252423385344⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨815762140808,0,false,-328202645440,-328202645376⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586361589,0,true,74731264,74731328⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436893963,0,false,-74736384,-74736320⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622696,0,false,-5120,-5056⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1383332081529,0,true,252479793152,252479793216⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨815691174023,0,false,-328298300992,-328298300928⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1383858872482,0,true,252898421824,252898421888⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨815164383070,0,false,-329008618688,-329008618624⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1025975929262,0,false,-76110196864,-76110196800⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1026248146124,0,false,-75818507840,-75818507776⟩
    { al := (528789/2048000), au := (264819/1024000), zl := (1999/2000), zu := 1,
      A := ⟨283891432685,284347236090⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨252536207744,252536207808⟩ : DyadicInterval 40),(⟨-328393981248,-328393981184⟩ : DyadicInterval 40),(⟨725054835317,725054854646⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨252898414976,252898415040⟩ : DyadicInterval 40),(⟨-329008607104,-329008607040⟩ : DyadicInterval 40),(⟨724934321568,724934340898⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨252423385280,252423385344⟩ : DyadicInterval 40),(⟨-328202645440,-328202645376⟩ : DyadicInterval 40),(⟨725092324220,725092343550⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨252898414976,252898415040⟩ : DyadicInterval 40),(⟨-329008607104,-329008607040⟩ : DyadicInterval 40),(⟨724934321568,724934340898⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,74733813⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74731264,74731328⟩ : DyadicInterval 40),(⟨-74736384,-74736320⟩ : DyadicInterval 40),(⟨762123381032,762123400361⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5120,0⟩ : DyadicInterval 40),(⟨762123383616,762123405440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨283820453753,284347244706⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨252479793152,252479793216⟩ : DyadicInterval 40),(⟨-328298300992,-328298300928⟩ : DyadicInterval 40),(⟨725073583812,725073603142⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨252898421824,252898421888⟩ : DyadicInterval 40),(⟨-329008618688,-329008618624⟩ : DyadicInterval 40),(⟨724934319273,724934338602⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-76110196864,-75818507776⟩ : DyadicInterval 40),(⟨800032637504,800178501312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨252536207744,252898415040⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-329008607104,-328393981184⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e473_ok : ecellOkT e473 = true := by decide +kernel
theorem e473_pos {a z : ℝ} (ha1 : ((528789/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((264819/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e473 e473_ok ha1 ha2 hz1 hz2 hz

-- box ['264819/1024000', '530487/2048000', '999/1000', '1999/2000']  interval_lower 1585270015/1099511627776
noncomputable def e474 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1383858863865,0,true,252898414976,252898415040⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨815164391687,0,false,-329008607104,-329008607040⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1384314667271,0,true,253260502976,253260503040⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨814708588281,0,false,-329623576704,-329623576640⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1383574516628,0,true,252672470528,252672470592⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨815448738924,0,false,-328625140160,-328625140096⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1384172265752,0,true,253147392704,253147392768⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨814850989800,0,false,-329431411712,-329431411648⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586357195,0,true,74726848,74726912⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436898357,0,false,-74731968,-74731904⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099661355771,0,true,149717760,149717824⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099361899781,0,false,-149738240,-149738176⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511607386,0,false,-20416,-20352⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622697,0,false,-5120,-5056⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1383716686789,0,true,252785445824,252785445888⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨815306568763,0,false,-328816852224,-328816852160⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1384243476015,0,true,253203956800,253203956864⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨814779779537,0,false,-329527502848,-329527502784⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1025776868312,0,false,-76323545984,-76323545920⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1026049452818,0,false,-76031406400,-76031406336⟩
    { al := (264819/1024000), au := (530487/2048000), zl := (999/1000), zu := (1999/2000),
      A := ⟨284347236089,284803039495⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨252898414976,252898415040⟩ : DyadicInterval 40),(⟨-329008607104,-329008607040⟩ : DyadicInterval 40),(⟨724934321568,724934340898⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨253260502976,253260503040⟩ : DyadicInterval 40),(⟨-329623576704,-329623576640⟩ : DyadicInterval 40),(⟨724813605284,724813624613⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨252672470528,252672470592⟩ : DyadicInterval 40),(⟨-328625140160,-328625140096⟩ : DyadicInterval 40),(⟨725009526320,725009545650⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨253147392704,253147392768⟩ : DyadicInterval 40),(⟨-329431411712,-329431411648⟩ : DyadicInterval 40),(⟨724851341059,724851360388⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨74729419,149727995⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74726848,74726912⟩ : DyadicInterval 40),(⟨-74731968,-74731904⟩ : DyadicInterval 40),(⟨762123381032,762123400362⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨149717760,149717824⟩ : DyadicInterval 40),(⟨-149738240,-149738176⟩ : DyadicInterval 40),(⟨762123373402,762123392731⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-20416,-5056⟩ : DyadicInterval 40),(⟨762123386144,762123413088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨284205059013,284731848239⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨252785445824,252785445888⟩ : DyadicInterval 40),(⟨-328816852224,-328816852160⟩ : DyadicInterval 40),(⟨724971934689,724971954018⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨253203956800,253203956864⟩ : DyadicInterval 40),(⟨-329527502848,-329527502784⟩ : DyadicInterval 40),(⟨724832473156,724832492486⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-76323545984,-76031406336⟩ : DyadicInterval 40),(⟨800139086784,800285175872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨252898414976,253260503040⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-329623576704,-329008607040⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e474_ok : ecellOkT e474 = true := by decide +kernel
theorem e474_pos {a z : ℝ} (ha1 : ((264819/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((530487/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e474 e474_ok ha1 ha2 hz1 hz2 hz

-- box ['530487/2048000', '66417/256000', '999/1000', '1999/2000']  interval_lower 803670133/549755813888
noncomputable def e475 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1384314667270,0,true,253260502976,253260503040⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨814708588282,0,false,-329623576704,-329623576640⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1384770470675,0,true,253622471680,253622471744⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨814252784877,0,false,-330238890432,-330238890368⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1384029864230,0,true,253034270784,253034270848⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨814993391322,0,false,-329239280320,-329239280256⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1384627841254,0,true,253509217728,253509217792⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨814395414298,0,false,-330046310208,-330046310144⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586489439,0,true,74859072,74859136⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436766113,0,false,-74864256,-74864192⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099661620408,0,true,149982400,149982464⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099361635144,0,false,-150002880,-150002816⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511607314,0,false,-20480,-20416⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622679,0,false,-5120,-5056⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1384172262305,0,true,253147389952,253147390016⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨814850993247,0,false,-329431407040,-329431406976⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1384699165468,0,true,253565853696,253565853760⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨814324090084,0,false,-330142608960,-330142608896⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1025540666850,0,false,-76576755200,-76576755136⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1025813747005,0,false,-76284017088,-76284017024⟩
    { al := (530487/2048000), au := (66417/256000), zl := (999/1000), zu := (1999/2000),
      A := ⟨284803039494,285258842899⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨253260502976,253260503040⟩ : DyadicInterval 40),(⟨-329623576704,-329623576640⟩ : DyadicInterval 40),(⟨724813605284,724813624614⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨253622471680,253622471744⟩ : DyadicInterval 40),(⟨-330238890432,-330238890368⟩ : DyadicInterval 40),(⟨724692686507,724692705836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨253034270784,253034270848⟩ : DyadicInterval 40),(⟨-329239280320,-329239280256⟩ : DyadicInterval 40),(⟨724889057081,724889076410⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨253509217728,253509217792⟩ : DyadicInterval 40),(⟨-330046310208,-330046310144⟩ : DyadicInterval 40),(⟨724730546011,724730565341⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨74861663,149992632⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74859072,74859136⟩ : DyadicInterval 40),(⟨-74864256,-74864192⟩ : DyadicInterval 40),(⟨762123381046,762123400376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨149982400,149982464⟩ : DyadicInterval 40),(⟨-150002880,-150002816⟩ : DyadicInterval 40),(⟨762123373329,762123392659⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-20480,-5056⟩ : DyadicInterval 40),(⟨762123386144,762123413120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨284660634529,285187537692⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨253147389952,253147390016⟩ : DyadicInterval 40),(⟨-329431407040,-329431406976⟩ : DyadicInterval 40),(⟨724851341973,724851361302⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨253565853696,253565853760⟩ : DyadicInterval 40),(⟨-330142608960,-330142608896⟩ : DyadicInterval 40),(⟨724711616233,724711635562⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-76576755200,-76284017024⟩ : DyadicInterval 40),(⟨800265392128,800411780480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨253260502976,253622471744⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-330238890432,-329623576640⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e475_ok : ecellOkT e475 = true := by decide +kernel
theorem e475_pos {a z : ℝ} (ha1 : ((530487/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((66417/256000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e475 e475_ok ha1 ha2 hz1 hz2 hz

-- box ['264819/1024000', '530487/2048000', '1999/2000', '1']  interval_lower 98751145/68719476736
noncomputable def e476 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1383858863865,0,true,252898414976,252898415040⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨815164391687,0,false,-329008607104,-329008607040⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1384314667271,0,true,253260502976,253260503040⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨814708588281,0,false,-329623576704,-329623576640⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1383716690246,0,true,252785448576,252785448640⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨815306565306,0,false,-328816856896,-328816856832⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586493851,0,true,74863488,74863552⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436761701,0,false,-74868672,-74868608⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622678,0,false,-5120,-5056⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1383787770976,0,true,252841928384,252841928448⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨815235484576,0,false,-328912719616,-328912719552⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1384314675895,0,true,253260509824,253260509888⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨814708579657,0,false,-329623588288,-329623588224⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1025739987559,0,false,-76363078464,-76363078400⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1026012700115,0,false,-76070791168,-76070791104⟩
    { al := (264819/1024000), au := (530487/2048000), zl := (1999/2000), zu := 1,
      A := ⟨284347236089,284803039495⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨252898414976,252898415040⟩ : DyadicInterval 40),(⟨-329008607104,-329008607040⟩ : DyadicInterval 40),(⟨724934321568,724934340898⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨253260502976,253260503040⟩ : DyadicInterval 40),(⟨-329623576704,-329623576640⟩ : DyadicInterval 40),(⟨724813605284,724813624613⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨252785448576,252785448640⟩ : DyadicInterval 40),(⟨-328816856896,-328816856832⟩ : DyadicInterval 40),(⟨724971933775,724971953105⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨253260502976,253260503040⟩ : DyadicInterval 40),(⟨-329623576704,-329623576640⟩ : DyadicInterval 40),(⟨724813605284,724813624613⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,74866075⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74863488,74863552⟩ : DyadicInterval 40),(⟨-74868672,-74868608⟩ : DyadicInterval 40),(⟨762123381046,762123400375⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5120,0⟩ : DyadicInterval 40),(⟨762123383616,762123405440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨284276143200,284803048119⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨252841928384,252841928448⟩ : DyadicInterval 40),(⟨-328912719616,-328912719552⟩ : DyadicInterval 40),(⟨724953131749,724953151078⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨253260509824,253260509888⟩ : DyadicInterval 40),(⟨-329623588288,-329623588224⟩ : DyadicInterval 40),(⟨724813602979,724813622308⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-76363078464,-76070791104⟩ : DyadicInterval 40),(⟨800158779168,800304942112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨252898414976,253260503040⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-329623576704,-329008607040⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e476_ok : ecellOkT e476 = true := by decide +kernel
theorem e476_pos {a z : ℝ} (ha1 : ((264819/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((530487/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e476 e476_ok ha1 ha2 hz1 hz2 hz

-- box ['530487/2048000', '66417/256000', '1999/2000', '1']  interval_lower 1602056077/1099511627776
noncomputable def e477 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1384314667270,0,true,253260502976,253260503040⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨814708588282,0,false,-329623576704,-329623576640⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1384770470675,0,true,253622471680,253622471744⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨814252784877,0,false,-330238890432,-330238890368⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1384172265750,0,true,253147392704,253147392768⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨814850989802,0,false,-329431411712,-329431411648⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586626180,0,true,74995840,74995904⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436629372,0,false,-75001024,-75000960⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622660,0,false,-5120,-5056⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1384243460429,0,true,253203944448,253203944512⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨814779795123,0,false,-329527481792,-329527481728⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1384770479290,0,true,253622478528,253622478592⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨814252776262,0,false,-330238902080,-330238902016⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1025503667958,0,false,-76616423488,-76616423424⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1025776876385,0,false,-76323537344,-76323537280⟩
    { al := (530487/2048000), au := (66417/256000), zl := (1999/2000), zu := 1,
      A := ⟨284803039494,285258842899⟩, Z := ⟨1098961871962,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨253260502976,253260503040⟩ : DyadicInterval 40),(⟨-329623576704,-329623576640⟩ : DyadicInterval 40),(⟨724813605284,724813624614⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨253622471680,253622471744⟩ : DyadicInterval 40),(⟨-330238890432,-330238890368⟩ : DyadicInterval 40),(⟨724692686507,724692705836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨253147392704,253147392768⟩ : DyadicInterval 40),(⟨-329431411712,-329431411648⟩ : DyadicInterval 40),(⟨724851341059,724851360389⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨253622471680,253622471744⟩ : DyadicInterval 40),(⟨-330238890432,-330238890368⟩ : DyadicInterval 40),(⟨724692686507,724692705836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,74998404⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74995840,74995904⟩ : DyadicInterval 40),(⟨-75001024,-75000960⟩ : DyadicInterval 40),(⟨762123381028,762123400357⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5120,0⟩ : DyadicInterval 40),(⟨762123383616,762123405440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨284731832653,285258851514⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨253203944448,253203944512⟩ : DyadicInterval 40),(⟨-329527481792,-329527481728⟩ : DyadicInterval 40),(⟨724832477260,724832496590⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨253622478528,253622478592⟩ : DyadicInterval 40),(⟨-330238902080,-330238902016⟩ : DyadicInterval 40),(⟨724692684220,724692703549⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-76616423488,-76323537280⟩ : DyadicInterval 40),(⟨800285152256,800431614624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨253260502976,253622471744⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-330238890432,-329623576640⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e477_ok : ecellOkT e477 = true := by decide +kernel
theorem e477_pos {a z : ℝ} (ha1 : ((530487/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((66417/256000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e477 e477_ok ha1 ha2 hz1 hz2 hz

-- box ['66417/256000', '106437/409600', '999/1000', '1999/2000']  interval_lower 814776823/549755813888
noncomputable def e478 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1384770470674,0,true,253622471680,253622471744⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨814252784878,0,false,-330238890432,-330238890368⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1385226274079,0,true,253984321344,253984321408⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨813796981473,0,false,-330854548672,-330854548608⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1384485211831,0,true,253395952064,253395952128⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨814538043721,0,false,-329853763712,-329853763648⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1385083416757,0,true,253870923712,253870923776⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨813939838795,0,false,-330661552768,-330661552704⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586621747,0,true,74991360,74991424⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436633805,0,false,-74996544,-74996480⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099661885174,0,true,150247104,150247168⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099361370378,0,false,-150267712,-150267648⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511607242,0,false,-20544,-20480⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622661,0,false,-5120,-5056⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1384627837814,0,true,253509214976,253509215040⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨814395417738,0,false,-330046305536,-330046305472⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1385154854933,0,true,253927631552,253927631616⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨813868400619,0,false,-330758059328,-330758059264⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1025304087665,0,false,-76830427776,-76830427712⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1025577663667,0,false,-76537090560,-76537090496⟩
    { al := (66417/256000), au := (106437/409600), zl := (999/1000), zu := (1999/2000),
      A := ⟨285258842898,285714646303⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨253622471680,253622471744⟩ : DyadicInterval 40),(⟨-330238890432,-330238890368⟩ : DyadicInterval 40),(⟨724692686507,724692705836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨253984321344,253984321408⟩ : DyadicInterval 40),(⟨-330854548672,-330854548608⟩ : DyadicInterval 40),(⟨724571565077,724571584406⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨253395952064,253395952128⟩ : DyadicInterval 40),(⟨-329853763712,-329853763648⟩ : DyadicInterval 40),(⟨724768385711,724768405040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨253870923712,253870923776⟩ : DyadicInterval 40),(⟨-330661552768,-330661552704⟩ : DyadicInterval 40),(⟨724609548595,724609567924⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨74993971,150257398⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74991360,74991424⟩ : DyadicInterval 40),(⟨-74996544,-74996480⟩ : DyadicInterval 40),(⟨762123381028,762123400358⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨150247104,150247168⟩ : DyadicInterval 40),(⟨-150267712,-150267648⟩ : DyadicInterval 40),(⟨762123373321,762123392651⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-20544,-5056⟩ : DyadicInterval 40),(⟨762123386144,762123413152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨285116210038,285643227157⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨253509214976,253509215040⟩ : DyadicInterval 40),(⟨-330046305536,-330046305472⟩ : DyadicInterval 40),(⟨724730546927,724730566256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨253927631552,253927631616⟩ : DyadicInterval 40),(⟨-330758059328,-330758059264⟩ : DyadicInterval 40),(⟨724590556784,724590576113⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-76830427776,-76537090496⟩ : DyadicInterval 40),(⟨800391928864,800538616768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨253622471680,253984321408⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-330854548672,-330238890368⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e478_ok : ecellOkT e478 = true := by decide +kernel
theorem e478_pos {a z : ℝ} (ha1 : ((66417/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((106437/409600 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e478 e478_ok ha1 ha2 hz1 hz2 hz

-- box ['106437/409600', '266517/1024000', '999/1000', '1999/2000']  interval_lower 1651910485/1099511627776
noncomputable def e479 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1385226274078,0,true,253984321344,253984321408⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨813796981474,0,false,-330854548672,-330854548608⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1385682077484,0,true,254346051904,254346051968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨813341178068,0,false,-331470551872,-331470551808⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1384940559431,0,true,253757514368,253757514432⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨814082696121,0,false,-330468590720,-330468590656⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1385538992260,0,true,254232510720,254232510784⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨813484263292,0,false,-331277139776,-331277139712⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586754120,0,true,75123776,75123840⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436501432,0,false,-75128960,-75128896⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099662150071,0,true,150511936,150512000⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099361105481,0,false,-150532608,-150532544⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511607169,0,false,-20608,-20544⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622643,0,false,-5184,-5120⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1385083413328,0,true,253870920960,253870921024⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨813939842224,0,false,-330661548160,-330661548096⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1385610544387,0,true,254289290304,254289290368⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨813412711165,0,false,-331373854464,-331373854400⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1025067130766,0,false,-77084564096,-77084564032⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1025341202796,0,false,-76790627136,-76790627072⟩
    { al := (106437/409600), au := (266517/1024000), zl := (999/1000), zu := (1999/2000),
      A := ⟨285714646302,286170449708⟩, Z := ⟨1098412116148,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨253984321344,253984321408⟩ : DyadicInterval 40),(⟨-330854548672,-330854548608⟩ : DyadicInterval 40),(⟨724571565077,724571584406⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨254346051904,254346051968⟩ : DyadicInterval 40),(⟨-331470551872,-331470551808⟩ : DyadicInterval 40),(⟨724450241060,724450260390⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨253757514368,253757514432⟩ : DyadicInterval 40),(⟨-330468590720,-330468590656⟩ : DyadicInterval 40),(⟨724647512214,724647531544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨254232510720,254232510784⟩ : DyadicInterval 40),(⟨-331277139776,-331277139712⟩ : DyadicInterval 40),(⟨724488348770,724488368100⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨75126344,150522295⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75123776,75123840⟩ : DyadicInterval 40),(⟨-75128960,-75128896⟩ : DyadicInterval 40),(⟨762123381010,762123400340⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨150511936,150512000⟩ : DyadicInterval 40),(⟨-150532608,-150532544⟩ : DyadicInterval 40),(⟨762123373281,762123392611⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-20608,-5120⟩ : DyadicInterval 40),(⟨762123386176,762123413184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨285571785552,286098916611⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨253870920960,253870921024⟩ : DyadicInterval 40),(⟨-330661548160,-330661548096⟩ : DyadicInterval 40),(⟨724609549534,724609568863⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨254289290304,254289290368⟩ : DyadicInterval 40),(⟨-331373854464,-331373854400⟩ : DyadicInterval 40),(⟨724469294904,724469314234⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-77084564096,-76790627072⟩ : DyadicInterval 40),(⟨800518697152,800665684928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨253984321344,254346051968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-331470551872,-330854548608⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e479_ok : ecellOkT e479 = true := by decide +kernel
theorem e479_pos {a z : ℝ} (ha1 : ((106437/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((266517/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e479 e479_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B007

end


