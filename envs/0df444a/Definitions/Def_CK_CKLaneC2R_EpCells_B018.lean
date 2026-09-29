-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B018
-- name    : CK_CKLaneC2R_EpCells_B018
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:19:03.602551+00:00
-- url     : https://prove2.me/theorems/8ff0cd02-1b0e-4431-95d2-dd651f42ac7a
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B018` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B018` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B018` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B018 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B018.lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheckT

-- ===== source module CKLaneC2R.EpCells.B018 =====
section

namespace CKLaneC2R.EpCells.B018

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['802029/4096000', '401439/2048000', '3999/4000', '1']  interval_lower 408560175/1099511627776
noncomputable def e1080 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1314804648116,0,true,196616859008,196616859072⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨884218607436,0,false,-239602341312,-239602341248⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1315032549819,0,true,196807426368,196807426432⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨883990705733,0,false,-239885769920,-239885769856⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1314750824860,0,true,196571848128,196571848192⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨884272430692,0,false,-239535414976,-239535414912⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539341232,0,true,27713088,27713152⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483914320,0,false,-27713856,-27713792⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627077,0,false,-704,-640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1314777731091,0,true,196594349248,196594349312⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨884245524461,0,false,-239568870912,-239568870848⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1315032558345,0,true,196807433472,196807433536⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨883990697207,0,false,-239885780544,-239885780480⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1057266261433,0,false,-43078347008,-43078346944⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1057366102376,0,false,-42974521600,-42974521536⟩
    { al := (802029/4096000), au := (401439/2048000), zl := (3999/4000), zu := 1,
      A := ⟨215293020340,215520922043⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196616859008,196616859072⟩ : DyadicInterval 40),(⟨-239602341312,-239602341248⟩ : DyadicInterval 40),(⟨740908550361,740908569690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196807426368,196807426432⟩ : DyadicInterval 40),(⟨-239885769920,-239885769856⟩ : DyadicInterval 40),(⟨740863317040,740863336370⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196571848128,196571848192⟩ : DyadicInterval 40),(⟨-239535414976,-239535414912⟩ : DyadicInterval 40),(⟨740919225880,740919245210⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196807426368,196807426432⟩ : DyadicInterval 40),(⟨-239885769920,-239885769856⟩ : DyadicInterval 40),(⟨740863317040,740863336370⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,27713456⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27713088,27713152⟩ : DyadicInterval 40),(⟨-27713856,-27713792⟩ : DyadicInterval 40),(⟨762123383237,762123402566⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-704,0⟩ : DyadicInterval 40),(⟨762123383616,762123403232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨215266103315,215520930569⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196594349248,196594349312⟩ : DyadicInterval 40),(⟨-239568870912,-239568870848⟩ : DyadicInterval 40),(⟨740913889551,740913908880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196807433472,196807433536⟩ : DyadicInterval 40),(⟨-239885780544,-239885780480⟩ : DyadicInterval 40),(⟨740863315369,740863334699⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-43078347008,-42974521536⟩ : DyadicInterval 40),(⟨783610644384,783662576384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨196616859008,196807426432⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-239885769920,-239602341248⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1080_ok : ecellOkT e1080 = true := by decide +kernel
theorem e1080_pos {a z : ℝ} (ha1 : ((802029/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((401439/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1080 e1080_ok ha1 ha2 hz1 hz2 hz

-- box ['401439/2048000', '803727/4096000', '1999/2000', '3999/4000']  interval_lower 103436157/274877906944
noncomputable def e1081 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1315032549818,0,true,196807426368,196807426432⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨883990705734,0,false,-239885769920,-239885769856⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1315260451521,0,true,196997960704,196997960768⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨883762804031,0,false,-240169271616,-240169271552⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1314924789356,0,true,196717323072,196717323136⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨884098466196,0,false,-239751745152,-239751745088⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1315206514316,0,true,196952870144,196952870208⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨883816741236,0,false,-240102169024,-240102168960⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539340316,0,true,27712128,27712192⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483915236,0,false,-27712896,-27712832⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567116029,0,true,55486848,55486912⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456139523,0,false,-55489664,-55489600⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624975,0,false,-2816,-2752⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627078,0,false,-704,-640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1314978664467,0,true,196762371328,196762371392⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨884044591085,0,false,-239818749120,-239818749056⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1315233491539,0,true,196975422848,196975422912⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨883789764013,0,false,-240135730560,-240135730496⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1057187452815,0,false,-43160307648,-43160307584⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1057287386825,0,false,-43056377728,-43056377664⟩
    { al := (401439/2048000), au := (803727/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨215520922042,215748823745⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196807426368,196807426432⟩ : DyadicInterval 40),(⟨-239885769920,-239885769856⟩ : DyadicInterval 40),(⟨740863317040,740863336370⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196997960704,196997960768⟩ : DyadicInterval 40),(⟨-240169271616,-240169271552⟩ : DyadicInterval 40),(⟨740818034597,740818053926⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196717323072,196717323136⟩ : DyadicInterval 40),(⟨-239751745152,-239751745088⟩ : DyadicInterval 40),(⟨740884711187,740884730516⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196952870144,196952870208⟩ : DyadicInterval 40),(⟨-240102169024,-240102168960⟩ : DyadicInterval 40),(⟨740828755985,740828775315⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨27712540,55488253⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27712128,27712192⟩ : DyadicInterval 40),(⟨-27712896,-27712832⟩ : DyadicInterval 40),(⟨762123383237,762123402566⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55486848,55486912⟩ : DyadicInterval 40),(⟨-55489664,-55489600⟩ : DyadicInterval 40),(⟨762123382159,762123401488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2816,-640⟩ : DyadicInterval 40),(⟨762123383936,762123404288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨215467036691,215721863763⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196762371328,196762371392⟩ : DyadicInterval 40),(⟨-239818749120,-239818749056⟩ : DyadicInterval 40),(⟨740874016521,740874035850⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196975422848,196975422912⟩ : DyadicInterval 40),(⟨-240135730560,-240135730496⟩ : DyadicInterval 40),(⟨740823393941,740823413270⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-43160307648,-43056377664⟩ : DyadicInterval 40),(⟨783651572448,783703556704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨196807426368,196997960768⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-240169271616,-239885769856⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1081_ok : ecellOkT e1081 = true := by decide +kernel
theorem e1081_pos {a z : ℝ} (ha1 : ((401439/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((803727/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1081 e1081_ok ha1 ha2 hz1 hz2 hz

-- box ['803727/4096000', '25143/128000', '1999/2000', '3999/4000']  interval_lower 104534365/274877906944
noncomputable def e1082 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1315260451520,0,true,196997960704,196997960768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨883762804032,0,false,-240169271616,-240169271552⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1315488353223,0,true,197188462016,197188462080⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨883534902329,0,false,-240452846464,-240452846400⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1315152577108,0,true,196907777792,196907777856⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨883870678444,0,false,-240035070528,-240035070464⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1315434359042,0,true,197143331648,197143331712⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨883588896510,0,false,-240385655680,-240385655616⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539371315,0,true,27743168,27743232⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483884237,0,false,-27743936,-27743872⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567178042,0,true,55548800,55548864⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456077510,0,false,-55551680,-55551616⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624969,0,false,-2816,-2752⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627076,0,false,-704,-640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1315206509195,0,true,196952865856,196952865920⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨883816746357,0,false,-240102162688,-240102162624⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1315461364748,0,true,197165904256,197165904320⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨883561890804,0,false,-240419261248,-240419261184⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1057097989102,0,false,-43253356928,-43253356864⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1057198039912,0,false,-43149296768,-43149296704⟩
    { al := (803727/4096000), au := (25143/128000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨215748823744,215976725447⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196997960704,196997960768⟩ : DyadicInterval 40),(⟨-240169271616,-240169271552⟩ : DyadicInterval 40),(⟨740818034597,740818053927⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197188462016,197188462080⟩ : DyadicInterval 40),(⟨-240452846464,-240452846400⟩ : DyadicInterval 40),(⟨740772703044,740772722374⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196907777792,196907777856⟩ : DyadicInterval 40),(⟨-240035070528,-240035070464⟩ : DyadicInterval 40),(⟨740839474589,740839493918⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197143331648,197143331712⟩ : DyadicInterval 40),(⟨-240385655680,-240385655616⟩ : DyadicInterval 40),(⟨740783447401,740783466730⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨27743539,55550266⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27743168,27743232⟩ : DyadicInterval 40),(⟨-27743936,-27743872⟩ : DyadicInterval 40),(⟨762123383235,762123402564⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55548800,55548864⟩ : DyadicInterval 40),(⟨-55551680,-55551616⟩ : DyadicInterval 40),(⟨762123382185,762123401514⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2816,-640⟩ : DyadicInterval 40),(⟨762123383936,762123404288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨215694881419,215949736972⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196952865856,196952865920⟩ : DyadicInterval 40),(⟨-240102162688,-240102162624⟩ : DyadicInterval 40),(⟨740828757021,740828776351⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197165904256,197165904320⟩ : DyadicInterval 40),(⟨-240419261248,-240419261184⟩ : DyadicInterval 40),(⟨740778073845,740778093175⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-43253356928,-43149296704⟩ : DyadicInterval 40),(⟨783698031968,783750081344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨196997960704,197188462080⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-240452846464,-240169271552⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1082_ok : ecellOkT e1082 = true := by decide +kernel
theorem e1082_pos {a z : ℝ} (ha1 : ((803727/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((25143/128000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1082 e1082_ok ha1 ha2 hz1 hz2 hz

-- box ['401439/2048000', '803727/4096000', '3999/4000', '1']  interval_lower 206465763/549755813888
noncomputable def e1083 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1315032549818,0,true,196807426368,196807426432⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨883990705734,0,false,-239885769920,-239885769856⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1315260451521,0,true,196997960704,196997960768⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨883762804031,0,false,-240169271616,-240169271552⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1314978669587,0,true,196762375616,196762375680⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨884044585965,0,false,-239818755520,-239818755456⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539372232,0,true,27744064,27744128⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483883320,0,false,-27744832,-27744768⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627075,0,false,-704,-640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1315005604297,0,true,196784896704,196784896768⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨884017651255,0,false,-239852255488,-239852255424⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1315260460048,0,true,196997967808,196997967872⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨883762795504,0,false,-240169282240,-240169282176⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1057176869824,0,false,-43171314368,-43171314304⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1057276827576,0,false,-43067358720,-43067358656⟩
    { al := (401439/2048000), au := (803727/4096000), zl := (3999/4000), zu := 1,
      A := ⟨215520922042,215748823745⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196807426368,196807426432⟩ : DyadicInterval 40),(⟨-239885769920,-239885769856⟩ : DyadicInterval 40),(⟨740863317040,740863336370⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196997960704,196997960768⟩ : DyadicInterval 40),(⟨-240169271616,-240169271552⟩ : DyadicInterval 40),(⟨740818034597,740818053926⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196762375616,196762375680⟩ : DyadicInterval 40),(⟨-239818755520,-239818755456⟩ : DyadicInterval 40),(⟨740874015513,740874034842⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196997960704,196997960768⟩ : DyadicInterval 40),(⟨-240169271616,-240169271552⟩ : DyadicInterval 40),(⟨740818034597,740818053926⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,27744456⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27744064,27744128⟩ : DyadicInterval 40),(⟨-27744832,-27744768⟩ : DyadicInterval 40),(⟨762123383235,762123402564⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-704,0⟩ : DyadicInterval 40),(⟨762123383616,762123403232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨215493976521,215748832272⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196784896704,196784896768⟩ : DyadicInterval 40),(⟨-239852255488,-239852255424⟩ : DyadicInterval 40),(⟨740868667693,740868687023⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196997967808,196997967872⟩ : DyadicInterval 40),(⟨-240169282240,-240169282176⟩ : DyadicInterval 40),(⟨740818032922,740818052252⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-43171314368,-43067358656⟩ : DyadicInterval 40),(⟨783657062944,783709060064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨196807426368,196997960768⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-240169271616,-239885769856⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1083_ok : ecellOkT e1083 = true := by decide +kernel
theorem e1083_pos {a z : ℝ} (ha1 : ((401439/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((803727/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1083 e1083_ok ha1 ha2 hz1 hz2 hz

-- box ['803727/4096000', '25143/128000', '3999/4000', '1']  interval_lower 208660573/549755813888
noncomputable def e1084 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1315260451520,0,true,196997960704,196997960768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨883762804032,0,false,-240169271616,-240169271552⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1315488353223,0,true,197188462016,197188462080⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨883534902329,0,false,-240452846464,-240452846400⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1315206514314,0,true,196952870144,196952870208⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨883816741238,0,false,-240102169024,-240102168960⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539403239,0,true,27775104,27775168⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483852313,0,false,-27775872,-27775808⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627074,0,false,-704,-640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1315233477510,0,true,196975411136,196975411200⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨883789778042,0,false,-240135713088,-240135713024⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1315488361746,0,true,197188469120,197188469184⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨883534893806,0,false,-240452857088,-240452857024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1057087383740,0,false,-43264387904,-43264387840⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1057187458321,0,false,-43160301952,-43160301888⟩
    { al := (803727/4096000), au := (25143/128000), zl := (3999/4000), zu := 1,
      A := ⟨215748823744,215976725447⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196997960704,196997960768⟩ : DyadicInterval 40),(⟨-240169271616,-240169271552⟩ : DyadicInterval 40),(⟨740818034597,740818053927⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197188462016,197188462080⟩ : DyadicInterval 40),(⟨-240452846464,-240452846400⟩ : DyadicInterval 40),(⟨740772703044,740772722374⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196952870144,196952870208⟩ : DyadicInterval 40),(⟨-240102169024,-240102168960⟩ : DyadicInterval 40),(⟨740828755985,740828775315⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197188462016,197188462080⟩ : DyadicInterval 40),(⟨-240452846464,-240452846400⟩ : DyadicInterval 40),(⟨740772703044,740772722374⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,27775463⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27775104,27775168⟩ : DyadicInterval 40),(⟨-27775872,-27775808⟩ : DyadicInterval 40),(⟨762123383234,762123402563⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-704,0⟩ : DyadicInterval 40),(⟨762123383616,762123403232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨215721849734,215976733970⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨196975411136,196975411200⟩ : DyadicInterval 40),(⟨-240135713088,-240135713024⟩ : DyadicInterval 40),(⟨740823396712,740823416042⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197188469120,197188469184⟩ : DyadicInterval 40),(⟨-240452857088,-240452857024⟩ : DyadicInterval 40),(⟨740772701367,740772720696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-43264387904,-43160301888⟩ : DyadicInterval 40),(⟨783703534560,783755596832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨196997960704,197188462080⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-240452846464,-240169271552⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1084_ok : ecellOkT e1084 = true := by decide +kernel
theorem e1084_pos {a z : ℝ} (ha1 : ((803727/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((25143/128000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1084 e1084_ok ha1 ha2 hz1 hz2 hz

-- box ['25143/128000', '32217/163840', '999/1000', '3997/4000']  interval_lower 212092659/549755813888
noncomputable def e1085 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1315488353222,0,true,197188462016,197188462080⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨883534902330,0,false,-240452846464,-240452846400⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1315716254925,0,true,197378930368,197378930432⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨883307000627,0,false,-240736494464,-240736494400⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1315272376496,0,true,197007929536,197007929600⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨883750879056,0,false,-240184107904,-240184107840⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1315554101455,0,true,197243414336,197243414400⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨883469154097,0,false,-240534669632,-240534669568⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594950716,0,true,83319744,83319808⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099428304836,0,false,-83326144,-83326080⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099622850480,0,true,111217024,111217088⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099400405072,0,false,-111228352,-111228288⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511616525,0,false,-11264,-11200⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621462,0,false,-6336,-6272⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1315380360873,0,true,197098196160,197098196224⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨883642894679,0,false,-240318464000,-240318463936⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1315635187572,0,true,197311182272,197311182336⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨883388067980,0,false,-240635589120,-240635589056⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1057029682229,0,false,-43324406784,-43324406720⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1057129802290,0,false,-43220267840,-43220267776⟩
    { al := (25143/128000), au := (32217/163840), zl := (999/1000), zu := (3997/4000),
      A := ⟨215976725446,216204627149⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197188462016,197188462080⟩ : DyadicInterval 40),(⟨-240452846464,-240452846400⟩ : DyadicInterval 40),(⟨740772703045,740772722374⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197378930368,197378930432⟩ : DyadicInterval 40),(⟨-240736494464,-240736494400⟩ : DyadicInterval 40),(⟨740727322332,740727341661⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197007929536,197007929600⟩ : DyadicInterval 40),(⟨-240184107904,-240184107840⟩ : DyadicInterval 40),(⟨740815663837,740815683167⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197243414336,197243414400⟩ : DyadicInterval 40),(⟨-240534669632,-240534669568⟩ : DyadicInterval 40),(⟨740759616031,740759635360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨83322940,111222704⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨83319744,83319808⟩ : DyadicInterval 40),(⟨-83326144,-83326080⟩ : DyadicInterval 40),(⟨762123380437,762123399766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨111217024,111217088⟩ : DyadicInterval 40),(⟨-111228352,-111228288⟩ : DyadicInterval 40),(⟨762123377964,762123397294⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-11264,-6272⟩ : DyadicInterval 40),(⟨762123386752,762123408512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨215868733097,216123559796⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197098196160,197098196224⟩ : DyadicInterval 40),(⟨-240318464000,-240318463936⟩ : DyadicInterval 40),(⟨740794189738,740794209067⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197311182272,197311182336⟩ : DyadicInterval 40),(⟨-240635589120,-240635589056⟩ : DyadicInterval 40),(⟨740743470438,740743489767⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-43324406784,-43220267776⟩ : DyadicInterval 40),(⟨783733517504,783785606272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨197188462016,197378930432⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-240736494464,-240452846400⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1085_ok : ecellOkT e1085 = true := by decide +kernel
theorem e1085_pos {a z : ℝ} (ha1 : ((25143/128000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((32217/163840 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1085 e1085_ok ha1 ha2 hz1 hz2 hz

-- box ['32217/163840', '403137/2048000', '999/1000', '3997/4000']  interval_lower 428620401/1099511627776
noncomputable def e1086 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1315716254924,0,true,197378930368,197378930432⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨883307000628,0,false,-240736494464,-240736494400⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1315944156627,0,true,197569365696,197569365760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨883079098925,0,false,-241020215616,-241020215552⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1315500050296,0,true,197198238656,197198238720⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨883523205256,0,false,-240467402944,-240467402880⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1315781832231,0,true,197433730304,197433730368⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨883241423321,0,false,-240818125952,-240818125888⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099595043745,0,true,83412800,83412864⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099428211807,0,false,-83419136,-83419072⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099622974543,0,true,111341120,111341184⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099400281009,0,false,-111352448,-111352384⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511616499,0,false,-11328,-11264⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621448,0,false,-6336,-6272⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1315608148625,0,true,197288584896,197288584960⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨883415106927,0,false,-240601935488,-240601935424⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1315863003813,0,true,197501557952,197501558016⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨883160251739,0,false,-240919177856,-240919177792⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1056940074433,0,false,-43417619840,-43417619776⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1057040311291,0,false,-43313350592,-43313350528⟩
    { al := (32217/163840), au := (403137/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨216204627148,216432528851⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197378930368,197378930432⟩ : DyadicInterval 40),(⟨-240736494464,-240736494400⟩ : DyadicInterval 40),(⟨740727322332,740727341661⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197569365696,197569365760⟩ : DyadicInterval 40),(⟨-241020215616,-241020215552⟩ : DyadicInterval 40),(⟨740681892486,740681911815⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197198238656,197198238720⟩ : DyadicInterval 40),(⟨-240467402944,-240467402880⟩ : DyadicInterval 40),(⟨740770375054,740770394384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197433730304,197433730368⟩ : DyadicInterval 40),(⟨-240818125952,-240818125888⟩ : DyadicInterval 40),(⟨740714255222,740714274552⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨83415969,111346767⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨83412800,83412864⟩ : DyadicInterval 40),(⟨-83419136,-83419072⟩ : DyadicInterval 40),(⟨762123380391,762123399720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨111341120,111341184⟩ : DyadicInterval 40),(⟨-111352448,-111352384⟩ : DyadicInterval 40),(⟨762123377939,762123397269⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-11328,-6272⟩ : DyadicInterval 40),(⟨762123386752,762123408544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨216096520849,216351376037⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197288584896,197288584960⟩ : DyadicInterval 40),(⟨-240601935488,-240601935424⟩ : DyadicInterval 40),(⟨740748855003,740748874333⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197501557952,197501558016⟩ : DyadicInterval 40),(⟨-240919177856,-240919177792⟩ : DyadicInterval 40),(⟨740698075100,740698094430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-43417619840,-43313350528⟩ : DyadicInterval 40),(⟨783780058880,783832212800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨197378930368,197569365760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-241020215616,-240736494400⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1086_ok : ecellOkT e1086 = true := by decide +kernel
theorem e1086_pos {a z : ℝ} (ha1 : ((32217/163840 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((403137/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1086 e1086_ok ha1 ha2 hz1 hz2 hz

-- box ['25143/128000', '32217/163840', '3997/4000', '1999/2000']  interval_lower 423366969/1099511627776
noncomputable def e1087 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1315488353222,0,true,197188462016,197188462080⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨883534902330,0,false,-240452846464,-240452846400⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1315716254925,0,true,197378930368,197378930432⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨883307000627,0,false,-240736494464,-240736494400⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1315326370677,0,true,197053065408,197053065472⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨883696884875,0,false,-240251286400,-240251286336⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1315608152612,0,true,197288588224,197288588288⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨883415102940,0,false,-240601940480,-240601940416⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567176721,0,true,55547520,55547584⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456078831,0,false,-55550400,-55550336⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099595045474,0,true,83414528,83414592⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099428210078,0,false,-83420864,-83420800⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621447,0,false,-6336,-6272⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624970,0,false,-2816,-2752⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1315407357294,0,true,197120761920,197120761984⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨883615898258,0,false,-240352056000,-240352055936⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1315662212675,0,true,197333767680,197333767744⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨883361042877,0,false,-240669226496,-240669226432⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1057019057282,0,false,-43335458816,-43335458752⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1057119201133,0,false,-43231294080,-43231294016⟩
    { al := (25143/128000), au := (32217/163840), zl := (3997/4000), zu := (1999/2000),
      A := ⟨215976725446,216204627149⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197188462016,197188462080⟩ : DyadicInterval 40),(⟨-240452846464,-240452846400⟩ : DyadicInterval 40),(⟨740772703045,740772722374⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197378930368,197378930432⟩ : DyadicInterval 40),(⟨-240736494464,-240736494400⟩ : DyadicInterval 40),(⟨740727322332,740727341661⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197053065408,197053065472⟩ : DyadicInterval 40),(⟨-240251286400,-240251286336⟩ : DyadicInterval 40),(⟨740804927797,740804947127⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197288588224,197288588288⟩ : DyadicInterval 40),(⟨-240601940480,-240601940416⟩ : DyadicInterval 40),(⟨740748854224,740748873553⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55548945,83417698⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55547520,55547584⟩ : DyadicInterval 40),(⟨-55550400,-55550336⟩ : DyadicInterval 40),(⟨762123382185,762123401514⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨83414528,83414592⟩ : DyadicInterval 40),(⟨-83420864,-83420800⟩ : DyadicInterval 40),(⟨762123380391,762123399720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6336,-2752⟩ : DyadicInterval 40),(⟨762123384992,762123406048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨215895729518,216150584899⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197120761920,197120761984⟩ : DyadicInterval 40),(⟨-240352056000,-240352055936⟩ : DyadicInterval 40),(⟨740788819433,740788838762⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197333767680,197333767744⟩ : DyadicInterval 40),(⟨-240669226496,-240669226432⟩ : DyadicInterval 40),(⟨740738087876,740738107206⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-43335458816,-43231294016⟩ : DyadicInterval 40),(⟨783739030624,783791132288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨197188462016,197378930432⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-240736494464,-240452846400⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1087_ok : ecellOkT e1087 = true := by decide +kernel
theorem e1087_pos {a z : ℝ} (ha1 : ((25143/128000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((32217/163840 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1087 e1087_ok ha1 ha2 hz1 hz2 hz

-- box ['32217/163840', '403137/2048000', '3997/4000', '1999/2000']  interval_lower 427798915/1099511627776
noncomputable def e1088 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1315716254924,0,true,197378930368,197378930432⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨883307000628,0,false,-240736494464,-240736494400⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1315944156627,0,true,197569365696,197569365760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨883079098925,0,false,-241020215616,-241020215552⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1315554101453,0,true,197243414336,197243414400⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨883469154099,0,false,-240534669632,-240534669568⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1315835940363,0,true,197478944000,197478944064⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨883187315189,0,false,-240885485056,-240885484992⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567238740,0,true,55609536,55609600⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456016812,0,false,-55612416,-55612352⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099595138524,0,true,83507520,83507584⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099428117028,0,false,-83513920,-83513856⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621433,0,false,-6400,-6336⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624964,0,false,-2816,-2752⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1315635173534,0,true,197311170560,197311170624⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨883388082018,0,false,-240635571648,-240635571584⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1315890057405,0,true,197524163200,197524163264⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨883133198147,0,false,-240952859392,-240952859328⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1056929427073,0,false,-43428696128,-43428696064⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1057029687749,0,false,-43324401024,-43324400960⟩
    { al := (32217/163840), au := (403137/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨216204627148,216432528851⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197378930368,197378930432⟩ : DyadicInterval 40),(⟨-240736494464,-240736494400⟩ : DyadicInterval 40),(⟨740727322332,740727341661⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197569365696,197569365760⟩ : DyadicInterval 40),(⟨-241020215616,-241020215552⟩ : DyadicInterval 40),(⟨740681892486,740681911815⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197243414336,197243414400⟩ : DyadicInterval 40),(⟨-240534669632,-240534669568⟩ : DyadicInterval 40),(⟨740759616031,740759635361⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197478944000,197478944064⟩ : DyadicInterval 40),(⟨-240885485056,-240885484992⟩ : DyadicInterval 40),(⟨740703470394,740703489723⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55610964,83510748⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55609536,55609600⟩ : DyadicInterval 40),(⟨-55612416,-55612352⟩ : DyadicInterval 40),(⟨762123382179,762123401508⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨83507520,83507584⟩ : DyadicInterval 40),(⟨-83513920,-83513856⟩ : DyadicInterval 40),(⟨762123380408,762123399738⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6400,-2752⟩ : DyadicInterval 40),(⟨762123384992,762123406080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨216123545758,216378429629⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197311170560,197311170624⟩ : DyadicInterval 40),(⟨-240635571648,-240635571584⟩ : DyadicInterval 40),(⟨740743473222,740743492551⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197524163200,197524163264⟩ : DyadicInterval 40),(⟨-240952859392,-240952859328⟩ : DyadicInterval 40),(⟨740692681072,740692700402⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-43428696128,-43324400960⟩ : DyadicInterval 40),(⟨783785584096,783837750944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨197378930368,197569365760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-241020215616,-240736494400⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1088_ok : ecellOkT e1088 = true := by decide +kernel
theorem e1088_pos {a z : ℝ} (ha1 : ((32217/163840 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((403137/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1088 e1088_ok ha1 ha2 hz1 hz2 hz

-- box ['403137/2048000', '807123/4096000', '999/1000', '3997/4000']  interval_lower 54134245/137438953472
noncomputable def e1089 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1315944156626,0,true,197569365696,197569365760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨883079098926,0,false,-241020215616,-241020215552⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1316172058330,0,true,197759768064,197759768128⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨882851197222,0,false,-241304010048,-241304009984⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1315727724097,0,true,197388514816,197388514880⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨883295531455,0,false,-240750771008,-240750770944⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1316009563008,0,true,197624013376,197624013440⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨883013692544,0,false,-241101655360,-241101655296⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099595136791,0,true,83505792,83505856⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099428118761,0,false,-83512192,-83512128⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099623098629,0,true,111465152,111465216⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099400156923,0,false,-111476544,-111476480⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511616474,0,false,-11328,-11264⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621434,0,false,-6400,-6336⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1315835936374,0,true,197478940672,197478940736⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨883187319178,0,false,-240885480064,-240885480000⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1316090820059,0,true,197691900672,197691900736⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨882932435493,0,false,-241202839744,-241202839680⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1056850372228,0,false,-43510939072,-43510939008⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1056950725910,0,false,-43406539392,-43406539328⟩
    { al := (403137/2048000), au := (807123/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨216432528850,216660430554⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197569365696,197569365760⟩ : DyadicInterval 40),(⟨-241020215616,-241020215552⟩ : DyadicInterval 40),(⟨740681892486,740681911815⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197759768064,197759768128⟩ : DyadicInterval 40),(⟨-241304010048,-241304009984⟩ : DyadicInterval 40),(⟨740636413505,740636432835⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197388514816,197388514880⟩ : DyadicInterval 40),(⟨-240750771008,-240750770944⟩ : DyadicInterval 40),(⟨740725037255,740725056584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197624013376,197624013440⟩ : DyadicInterval 40),(⟨-241101655360,-241101655296⟩ : DyadicInterval 40),(⟨740668845321,740668864651⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨83509015,111470853⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨83505792,83505856⟩ : DyadicInterval 40),(⟨-83512192,-83512128⟩ : DyadicInterval 40),(⟨762123380409,762123399738⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨111465152,111465216⟩ : DyadicInterval 40),(⟨-111476544,-111476480⟩ : DyadicInterval 40),(⟨762123377946,762123397276⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-11328,-6336⟩ : DyadicInterval 40),(⟨762123386784,762123408544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨216324308598,216579192283⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197478940672,197478940736⟩ : DyadicInterval 40),(⟨-240885480064,-240885480000⟩ : DyadicInterval 40),(⟨740703471175,740703490505⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197691900672,197691900736⟩ : DyadicInterval 40),(⟨-241202839744,-241202839680⟩ : DyadicInterval 40),(⟨740652630656,740652649985⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-43510939072,-43406539328⟩ : DyadicInterval 40),(⟨783826653280,783878872416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨197569365696,197759768128⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-241304010048,-241020215552⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1089_ok : ecellOkT e1089 = true := by decide +kernel
theorem e1089_pos {a z : ℝ} (ha1 : ((403137/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((807123/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1089 e1089_ok ha1 ha2 hz1 hz2 hz

-- box ['807123/4096000', '201993/1024000', '999/1000', '3997/4000']  interval_lower 218772847/549755813888
noncomputable def e1090 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1316172058329,0,true,197759768064,197759768128⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨882851197223,0,false,-241304010048,-241304009984⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1316399960032,0,true,197950137472,197950137536⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨882623295520,0,false,-241587877696,-241587877632⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1315955397898,0,true,197578758080,197578758144⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨883067857654,0,false,-241034212096,-241034212032⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1316237293783,0,true,197814263488,197814263552⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨882785961769,0,false,-241385257920,-241385257856⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099595229853,0,true,83598848,83598912⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099428025699,0,false,-83605312,-83605248⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099623222738,0,true,111589248,111589312⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099400032814,0,false,-111600640,-111600576⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511616449,0,false,-11328,-11264⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621420,0,false,-6400,-6336⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1316063724126,0,true,197669263488,197669263552⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨882959531426,0,false,-241169097792,-241169097728⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1316318636302,0,true,197882210432,197882210496⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨882704619250,0,false,-241486574848,-241486574784⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1056760575619,0,false,-43604364416,-43604364352⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1056861046147,0,false,-43499834304,-43499834240⟩
    { al := (807123/4096000), au := (201993/1024000), zl := (999/1000), zu := (3997/4000),
      A := ⟨216660430553,216888332256⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197759768064,197759768128⟩ : DyadicInterval 40),(⟨-241304010048,-241304009984⟩ : DyadicInterval 40),(⟨740636413505,740636432835⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197950137472,197950137536⟩ : DyadicInterval 40),(⟨-241587877696,-241587877632⟩ : DyadicInterval 40),(⟨740590885353,740590904683⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197578758080,197578758144⟩ : DyadicInterval 40),(⟨-241034212096,-241034212032⟩ : DyadicInterval 40),(⟨740679650389,740679669719⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197814263488,197814263552⟩ : DyadicInterval 40),(⟨-241385257920,-241385257856⟩ : DyadicInterval 40),(⟨740623386379,740623405709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨83602077,111594962⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨83598848,83598912⟩ : DyadicInterval 40),(⟨-83605312,-83605248⟩ : DyadicInterval 40),(⟨762123380427,762123399756⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨111589248,111589312⟩ : DyadicInterval 40),(⟨-111600640,-111600576⟩ : DyadicInterval 40),(⟨762123377921,762123397251⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-11328,-6336⟩ : DyadicInterval 40),(⟨762123386784,762123408544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨216552096350,216807008526⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197669263488,197669263552⟩ : DyadicInterval 40),(⟨-241169097792,-241169097728⟩ : DyadicInterval 40),(⟨740658038266,740658057595⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197882210432,197882210496⟩ : DyadicInterval 40),(⟨-241486574848,-241486574784⟩ : DyadicInterval 40),(⟨740607137118,740607156448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-43604364416,-43499834240⟩ : DyadicInterval 40),(⟨783873300736,783925585088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨197759768064,197950137536⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-241587877696,-241304009984⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1090_ok : ecellOkT e1090 = true := by decide +kernel
theorem e1090_pos {a z : ℝ} (ha1 : ((807123/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((201993/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1090 e1090_ok ha1 ha2 hz1 hz2 hz

-- box ['403137/2048000', '807123/4096000', '3997/4000', '1999/2000']  interval_lower 432249497/1099511627776
noncomputable def e1091 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1315944156626,0,true,197569365696,197569365760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨883079098926,0,false,-241020215616,-241020215552⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1316172058330,0,true,197759768064,197759768128⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨882851197222,0,false,-241304010048,-241304009984⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1315781832229,0,true,197433730304,197433730368⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨883241423323,0,false,-240818125952,-240818125888⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1316063728115,0,true,197669266816,197669266880⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨882959527437,0,false,-241169102784,-241169102720⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567300772,0,true,55671552,55671616⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455954780,0,false,-55674432,-55674368⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099595231590,0,true,83600576,83600640⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099428023962,0,false,-83607040,-83606976⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621418,0,false,-6400,-6336⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624958,0,false,-2880,-2816⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1315862989771,0,true,197501546240,197501546304⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨883160265781,0,false,-240919160320,-240919160256⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1316117902134,0,true,197714525824,197714525888⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨882905353418,0,false,-241236565440,-241236565376⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1056839702435,0,false,-43522039616,-43522039552⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1056940079960,0,false,-43417614080,-43417614016⟩
    { al := (403137/2048000), au := (807123/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨216432528850,216660430554⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197569365696,197569365760⟩ : DyadicInterval 40),(⟨-241020215616,-241020215552⟩ : DyadicInterval 40),(⟨740681892486,740681911815⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197759768064,197759768128⟩ : DyadicInterval 40),(⟨-241304010048,-241304009984⟩ : DyadicInterval 40),(⟨740636413505,740636432835⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197433730304,197433730368⟩ : DyadicInterval 40),(⟨-240818125952,-240818125888⟩ : DyadicInterval 40),(⟨740714255223,740714274552⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197669266816,197669266880⟩ : DyadicInterval 40),(⟨-241169102784,-241169102720⟩ : DyadicInterval 40),(⟨740658037483,740658056812⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55672996,83603814⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55671552,55671616⟩ : DyadicInterval 40),(⟨-55674432,-55674368⟩ : DyadicInterval 40),(⟨762123382172,762123401502⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨83600576,83600640⟩ : DyadicInterval 40),(⟨-83607040,-83606976⟩ : DyadicInterval 40),(⟨762123380426,762123399756⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6400,-2816⟩ : DyadicInterval 40),(⟨762123385024,762123406080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨216351361995,216606274358⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197501546240,197501546304⟩ : DyadicInterval 40),(⟨-240919160320,-240919160256⟩ : DyadicInterval 40),(⟨740698077866,740698097195⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197714525824,197714525888⟩ : DyadicInterval 40),(⟨-241236565440,-241236565376⟩ : DyadicInterval 40),(⟨740647225096,740647244426⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-43522039616,-43417614016⟩ : DyadicInterval 40),(⟨783832190624,783884422688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨197569365696,197759768128⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-241304010048,-241020215552⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1091_ok : ecellOkT e1091 = true := by decide +kernel
theorem e1091_pos {a z : ℝ} (ha1 : ((403137/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((807123/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1091 e1091_ok ha1 ha2 hz1 hz2 hz

-- box ['807123/4096000', '201993/1024000', '3997/4000', '1999/2000']  interval_lower 218358903/549755813888
noncomputable def e1092 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1316172058329,0,true,197759768064,197759768128⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨882851197223,0,false,-241304010048,-241304009984⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1316399960032,0,true,197950137472,197950137536⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨882623295520,0,false,-241587877696,-241587877632⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1316009563006,0,true,197624013376,197624013440⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨883013692546,0,false,-241101655360,-241101655296⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1316291515867,0,true,197859556672,197859556736⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨882731739685,0,false,-241452793728,-241452793664⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567362815,0,true,55733568,55733632⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455892737,0,false,-55736512,-55736448⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099595324674,0,true,83693696,83693760⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099427930878,0,false,-83700096,-83700032⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621404,0,false,-6400,-6336⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624951,0,false,-2880,-2816⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1316090806010,0,true,197691888896,197691888960⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨882932449542,0,false,-241202822272,-241202822208⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1316345746862,0,true,197904855424,197904855488⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨882677508690,0,false,-241520344768,-241520344704⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1056749883368,0,false,-43615489280,-43615489216⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1056850377764,0,false,-43510933312,-43510933248⟩
    { al := (807123/4096000), au := (201993/1024000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨216660430553,216888332256⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197759768064,197759768128⟩ : DyadicInterval 40),(⟨-241304010048,-241304009984⟩ : DyadicInterval 40),(⟨740636413505,740636432835⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197950137472,197950137536⟩ : DyadicInterval 40),(⟨-241587877696,-241587877632⟩ : DyadicInterval 40),(⟨740590885353,740590904683⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197624013376,197624013440⟩ : DyadicInterval 40),(⟨-241101655360,-241101655296⟩ : DyadicInterval 40),(⟨740668845322,740668864651⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197859556672,197859556736⟩ : DyadicInterval 40),(⟨-241452793728,-241452793664⟩ : DyadicInterval 40),(⟨740612555504,740612574834⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55735039,83696898⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55733568,55733632⟩ : DyadicInterval 40),(⟨-55736512,-55736448⟩ : DyadicInterval 40),(⟨762123382198,762123401527⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨83693696,83693760⟩ : DyadicInterval 40),(⟨-83700096,-83700032⟩ : DyadicInterval 40),(⟨762123380380,762123399710⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6400,-2816⟩ : DyadicInterval 40),(⟨762123385024,762123406080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨216579178234,216834119086⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197691888896,197691888960⟩ : DyadicInterval 40),(⟨-241202822272,-241202822208⟩ : DyadicInterval 40),(⟨740652633492,740652652822⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197904855424,197904855488⟩ : DyadicInterval 40),(⟨-241520344768,-241520344704⟩ : DyadicInterval 40),(⟨740601720066,740601739395⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-43615489280,-43510933248⟩ : DyadicInterval 40),(⟨783878850240,783931147520⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨197759768064,197950137536⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-241587877696,-241304009984⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1092_ok : ecellOkT e1092 = true := by decide +kernel
theorem e1092_pos {a z : ℝ} (ha1 : ((807123/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((201993/1024000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1092 e1092_ok ha1 ha2 hz1 hz2 hz

-- box ['25143/128000', '32217/163840', '1999/2000', '3999/4000']  interval_lower 105636981/274877906944
noncomputable def e1093 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1315488353222,0,true,197188462016,197188462080⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨883534902330,0,false,-240452846464,-240452846400⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1315716254925,0,true,197378930368,197378930432⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨883307000627,0,false,-240736494464,-240736494400⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1315380364859,0,true,197098199488,197098199552⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨883642890693,0,false,-240318468992,-240318468928⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1315662203769,0,true,197333760192,197333760256⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨883361051783,0,false,-240669215424,-240669215360⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539402321,0,true,27774144,27774208⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483853231,0,false,-27774912,-27774848⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567240065,0,true,55610880,55610944⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456015487,0,false,-55613696,-55613632⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624963,0,false,-2816,-2752⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627075,0,false,-704,-640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1315434353912,0,true,197143327360,197143327424⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨883588901640,0,false,-240385649280,-240385649216⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1315689237965,0,true,197356352704,197356352768⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨883334017587,0,false,-240702865152,-240702865088⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1057008430932,0,false,-43346512384,-43346512320⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1057108598573,0,false,-43242321856,-43242321792⟩
    { al := (25143/128000), au := (32217/163840), zl := (1999/2000), zu := (3999/4000),
      A := ⟨215976725446,216204627149⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197188462016,197188462080⟩ : DyadicInterval 40),(⟨-240452846464,-240452846400⟩ : DyadicInterval 40),(⟨740772703045,740772722374⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197378930368,197378930432⟩ : DyadicInterval 40),(⟨-240736494464,-240736494400⟩ : DyadicInterval 40),(⟨740727322332,740727341661⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197098199488,197098199552⟩ : DyadicInterval 40),(⟨-240318468992,-240318468928⟩ : DyadicInterval 40),(⟨740794188960,740794208289⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197333760192,197333760256⟩ : DyadicInterval 40),(⟨-240669215424,-240669215360⟩ : DyadicInterval 40),(⟨740738089683,740738109012⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨27774545,55612289⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27774144,27774208⟩ : DyadicInterval 40),(⟨-27774912,-27774848⟩ : DyadicInterval 40),(⟨762123383234,762123402563⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55610880,55610944⟩ : DyadicInterval 40),(⟨-55613696,-55613632⟩ : DyadicInterval 40),(⟨762123382147,762123401476⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2816,-640⟩ : DyadicInterval 40),(⟨762123383936,762123404288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨215922726136,216177610189⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197143327360,197143327424⟩ : DyadicInterval 40),(⟨-240385649280,-240385649216⟩ : DyadicInterval 40),(⟨740783448415,740783467745⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197356352704,197356352768⟩ : DyadicInterval 40),(⟨-240702865152,-240702865088⟩ : DyadicInterval 40),(⟨740732704640,740732723970⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-43346512384,-43242321792⟩ : DyadicInterval 40),(⟨783744544512,783796659072⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨197188462016,197378930432⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-240736494464,-240452846400⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1093_ok : ecellOkT e1093 = true := by decide +kernel
theorem e1093_pos {a z : ℝ} (ha1 : ((25143/128000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((32217/163840 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1093 e1093_ok ha1 ha2 hz1 hz2 hz

-- box ['32217/163840', '403137/2048000', '1999/2000', '3999/4000']  interval_lower 6671513/17179869184
noncomputable def e1094 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1315716254924,0,true,197378930368,197378930432⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨883307000628,0,false,-240736494464,-240736494400⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1315944156627,0,true,197569365696,197569365760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨883079098925,0,false,-241020215616,-241020215552⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1315608152610,0,true,197288588224,197288588288⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨883415102942,0,false,-240601940480,-240601940416⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1315890048495,0,true,197524155776,197524155840⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨883133207057,0,false,-240952848256,-240952848192⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539433331,0,true,27805184,27805248⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483822221,0,false,-27805952,-27805888⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567302099,0,true,55672896,55672960⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455953453,0,false,-55675776,-55675712⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624956,0,false,-2880,-2816⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627073,0,false,-704,-640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1315662198637,0,true,197333755904,197333755968⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨883361056915,0,false,-240669209024,-240669208960⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1315917111184,0,true,197546768192,197546768256⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨883106144368,0,false,-240986542144,-240986542080⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1056918778309,0,false,-43439773952,-43439773888⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1057019062802,0,false,-43335453056,-43335452992⟩
    { al := (32217/163840), au := (403137/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨216204627148,216432528851⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197378930368,197378930432⟩ : DyadicInterval 40),(⟨-240736494464,-240736494400⟩ : DyadicInterval 40),(⟨740727322332,740727341661⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197569365696,197569365760⟩ : DyadicInterval 40),(⟨-241020215616,-241020215552⟩ : DyadicInterval 40),(⟨740681892486,740681911815⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197288588224,197288588288⟩ : DyadicInterval 40),(⟨-240601940480,-240601940416⟩ : DyadicInterval 40),(⟨740748854224,740748873554⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197524155776,197524155840⟩ : DyadicInterval 40),(⟨-240952848256,-240952848192⟩ : DyadicInterval 40),(⟨740692682819,740692702149⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨27805555,55674323⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27805184,27805248⟩ : DyadicInterval 40),(⟨-27805952,-27805888⟩ : DyadicInterval 40),(⟨762123383232,762123402561⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55672896,55672960⟩ : DyadicInterval 40),(⟨-55675776,-55675712⟩ : DyadicInterval 40),(⟨762123382172,762123401501⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2880,-640⟩ : DyadicInterval 40),(⟨762123383936,762123404320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨216150570861,216405483408⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197333755904,197333755968⟩ : DyadicInterval 40),(⟨-240669209024,-240669208960⟩ : DyadicInterval 40),(⟨740738090700,740738110029⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197546768192,197546768256⟩ : DyadicInterval 40),(⟨-240986542144,-240986542080⟩ : DyadicInterval 40),(⟨740687286263,740687305592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-43439773952,-43335452992⟩ : DyadicInterval 40),(⟨783791110112,783843289856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨197378930368,197569365760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-241020215616,-240736494400⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1094_ok : ecellOkT e1094 = true := by decide +kernel
theorem e1094_pos {a z : ℝ} (ha1 : ((32217/163840 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((403137/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1094 e1094_ok ha1 ha2 hz1 hz2 hz

-- box ['25143/128000', '32217/163840', '3999/4000', '1']  interval_lower 52716047/137438953472
noncomputable def e1095 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1315488353222,0,true,197188462016,197188462080⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨883534902330,0,false,-240452846464,-240452846400⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1315716254925,0,true,197378930368,197378930432⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨883307000627,0,false,-240736494464,-240736494400⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1315434359040,0,true,197143331648,197143331712⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨883588896512,0,false,-240385655680,-240385655616⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539434251,0,true,27806080,27806144⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483821301,0,false,-27806848,-27806784⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627072,0,false,-768,-704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1315461350715,0,true,197165892544,197165892608⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨883561904837,0,false,-240419243840,-240419243776⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1315716263450,0,true,197378937472,197378937536⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨883306992102,0,false,-240736505088,-240736505024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1056997803177,0,false,-43357567552,-43357567488⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1057097994615,0,false,-43253351232,-43253351168⟩
    { al := (25143/128000), au := (32217/163840), zl := (3999/4000), zu := 1,
      A := ⟨215976725446,216204627149⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197188462016,197188462080⟩ : DyadicInterval 40),(⟨-240452846464,-240452846400⟩ : DyadicInterval 40),(⟨740772703045,740772722374⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197378930368,197378930432⟩ : DyadicInterval 40),(⟨-240736494464,-240736494400⟩ : DyadicInterval 40),(⟨740727322332,740727341661⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197143331648,197143331712⟩ : DyadicInterval 40),(⟨-240385655680,-240385655616⟩ : DyadicInterval 40),(⟨740783447401,740783466731⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197378930368,197378930432⟩ : DyadicInterval 40),(⟨-240736494464,-240736494400⟩ : DyadicInterval 40),(⟨740727322332,740727341661⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,27806475⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27806080,27806144⟩ : DyadicInterval 40),(⟨-27806848,-27806784⟩ : DyadicInterval 40),(⟨762123383232,762123402561⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-768,0⟩ : DyadicInterval 40),(⟨762123383616,762123403264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨215949722939,216204635674⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197165892544,197165892608⟩ : DyadicInterval 40),(⟨-240419243840,-240419243776⟩ : DyadicInterval 40),(⟨740778076650,740778095979⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197378937472,197378937536⟩ : DyadicInterval 40),(⟨-240736505088,-240736505024⟩ : DyadicInterval 40),(⟨740727320650,740727339980⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-43357567552,-43253351168⟩ : DyadicInterval 40),(⟨783750059200,783802186656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨197188462016,197378930432⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-240736494464,-240452846400⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1095_ok : ecellOkT e1095 = true := by decide +kernel
theorem e1095_pos {a z : ℝ} (ha1 : ((25143/128000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((32217/163840 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1095 e1095_ok ha1 ha2 hz1 hz2 hz

-- box ['32217/163840', '403137/2048000', '3999/4000', '1']  interval_lower 426154149/1099511627776
noncomputable def e1096 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1315716254924,0,true,197378930368,197378930432⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨883307000628,0,false,-240736494464,-240736494400⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1315944156627,0,true,197569365696,197569365760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨883079098925,0,false,-241020215616,-241020215552⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1315662203767,0,true,197333760192,197333760256⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨883361051785,0,false,-240669215424,-240669215360⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539465270,0,true,27837120,27837184⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483790282,0,false,-27837888,-27837824⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627071,0,false,-768,-704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1315689223925,0,true,197356340992,197356341056⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨883334031627,0,false,-240702847680,-240702847616⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1315944165153,0,true,197569372800,197569372864⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨883079090399,0,false,-241020226240,-241020226176⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1056908128138,0,false,-43450853376,-43450853312⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1057008436454,0,false,-43346506624,-43346506560⟩
    { al := (32217/163840), au := (403137/2048000), zl := (3999/4000), zu := 1,
      A := ⟨216204627148,216432528851⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197378930368,197378930432⟩ : DyadicInterval 40),(⟨-240736494464,-240736494400⟩ : DyadicInterval 40),(⟨740727322332,740727341661⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197569365696,197569365760⟩ : DyadicInterval 40),(⟨-241020215616,-241020215552⟩ : DyadicInterval 40),(⟨740681892486,740681911815⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197333760192,197333760256⟩ : DyadicInterval 40),(⟨-240669215424,-240669215360⟩ : DyadicInterval 40),(⟨740738089683,740738109013⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197569365696,197569365760⟩ : DyadicInterval 40),(⟨-241020215616,-241020215552⟩ : DyadicInterval 40),(⟨740681892486,740681911815⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,27837494⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27837120,27837184⟩ : DyadicInterval 40),(⟨-27837888,-27837824⟩ : DyadicInterval 40),(⟨762123383231,762123402560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-768,0⟩ : DyadicInterval 40),(⟨762123383616,762123403264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨216177596149,216432537377⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197356340992,197356341056⟩ : DyadicInterval 40),(⟨-240702847680,-240702847616⟩ : DyadicInterval 40),(⟨740732707426,740732726756⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197569372800,197569372864⟩ : DyadicInterval 40),(⟨-241020226240,-241020226176⟩ : DyadicInterval 40),(⟨740681890800,740681910130⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-43450853376,-43346506560⟩ : DyadicInterval 40),(⟨783796636896,783848829568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨197378930368,197569365760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-241020215616,-240736494400⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1096_ok : ecellOkT e1096 = true := by decide +kernel
theorem e1096_pos {a z : ℝ} (ha1 : ((32217/163840 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((403137/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1096 e1096_ok ha1 ha2 hz1 hz2 hz

-- box ['403137/2048000', '807123/4096000', '1999/2000', '3999/4000']  interval_lower 215712073/549755813888
noncomputable def e1097 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1315944156626,0,true,197569365696,197569365760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨883079098926,0,false,-241020215616,-241020215552⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1316172058330,0,true,197759768064,197759768128⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨882851197222,0,false,-241304010048,-241304009984⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1315835940361,0,true,197478944000,197478944064⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨883187315191,0,false,-240885485056,-240885484992⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1316117893223,0,true,197714518336,197714518400⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨882905362329,0,false,-241236554368,-241236554304⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539464348,0,true,27836160,27836224⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483791204,0,false,-27836928,-27836864⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567364145,0,true,55734912,55734976⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455891407,0,false,-55737792,-55737728⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624950,0,false,-2880,-2816⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627072,0,false,-768,-704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1315890043361,0,true,197524151488,197524151552⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨883133212191,0,false,-240952841856,-240952841792⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1316144984395,0,true,197737150656,197737150720⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨882878271157,0,false,-241270292416,-241270292352⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1056829031235,0,false,-43533141760,-43533141696⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1056929432602,0,false,-43428690368,-43428690304⟩
    { al := (403137/2048000), au := (807123/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨216432528850,216660430554⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197569365696,197569365760⟩ : DyadicInterval 40),(⟨-241020215616,-241020215552⟩ : DyadicInterval 40),(⟨740681892486,740681911815⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197759768064,197759768128⟩ : DyadicInterval 40),(⟨-241304010048,-241304009984⟩ : DyadicInterval 40),(⟨740636413505,740636432835⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197478944000,197478944064⟩ : DyadicInterval 40),(⟨-240885485056,-240885484992⟩ : DyadicInterval 40),(⟨740703470394,740703489724⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197714518336,197714518400⟩ : DyadicInterval 40),(⟨-241236554368,-241236554304⟩ : DyadicInterval 40),(⟨740647226912,740647246241⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨27836572,55736369⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27836160,27836224⟩ : DyadicInterval 40),(⟨-27836928,-27836864⟩ : DyadicInterval 40),(⟨762123383231,762123402560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55734912,55734976⟩ : DyadicInterval 40),(⟨-55737792,-55737728⟩ : DyadicInterval 40),(⟨762123382166,762123401495⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2880,-704⟩ : DyadicInterval 40),(⟨762123383968,762123404320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨216378415585,216633356619⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197524151488,197524151552⟩ : DyadicInterval 40),(⟨-240952841856,-240952841792⟩ : DyadicInterval 40),(⟨740692683838,740692703168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197737150656,197737150720⟩ : DyadicInterval 40),(⟨-241270292416,-241270292352⟩ : DyadicInterval 40),(⟨740641818818,740641838147⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-43533141760,-43428690304⟩ : DyadicInterval 40),(⟨783837728768,783889973760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨197569365696,197759768128⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-241304010048,-241020215552⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1097_ok : ecellOkT e1097 = true := by decide +kernel
theorem e1097_pos {a z : ℝ} (ha1 : ((403137/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((807123/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1097 e1097_ok ha1 ha2 hz1 hz2 hz

-- box ['807123/4096000', '201993/1024000', '1999/2000', '3999/4000']  interval_lower 217944705/549755813888
noncomputable def e1098 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1316172058329,0,true,197759768064,197759768128⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨882851197223,0,false,-241304010048,-241304009984⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1316399960032,0,true,197950137472,197950137536⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨882623295520,0,false,-241587877696,-241587877632⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1316063728113,0,true,197669266816,197669266880⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨882959527439,0,false,-241169102784,-241169102720⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1316345737950,0,true,197904848000,197904848064⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨882677517602,0,false,-241520333632,-241520333568⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539495370,0,true,27867200,27867264⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483760182,0,false,-27867968,-27867904⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567426202,0,true,55796992,55797056⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455829350,0,false,-55799872,-55799808⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624944,0,false,-2880,-2816⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627070,0,false,-768,-704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1316117888085,0,true,197714514048,197714514112⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨882905367467,0,false,-241236547968,-241236547904⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1316372857616,0,true,197927500160,197927500224⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨882650397936,0,false,-241554115904,-241554115840⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1056739189704,0,false,-43626615680,-43626615616⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1056839707972,0,false,-43522033856,-43522033792⟩
    { al := (807123/4096000), au := (201993/1024000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨216660430553,216888332256⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197759768064,197759768128⟩ : DyadicInterval 40),(⟨-241304010048,-241304009984⟩ : DyadicInterval 40),(⟨740636413505,740636432835⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197950137472,197950137536⟩ : DyadicInterval 40),(⟨-241587877696,-241587877632⟩ : DyadicInterval 40),(⟨740590885353,740590904683⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197669266816,197669266880⟩ : DyadicInterval 40),(⟨-241169102784,-241169102720⟩ : DyadicInterval 40),(⟨740658037483,740658056813⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197904848000,197904848064⟩ : DyadicInterval 40),(⟨-241520333632,-241520333568⟩ : DyadicInterval 40),(⟨740601721821,740601741150⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨27867594,55798426⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27867200,27867264⟩ : DyadicInterval 40),(⟨-27867968,-27867904⟩ : DyadicInterval 40),(⟨762123383229,762123402558⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55796992,55797056⟩ : DyadicInterval 40),(⟨-55799872,-55799808⟩ : DyadicInterval 40),(⟨762123382160,762123401489⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2880,-704⟩ : DyadicInterval 40),(⟨762123383968,762123404320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨216606260309,216861229840⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197714514048,197714514112⟩ : DyadicInterval 40),(⟨-241236547968,-241236547904⟩ : DyadicInterval 40),(⟨740647227934,740647247263⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197927500160,197927500224⟩ : DyadicInterval 40),(⟨-241554115904,-241554115840⟩ : DyadicInterval 40),(⟨740596302225,740596321554⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-43626615680,-43522033792⟩ : DyadicInterval 40),(⟨783884400512,783936710720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨197759768064,197950137536⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-241587877696,-241304009984⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1098_ok : ecellOkT e1098 = true := by decide +kernel
theorem e1098_pos {a z : ℝ} (ha1 : ((807123/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((201993/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1098 e1098_ok ha1 ha2 hz1 hz2 hz

-- box ['403137/2048000', '807123/4096000', '3999/4000', '1']  interval_lower 430598109/1099511627776
noncomputable def e1099 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1315944156626,0,true,197569365696,197569365760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨883079098926,0,false,-241020215616,-241020215552⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1316172058330,0,true,197759768064,197759768128⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨882851197222,0,false,-241304010048,-241304009984⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1315890048493,0,true,197524155776,197524155840⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨883133207059,0,false,-240952848256,-240952848192⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539496292,0,true,27868160,27868224⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483759260,0,false,-27868928,-27868864⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627069,0,false,-768,-704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1315917097140,0,true,197546756416,197546756480⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨883106158412,0,false,-240986524672,-240986524608⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1316172066856,0,true,197759775168,197759775232⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨882851188696,0,false,-241304020672,-241304020608⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1056818358622,0,false,-43544245440,-43544245376⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1056918783838,0,false,-43439768192,-43439768128⟩
    { al := (403137/2048000), au := (807123/4096000), zl := (3999/4000), zu := 1,
      A := ⟨216432528850,216660430554⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197569365696,197569365760⟩ : DyadicInterval 40),(⟨-241020215616,-241020215552⟩ : DyadicInterval 40),(⟨740681892486,740681911815⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197759768064,197759768128⟩ : DyadicInterval 40),(⟨-241304010048,-241304009984⟩ : DyadicInterval 40),(⟨740636413505,740636432835⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197524155776,197524155840⟩ : DyadicInterval 40),(⟨-240952848256,-240952848192⟩ : DyadicInterval 40),(⟨740692682819,740692702149⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197759768064,197759768128⟩ : DyadicInterval 40),(⟨-241304010048,-241304009984⟩ : DyadicInterval 40),(⟨740636413505,740636432835⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,27868516⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27868160,27868224⟩ : DyadicInterval 40),(⟨-27868928,-27868864⟩ : DyadicInterval 40),(⟨762123383229,762123402558⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-768,0⟩ : DyadicInterval 40),(⟨762123383616,762123403264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨216405469364,216660439080⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197546756416,197546756480⟩ : DyadicInterval 40),(⟨-240986524672,-240986524608⟩ : DyadicInterval 40),(⟨740687289094,740687308423⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197759775168,197759775232⟩ : DyadicInterval 40),(⟨-241304020672,-241304020608⟩ : DyadicInterval 40),(⟨740636411816,740636431146⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-43544245440,-43439768128⟩ : DyadicInterval 40),(⟨783843267680,783895525600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨197569365696,197759768128⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-241304010048,-241020215552⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1099_ok : ecellOkT e1099 = true := by decide +kernel
theorem e1099_pos {a z : ℝ} (ha1 : ((403137/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((807123/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1099 e1099_ok ha1 ha2 hz1 hz2 hz

-- box ['807123/4096000', '201993/1024000', '3999/4000', '1']  interval_lower 108765093/274877906944
noncomputable def e1100 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1316172058329,0,true,197759768064,197759768128⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨882851197223,0,false,-241304010048,-241304009984⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1316399960032,0,true,197950137472,197950137536⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨882623295520,0,false,-241587877696,-241587877632⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1316117893221,0,true,197714518336,197714518400⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨882905362331,0,false,-241236554368,-241236554304⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539527322,0,true,27899136,27899200⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483728230,0,false,-27899904,-27899840⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627068,0,false,-768,-704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1316144970346,0,true,197737138880,197737138944⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨882878285206,0,false,-241270274880,-241270274816⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1316399968563,0,true,197950144576,197950144640⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨882623286989,0,false,-241587888320,-241587888256⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1056728494627,0,false,-43637743744,-43637743680⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1056829036772,0,false,-43533136000,-43533135936⟩
    { al := (807123/4096000), au := (201993/1024000), zl := (3999/4000), zu := 1,
      A := ⟨216660430553,216888332256⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197759768064,197759768128⟩ : DyadicInterval 40),(⟨-241304010048,-241304009984⟩ : DyadicInterval 40),(⟨740636413505,740636432835⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197950137472,197950137536⟩ : DyadicInterval 40),(⟨-241587877696,-241587877632⟩ : DyadicInterval 40),(⟨740590885353,740590904683⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197714518336,197714518400⟩ : DyadicInterval 40),(⟨-241236554368,-241236554304⟩ : DyadicInterval 40),(⟨740647226912,740647246241⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197950137472,197950137536⟩ : DyadicInterval 40),(⟨-241587877696,-241587877632⟩ : DyadicInterval 40),(⟨740590885353,740590904683⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,27899546⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27899136,27899200⟩ : DyadicInterval 40),(⟨-27899904,-27899840⟩ : DyadicInterval 40),(⟨762123383228,762123402557⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-768,0⟩ : DyadicInterval 40),(⟨762123383616,762123403264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨216633342570,216888340787⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197737138880,197737138944⟩ : DyadicInterval 40),(⟨-241270274880,-241270274816⟩ : DyadicInterval 40),(⟨740641821630,740641840960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197950144576,197950144640⟩ : DyadicInterval 40),(⟨-241587888320,-241587888256⟩ : DyadicInterval 40),(⟨740590883660,740590902990⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-43637743744,-43533135936⟩ : DyadicInterval 40),(⟨783889951584,783942274752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨197759768064,197950137536⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-241587877696,-241304009984⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1100_ok : ecellOkT e1100 = true := by decide +kernel
theorem e1100_pos {a z : ℝ} (ha1 : ((807123/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((201993/1024000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1100 e1100_ok ha1 ha2 hz1 hz2 hz

-- box ['201993/1024000', '808821/4096000', '999/1000', '3997/4000']  interval_lower 442035651/1099511627776
noncomputable def e1101 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1316399960031,0,true,197950137472,197950137536⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨882623295521,0,false,-241587877696,-241587877632⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1316627861734,0,true,198140473920,198140473984⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨882395393818,0,false,-241871818688,-241871818624⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1316183071698,0,true,197768968448,197768968512⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨882840183854,0,false,-241317726272,-241317726208⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1316465024559,0,true,198004480704,198004480768⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨882558230993,0,false,-241668933632,-241668933568⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099595322933,0,true,83691968,83692032⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099427932619,0,false,-83698368,-83698304⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099623346869,0,true,111713408,111713472⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099399908683,0,false,-111724800,-111724736⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511616424,0,false,-11392,-11328⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621406,0,false,-6400,-6336⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1316291511882,0,true,197859553344,197859553408⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨882731743670,0,false,-241452788736,-241452788672⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1316546452546,0,true,198072487232,198072487296⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨882476803006,0,false,-241770383168,-241770383104⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1056670684603,0,false,-43697895936,-43697895872⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1056771271999,0,false,-43593235392,-43593235328⟩
    { al := (201993/1024000), au := (808821/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨216888332255,217116233958⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197950137472,197950137536⟩ : DyadicInterval 40),(⟨-241587877696,-241587877632⟩ : DyadicInterval 40),(⟨740590885354,740590904683⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198140473920,198140473984⟩ : DyadicInterval 40),(⟨-241871818688,-241871818624⟩ : DyadicInterval 40),(⟨740545308069,740545327399⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197768968448,197768968512⟩ : DyadicInterval 40),(⟨-241317726272,-241317726208⟩ : DyadicInterval 40),(⟨740634214471,740634233801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198004480704,198004480768⟩ : DyadicInterval 40),(⟨-241668933632,-241668933568⟩ : DyadicInterval 40),(⟨740577878345,740577897675⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨83695157,111719093⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨83691968,83692032⟩ : DyadicInterval 40),(⟨-83698368,-83698304⟩ : DyadicInterval 40),(⟨762123380380,762123399710⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨111713408,111713472⟩ : DyadicInterval 40),(⟨-111724800,-111724736⟩ : DyadicInterval 40),(⟨762123377896,762123397225⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-11392,-6336⟩ : DyadicInterval 40),(⟨762123386784,762123408576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨216779884106,217034824770⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197859553344,197859553408⟩ : DyadicInterval 40),(⟨-241452788736,-241452788672⟩ : DyadicInterval 40),(⟨740612556289,740612575618⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198072487232,198072487296⟩ : DyadicInterval 40),(⟨-241770383168,-241770383104⟩ : DyadicInterval 40),(⟨740561594474,740561613803⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-43697895936,-43593235328⟩ : DyadicInterval 40),(⟨783920001280,783972350848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨197950137472,198140473984⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-241871818688,-241587877632⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1101_ok : ecellOkT e1101 = true := by decide +kernel
theorem e1101_pos {a z : ℝ} (ha1 : ((201993/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((808821/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1101 e1101_ok ha1 ha2 hz1 hz2 hz

-- box ['808821/4096000', '80967/409600', '999/1000', '3997/4000']  interval_lower 55818035/137438953472
noncomputable def e1102 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1316627861733,0,true,198140473920,198140473984⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨882395393819,0,false,-241871818688,-241871818624⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1316855763436,0,true,198330777408,198330777472⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨882167492116,0,false,-242155833024,-242155832960⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1316410745498,0,true,197959145856,197959145920⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨882612510054,0,false,-241601313600,-241601313536⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1316692755335,0,true,198194664960,198194665024⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨882330500217,0,false,-241952682560,-241952682496⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099595416029,0,true,83785024,83785088⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099427839523,0,false,-83791488,-83791424⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099623471023,0,true,111837504,111837568⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099399784529,0,false,-111848960,-111848896⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511616399,0,false,-11392,-11328⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621391,0,false,-6400,-6336⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1316519299629,0,true,198049810304,198049810368⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨882503955923,0,false,-241736552832,-241736552768⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1316774268782,0,true,198262731136,198262731200⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨882248986770,0,false,-242054264832,-242054264768⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1056580699185,0,false,-43791533632,-43791533568⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1056681403472,0,false,-43686742528,-43686742464⟩
    { al := (808821/4096000), au := (80967/409600), zl := (999/1000), zu := (3997/4000),
      A := ⟨217116233957,217344135660⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198140473920,198140473984⟩ : DyadicInterval 40),(⟨-241871818688,-241871818624⟩ : DyadicInterval 40),(⟨740545308069,740545327399⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198330777408,198330777472⟩ : DyadicInterval 40),(⟨-242155833024,-242155832960⟩ : DyadicInterval 40),(⟨740499681639,740499700968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197959145856,197959145920⟩ : DyadicInterval 40),(⟨-241601313600,-241601313536⟩ : DyadicInterval 40),(⟨740588729552,740588748881⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198194664960,198194665024⟩ : DyadicInterval 40),(⟨-241952682560,-241952682496⟩ : DyadicInterval 40),(⟨740532321271,740532340600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨83788253,111843247⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨83785024,83785088⟩ : DyadicInterval 40),(⟨-83791488,-83791424⟩ : DyadicInterval 40),(⟨762123380398,762123399728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨111837504,111837568⟩ : DyadicInterval 40),(⟨-111848960,-111848896⟩ : DyadicInterval 40),(⟨762123377902,762123397232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-11392,-6336⟩ : DyadicInterval 40),(⟨762123386784,762123408576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨217007671853,217262641006⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198049810304,198049810368⟩ : DyadicInterval 40),(⟨-241736552832,-241736552768⟩ : DyadicInterval 40),(⟨740567025169,740567044499⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198262731136,198262731200⟩ : DyadicInterval 40),(⟨-242054264832,-242054264768⟩ : DyadicInterval 40),(⟨740516002726,740516022055⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-43791533632,-43686742464⟩ : DyadicInterval 40),(⟨783966754848,784019169696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨198140473920,198330777472⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-242155833024,-241871818624⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1102_ok : ecellOkT e1102 = true := by decide +kernel
theorem e1102_pos {a z : ℝ} (ha1 : ((808821/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((80967/409600 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1102 e1102_ok ha1 ha2 hz1 hz2 hz

-- box ['201993/1024000', '808821/4096000', '3997/4000', '1999/2000']  interval_lower 441204857/1099511627776
noncomputable def e1103 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1316399960031,0,true,197950137472,197950137536⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨882623295521,0,false,-241587877696,-241587877632⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1316627861734,0,true,198140473920,198140473984⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨882395393818,0,false,-241871818688,-241871818624⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1316237293781,0,true,197814263488,197814263552⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨882785961771,0,false,-241385257920,-241385257856⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1316519303618,0,true,198049813632,198049813696⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨882503951934,0,false,-241736557824,-241736557760⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567424869,0,true,55795648,55795712⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455830683,0,false,-55798528,-55798464⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099595417774,0,true,83786752,83786816⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099427837778,0,false,-83793216,-83793152⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621390,0,false,-6400,-6336⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624945,0,false,-2880,-2816⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1316318622248,0,true,197882198656,197882198720⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨882704633304,0,false,-241486557376,-241486557312⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1316573591592,0,true,198095152128,198095152192⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨882449663960,0,false,-241804197312,-241804197248⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1056659969871,0,false,-43709045120,-43709045056⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1056760581162,0,false,-43604358656,-43604358592⟩
    { al := (201993/1024000), au := (808821/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨216888332255,217116233958⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197950137472,197950137536⟩ : DyadicInterval 40),(⟨-241587877696,-241587877632⟩ : DyadicInterval 40),(⟨740590885354,740590904683⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198140473920,198140473984⟩ : DyadicInterval 40),(⟨-241871818688,-241871818624⟩ : DyadicInterval 40),(⟨740545308069,740545327399⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197814263488,197814263552⟩ : DyadicInterval 40),(⟨-241385257920,-241385257856⟩ : DyadicInterval 40),(⟨740623386380,740623405709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198049813632,198049813696⟩ : DyadicInterval 40),(⟨-241736557824,-241736557760⟩ : DyadicInterval 40),(⟨740567024382,740567043712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55797093,83789998⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55795648,55795712⟩ : DyadicInterval 40),(⟨-55798528,-55798464⟩ : DyadicInterval 40),(⟨762123382160,762123401489⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨83786752,83786816⟩ : DyadicInterval 40),(⟨-83793216,-83793152⟩ : DyadicInterval 40),(⟨762123380398,762123399727⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6400,-2816⟩ : DyadicInterval 40),(⟨762123385024,762123406080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨216806994472,217061963816⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197882198656,197882198720⟩ : DyadicInterval 40),(⟨-241486557376,-241486557312⟩ : DyadicInterval 40),(⟨740607139961,740607159291⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198095152128,198095152192⟩ : DyadicInterval 40),(⟨-241804197312,-241804197248⟩ : DyadicInterval 40),(⟨740556165864,740556185193⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-43709045120,-43604358592⟩ : DyadicInterval 40),(⟨783925562912,783977925440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨197950137472,198140473984⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-241871818688,-241587877632⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1103_ok : ecellOkT e1103 = true := by decide +kernel
theorem e1103_pos {a z : ℝ} (ha1 : ((201993/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((808821/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1103 e1103_ok ha1 ha2 hz1 hz2 hz

-- box ['808821/4096000', '80967/409600', '3997/4000', '1999/2000']  interval_lower 445710205/1099511627776
noncomputable def e1104 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1316627861733,0,true,198140473920,198140473984⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨882395393819,0,false,-241871818688,-241871818624⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1316855763436,0,true,198330777408,198330777472⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨882167492116,0,false,-242155833024,-242155832960⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1316465024557,0,true,198004480704,198004480768⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨882558230995,0,false,-241668933632,-241668933568⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1316747091369,0,true,198240037632,198240037696⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨882276164183,0,false,-242020395200,-242020395136⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567486935,0,true,55857728,55857792⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455768617,0,false,-55860608,-55860544⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099595510891,0,true,83879872,83879936⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099427744661,0,false,-83886336,-83886272⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621376,0,false,-6464,-6400⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624939,0,false,-2880,-2816⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1316546438487,0,true,198072475520,198072475584⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨882476817065,0,false,-241770365696,-241770365632⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1316801436316,0,true,198285415936,198285416000⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨882221819236,0,false,-242088123136,-242088123072⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1056569961946,0,false,-43802707200,-43802707136⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1056670690154,0,false,-43697890176,-43697890112⟩
    { al := (808821/4096000), au := (80967/409600), zl := (3997/4000), zu := (1999/2000),
      A := ⟨217116233957,217344135660⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198140473920,198140473984⟩ : DyadicInterval 40),(⟨-241871818688,-241871818624⟩ : DyadicInterval 40),(⟨740545308069,740545327399⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198330777408,198330777472⟩ : DyadicInterval 40),(⟨-242155833024,-242155832960⟩ : DyadicInterval 40),(⟨740499681639,740499700968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198004480704,198004480768⟩ : DyadicInterval 40),(⟨-241668933632,-241668933568⟩ : DyadicInterval 40),(⟨740577878345,740577897675⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198240037632,198240037696⟩ : DyadicInterval 40),(⟨-242020395200,-242020395136⟩ : DyadicInterval 40),(⟨740521444193,740521463523⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55859159,83883115⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55857728,55857792⟩ : DyadicInterval 40),(⟨-55860608,-55860544⟩ : DyadicInterval 40),(⟨762123382154,762123401483⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨83879872,83879936⟩ : DyadicInterval 40),(⟨-83886336,-83886272⟩ : DyadicInterval 40),(⟨762123380384,762123399713⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6464,-2816⟩ : DyadicInterval 40),(⟨762123385024,762123406112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨217034810711,217289808540⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198072475520,198072475584⟩ : DyadicInterval 40),(⟨-241770365696,-241770365632⟩ : DyadicInterval 40),(⟨740561597286,740561616615⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198285415936,198285416000⟩ : DyadicInterval 40),(⟨-242088123136,-242088123072⟩ : DyadicInterval 40),(⟨740510562506,740510581836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-43802707200,-43697890112⟩ : DyadicInterval 40),(⟨783972328672,784024756480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨198140473920,198330777472⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-242155833024,-241871818624⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1104_ok : ecellOkT e1104 = true := by decide +kernel
theorem e1104_pos {a z : ℝ} (ha1 : ((808821/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((80967/409600 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1104 e1104_ok ha1 ha2 hz1 hz2 hz

-- box ['80967/409600', '810519/4096000', '999/1000', '3997/4000']  interval_lower 112767797/274877906944
noncomputable def e1105 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1316855763435,0,true,198330777408,198330777472⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨882167492117,0,false,-242155833024,-242155832960⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1317083665138,0,true,198521047936,198521048000⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨881939590414,0,false,-242439920768,-242439920704⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1316638419299,0,true,198149290432,198149290496⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨882384836253,0,false,-241884974080,-241884974016⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1316920486111,0,true,198384816384,198384816448⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨882102769441,0,false,-242236504704,-242236504640⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099595509142,0,true,83878144,83878208⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099427746410,0,false,-83884608,-83884544⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099623595200,0,true,111961664,111961728⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099399660352,0,false,-111973184,-111973120⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511616373,0,false,-11456,-11392⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621377,0,false,-6400,-6336⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1316747087380,0,true,198240034304,198240034368⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨882276168172,0,false,-242020390208,-242020390144⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1317002085022,0,true,198452942144,198452942208⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨882021170530,0,false,-242338219712,-242338219648⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1056490619359,0,false,-43885277568,-43885277504⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1056591440561,0,false,-43780355904,-43780355840⟩
    { al := (80967/409600), au := (810519/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨217344135659,217572037362⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198330777408,198330777472⟩ : DyadicInterval 40),(⟨-242155833024,-242155832960⟩ : DyadicInterval 40),(⟨740499681639,740499700969⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198521047936,198521048000⟩ : DyadicInterval 40),(⟨-242439920768,-242439920704⟩ : DyadicInterval 40),(⟨740454006076,740454025406⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198149290432,198149290496⟩ : DyadicInterval 40),(⟨-241884974080,-241884974016⟩ : DyadicInterval 40),(⟨740543195541,740543214870⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198384816384,198384816448⟩ : DyadicInterval 40),(⟨-242236504704,-242236504640⟩ : DyadicInterval 40),(⟨740486715067,740486734396⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨83881366,111967424⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨83878144,83878208⟩ : DyadicInterval 40),(⟨-83884608,-83884544⟩ : DyadicInterval 40),(⟨762123380384,762123399713⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨111961664,111961728⟩ : DyadicInterval 40),(⟨-111973184,-111973120⟩ : DyadicInterval 40),(⟨762123377909,762123397239⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-11456,-6336⟩ : DyadicInterval 40),(⟨762123386784,762123408608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨217235459604,217490457246⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198240034304,198240034368⟩ : DyadicInterval 40),(⟨-242020390208,-242020390144⟩ : DyadicInterval 40),(⟨740521444982,740521464311⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198452942144,198452942208⟩ : DyadicInterval 40),(⟨-242338219712,-242338219648⟩ : DyadicInterval 40),(⟨740470361807,740470381137⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-43885277568,-43780355840⟩ : DyadicInterval 40),(⟨784013561536,784066041664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨198330777408,198521048000⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-242439920768,-242155832960⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1105_ok : ecellOkT e1105 = true := by decide +kernel
theorem e1105_pos {a z : ℝ} (ha1 : ((80967/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((810519/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1105 e1105_ok ha1 ha2 hz1 hz2 hz

-- box ['810519/4096000', '101421/512000', '999/1000', '3997/4000']  interval_lower 28476025/68719476736
noncomputable def e1106 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1317083665137,0,true,198521047936,198521048000⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨881939590415,0,false,-242439920768,-242439920704⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1317311566840,0,true,198711285568,198711285632⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨881711688712,0,false,-242724081856,-242724081792⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1316866093099,0,true,198339402112,198339402176⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨882157162453,0,false,-242168707712,-242168707648⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1317148216886,0,true,198574934912,198574934976⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨881875038666,0,false,-242520400192,-242520400128⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099595602273,0,true,83971264,83971328⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099427653279,0,false,-83977728,-83977664⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099623719399,0,true,112085888,112085952⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099399536153,0,false,-112097344,-112097280⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511616348,0,false,-11456,-11392⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621363,0,false,-6464,-6400⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1316974875128,0,true,198430225472,198430225536⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨882048380424,0,false,-242304300928,-242304300864⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1317229901262,0,true,198643120256,198643120320⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨881793354290,0,false,-242622248000,-242622247936⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1056400445127,0,false,-43979127744,-43979127680⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1056501383270,0,false,-43874075392,-43874075328⟩
    { al := (810519/4096000), au := (101421/512000), zl := (999/1000), zu := (3997/4000),
      A := ⟨217572037361,217799939064⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198521047936,198521048000⟩ : DyadicInterval 40),(⟨-242439920768,-242439920704⟩ : DyadicInterval 40),(⟨740454006076,740454025406⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198711285568,198711285632⟩ : DyadicInterval 40),(⟨-242724081856,-242724081792⟩ : DyadicInterval 40),(⟨740408281305,740408300635⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198339402112,198339402176⟩ : DyadicInterval 40),(⟨-242168707712,-242168707648⟩ : DyadicInterval 40),(⟨740497612466,740497631795⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198574934912,198574934976⟩ : DyadicInterval 40),(⟨-242520400192,-242520400128⟩ : DyadicInterval 40),(⟨740441059810,740441079140⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨83974497,112091623⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨83971264,83971328⟩ : DyadicInterval 40),(⟨-83977728,-83977664⟩ : DyadicInterval 40),(⟨762123380370,762123399699⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨112085888,112085952⟩ : DyadicInterval 40),(⟨-112097344,-112097280⟩ : DyadicInterval 40),(⟨762123377852,762123397182⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-11456,-6400⟩ : DyadicInterval 40),(⟨762123386816,762123408608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨217463247352,217718273486⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198430225472,198430225536⟩ : DyadicInterval 40),(⟨-242304300928,-242304300864⟩ : DyadicInterval 40),(⟨740475815664,740475834994⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198643120256,198643120320⟩ : DyadicInterval 40),(⟨-242622248000,-242622247936⟩ : DyadicInterval 40),(⟨740424671784,740424691113⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-43979127744,-43874075328⟩ : DyadicInterval 40),(⟨784060421280,784112966752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨198521047936,198711285632⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-242724081856,-242439920704⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1106_ok : ecellOkT e1106 = true := by decide +kernel
theorem e1106_pos {a z : ℝ} (ha1 : ((810519/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((101421/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1106 e1106_ok ha1 ha2 hz1 hz2 hz

-- box ['80967/409600', '810519/4096000', '3997/4000', '1999/2000']  interval_lower 225117019/549755813888
noncomputable def e1107 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1316855763435,0,true,198330777408,198330777472⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨882167492117,0,false,-242155833024,-242155832960⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1317083665138,0,true,198521047936,198521048000⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨881939590414,0,false,-242439920768,-242439920704⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1316692755333,0,true,198194664960,198194665024⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨882330500219,0,false,-241952682560,-241952682496⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1316974879120,0,true,198430228800,198430228864⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨882048376432,0,false,-242304305856,-242304305792⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567549012,0,true,55919808,55919872⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455706540,0,false,-55922688,-55922624⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099595604027,0,true,83972992,83973056⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099427651525,0,false,-83979520,-83979456⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621362,0,false,-6464,-6400⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624932,0,false,-2880,-2816⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1316774254718,0,true,198262719424,198262719488⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨882249000834,0,false,-242054247296,-242054247232⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1317029281043,0,true,198475646784,198475646848⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨881993974509,0,false,-242372122304,-242372122240⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1056479859591,0,false,-43896475520,-43896475456⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1056580704744,0,false,-43791527872,-43791527808⟩
    { al := (80967/409600), au := (810519/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨217344135659,217572037362⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198330777408,198330777472⟩ : DyadicInterval 40),(⟨-242155833024,-242155832960⟩ : DyadicInterval 40),(⟨740499681639,740499700969⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198521047936,198521048000⟩ : DyadicInterval 40),(⟨-242439920768,-242439920704⟩ : DyadicInterval 40),(⟨740454006076,740454025406⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198194664960,198194665024⟩ : DyadicInterval 40),(⟨-241952682560,-241952682496⟩ : DyadicInterval 40),(⟨740532321271,740532340601⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198430228800,198430228864⟩ : DyadicInterval 40),(⟨-242304305856,-242304305792⟩ : DyadicInterval 40),(⟨740475814848,740475834177⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55921236,83976251⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55919808,55919872⟩ : DyadicInterval 40),(⟨-55922688,-55922624⟩ : DyadicInterval 40),(⟨762123382147,762123401476⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨83972992,83973056⟩ : DyadicInterval 40),(⟨-83979520,-83979456⟩ : DyadicInterval 40),(⟨762123380401,762123399731⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6464,-2816⟩ : DyadicInterval 40),(⟨762123385024,762123406112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨217262626942,217517653267⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198262719424,198262719488⟩ : DyadicInterval 40),(⟨-242054247296,-242054247232⟩ : DyadicInterval 40),(⟨740516005520,740516024849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198475646784,198475646848⟩ : DyadicInterval 40),(⟨-242372122304,-242372122240⟩ : DyadicInterval 40),(⟨740464910042,740464929371⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-43896475520,-43791527808⟩ : DyadicInterval 40),(⟨784019147520,784071640640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨198330777408,198521048000⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-242439920768,-242155832960⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1107_ok : ecellOkT e1107 = true := by decide +kernel
theorem e1107_pos {a z : ℝ} (ha1 : ((80967/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((810519/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1107 e1107_ok ha1 ha2 hz1 hz2 hz

-- box ['810519/4096000', '101421/512000', '3997/4000', '1999/2000']  interval_lower 454776047/1099511627776
noncomputable def e1108 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1317083665137,0,true,198521047936,198521048000⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨881939590415,0,false,-242439920768,-242439920704⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1317311566840,0,true,198711285568,198711285632⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨881711688712,0,false,-242724081856,-242724081792⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1316920486108,0,true,198384816384,198384816448⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨882102769444,0,false,-242236504704,-242236504640⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1317202666871,0,true,198620387008,198620387072⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨881820588681,0,false,-242588289856,-242588289792⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567611101,0,true,55981888,55981952⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455644451,0,false,-55984768,-55984704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099595697179,0,true,84066176,84066240⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099427558373,0,false,-84072640,-84072576⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621347,0,false,-6464,-6400⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624926,0,false,-2880,-2816⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1317002070951,0,true,198452930368,198452930432⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨882021184601,0,false,-242338202176,-242338202112⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1317257125770,0,true,198665844672,198665844736⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨881766129782,0,false,-242656194880,-242656194816⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1056389662806,0,false,-43990350144,-43990350080⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1056490624926,0,false,-43885271808,-43885271744⟩
    { al := (810519/4096000), au := (101421/512000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨217572037361,217799939064⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198521047936,198521048000⟩ : DyadicInterval 40),(⟨-242439920768,-242439920704⟩ : DyadicInterval 40),(⟨740454006076,740454025406⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198711285568,198711285632⟩ : DyadicInterval 40),(⟨-242724081856,-242724081792⟩ : DyadicInterval 40),(⟨740408281305,740408300635⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198384816384,198384816448⟩ : DyadicInterval 40),(⟨-242236504704,-242236504640⟩ : DyadicInterval 40),(⟨740486715067,740486734397⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198620387008,198620387072⟩ : DyadicInterval 40),(⟨-242588289856,-242588289792⟩ : DyadicInterval 40),(⟨740430136436,740430155766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55983325,84069403⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55981888,55981952⟩ : DyadicInterval 40),(⟨-55984768,-55984704⟩ : DyadicInterval 40),(⟨762123382141,762123401470⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨84066176,84066240⟩ : DyadicInterval 40),(⟨-84072640,-84072576⟩ : DyadicInterval 40),(⟨762123380355,762123399685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6464,-2816⟩ : DyadicInterval 40),(⟨762123385024,762123406112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨217490443175,217745497994⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198452930368,198452930432⟩ : DyadicInterval 40),(⟨-242338202176,-242338202112⟩ : DyadicInterval 40),(⟨740470364647,740470383976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198665844672,198665844736⟩ : DyadicInterval 40),(⟨-242656194880,-242656194816⟩ : DyadicInterval 40),(⟨740419208484,740419227814⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-43990350144,-43885271744⟩ : DyadicInterval 40),(⟨784066019488,784118577952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨198521047936,198711285632⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-242724081856,-242439920704⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1108_ok : ecellOkT e1108 = true := by decide +kernel
theorem e1108_pos {a z : ℝ} (ha1 : ((810519/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((101421/512000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1108 e1108_ok ha1 ha2 hz1 hz2 hz

-- box ['201993/1024000', '808821/4096000', '1999/2000', '3999/4000']  interval_lower 440373235/1099511627776
noncomputable def e1109 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1316399960031,0,true,197950137472,197950137536⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨882623295521,0,false,-241587877696,-241587877632⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1316627861734,0,true,198140473920,198140473984⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨882395393818,0,false,-241871818688,-241871818624⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1316291515864,0,true,197859556672,197859556736⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨882731739688,0,false,-241452793728,-241452793664⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1316573582676,0,true,198095144704,198095144768⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨882449672876,0,false,-241804186176,-241804186112⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539526398,0,true,27898240,27898304⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483729154,0,false,-27899008,-27898944⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567488270,0,true,55859072,55859136⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455767282,0,false,-55861952,-55861888⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624938,0,false,-2880,-2816⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627069,0,false,-768,-704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1316345732806,0,true,197904843712,197904843776⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨882677522746,0,false,-241520327232,-241520327168⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1316600730832,0,true,198117816704,198117816768⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨882422524720,0,false,-241838012672,-241838012608⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1056649253722,0,false,-43720195904,-43720195840⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1056749888913,0,false,-43615483520,-43615483456⟩
    { al := (201993/1024000), au := (808821/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨216888332255,217116233958⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197950137472,197950137536⟩ : DyadicInterval 40),(⟨-241587877696,-241587877632⟩ : DyadicInterval 40),(⟨740590885354,740590904683⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198140473920,198140473984⟩ : DyadicInterval 40),(⟨-241871818688,-241871818624⟩ : DyadicInterval 40),(⟨740545308069,740545327399⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197859556672,197859556736⟩ : DyadicInterval 40),(⟨-241452793728,-241452793664⟩ : DyadicInterval 40),(⟨740612555505,740612574834⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198095144704,198095144768⟩ : DyadicInterval 40),(⟨-241804186176,-241804186112⟩ : DyadicInterval 40),(⟨740556167624,740556186953⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨27898622,55860494⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27898240,27898304⟩ : DyadicInterval 40),(⟨-27899008,-27898944⟩ : DyadicInterval 40),(⟨762123383228,762123402557⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55859072,55859136⟩ : DyadicInterval 40),(⟨-55861952,-55861888⟩ : DyadicInterval 40),(⟨762123382153,762123401483⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2880,-704⟩ : DyadicInterval 40),(⟨762123383968,762123404320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨216834105030,217089103056⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197904843712,197904843776⟩ : DyadicInterval 40),(⟨-241520327232,-241520327168⟩ : DyadicInterval 40),(⟨740601722847,740601742176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198117816704,198117816768⟩ : DyadicInterval 40),(⟨-241838012672,-241838012608⟩ : DyadicInterval 40),(⟨740550736501,740550755830⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-43720195904,-43615483456⟩ : DyadicInterval 40),(⟨783931125344,783983500832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨197950137472,198140473984⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-241871818688,-241587877632⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1109_ok : ecellOkT e1109 = true := by decide +kernel
theorem e1109_pos {a z : ℝ} (ha1 : ((201993/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((808821/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1109 e1109_ok ha1 ha2 hz1 hz2 hz

-- box ['808821/4096000', '80967/409600', '1999/2000', '3999/4000']  interval_lower 444875525/1099511627776
noncomputable def e1110 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1316627861733,0,true,198140473920,198140473984⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨882395393819,0,false,-241871818688,-241871818624⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1316855763436,0,true,198330777408,198330777472⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨882167492116,0,false,-242155833024,-242155832960⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1316519303615,0,true,198049813632,198049813696⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨882503951937,0,false,-241736557824,-241736557760⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1316801427403,0,true,198285408448,198285408512⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨882221828149,0,false,-242088112064,-242088112000⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539557432,0,true,27929280,27929344⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483698120,0,false,-27930048,-27929984⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567550350,0,true,55921088,55921152⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455705202,0,false,-55924032,-55923968⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624931,0,false,-2880,-2816⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627067,0,false,-768,-704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1316573577532,0,true,198095140416,198095140480⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨882449678020,0,false,-241804179776,-241804179712⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1316828604042,0,true,198308100352,198308100416⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨882194651510,0,false,-242121982784,-242121982720⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1056559223289,0,false,-43813882368,-43813882304⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1056659975423,0,false,-43709039360,-43709039296⟩
    { al := (808821/4096000), au := (80967/409600), zl := (1999/2000), zu := (3999/4000),
      A := ⟨217116233957,217344135660⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198140473920,198140473984⟩ : DyadicInterval 40),(⟨-241871818688,-241871818624⟩ : DyadicInterval 40),(⟨740545308069,740545327399⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198330777408,198330777472⟩ : DyadicInterval 40),(⟨-242155833024,-242155832960⟩ : DyadicInterval 40),(⟨740499681639,740499700968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198049813632,198049813696⟩ : DyadicInterval 40),(⟨-241736557824,-241736557760⟩ : DyadicInterval 40),(⟨740567024383,740567043712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198285408448,198285408512⟩ : DyadicInterval 40),(⟨-242088112064,-242088112000⟩ : DyadicInterval 40),(⟨740510564333,740510583662⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨27929656,55922574⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27929280,27929344⟩ : DyadicInterval 40),(⟨-27930048,-27929984⟩ : DyadicInterval 40),(⟨762123383226,762123402555⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55921088,55921152⟩ : DyadicInterval 40),(⟨-55924032,-55923968⟩ : DyadicInterval 40),(⟨762123382179,762123401508⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2880,-704⟩ : DyadicInterval 40),(⟨762123383968,762123404320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨217061949756,217316976266⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198095140416,198095140480⟩ : DyadicInterval 40),(⟨-241804179776,-241804179712⟩ : DyadicInterval 40),(⟨740556168651,740556187981⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198308100352,198308100416⟩ : DyadicInterval 40),(⟨-242121982784,-242121982720⟩ : DyadicInterval 40),(⟨740505121620,740505140950⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-43813882368,-43709039296⟩ : DyadicInterval 40),(⟨783977903264,784030344064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨198140473920,198330777472⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-242155833024,-241871818624⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1110_ok : ecellOkT e1110 = true := by decide +kernel
theorem e1110_pos {a z : ℝ} (ha1 : ((808821/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((80967/409600 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1110 e1110_ok ha1 ha2 hz1 hz2 hz

-- box ['201993/1024000', '808821/4096000', '3999/4000', '1']  interval_lower 219770485/549755813888
noncomputable def e1111 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1316399960031,0,true,197950137472,197950137536⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨882623295521,0,false,-241587877696,-241587877632⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1316627861734,0,true,198140473920,198140473984⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨882395393818,0,false,-241871818688,-241871818624⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1316345737947,0,true,197904848000,197904848064⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨882677517605,0,false,-241520333632,-241520333568⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539558357,0,true,27930176,27930240⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483697195,0,false,-27930944,-27930880⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627066,0,false,-768,-704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1316372843561,0,true,197927488448,197927488512⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨882650411991,0,false,-241554098368,-241554098304⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1316627870266,0,true,198140481024,198140481088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨882395385286,0,false,-241871829312,-241871829248⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1056638536157,0,false,-43731348288,-43731348224⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1056739195249,0,false,-43626609920,-43626609856⟩
    { al := (201993/1024000), au := (808821/4096000), zl := (3999/4000), zu := 1,
      A := ⟨216888332255,217116233958⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197950137472,197950137536⟩ : DyadicInterval 40),(⟨-241587877696,-241587877632⟩ : DyadicInterval 40),(⟨740590885354,740590904683⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198140473920,198140473984⟩ : DyadicInterval 40),(⟨-241871818688,-241871818624⟩ : DyadicInterval 40),(⟨740545308069,740545327399⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197904848000,197904848064⟩ : DyadicInterval 40),(⟨-241520333632,-241520333568⟩ : DyadicInterval 40),(⟨740601721821,740601741151⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198140473920,198140473984⟩ : DyadicInterval 40),(⟨-241871818688,-241871818624⟩ : DyadicInterval 40),(⟨740545308069,740545327399⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,27930581⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27930176,27930240⟩ : DyadicInterval 40),(⟨-27930944,-27930880⟩ : DyadicInterval 40),(⟨762123383226,762123402555⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-768,0⟩ : DyadicInterval 40),(⟨762123383616,762123403264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨216861215785,217116242490⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨197927488448,197927488512⟩ : DyadicInterval 40),(⟨-241554098368,-241554098304⟩ : DyadicInterval 40),(⟨740596305006,740596324336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198140481024,198140481088⟩ : DyadicInterval 40),(⟨-241871829312,-241871829248⟩ : DyadicInterval 40),(⟨740545306372,740545325701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-43731348288,-43626609856⟩ : DyadicInterval 40),(⟨783936688544,783989077024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨197950137472,198140473984⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-241871818688,-241587877632⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1111_ok : ecellOkT e1111 = true := by decide +kernel
theorem e1111_pos {a z : ℝ} (ha1 : ((201993/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((808821/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1111 e1111_ok ha1 ha2 hz1 hz2 hz

-- box ['808821/4096000', '80967/409600', '3999/4000', '1']  interval_lower 444039875/1099511627776
noncomputable def e1112 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1316627861733,0,true,198140473920,198140473984⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨882395393819,0,false,-241871818688,-241871818624⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1316855763436,0,true,198330777408,198330777472⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨882167492116,0,false,-242155833024,-242155832960⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1316573582674,0,true,198095144704,198095144768⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨882449672878,0,false,-241804186176,-241804186112⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539589397,0,true,27961216,27961280⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483666155,0,false,-27961984,-27961920⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627064,0,false,-768,-704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1316600716772,0,true,198117804992,198117805056⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨882422538780,0,false,-241837995136,-241837995072⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1316855771966,0,true,198330784512,198330784576⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨882167483586,0,false,-242155843648,-242155843584⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1056548483212,0,false,-43825059136,-43825059072⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1056649259275,0,false,-43720190144,-43720190080⟩
    { al := (808821/4096000), au := (80967/409600), zl := (3999/4000), zu := 1,
      A := ⟨217116233957,217344135660⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198140473920,198140473984⟩ : DyadicInterval 40),(⟨-241871818688,-241871818624⟩ : DyadicInterval 40),(⟨740545308069,740545327399⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198330777408,198330777472⟩ : DyadicInterval 40),(⟨-242155833024,-242155832960⟩ : DyadicInterval 40),(⟨740499681639,740499700968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198095144704,198095144768⟩ : DyadicInterval 40),(⟨-241804186176,-241804186112⟩ : DyadicInterval 40),(⟨740556167624,740556186953⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198330777408,198330777472⟩ : DyadicInterval 40),(⟨-242155833024,-242155832960⟩ : DyadicInterval 40),(⟨740499681639,740499700968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,27961621⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27961216,27961280⟩ : DyadicInterval 40),(⟨-27961984,-27961920⟩ : DyadicInterval 40),(⟨762123383224,762123402553⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-768,0⟩ : DyadicInterval 40),(⟨762123383616,762123403264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨217089088996,217344144190⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198117804992,198117805056⟩ : DyadicInterval 40),(⟨-241837995136,-241837995072⟩ : DyadicInterval 40),(⟨740550739289,740550758618⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198330784512,198330784576⟩ : DyadicInterval 40),(⟨-242155843648,-242155843584⟩ : DyadicInterval 40),(⟨740499679938,740499699267⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-43825059136,-43720190080⟩ : DyadicInterval 40),(⟨783983478656,784035932448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨198140473920,198330777472⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-242155833024,-241871818624⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1112_ok : ecellOkT e1112 = true := by decide +kernel
theorem e1112_pos {a z : ℝ} (ha1 : ((808821/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((80967/409600 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1112 e1112_ok ha1 ha2 hz1 hz2 hz

-- box ['80967/409600', '810519/4096000', '1999/2000', '3999/4000']  interval_lower 449395865/1099511627776
noncomputable def e1113 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1316855763435,0,true,198330777408,198330777472⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨882167492117,0,false,-242155833024,-242155832960⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1317083665138,0,true,198521047936,198521048000⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨881939590414,0,false,-242439920768,-242439920704⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1316747091367,0,true,198240037632,198240037696⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨882276164185,0,false,-242020395200,-242020395136⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1317029272129,0,true,198475639296,198475639360⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨881993983423,0,false,-242372111232,-242372111168⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539588470,0,true,27960320,27960384⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483667082,0,false,-27961088,-27961024⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567612441,0,true,55983232,55983296⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455643111,0,false,-55986112,-55986048⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624925,0,false,-2880,-2816⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627065,0,false,-768,-704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1316801422251,0,true,198285404160,198285404224⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨882221833301,0,false,-242088105600,-242088105536⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1317056477253,0,true,198498351040,198498351104⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨881966778299,0,false,-242406026176,-242406026112⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1056469098403,0,false,-43907675136,-43907675072⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1056569967506,0,false,-43802701440,-43802701376⟩
    { al := (80967/409600), au := (810519/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨217344135659,217572037362⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198330777408,198330777472⟩ : DyadicInterval 40),(⟨-242155833024,-242155832960⟩ : DyadicInterval 40),(⟨740499681639,740499700969⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198521047936,198521048000⟩ : DyadicInterval 40),(⟨-242439920768,-242439920704⟩ : DyadicInterval 40),(⟨740454006076,740454025406⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198240037632,198240037696⟩ : DyadicInterval 40),(⟨-242020395200,-242020395136⟩ : DyadicInterval 40),(⟨740521444194,740521463523⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198475639296,198475639360⟩ : DyadicInterval 40),(⟨-242372111232,-242372111168⟩ : DyadicInterval 40),(⟨740464911872,740464931202⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨27960694,55984665⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27960320,27960384⟩ : DyadicInterval 40),(⟨-27961088,-27961024⟩ : DyadicInterval 40),(⟨762123383224,762123402553⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55983232,55983296⟩ : DyadicInterval 40),(⟨-55986112,-55986048⟩ : DyadicInterval 40),(⟨762123382141,762123401470⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2880,-704⟩ : DyadicInterval 40),(⟨762123383968,762123404320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨217289794475,217544849477⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198285404160,198285404224⟩ : DyadicInterval 40),(⟨-242088105600,-242088105536⟩ : DyadicInterval 40),(⟨740510565339,740510584668⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198498351040,198498351104⟩ : DyadicInterval 40),(⟨-242406026176,-242406026112⟩ : DyadicInterval 40),(⟨740459457581,740459476911⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-43907675136,-43802701376⟩ : DyadicInterval 40),(⟨784024734304,784077240448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨198330777408,198521048000⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-242439920768,-242155832960⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1113_ok : ecellOkT e1113 = true := by decide +kernel
theorem e1113_pos {a z : ℝ} (ha1 : ((80967/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((810519/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1113 e1113_ok ha1 ha2 hz1 hz2 hz

-- box ['810519/4096000', '101421/512000', '1999/2000', '3999/4000']  interval_lower 453935005/1099511627776
noncomputable def e1114 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1317083665137,0,true,198521047936,198521048000⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨881939590415,0,false,-242439920768,-242439920704⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1317311566840,0,true,198711285568,198711285632⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨881711688712,0,false,-242724081856,-242724081792⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1316974879118,0,true,198430228800,198430228864⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨882048376434,0,false,-242304305856,-242304305792⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1317257116856,0,true,198665837248,198665837312⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨881766138696,0,false,-242656183808,-242656183744⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539619516,0,true,27991360,27991424⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483636036,0,false,-27992128,-27992064⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567674543,0,true,56045312,56045376⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455581009,0,false,-56048256,-56048192⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624919,0,false,-2880,-2816⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627064,0,false,-768,-704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1317029266973,0,true,198475635008,198475635072⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨881993988579,0,false,-242372104768,-242372104704⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1317284350468,0,true,198688568832,198688568896⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨881738905084,0,false,-242690143040,-242690142976⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1056378879062,0,false,-44001574144,-44001574080⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1056479865159,0,false,-43896469760,-43896469696⟩
    { al := (810519/4096000), au := (101421/512000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨217572037361,217799939064⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198521047936,198521048000⟩ : DyadicInterval 40),(⟨-242439920768,-242439920704⟩ : DyadicInterval 40),(⟨740454006076,740454025406⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198711285568,198711285632⟩ : DyadicInterval 40),(⟨-242724081856,-242724081792⟩ : DyadicInterval 40),(⟨740408281305,740408300635⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198430228800,198430228864⟩ : DyadicInterval 40),(⟨-242304305856,-242304305792⟩ : DyadicInterval 40),(⟨740475814848,740475834178⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198665837248,198665837312⟩ : DyadicInterval 40),(⟨-242656183808,-242656183744⟩ : DyadicInterval 40),(⟨740419210281,740419229611⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨27991740,56046767⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27991360,27991424⟩ : DyadicInterval 40),(⟨-27992128,-27992064⟩ : DyadicInterval 40),(⟨762123383223,762123402552⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56045312,56045376⟩ : DyadicInterval 40),(⟨-56048256,-56048192⟩ : DyadicInterval 40),(⟨762123382166,762123401496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2880,-704⟩ : DyadicInterval 40),(⟨762123383968,762123404320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨217517639197,217772722692⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198475635008,198475635072⟩ : DyadicInterval 40),(⟨-242372104768,-242372104704⟩ : DyadicInterval 40),(⟨740464912882,740464932211⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198688568832,198688568896⟩ : DyadicInterval 40),(⟨-242690143040,-242690142976⟩ : DyadicInterval 40),(⟨740413744410,740413763740⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-44001574144,-43896469696⟩ : DyadicInterval 40),(⟨784071618464,784124189952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨198521047936,198711285632⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-242724081856,-242439920704⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1114_ok : ecellOkT e1114 = true := by decide +kernel
theorem e1114_pos {a z : ℝ} (ha1 : ((810519/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((101421/512000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1114 e1114_ok ha1 ha2 hz1 hz2 hz

-- box ['80967/409600', '810519/4096000', '3999/4000', '1']  interval_lower 448557231/1099511627776
noncomputable def e1115 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1316855763435,0,true,198330777408,198330777472⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨882167492117,0,false,-242155833024,-242155832960⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1317083665138,0,true,198521047936,198521048000⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨881939590414,0,false,-242439920768,-242439920704⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1316801427401,0,true,198285408448,198285408512⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨882221828151,0,false,-242088112064,-242088112000⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539620443,0,true,27992256,27992320⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483635109,0,false,-27993024,-27992960⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627063,0,false,-768,-704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1316828589977,0,true,198308088640,198308088704⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨882194665575,0,false,-242121965248,-242121965184⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1317083673659,0,true,198521055040,198521055104⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨881939581893,0,false,-242439931392,-242439931328⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1056458335792,0,false,-43918876288,-43918876224⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1056559228850,0,false,-43813876608,-43813876544⟩
    { al := (80967/409600), au := (810519/4096000), zl := (3999/4000), zu := 1,
      A := ⟨217344135659,217572037362⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198330777408,198330777472⟩ : DyadicInterval 40),(⟨-242155833024,-242155832960⟩ : DyadicInterval 40),(⟨740499681639,740499700969⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198521047936,198521048000⟩ : DyadicInterval 40),(⟨-242439920768,-242439920704⟩ : DyadicInterval 40),(⟨740454006076,740454025406⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198285408448,198285408512⟩ : DyadicInterval 40),(⟨-242088112064,-242088112000⟩ : DyadicInterval 40),(⟨740510564333,740510583663⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198521047936,198521048000⟩ : DyadicInterval 40),(⟨-242439920768,-242439920704⟩ : DyadicInterval 40),(⟨740454006076,740454025406⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,27992667⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27992256,27992320⟩ : DyadicInterval 40),(⟨-27993024,-27992960⟩ : DyadicInterval 40),(⟨762123383223,762123402552⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-768,0⟩ : DyadicInterval 40),(⟨762123383616,762123403264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨217316962201,217572045883⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198308088640,198308088704⟩ : DyadicInterval 40),(⟨-242121965248,-242121965184⟩ : DyadicInterval 40),(⟨740505124416,740505143745⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198521055040,198521055104⟩ : DyadicInterval 40),(⟨-242439931392,-242439931328⟩ : DyadicInterval 40),(⟨740454004374,740454023703⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-43918876288,-43813876544⟩ : DyadicInterval 40),(⟨784030321888,784082841024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨198330777408,198521048000⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-242439920768,-242155832960⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1115_ok : ecellOkT e1115 = true := by decide +kernel
theorem e1115_pos {a z : ℝ} (ha1 : ((80967/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((810519/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1115 e1115_ok ha1 ha2 hz1 hz2 hz

-- box ['810519/4096000', '101421/512000', '3999/4000', '1']  interval_lower 226546473/549755813888
noncomputable def e1116 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1317083665137,0,true,198521047936,198521048000⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨881939590415,0,false,-242439920768,-242439920704⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1317311566840,0,true,198711285568,198711285632⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨881711688712,0,false,-242724081856,-242724081792⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1317029272127,0,true,198475639296,198475639360⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨881993983425,0,false,-242372111232,-242372111168⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539651495,0,true,28023360,28023424⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483604057,0,false,-28024128,-28024064⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627061,0,false,-768,-704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1317056463182,0,true,198498339328,198498339392⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨881966792370,0,false,-242406008640,-242406008576⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1317311575364,0,true,198711292736,198711292800⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨881711680188,0,false,-242724092480,-242724092416⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1056368093891,0,false,-44012799744,-44012799680⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1056469103972,0,false,-43907669312,-43907669248⟩
    { al := (810519/4096000), au := (101421/512000), zl := (3999/4000), zu := 1,
      A := ⟨217572037361,217799939064⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198521047936,198521048000⟩ : DyadicInterval 40),(⟨-242439920768,-242439920704⟩ : DyadicInterval 40),(⟨740454006076,740454025406⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198711285568,198711285632⟩ : DyadicInterval 40),(⟨-242724081856,-242724081792⟩ : DyadicInterval 40),(⟨740408281305,740408300635⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198475639296,198475639360⟩ : DyadicInterval 40),(⟨-242372111232,-242372111168⟩ : DyadicInterval 40),(⟨740464911873,740464931202⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198711285568,198711285632⟩ : DyadicInterval 40),(⟨-242724081856,-242724081792⟩ : DyadicInterval 40),(⟨740408281305,740408300635⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,28023719⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28023360,28023424⟩ : DyadicInterval 40),(⟨-28024128,-28024064⟩ : DyadicInterval 40),(⟨762123383221,762123402550⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-768,0⟩ : DyadicInterval 40),(⟨762123383616,762123403264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨217544835406,217799947588⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198498339328,198498339392⟩ : DyadicInterval 40),(⟨-242406008640,-242406008576⟩ : DyadicInterval 40),(⟨740459460384,740459479713⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198711292736,198711292800⟩ : DyadicInterval 40),(⟨-242724092480,-242724092416⟩ : DyadicInterval 40),(⟨740408279560,740408298890⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-44012799744,-43907669248⟩ : DyadicInterval 40),(⟨784077218240,784129802752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨198521047936,198711285632⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-242724081856,-242439920704⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1116_ok : ecellOkT e1116 = true := by decide +kernel
theorem e1116_pos {a z : ℝ} (ha1 : ((810519/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((101421/512000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1116 e1116_ok ha1 ha2 hz1 hz2 hz

-- box ['101421/512000', '812217/4096000', '999/1000', '3997/4000']  interval_lower 14380639/34359738368
noncomputable def e1117 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1317311566839,0,true,198711285568,198711285632⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨881711688713,0,false,-242724081856,-242724081792⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1317539468542,0,true,198901490304,198901490368⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨881483787010,0,false,-243008316480,-243008316416⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1317093766899,0,true,198529480960,198529481024⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨881929488653,0,false,-242452514624,-242452514560⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1317375947662,0,true,198765020608,198765020672⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨881647307890,0,false,-242804368960,-242804368896⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099595695422,0,true,84064384,84064448⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099427560130,0,false,-84070912,-84070848⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099623843622,0,true,112210112,112210176⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099399411930,0,false,-112221632,-112221568⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511616323,0,false,-11456,-11392⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621349,0,false,-6464,-6400⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1317202662883,0,true,198620383680,198620383744⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨881820592669,0,false,-242588284928,-242588284864⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1317457717505,0,true,198833265408,198833265472⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨881565538047,0,false,-242906349696,-242906349632⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1056310176487,0,false,-44073084224,-44073084160⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1056411231593,0,false,-43967901184,-43967901120⟩
    { al := (101421/512000), au := (812217/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨217799939063,218027840766⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198711285568,198711285632⟩ : DyadicInterval 40),(⟨-242724081856,-242724081792⟩ : DyadicInterval 40),(⟨740408281305,740408300635⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198901490304,198901490368⟩ : DyadicInterval 40),(⟨-243008316480,-243008316416⟩ : DyadicInterval 40),(⟨740362507389,740362526719⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198529480960,198529481024⟩ : DyadicInterval 40),(⟨-242452514624,-242452514560⟩ : DyadicInterval 40),(⟨740451980326,740451999655⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198765020608,198765020672⟩ : DyadicInterval 40),(⟨-242804368960,-242804368896⟩ : DyadicInterval 40),(⟨740395355424,740395374754⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨84067646,112215846⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨84064384,84064448⟩ : DyadicInterval 40),(⟨-84070912,-84070848⟩ : DyadicInterval 40),(⟨762123380388,762123399717⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨112210112,112210176⟩ : DyadicInterval 40),(⟨-112221632,-112221568⟩ : DyadicInterval 40),(⟨762123377858,762123397188⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-11456,-6400⟩ : DyadicInterval 40),(⟨762123386816,762123408608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨217691035107,217946089729⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198620383680,198620383744⟩ : DyadicInterval 40),(⟨-242588284928,-242588284864⟩ : DyadicInterval 40),(⟨740430137254,740430156583⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198833265408,198833265472⟩ : DyadicInterval 40),(⟨-242906349696,-242906349632⟩ : DyadicInterval 40),(⟨740378932681,740378952010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-44073084224,-43967901120⟩ : DyadicInterval 40),(⟨784107334176,784159944992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨198711285568,198901490368⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-243008316480,-242724081792⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1117_ok : ecellOkT e1117 = true := by decide +kernel
theorem e1117_pos {a z : ℝ} (ha1 : ((101421/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((812217/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1117 e1117_ok ha1 ha2 hz1 hz2 hz

-- box ['812217/4096000', '406533/2048000', '999/1000', '3997/4000']  interval_lower 232381381/549755813888
noncomputable def e1118 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1317539468541,0,true,198901490304,198901490368⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨881483787011,0,false,-243008316480,-243008316416⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1317767370245,0,true,199091662144,199091662208⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨881255885307,0,false,-243292624576,-243292624512⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1317321440700,0,true,198719526912,198719526976⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨881701814852,0,false,-242736394816,-242736394752⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1317603678439,0,true,198955073408,198955073472⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨881419577113,0,false,-243088411072,-243088411008⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099595788586,0,true,84157568,84157632⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099427466966,0,false,-84164032,-84163968⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099623967867,0,true,112334336,112334400⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099399287685,0,false,-112345856,-112345792⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511616297,0,false,-11520,-11456⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621335,0,false,-6464,-6400⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1317430450630,0,true,198810509056,198810509120⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨881592804922,0,false,-242872342272,-242872342208⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1317685533749,0,true,199023377728,199023377792⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨881337721803,0,false,-243190524800,-243190524736⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1056219813442,0,false,-44167147008,-44167146944⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1056320985536,0,false,-44061833152,-44061833088⟩
    { al := (812217/4096000), au := (406533/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨218027840765,218255742469⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198901490304,198901490368⟩ : DyadicInterval 40),(⟨-243008316480,-243008316416⟩ : DyadicInterval 40),(⟨740362507389,740362526719⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199091662144,199091662208⟩ : DyadicInterval 40),(⟨-243292624576,-243292624512⟩ : DyadicInterval 40),(⟨740316684290,740316703620⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198719526912,198719526976⟩ : DyadicInterval 40),(⟨-242736394816,-242736394752⟩ : DyadicInterval 40),(⟨740406299147,740406318477⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198955073408,198955073472⟩ : DyadicInterval 40),(⟨-243088411072,-243088411008⟩ : DyadicInterval 40),(⟨740349601961,740349621290⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨84160810,112340091⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨84157568,84157632⟩ : DyadicInterval 40),(⟨-84164032,-84163968⟩ : DyadicInterval 40),(⟨762123380341,762123399671⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨112334336,112334400⟩ : DyadicInterval 40),(⟨-112345856,-112345792⟩ : DyadicInterval 40),(⟨762123377833,762123397163⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-11520,-6400⟩ : DyadicInterval 40),(⟨762123386816,762123408640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨217918822854,218173905973⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198810509056,198810509120⟩ : DyadicInterval 40),(⟨-242872342272,-242872342208⟩ : DyadicInterval 40),(⟨740384409689,740384429019⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199023377728,199023377792⟩ : DyadicInterval 40),(⟨-243190524800,-243190524736⟩ : DyadicInterval 40),(⟨740333144409,740333163738⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-44167147008,-44061833088⟩ : DyadicInterval 40),(⟨784154300160,784206976384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨198901490304,199091662208⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-243292624576,-243008316416⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1118_ok : ecellOkT e1118 = true := by decide +kernel
theorem e1118_pos {a z : ℝ} (ha1 : ((812217/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((406533/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1118 e1118_ok ha1 ha2 hz1 hz2 hz

-- box ['101421/512000', '812217/4096000', '3997/4000', '1999/2000']  interval_lower 114834227/274877906944
noncomputable def e1119 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1317311566839,0,true,198711285568,198711285632⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨881711688713,0,false,-242724081856,-242724081792⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1317539468542,0,true,198901490304,198901490368⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨881483787010,0,false,-243008316480,-243008316416⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1317148216884,0,true,198574934912,198574934976⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨881875038668,0,false,-242520400192,-242520400128⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1317430454622,0,true,198810512384,198810512448⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨881592800930,0,false,-242872347264,-242872347200⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567673200,0,true,56043968,56044032⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455582352,0,false,-56046912,-56046848⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099595790348,0,true,84159296,84159360⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099427465204,0,false,-84165824,-84165760⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621333,0,false,-6464,-6400⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624920,0,false,-2880,-2816⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1317229887187,0,true,198643108480,198643108544⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨881793368365,0,false,-242622230464,-242622230400⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1317484970496,0,true,198856009728,198856009792⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨881538285056,0,false,-242940340864,-242940340800⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1056299371592,0,false,-44084331072,-44084331008⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1056400450702,0,false,-43979121984,-43979121920⟩
    { al := (101421/512000), au := (812217/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨217799939063,218027840766⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198711285568,198711285632⟩ : DyadicInterval 40),(⟨-242724081856,-242724081792⟩ : DyadicInterval 40),(⟨740408281305,740408300635⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198901490304,198901490368⟩ : DyadicInterval 40),(⟨-243008316480,-243008316416⟩ : DyadicInterval 40),(⟨740362507389,740362526719⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198574934912,198574934976⟩ : DyadicInterval 40),(⟨-242520400192,-242520400128⟩ : DyadicInterval 40),(⟨740441059811,740441079140⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198810512384,198810512448⟩ : DyadicInterval 40),(⟨-242872347264,-242872347200⟩ : DyadicInterval 40),(⟨740384408895,740384428224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨56045424,84162572⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56043968,56044032⟩ : DyadicInterval 40),(⟨-56046912,-56046848⟩ : DyadicInterval 40),(⟨762123382167,762123401496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨84159296,84159360⟩ : DyadicInterval 40),(⟨-84165824,-84165760⟩ : DyadicInterval 40),(⟨762123380373,762123399702⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6464,-2816⟩ : DyadicInterval 40),(⟨762123385024,762123406112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨217718259411,217973342720⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198643108480,198643108544⟩ : DyadicInterval 40),(⟨-242622230464,-242622230400⟩ : DyadicInterval 40),(⟨740424674630,740424693960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198856009728,198856009792⟩ : DyadicInterval 40),(⟨-242940340864,-242940340800⟩ : DyadicInterval 40),(⟨740373457746,740373477075⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-44084331072,-43979121920⟩ : DyadicInterval 40),(⟨784112944576,784165568416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨198711285568,198901490368⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-243008316480,-242724081792⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1119_ok : ecellOkT e1119 = true := by decide +kernel
theorem e1119_pos {a z : ℝ} (ha1 : ((101421/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((812217/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1119 e1119_ok ha1 ha2 hz1 hz2 hz

-- box ['812217/4096000', '406533/2048000', '3997/4000', '1999/2000']  interval_lower 463916037/1099511627776
noncomputable def e1120 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1317539468541,0,true,198901490304,198901490368⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨881483787011,0,false,-243008316480,-243008316416⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1317767370245,0,true,199091662144,199091662208⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨881255885307,0,false,-243292624576,-243292624512⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1317375947660,0,true,198765020608,198765020672⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨881647307892,0,false,-242804368960,-242804368896⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1317658242374,0,true,199000604864,199000604928⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨881365013178,0,false,-243156478016,-243156477952⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567735312,0,true,56106048,56106112⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455520240,0,false,-56108992,-56108928⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099595883533,0,true,84252480,84252544⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099427372019,0,false,-84259008,-84258944⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621319,0,false,-6464,-6400⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624913,0,false,-2880,-2816⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1317457703425,0,true,198833253696,198833253760⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨881565552127,0,false,-242906332160,-242906332096⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1317712815225,0,true,199046141888,199046141952⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨881310440327,0,false,-243224560320,-243224560256⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1056208985947,0,false,-44178418368,-44178418304⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1056310182070,0,false,-44073078400,-44073078336⟩
    { al := (812217/4096000), au := (406533/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨218027840765,218255742469⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198901490304,198901490368⟩ : DyadicInterval 40),(⟨-243008316480,-243008316416⟩ : DyadicInterval 40),(⟨740362507389,740362526719⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199091662144,199091662208⟩ : DyadicInterval 40),(⟨-243292624576,-243292624512⟩ : DyadicInterval 40),(⟨740316684290,740316703620⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198765020608,198765020672⟩ : DyadicInterval 40),(⟨-242804368960,-242804368896⟩ : DyadicInterval 40),(⟨740395355425,740395374754⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199000604864,199000604928⟩ : DyadicInterval 40),(⟨-243156478016,-243156477952⟩ : DyadicInterval 40),(⟨740338632224,740338651553⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨56107536,84255757⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56106048,56106112⟩ : DyadicInterval 40),(⟨-56108992,-56108928⟩ : DyadicInterval 40),(⟨762123382160,762123401489⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨84252480,84252544⟩ : DyadicInterval 40),(⟨-84259008,-84258944⟩ : DyadicInterval 40),(⟨762123380359,762123399688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6464,-2816⟩ : DyadicInterval 40),(⟨762123385024,762123406112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨217946075649,218201187449⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198833253696,198833253760⟩ : DyadicInterval 40),(⟨-242906332160,-242906332096⟩ : DyadicInterval 40),(⟨740378935496,740378954826⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199046141888,199046141952⟩ : DyadicInterval 40),(⟨-243224560320,-243224560256⟩ : DyadicInterval 40),(⟨740327657876,740327677205⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-44178418368,-44073078336⟩ : DyadicInterval 40),(⟨784159922784,784212612064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨198901490304,199091662208⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-243292624576,-243008316416⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1120_ok : ecellOkT e1120 = true := by decide +kernel
theorem e1120_pos {a z : ℝ} (ha1 : ((812217/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((406533/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1120 e1120_ok ha1 ha2 hz1 hz2 hz

-- box ['406533/2048000', '162783/819200', '999/1000', '3997/4000']  interval_lower 117341015/274877906944
noncomputable def e1121 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1317767370244,0,true,199091662144,199091662208⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨881255885308,0,false,-243292624576,-243292624512⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1317995271947,0,true,199281801152,199281801216⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨881027983605,0,false,-243577006208,-243577006144⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1317549114501,0,true,198909540032,198909540096⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨881474141051,0,false,-243020348352,-243020348288⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1317831409215,0,true,199145093376,199145093440⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨881191846337,0,false,-243372526592,-243372526528⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099595881768,0,true,84250752,84250816⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099427373784,0,false,-84257280,-84257216⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099624092135,0,true,112458560,112458624⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099399163417,0,false,-112470144,-112470080⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511616272,0,false,-11520,-11456⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621320,0,false,-6464,-6400⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1317658238380,0,true,199000601536,199000601600⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨881365017172,0,false,-243156473024,-243156472960⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1317913349996,0,true,199213457216,199213457280⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨881109905556,0,false,-243474773376,-243474773312⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1056129355989,0,false,-44261316160,-44261316096⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1056230645097,0,false,-44155871488,-44155871424⟩
    { al := (406533/2048000), au := (162783/819200), zl := (999/1000), zu := (3997/4000),
      A := ⟨218255742468,218483644171⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199091662144,199091662208⟩ : DyadicInterval 40),(⟨-243292624576,-243292624512⟩ : DyadicInterval 40),(⟨740316684291,740316703620⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199281801152,199281801216⟩ : DyadicInterval 40),(⟨-243577006208,-243577006144⟩ : DyadicInterval 40),(⟨740270811983,740270831313⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198909540032,198909540096⟩ : DyadicInterval 40),(⟨-243020348352,-243020348288⟩ : DyadicInterval 40),(⟨740360568905,740360588235⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199145093376,199145093440⟩ : DyadicInterval 40),(⟨-243372526592,-243372526528⟩ : DyadicInterval 40),(⟨740303799395,740303818724⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨84253992,112464359⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨84250752,84250816⟩ : DyadicInterval 40),(⟨-84257280,-84257216⟩ : DyadicInterval 40),(⟨762123380359,762123399688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨112458560,112458624⟩ : DyadicInterval 40),(⟨-112470144,-112470080⟩ : DyadicInterval 40),(⟨762123377840,762123397169⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-11520,-6400⟩ : DyadicInterval 40),(⟨762123386816,762123408640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨218146610604,218401722220⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199000601536,199000601600⟩ : DyadicInterval 40),(⟨-243156473024,-243156472960⟩ : DyadicInterval 40),(⟨740338633020,740338652350⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199213457216,199213457280⟩ : DyadicInterval 40),(⟨-243474773376,-243474773312⟩ : DyadicInterval 40),(⟨740287306981,740287326310⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-44261316160,-44155871424⟩ : DyadicInterval 40),(⟨784201319328,784254060960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨199091662144,199281801216⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-243577006208,-243292624512⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1121_ok : ecellOkT e1121 = true := by decide +kernel
theorem e1121_pos {a z : ℝ} (ha1 : ((406533/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((162783/819200 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1121 e1121_ok ha1 ha2 hz1 hz2 hz

-- box ['162783/819200', '203691/1024000', '999/1000', '3997/4000']  interval_lower 473983863/1099511627776
noncomputable def e1122 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1317995271946,0,true,199281801152,199281801216⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨881027983606,0,false,-243577006208,-243577006144⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1318223173649,0,true,199471907200,199471907264⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨880800081903,0,false,-243861461376,-243861461312⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1317776788301,0,true,199099520320,199099520384⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨881246467251,0,false,-243304375168,-243304375104⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1318059139990,0,true,199335080512,199335080576⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨880964115562,0,false,-243656715584,-243656715520⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099595974966,0,true,84343936,84344000⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099427280586,0,false,-84350464,-84350400⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099624216425,0,true,112582848,112582912⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099399039127,0,false,-112594432,-112594368⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511616247,0,false,-11584,-11520⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621306,0,false,-6528,-6464⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1317886026137,0,true,199190661184,199190661248⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨881137229415,0,false,-243440677248,-243440677184⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1318141166236,0,true,199403503808,199403503872⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨880882089316,0,false,-243759095488,-243759095424⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1056038804133,0,false,-44355591616,-44355591552⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1056140210272,0,false,-44250016064,-44250016000⟩
    { al := (162783/819200), au := (203691/1024000), zl := (999/1000), zu := (3997/4000),
      A := ⟨218483644170,218711545873⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199281801152,199281801216⟩ : DyadicInterval 40),(⟨-243577006208,-243577006144⟩ : DyadicInterval 40),(⟨740270811983,740270831313⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199471907200,199471907264⟩ : DyadicInterval 40),(⟨-243861461376,-243861461312⟩ : DyadicInterval 40),(⟨740224890533,740224909862⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199099520320,199099520384⟩ : DyadicInterval 40),(⟨-243304375168,-243304375104⟩ : DyadicInterval 40),(⟨740314789561,740314808890⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199335080512,199335080576⟩ : DyadicInterval 40),(⟨-243656715584,-243656715520⟩ : DyadicInterval 40),(⟨740257947739,740257967068⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨84347190,112588649⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨84343936,84344000⟩ : DyadicInterval 40),(⟨-84350464,-84350400⟩ : DyadicInterval 40),(⟨762123380345,762123399674⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨112582848,112582912⟩ : DyadicInterval 40),(⟨-112594432,-112594368⟩ : DyadicInterval 40),(⟨762123377814,762123397144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-11584,-6464⟩ : DyadicInterval 40),(⟨762123386848,762123408672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨218374398361,218629538460⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199190661184,199190661248⟩ : DyadicInterval 40),(⟨-243440677248,-243440677184⟩ : DyadicInterval 40),(⟨740292807220,740292826550⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199403503808,199403503872⟩ : DyadicInterval 40),(⟨-243759095488,-243759095424⟩ : DyadicInterval 40),(⟨740241420449,740241439779⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-44355591616,-44250016000⟩ : DyadicInterval 40),(⟨784248391616,784301198688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨199281801152,199471907264⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-243861461376,-243577006144⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1122_ok : ecellOkT e1122 = true := by decide +kernel
theorem e1122_pos {a z : ℝ} (ha1 : ((162783/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((203691/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1122 e1122_ok ha1 ha2 hz1 hz2 hz

-- box ['406533/2048000', '162783/819200', '3997/4000', '1999/2000']  interval_lower 468513889/1099511627776
noncomputable def e1123 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1317767370244,0,true,199091662144,199091662208⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨881255885308,0,false,-243292624576,-243292624512⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1317995271947,0,true,199281801152,199281801216⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨881027983605,0,false,-243577006208,-243577006144⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1317603678437,0,true,198955073408,198955073472⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨881419577115,0,false,-243088411072,-243088411008⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1317886030126,0,true,199190664512,199190664576⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨881137225426,0,false,-243440682240,-243440682176⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567797434,0,true,56168192,56168256⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455458118,0,false,-56171136,-56171072⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099595976736,0,true,84345664,84345728⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099427278816,0,false,-84352256,-84352192⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621305,0,false,-6528,-6464⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624907,0,false,-2880,-2816⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1317685519664,0,true,199023366016,199023366080⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨881337735888,0,false,-243190507264,-243190507200⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1317940659959,0,true,199236241216,199236241280⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨881082595593,0,false,-243508853248,-243508853184⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1056118505870,0,false,-44272611968,-44272611904⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1056219819032,0,false,-44167141184,-44167141120⟩
    { al := (406533/2048000), au := (162783/819200), zl := (3997/4000), zu := (1999/2000),
      A := ⟨218255742468,218483644171⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199091662144,199091662208⟩ : DyadicInterval 40),(⟨-243292624576,-243292624512⟩ : DyadicInterval 40),(⟨740316684291,740316703620⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199281801152,199281801216⟩ : DyadicInterval 40),(⟨-243577006208,-243577006144⟩ : DyadicInterval 40),(⟨740270811983,740270831313⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198955073408,198955073472⟩ : DyadicInterval 40),(⟨-243088411072,-243088411008⟩ : DyadicInterval 40),(⟨740349601961,740349621291⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199190664512,199190664576⟩ : DyadicInterval 40),(⟨-243440682240,-243440682176⟩ : DyadicInterval 40),(⟨740292806423,740292825753⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨56169658,84348960⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56168192,56168256⟩ : DyadicInterval 40),(⟨-56171136,-56171072⟩ : DyadicInterval 40),(⟨762123382154,762123401483⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨84345664,84345728⟩ : DyadicInterval 40),(⟨-84352256,-84352192⟩ : DyadicInterval 40),(⟨762123380376,762123399706⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6528,-2816⟩ : DyadicInterval 40),(⟨762123385024,762123406144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨218173891888,218429032183⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199023366016,199023366080⟩ : DyadicInterval 40),(⟨-243190507264,-243190507200⟩ : DyadicInterval 40),(⟨740333147231,740333166560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199236241216,199236241280⟩ : DyadicInterval 40),(⟨-243508853248,-243508853184⟩ : DyadicInterval 40),(⟨740281808822,740281828152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-44272611968,-44167141120⟩ : DyadicInterval 40),(⟨784206954176,784259708864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨199091662144,199281801216⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-243577006208,-243292624512⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1123_ok : ecellOkT e1123 = true := by decide +kernel
theorem e1123_pos {a z : ℝ} (ha1 : ((406533/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((162783/819200 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1123 e1123_ok ha1 ha2 hz1 hz2 hz

-- box ['162783/819200', '203691/1024000', '3997/4000', '1999/2000']  interval_lower 473130323/1099511627776
noncomputable def e1124 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1317995271946,0,true,199281801152,199281801216⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨881027983606,0,false,-243577006208,-243577006144⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1318223173649,0,true,199471907200,199471907264⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨880800081903,0,false,-243861461376,-243861461312⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1317831409212,0,true,199145093376,199145093440⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨881191846340,0,false,-243372526592,-243372526528⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1318113817877,0,true,199380691264,199380691328⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨880909437675,0,false,-243724959936,-243724959872⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567859568,0,true,56230336,56230400⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455395984,0,false,-56233280,-56233216⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099596069956,0,true,84438912,84438976⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099427185596,0,false,-84445440,-84445376⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621290,0,false,-6528,-6464⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624901,0,false,-2880,-2816⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1317913335905,0,true,199213445440,199213445504⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨881109919647,0,false,-243474755776,-243474755712⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1318168504683,0,true,199426307648,199426307712⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨880854750869,0,false,-243793219648,-243793219584⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1056027931368,0,false,-44366912000,-44366911936⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1056129361588,0,false,-44261310272,-44261310208⟩
    { al := (162783/819200), au := (203691/1024000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨218483644170,218711545873⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199281801152,199281801216⟩ : DyadicInterval 40),(⟨-243577006208,-243577006144⟩ : DyadicInterval 40),(⟨740270811983,740270831313⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199471907200,199471907264⟩ : DyadicInterval 40),(⟨-243861461376,-243861461312⟩ : DyadicInterval 40),(⟨740224890533,740224909862⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199145093376,199145093440⟩ : DyadicInterval 40),(⟨-243372526592,-243372526528⟩ : DyadicInterval 40),(⟨740303799396,740303818725⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199380691264,199380691328⟩ : DyadicInterval 40),(⟨-243724959936,-243724959872⟩ : DyadicInterval 40),(⟨740246931519,740246950848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨56231792,84442180⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56230336,56230400⟩ : DyadicInterval 40),(⟨-56233280,-56233216⟩ : DyadicInterval 40),(⟨762123382148,762123401477⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨84438912,84438976⟩ : DyadicInterval 40),(⟨-84445440,-84445376⟩ : DyadicInterval 40),(⟨762123380330,762123399660⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6528,-2816⟩ : DyadicInterval 40),(⟨762123385024,762123406144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨218401708129,218656876907⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199213445440,199213445504⟩ : DyadicInterval 40),(⟨-243474755776,-243474755712⟩ : DyadicInterval 40),(⟨740287309823,740287329152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199426307648,199426307712⟩ : DyadicInterval 40),(⟨-243793219648,-243793219584⟩ : DyadicInterval 40),(⟨740235910616,740235929945⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-44366912000,-44261310208⟩ : DyadicInterval 40),(⟨784254038720,784306858880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨199281801152,199471907264⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-243861461376,-243577006144⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1124_ok : ecellOkT e1124 = true := by decide +kernel
theorem e1124_pos {a z : ℝ} (ha1 : ((162783/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((203691/1024000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1124 e1124_ok ha1 ha2 hz1 hz2 hz

-- box ['101421/512000', '812217/4096000', '1999/2000', '3999/4000']  interval_lower 229246217/549755813888
noncomputable def e1125 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1317311566839,0,true,198711285568,198711285632⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨881711688713,0,false,-242724081856,-242724081792⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1317539468542,0,true,198901490304,198901490368⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨881483787010,0,false,-243008316480,-243008316416⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1317202666869,0,true,198620387008,198620387072⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨881820588683,0,false,-242588289856,-242588289792⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1317484961582,0,true,198856002304,198856002368⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨881538293970,0,false,-242940329728,-242940329664⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539650567,0,true,28022400,28022464⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483604985,0,false,-28023168,-28023104⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567736658,0,true,56107392,56107456⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455518894,0,false,-56110336,-56110272⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624912,0,false,-2880,-2816⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627062,0,false,-768,-704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1317257111695,0,true,198665832960,198665833024⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨881766143857,0,false,-242656177344,-242656177280⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1317512223685,0,true,198878753728,198878753792⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨881511031867,0,false,-242974333312,-242974333248⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1056288565267,0,false,-44095579584,-44095579520⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1056389668382,0,false,-43990344384,-43990344320⟩
    { al := (101421/512000), au := (812217/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨217799939063,218027840766⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198711285568,198711285632⟩ : DyadicInterval 40),(⟨-242724081856,-242724081792⟩ : DyadicInterval 40),(⟨740408281305,740408300635⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198901490304,198901490368⟩ : DyadicInterval 40),(⟨-243008316480,-243008316416⟩ : DyadicInterval 40),(⟨740362507389,740362526719⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198620387008,198620387072⟩ : DyadicInterval 40),(⟨-242588289856,-242588289792⟩ : DyadicInterval 40),(⟨740430136437,740430155766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198856002304,198856002368⟩ : DyadicInterval 40),(⟨-242940329728,-242940329664⟩ : DyadicInterval 40),(⟨740373459520,740373478849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨28022791,56108882⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28022400,28022464⟩ : DyadicInterval 40),(⟨-28023168,-28023104⟩ : DyadicInterval 40),(⟨762123383221,762123402550⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56107392,56107456⟩ : DyadicInterval 40),(⟨-56110336,-56110272⟩ : DyadicInterval 40),(⟨762123382160,762123401489⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2880,-704⟩ : DyadicInterval 40),(⟨762123383968,762123404320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨217745483919,218000595909⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198665832960,198665833024⟩ : DyadicInterval 40),(⟨-242656177344,-242656177280⟩ : DyadicInterval 40),(⟨740419211293,740419230623⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198878753728,198878753792⟩ : DyadicInterval 40),(⟨-242974333312,-242974333248⟩ : DyadicInterval 40),(⟨740367982069,740368001399⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-44095579584,-43990344320⟩ : DyadicInterval 40),(⟨784118555776,784171192672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨198711285568,198901490368⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-243008316480,-242724081792⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1125_ok : ecellOkT e1125 = true := by decide +kernel
theorem e1125_pos {a z : ℝ} (ha1 : ((101421/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((812217/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1125 e1125_ok ha1 ha2 hz1 hz2 hz

-- box ['812217/4096000', '406533/2048000', '1999/2000', '3999/4000']  interval_lower 115767121/274877906944
noncomputable def e1126 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1317539468541,0,true,198901490304,198901490368⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨881483787011,0,false,-243008316480,-243008316416⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1317767370245,0,true,199091662144,199091662208⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨881255885307,0,false,-243292624576,-243292624512⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1317430454620,0,true,198810512384,198810512448⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨881592800932,0,false,-242872347264,-242872347200⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1317712806310,0,true,199046134464,199046134528⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨881310449242,0,false,-243224549184,-243224549120⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539681623,0,true,28053440,28053504⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483573929,0,false,-28054208,-28054144⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567798783,0,true,56169536,56169600⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455456769,0,false,-56172480,-56172416⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624906,0,false,-2880,-2816⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627061,0,false,-768,-704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1317484956415,0,true,198855998016,198855998080⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨881538299137,0,false,-242940323328,-242940323264⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1317740096899,0,true,199068905728,199068905792⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨881283158653,0,false,-243258597120,-243258597056⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1056198157019,0,false,-44189691328,-44189691264⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1056299377176,0,false,-44084325312,-44084325248⟩
    { al := (812217/4096000), au := (406533/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨218027840765,218255742469⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198901490304,198901490368⟩ : DyadicInterval 40),(⟨-243008316480,-243008316416⟩ : DyadicInterval 40),(⟨740362507389,740362526719⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199091662144,199091662208⟩ : DyadicInterval 40),(⟨-243292624576,-243292624512⟩ : DyadicInterval 40),(⟨740316684290,740316703620⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198810512384,198810512448⟩ : DyadicInterval 40),(⟨-242872347264,-242872347200⟩ : DyadicInterval 40),(⟨740384408895,740384428225⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199046134464,199046134528⟩ : DyadicInterval 40),(⟨-243224549184,-243224549120⟩ : DyadicInterval 40),(⟨740327659654,740327678984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨28053847,56171007⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28053440,28053504⟩ : DyadicInterval 40),(⟨-28054208,-28054144⟩ : DyadicInterval 40),(⟨762123383220,762123402549⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56169536,56169600⟩ : DyadicInterval 40),(⟨-56172480,-56172416⟩ : DyadicInterval 40),(⟨762123382154,762123401483⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2880,-704⟩ : DyadicInterval 40),(⟨762123383968,762123404320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨217973328639,218228469123⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198855998016,198855998080⟩ : DyadicInterval 40),(⟨-242940323328,-242940323264⟩ : DyadicInterval 40),(⟨740373460562,740373479891⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199068905728,199068905792⟩ : DyadicInterval 40),(⟨-243258597120,-243258597056⟩ : DyadicInterval 40),(⟨740322170598,740322189927⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-44189691328,-44084325248⟩ : DyadicInterval 40),(⟨784165546240,784218248544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨198901490304,199091662208⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-243292624576,-243008316416⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1126_ok : ecellOkT e1126 = true := by decide +kernel
theorem e1126_pos {a z : ℝ} (ha1 : ((812217/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((406533/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1126 e1126_ok ha1 ha2 hz1 hz2 hz

-- box ['101421/512000', '812217/4096000', '3999/4000', '1']  interval_lower 457647215/1099511627776
noncomputable def e1127 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1317311566839,0,true,198711285568,198711285632⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨881711688713,0,false,-242724081856,-242724081792⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1317539468542,0,true,198901490304,198901490368⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨881483787010,0,false,-243008316480,-243008316416⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1317257116854,0,true,198665837248,198665837312⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨881766138698,0,false,-242656183808,-242656183744⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539682553,0,true,28054400,28054464⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483572999,0,false,-28055168,-28055104⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627060,0,false,-768,-704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1317284336392,0,true,198688557120,198688557184⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨881738919160,0,false,-242690125504,-242690125440⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1317539477062,0,true,198901497472,198901497536⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨881483778490,0,false,-243008327104,-243008327040⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1056277757516,0,false,-44106829632,-44106829568⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1056378884639,0,false,-44001568384,-44001568320⟩
    { al := (101421/512000), au := (812217/4096000), zl := (3999/4000), zu := 1,
      A := ⟨217799939063,218027840766⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198711285568,198711285632⟩ : DyadicInterval 40),(⟨-242724081856,-242724081792⟩ : DyadicInterval 40),(⟨740408281305,740408300635⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198901490304,198901490368⟩ : DyadicInterval 40),(⟨-243008316480,-243008316416⟩ : DyadicInterval 40),(⟨740362507389,740362526719⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198665837248,198665837312⟩ : DyadicInterval 40),(⟨-242656183808,-242656183744⟩ : DyadicInterval 40),(⟨740419210281,740419229611⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198901490304,198901490368⟩ : DyadicInterval 40),(⟨-243008316480,-243008316416⟩ : DyadicInterval 40),(⟨740362507389,740362526719⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,28054777⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28054400,28054464⟩ : DyadicInterval 40),(⟨-28055168,-28055104⟩ : DyadicInterval 40),(⟨762123383220,762123402549⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-768,0⟩ : DyadicInterval 40),(⟨762123383616,762123403264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨217772708616,218027849286⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198688557120,198688557184⟩ : DyadicInterval 40),(⟨-242690125504,-242690125440⟩ : DyadicInterval 40),(⟨740413747220,740413766550⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198901497472,198901497536⟩ : DyadicInterval 40),(⟨-243008327104,-243008327040⟩ : DyadicInterval 40),(⟨740362505641,740362524970⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-44106829632,-44001568320⟩ : DyadicInterval 40),(⟨784124167776,784176817696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨198711285568,198901490368⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-243008316480,-242724081792⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1127_ok : ecellOkT e1127 = true := by decide +kernel
theorem e1127_pos {a z : ℝ} (ha1 : ((101421/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((812217/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1127 e1127_ok ha1 ha2 hz1 hz2 hz

-- box ['812217/4096000', '406533/2048000', '3999/4000', '1']  interval_lower 462220017/1099511627776
noncomputable def e1128 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1317539468541,0,true,198901490304,198901490368⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨881483787011,0,false,-243008316480,-243008316416⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1317767370245,0,true,199091662144,199091662208⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨881255885307,0,false,-243292624576,-243292624512⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1317484961580,0,true,198856002304,198856002368⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨881538293972,0,false,-242940329728,-242940329664⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539713616,0,true,28085440,28085504⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483541936,0,false,-28086208,-28086144⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627058,0,false,-768,-704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1317512209604,0,true,198878742016,198878742080⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨881511045948,0,false,-242974315776,-242974315712⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1317767378766,0,true,199091669312,199091669376⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨881255876786,0,false,-243292635200,-243292635136⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1056187326661,0,false,-44200965888,-44200965824⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1056288570851,0,false,-44095573760,-44095573696⟩
    { al := (812217/4096000), au := (406533/2048000), zl := (3999/4000), zu := 1,
      A := ⟨218027840765,218255742469⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198901490304,198901490368⟩ : DyadicInterval 40),(⟨-243008316480,-243008316416⟩ : DyadicInterval 40),(⟨740362507389,740362526719⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199091662144,199091662208⟩ : DyadicInterval 40),(⟨-243292624576,-243292624512⟩ : DyadicInterval 40),(⟨740316684290,740316703620⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198856002304,198856002368⟩ : DyadicInterval 40),(⟨-242940329728,-242940329664⟩ : DyadicInterval 40),(⟨740373459521,740373478850⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199091662144,199091662208⟩ : DyadicInterval 40),(⟨-243292624576,-243292624512⟩ : DyadicInterval 40),(⟨740316684290,740316703620⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,28085840⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28085440,28085504⟩ : DyadicInterval 40),(⟨-28086208,-28086144⟩ : DyadicInterval 40),(⟨762123383218,762123402547⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-768,0⟩ : DyadicInterval 40),(⟨762123383616,762123403264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨218000581828,218255750990⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨198878742016,198878742080⟩ : DyadicInterval 40),(⟨-242974315776,-242974315712⟩ : DyadicInterval 40),(⟨740367984886,740368004215⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199091669312,199091669376⟩ : DyadicInterval 40),(⟨-243292635200,-243292635136⟩ : DyadicInterval 40),(⟨740316682538,740316701867⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-44200965888,-44095573696⟩ : DyadicInterval 40),(⟨784171170464,784223885824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨198901490304,199091662208⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-243292624576,-243008316416⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1128_ok : ecellOkT e1128 = true := by decide +kernel
theorem e1128_pos {a z : ℝ} (ha1 : ((812217/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((406533/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1128 e1128_ok ha1 ha2 hz1 hz2 hz

-- box ['406533/2048000', '162783/819200', '1999/2000', '3999/4000']  interval_lower 467663113/1099511627776
noncomputable def e1129 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1317767370244,0,true,199091662144,199091662208⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨881255885308,0,false,-243292624576,-243292624512⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1317995271947,0,true,199281801152,199281801216⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨881027983605,0,false,-243577006208,-243577006144⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1317658242372,0,true,199000604864,199000604928⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨881365013180,0,false,-243156478016,-243156477952⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1317940651037,0,true,199236233728,199236233792⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨881082604515,0,false,-243508842112,-243508842048⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539712684,0,true,28084544,28084608⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483542868,0,false,-28085312,-28085248⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567860920,0,true,56231680,56231744⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455394632,0,false,-56234624,-56234560⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624900,0,false,-2880,-2816⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627059,0,false,-768,-704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1317712801139,0,true,199046130176,199046130240⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨881310454413,0,false,-243224542720,-243224542656⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1317967970115,0,true,199259024896,199259024960⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨881055285437,0,false,-243542934400,-243542934336⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1056107654318,0,false,-44283909440,-44283909376⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1056208991539,0,false,-44178412544,-44178412480⟩
    { al := (406533/2048000), au := (162783/819200), zl := (1999/2000), zu := (3999/4000),
      A := ⟨218255742468,218483644171⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199091662144,199091662208⟩ : DyadicInterval 40),(⟨-243292624576,-243292624512⟩ : DyadicInterval 40),(⟨740316684291,740316703620⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199281801152,199281801216⟩ : DyadicInterval 40),(⟨-243577006208,-243577006144⟩ : DyadicInterval 40),(⟨740270811983,740270831313⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199000604864,199000604928⟩ : DyadicInterval 40),(⟨-243156478016,-243156477952⟩ : DyadicInterval 40),(⟨740338632224,740338651554⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199236233728,199236233792⟩ : DyadicInterval 40),(⟨-243508842112,-243508842048⟩ : DyadicInterval 40),(⟨740281810645,740281829974⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨28084908,56233144⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28084544,28084608⟩ : DyadicInterval 40),(⟨-28085312,-28085248⟩ : DyadicInterval 40),(⟨762123383218,762123402547⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56231680,56231744⟩ : DyadicInterval 40),(⟨-56234624,-56234560⟩ : DyadicInterval 40),(⟨762123382147,762123401477⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2880,-704⟩ : DyadicInterval 40),(⟨762123383968,762123404320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨218201173363,218456342339⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199046130176,199046130240⟩ : DyadicInterval 40),(⟨-243224542720,-243224542656⟩ : DyadicInterval 40),(⟨740327660673,740327680003⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199259024896,199259024960⟩ : DyadicInterval 40),(⟨-243542934400,-243542934336⟩ : DyadicInterval 40),(⟨740276309918,740276329247⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-44283909440,-44178412480⟩ : DyadicInterval 40),(⟨784212589856,784265357600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨199091662144,199281801216⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-243577006208,-243292624512⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1129_ok : ecellOkT e1129 = true := by decide +kernel
theorem e1129_pos {a z : ℝ} (ha1 : ((406533/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((162783/819200 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1129 e1129_ok ha1 ha2 hz1 hz2 hz

-- box ['162783/819200', '203691/1024000', '1999/2000', '3999/4000']  interval_lower 472276133/1099511627776
noncomputable def e1130 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1317995271946,0,true,199281801152,199281801216⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨881027983606,0,false,-243577006208,-243577006144⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1318223173649,0,true,199471907200,199471907264⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨880800081903,0,false,-243861461376,-243861461312⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1317886030123,0,true,199190664512,199190664576⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨881137225429,0,false,-243440682240,-243440682176⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1318168495763,0,true,199426300160,199426300224⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨880854759789,0,false,-243793208512,-243793208448⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539743752,0,true,28115584,28115648⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483511800,0,false,-28116352,-28116288⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567923068,0,true,56293824,56293888⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455332484,0,false,-56296768,-56296704⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624893,0,false,-2944,-2880⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627058,0,false,-768,-704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1317940645867,0,true,199236229440,199236229504⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨881082609685,0,false,-243508835648,-243508835584⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1318195843331,0,true,199449111104,199449111168⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨880827412221,0,false,-243827345216,-243827345152⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1056017057164,0,false,-44378234048,-44378233984⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1056118511470,0,false,-44272606144,-44272606080⟩
    { al := (162783/819200), au := (203691/1024000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨218483644170,218711545873⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199281801152,199281801216⟩ : DyadicInterval 40),(⟨-243577006208,-243577006144⟩ : DyadicInterval 40),(⟨740270811983,740270831313⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199471907200,199471907264⟩ : DyadicInterval 40),(⟨-243861461376,-243861461312⟩ : DyadicInterval 40),(⟨740224890533,740224909862⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199190664512,199190664576⟩ : DyadicInterval 40),(⟨-243440682240,-243440682176⟩ : DyadicInterval 40),(⟨740292806424,740292825753⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199426300160,199426300224⟩ : DyadicInterval 40),(⟨-243793208512,-243793208448⟩ : DyadicInterval 40),(⟨740235912442,740235931771⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨28115976,56295292⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28115584,28115648⟩ : DyadicInterval 40),(⟨-28116352,-28116288⟩ : DyadicInterval 40),(⟨762123383217,762123402546⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56293824,56293888⟩ : DyadicInterval 40),(⟨-56296768,-56296704⟩ : DyadicInterval 40),(⟨762123382141,762123401470⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2944,-704⟩ : DyadicInterval 40),(⟨762123383968,762123404352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨218429018091,218684215555⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199236229440,199236229504⟩ : DyadicInterval 40),(⟨-243508835648,-243508835584⟩ : DyadicInterval 40),(⟨740281811666,740281830995⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199449111104,199449111168⟩ : DyadicInterval 40),(⟨-243827345216,-243827345152⟩ : DyadicInterval 40),(⟨740230400120,740230419450⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-44378234048,-44272606080⟩ : DyadicInterval 40),(⟨784259686656,784312519904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨199281801152,199471907264⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-243861461376,-243577006144⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1130_ok : ecellOkT e1130 = true := by decide +kernel
theorem e1130_pos {a z : ℝ} (ha1 : ((162783/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((203691/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1130 e1130_ok ha1 ha2 hz1 hz2 hz

-- box ['406533/2048000', '162783/819200', '3999/4000', '1']  interval_lower 466811301/1099511627776
noncomputable def e1131 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1317767370244,0,true,199091662144,199091662208⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨881255885308,0,false,-243292624576,-243292624512⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1317995271947,0,true,199281801152,199281801216⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨881027983605,0,false,-243577006208,-243577006144⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1317712806308,0,true,199046134464,199046134528⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨881310449244,0,false,-243224549184,-243224549120⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539744686,0,true,28116544,28116608⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483510866,0,false,-28117312,-28117248⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627056,0,false,-768,-704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1317740082813,0,true,199068894016,199068894080⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨881283172739,0,false,-243258579520,-243258579456⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1317995280476,0,true,199281808256,199281808320⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨881027975076,0,false,-243577016832,-243577016768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1056096801328,0,false,-44295208576,-44295208512⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1056198162612,0,false,-44189685504,-44189685440⟩
    { al := (406533/2048000), au := (162783/819200), zl := (3999/4000), zu := 1,
      A := ⟨218255742468,218483644171⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199091662144,199091662208⟩ : DyadicInterval 40),(⟨-243292624576,-243292624512⟩ : DyadicInterval 40),(⟨740316684291,740316703620⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199281801152,199281801216⟩ : DyadicInterval 40),(⟨-243577006208,-243577006144⟩ : DyadicInterval 40),(⟨740270811983,740270831313⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199046134464,199046134528⟩ : DyadicInterval 40),(⟨-243224549184,-243224549120⟩ : DyadicInterval 40),(⟨740327659654,740327678984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199281801152,199281801216⟩ : DyadicInterval 40),(⟨-243577006208,-243577006144⟩ : DyadicInterval 40),(⟨740270811983,740270831313⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,28116910⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28116544,28116608⟩ : DyadicInterval 40),(⟨-28117312,-28117248⟩ : DyadicInterval 40),(⟨762123383216,762123402545⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-768,0⟩ : DyadicInterval 40),(⟨762123383616,762123403264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨218228455037,218483652700⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199068894016,199068894080⟩ : DyadicInterval 40),(⟨-243258579520,-243258579456⟩ : DyadicInterval 40),(⟨740322173396,740322192725⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199281808256,199281808320⟩ : DyadicInterval 40),(⟨-243577016832,-243577016768⟩ : DyadicInterval 40),(⟨740270810264,740270829594⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-44295208576,-44189685440⟩ : DyadicInterval 40),(⟨784218226336,784271007168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨199091662144,199281801216⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-243577006208,-243292624512⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1131_ok : ecellOkT e1131 = true := by decide +kernel
theorem e1131_pos {a z : ℝ} (ha1 : ((406533/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((162783/819200 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1131 e1131_ok ha1 ha2 hz1 hz2 hz

-- box ['162783/819200', '203691/1024000', '3999/4000', '1']  interval_lower 235710613/549755813888
noncomputable def e1132 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1317995271946,0,true,199281801152,199281801216⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨881027983606,0,false,-243577006208,-243577006144⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1318223173649,0,true,199471907200,199471907264⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨880800081903,0,false,-243861461376,-243861461312⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1317940651034,0,true,199236233728,199236233792⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨881082604518,0,false,-243508842112,-243508842048⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099539775760,0,true,28147584,28147648⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099483479792,0,false,-28148352,-28148288⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627055,0,false,-768,-704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1317967956023,0,true,199259013120,199259013184⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨881055299529,0,false,-243542916800,-243542916736⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1318223182177,0,true,199471914304,199471914368⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨880800073375,0,false,-243861472000,-243861471936⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1056006181521,0,false,-44389557696,-44389557632⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1056107659919,0,false,-44283903616,-44283903552⟩
    { al := (162783/819200), au := (203691/1024000), zl := (3999/4000), zu := 1,
      A := ⟨218483644170,218711545873⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199281801152,199281801216⟩ : DyadicInterval 40),(⟨-243577006208,-243577006144⟩ : DyadicInterval 40),(⟨740270811983,740270831313⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199471907200,199471907264⟩ : DyadicInterval 40),(⟨-243861461376,-243861461312⟩ : DyadicInterval 40),(⟨740224890533,740224909862⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199236233728,199236233792⟩ : DyadicInterval 40),(⟨-243508842112,-243508842048⟩ : DyadicInterval 40),(⟨740281810645,740281829975⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199471907200,199471907264⟩ : DyadicInterval 40),(⟨-243861461376,-243861461312⟩ : DyadicInterval 40),(⟨740224890533,740224909862⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,28147984⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28147584,28147648⟩ : DyadicInterval 40),(⟨-28148352,-28148288⟩ : DyadicInterval 40),(⟨762123383215,762123402544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-768,0⟩ : DyadicInterval 40),(⟨762123383616,762123403264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨218456328247,218711554401⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199259013120,199259013184⟩ : DyadicInterval 40),(⟨-243542916800,-243542916736⟩ : DyadicInterval 40),(⟨740276312762,740276332091⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199471914304,199471914368⟩ : DyadicInterval 40),(⟨-243861472000,-243861471936⟩ : DyadicInterval 40),(⟨740224888810,740224908139⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-44389557696,-44283903552⟩ : DyadicInterval 40),(⟨784265335392,784318181728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨199281801152,199471907264⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-243861461376,-243577006144⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1132_ok : ecellOkT e1132 = true := by decide +kernel
theorem e1132_pos {a z : ℝ} (ha1 : ((162783/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((203691/1024000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1132 e1132_ok ha1 ha2 hz1 hz2 hz

-- box ['203691/1024000', '815613/4096000', '999/1000', '3997/4000']  interval_lower 478622351/1099511627776
noncomputable def e1133 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1318223173648,0,true,199471907200,199471907264⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨880800081904,0,false,-243861461376,-243861461312⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1318451075351,0,true,199661980416,199661980480⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨880572180201,0,false,-244145990208,-244145990144⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1318004462102,0,true,199289467776,199289467840⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨881018793450,0,false,-243588475456,-243588475392⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1318286870766,0,true,199525034816,199525034880⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨880736384786,0,false,-243940977984,-243940977920⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099596068182,0,true,84437120,84437184⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099427187370,0,false,-84443712,-84443648⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099624340739,0,true,112707136,112707200⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099398914813,0,false,-112718784,-112718720⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511616221,0,false,-11584,-11520⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621292,0,false,-6528,-6464⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1318113813884,0,true,199380687936,199380688000⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨880909441668,0,false,-243724954944,-243724954880⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1318368982479,0,true,199593517568,199593517632⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨880654273073,0,false,-244043491072,-244043491008⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1055948157870,0,false,-44449973440,-44449973376⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1056049681069,0,false,-44344266944,-44344266880⟩
    { al := (203691/1024000), au := (815613/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨218711545872,218939447575⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199471907200,199471907264⟩ : DyadicInterval 40),(⟨-243861461376,-243861461312⟩ : DyadicInterval 40),(⟨740224890533,740224909862⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199661980416,199661980480⟩ : DyadicInterval 40),(⟨-244145990208,-244145990144⟩ : DyadicInterval 40),(⟨740178919899,740178939229⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199289467776,199289467840⟩ : DyadicInterval 40),(⟨-243588475456,-243588475392⟩ : DyadicInterval 40),(⟨740268961179,740268980508⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199525034816,199525034880⟩ : DyadicInterval 40),(⟨-243940977984,-243940977920⟩ : DyadicInterval 40),(⟨740212046955,740212066284⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨84440406,112712963⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨84437120,84437184⟩ : DyadicInterval 40),(⟨-84443712,-84443648⟩ : DyadicInterval 40),(⟨762123380362,762123399692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨112707136,112707200⟩ : DyadicInterval 40),(⟨-112718784,-112718720⟩ : DyadicInterval 40),(⟨762123377821,762123397150⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-11584,-6464⟩ : DyadicInterval 40),(⟨762123386848,762123408672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨218602186108,218857354703⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199380687936,199380688000⟩ : DyadicInterval 40),(⟨-243724954944,-243724954880⟩ : DyadicInterval 40),(⟨740246932318,740246951648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199593517568,199593517632⟩ : DyadicInterval 40),(⟨-244043491072,-244043491008⟩ : DyadicInterval 40),(⟨740195484737,740195504067⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-44449973440,-44344266880⟩ : DyadicInterval 40),(⟨784295517056,784348389600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨199471907200,199661980480⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-244145990208,-243861461312⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1133_ok : ecellOkT e1133 = true := by decide +kernel
theorem e1133_pos {a z : ℝ} (ha1 : ((203691/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((815613/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1133 e1133_ok ha1 ha2 hz1 hz2 hz

-- box ['815613/4096000', '408231/2048000', '999/1000', '3997/4000']  interval_lower 241639909/549755813888
noncomputable def e1134 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1318451075350,0,true,199661980416,199661980480⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨880572180202,0,false,-244145990208,-244145990144⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1318678977053,0,true,199852020800,199852020864⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨880344278499,0,false,-244430592640,-244430592576⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1318232135902,0,true,199479382464,199479382528⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨880791119650,0,false,-243872649088,-243872649024⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1318514601542,0,true,199714956288,199714956352⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨880508654010,0,false,-244225313920,-244225313856⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099596161415,0,true,84530368,84530432⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099427094137,0,false,-84536896,-84536832⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099624465076,0,true,112831488,112831552⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099398790476,0,false,-112843136,-112843072⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511616196,0,false,-11584,-11520⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621277,0,false,-6528,-6464⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1318341601638,0,true,199570681920,199570681984⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨880681653914,0,false,-244009306176,-244009306112⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1318596798724,0,true,199783498496,199783498560⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨880426456828,0,false,-244327960256,-244327960192⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1055857417200,0,false,-44544461696,-44544461632⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1055959057480,0,false,-44438624256,-44438624192⟩
    { al := (815613/4096000), au := (408231/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨218939447574,219167349277⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199661980416,199661980480⟩ : DyadicInterval 40),(⟨-244145990208,-244145990144⟩ : DyadicInterval 40),(⟨740178919899,740178939229⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199852020800,199852020864⟩ : DyadicInterval 40),(⟨-244430592640,-244430592576⟩ : DyadicInterval 40),(⟨740132900045,740132919375⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199479382464,199479382528⟩ : DyadicInterval 40),(⟨-243872649088,-243872649024⟩ : DyadicInterval 40),(⟨740223083657,740223102986⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199714956288,199714956352⟩ : DyadicInterval 40),(⟨-244225313920,-244225313856⟩ : DyadicInterval 40),(⟨740166097081,740166116410⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨84533639,112837300⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨84530368,84530432⟩ : DyadicInterval 40),(⟨-84536896,-84536832⟩ : DyadicInterval 40),(⟨762123380316,762123399646⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨112831488,112831552⟩ : DyadicInterval 40),(⟨-112843136,-112843072⟩ : DyadicInterval 40),(⟨762123377795,762123397125⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-11584,-6464⟩ : DyadicInterval 40),(⟨762123386848,762123408672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨218829973862,219085170948⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199570681920,199570681984⟩ : DyadicInterval 40),(⟨-244009306176,-244009306112⟩ : DyadicInterval 40),(⟨740201008248,740201027577⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199783498496,199783498560⟩ : DyadicInterval 40),(⟨-244327960256,-244327960192⟩ : DyadicInterval 40),(⟨740149499882,740149519212⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-44544461696,-44438624192⟩ : DyadicInterval 40),(⟨784342695712,784395633728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨199661980416,199852020864⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-244430592640,-244145990144⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1134_ok : ecellOkT e1134 = true := by decide +kernel
theorem e1134_pos {a z : ℝ} (ha1 : ((815613/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((408231/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1134 e1134_ok ha1 ha2 hz1 hz2 hz

-- box ['203691/1024000', '815613/4096000', '3997/4000', '1999/2000']  interval_lower 238882811/549755813888
noncomputable def e1135 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1318223173648,0,true,199471907200,199471907264⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨880800081904,0,false,-243861461376,-243861461312⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1318451075351,0,true,199661980416,199661980480⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨880572180201,0,false,-244145990208,-244145990144⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1318059139988,0,true,199335080512,199335080576⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨880964115564,0,false,-243656715584,-243656715520⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1318341605628,0,true,199570685248,199570685312⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨880681649924,0,false,-244009311168,-244009311104⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567921714,0,true,56292480,56292544⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455333838,0,false,-56295424,-56295360⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099596163193,0,true,84532160,84532224⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099427092359,0,false,-84538688,-84538624⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621276,0,false,-6528,-6464⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624894,0,false,-2944,-2880⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1318141152140,0,true,199403492096,199403492160⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨880882103412,0,false,-243759077888,-243759077824⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1318396349414,0,true,199616341184,199616341248⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨880626906138,0,false,-244077659712,-244077659648⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1055937262433,0,false,-44461318464,-44461318400⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1056038809740,0,false,-44355585728,-44355585664⟩
    { al := (203691/1024000), au := (815613/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨218711545872,218939447575⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199471907200,199471907264⟩ : DyadicInterval 40),(⟨-243861461376,-243861461312⟩ : DyadicInterval 40),(⟨740224890533,740224909862⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199661980416,199661980480⟩ : DyadicInterval 40),(⟨-244145990208,-244145990144⟩ : DyadicInterval 40),(⟨740178919899,740178939229⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199335080512,199335080576⟩ : DyadicInterval 40),(⟨-243656715584,-243656715520⟩ : DyadicInterval 40),(⟨740257947739,740257967069⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199570685248,199570685312⟩ : DyadicInterval 40),(⟨-244009311168,-244009311104⟩ : DyadicInterval 40),(⟨740201007447,740201026776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨56293938,84535417⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56292480,56292544⟩ : DyadicInterval 40),(⟨-56295424,-56295360⟩ : DyadicInterval 40),(⟨762123382141,762123401470⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨84532160,84532224⟩ : DyadicInterval 40),(⟨-84538688,-84538624⟩ : DyadicInterval 40),(⟨762123380316,762123399645⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6528,-2880⟩ : DyadicInterval 40),(⟨762123385056,762123406144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨218629524364,218884721638⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199403492096,199403492160⟩ : DyadicInterval 40),(⟨-243759077888,-243759077824⟩ : DyadicInterval 40),(⟨740241423260,740241442590⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199616341184,199616341248⟩ : DyadicInterval 40),(⟨-244077659712,-244077659648⟩ : DyadicInterval 40),(⟨740189963316,740189982646⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-44461318464,-44355585664⟩ : DyadicInterval 40),(⟨784301176448,784354062112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨199471907200,199661980480⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-244145990208,-243861461312⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1135_ok : ecellOkT e1135 = true := by decide +kernel
theorem e1135_pos {a z : ℝ} (ha1 : ((203691/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((815613/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1135 e1135_ok ha1 ha2 hz1 hz2 hz

-- box ['815613/4096000', '408231/2048000', '3997/4000', '1999/2000']  interval_lower 482419799/1099511627776
noncomputable def e1136 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1318451075350,0,true,199661980416,199661980480⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨880572180202,0,false,-244145990208,-244145990144⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1318678977053,0,true,199852020800,199852020864⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨880344278499,0,false,-244430592640,-244430592576⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1318286870764,0,true,199525034816,199525034880⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨880736384788,0,false,-243940977984,-243940977920⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1318569393379,0,true,199760646336,199760646400⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨880453862173,0,false,-244293735936,-244293735872⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567983870,0,true,56354624,56354688⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455271682,0,false,-56357568,-56357504⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099596256447,0,true,84625408,84625472⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099426999105,0,false,-84631936,-84631872⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621262,0,false,-6528,-6464⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624888,0,false,-2944,-2880⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1318368968378,0,true,199593505856,199593505920⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨880654287174,0,false,-244043473472,-244043473408⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1318624194142,0,true,199806341952,199806342016⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨880399061410,0,false,-244362173312,-244362173248⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1055846499070,0,false,-44555831296,-44555831232⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1055948163484,0,false,-44449967616,-44449967552⟩
    { al := (815613/4096000), au := (408231/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨218939447574,219167349277⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199661980416,199661980480⟩ : DyadicInterval 40),(⟨-244145990208,-244145990144⟩ : DyadicInterval 40),(⟨740178919899,740178939229⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199852020800,199852020864⟩ : DyadicInterval 40),(⟨-244430592640,-244430592576⟩ : DyadicInterval 40),(⟨740132900045,740132919375⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199525034816,199525034880⟩ : DyadicInterval 40),(⟨-243940977984,-243940977920⟩ : DyadicInterval 40),(⟨740212046955,740212066285⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199760646336,199760646400⟩ : DyadicInterval 40),(⟨-244293735936,-244293735872⟩ : DyadicInterval 40),(⟨740155034272,740155053602⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨56356094,84628671⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56354624,56354688⟩ : DyadicInterval 40),(⟨-56357568,-56357504⟩ : DyadicInterval 40),(⟨762123382135,762123401464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨84625408,84625472⟩ : DyadicInterval 40),(⟨-84631936,-84631872⟩ : DyadicInterval 40),(⟨762123380301,762123399631⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6528,-2880⟩ : DyadicInterval 40),(⟨762123385056,762123406144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨218857340602,219112566366⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199593505856,199593505920⟩ : DyadicInterval 40),(⟨-244043473472,-244043473408⟩ : DyadicInterval 40),(⟨740195487555,740195506885⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199806341952,199806342016⟩ : DyadicInterval 40),(⟨-244362173312,-244362173248⟩ : DyadicInterval 40),(⟨740143966785,740143986114⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-44555831296,-44449967552⟩ : DyadicInterval 40),(⟨784348367392,784401318528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨199661980416,199852020864⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-244430592640,-244145990144⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1136_ok : ecellOkT e1136 = true := by decide +kernel
theorem e1136_pos {a z : ℝ} (ha1 : ((815613/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((408231/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1136 e1136_ok ha1 ha2 hz1 hz2 hz

-- box ['408231/2048000', '817311/4096000', '999/1000', '3997/4000']  interval_lower 487955681/1099511627776
noncomputable def e1137 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1318678977052,0,true,199852020800,199852020864⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨880344278500,0,false,-244430592640,-244430592576⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1318906878755,0,true,200042028288,200042028352⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨880116376797,0,false,-244715268800,-244715268736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1318459809702,0,true,199669264320,199669264384⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨880563445850,0,false,-244156896256,-244156896192⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1318742332317,0,true,199904844992,199904845056⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨880280923235,0,false,-244509723456,-244509723392⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099596254666,0,true,84623616,84623680⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099427000886,0,false,-84630208,-84630144⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099624589435,0,true,112955840,112955904⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099398666117,0,false,-112967488,-112967424⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511616170,0,false,-11648,-11584⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621263,0,false,-6528,-6464⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1318569389390,0,true,199760643008,199760643072⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨880453866162,0,false,-244293730944,-244293730880⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1318824614960,0,true,199973446656,199973446720⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨880198640592,0,false,-244612503104,-244612503040⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1055766582127,0,false,-44639056384,-44639056320⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1055868339510,0,false,-44533087872,-44533087808⟩
    { al := (408231/2048000), au := (817311/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨219167349276,219395250979⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199852020800,199852020864⟩ : DyadicInterval 40),(⟨-244430592640,-244430592576⟩ : DyadicInterval 40),(⟨740132900046,740132919375⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200042028288,200042028352⟩ : DyadicInterval 40),(⟨-244715268800,-244715268736⟩ : DyadicInterval 40),(⟨740086831048,740086850378⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199669264320,199669264384⟩ : DyadicInterval 40),(⟨-244156896256,-244156896192⟩ : DyadicInterval 40),(⟨740177157097,740177176427⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199904844992,199904845056⟩ : DyadicInterval 40),(⟨-244509723456,-244509723392⟩ : DyadicInterval 40),(⟨740120098092,740120117422⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨84626890,112961659⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨84623616,84623680⟩ : DyadicInterval 40),(⟨-84630208,-84630144⟩ : DyadicInterval 40),(⟨762123380334,762123399663⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨112955840,112955904⟩ : DyadicInterval 40),(⟨-112967488,-112967424⟩ : DyadicInterval 40),(⟨762123377770,762123397099⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-11648,-6464⟩ : DyadicInterval 40),(⟨762123386848,762123408704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨219057761614,219312987184⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199760643008,199760643072⟩ : DyadicInterval 40),(⟨-244293730944,-244293730880⟩ : DyadicInterval 40),(⟨740155035075,740155054404⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199973446656,199973446720⟩ : DyadicInterval 40),(⟨-244612503104,-244612503040⟩ : DyadicInterval 40),(⟨740103465862,740103485191⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-44639056384,-44533087808⟩ : DyadicInterval 40),(⟨784389927520,784442931072⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨199852020800,200042028352⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-244715268800,-244430592576⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1137_ok : ecellOkT e1137 = true := by decide +kernel
theorem e1137_pos {a z : ℝ} (ha1 : ((408231/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((817311/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1137 e1137_ok ha1 ha2 hz1 hz2 hz

-- box ['817311/4096000', '10227/51200', '999/1000', '3997/4000']  interval_lower 492650749/1099511627776
noncomputable def e1138 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1318906878754,0,true,200042028288,200042028352⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨880116376798,0,false,-244715268800,-244715268736⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1319134780457,0,true,200232003008,200232003072⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨879888475095,0,false,-245000018624,-245000018560⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1318687483502,0,true,199859113408,199859113472⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨880335772050,0,false,-244441216896,-244441216832⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1318970063093,0,true,200094700864,200094700928⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨880053192459,0,false,-244794206528,-244794206464⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099596347934,0,true,84716864,84716928⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099426907618,0,false,-84723456,-84723392⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099624713818,0,true,113080192,113080256⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099398541734,0,false,-113091904,-113091840⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511616144,0,false,-11648,-11584⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621249,0,false,-6528,-6464⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1318797177138,0,true,199950571328,199950571392⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨880226078414,0,false,-244578229312,-244578229248⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1319052431205,0,true,200163361920,200163361984⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨879970824347,0,false,-244897119552,-244897119488⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1055675652646,0,false,-44733757568,-44733757504⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1055777527159,0,false,-44627657920,-44627657856⟩
    { al := (817311/4096000), au := (10227/51200), zl := (999/1000), zu := (3997/4000),
      A := ⟨219395250978,219623152681⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200042028288,200042028352⟩ : DyadicInterval 40),(⟨-244715268800,-244715268736⟩ : DyadicInterval 40),(⟨740086831049,740086850378⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200232003008,200232003072⟩ : DyadicInterval 40),(⟨-245000018624,-245000018560⟩ : DyadicInterval 40),(⟨740040712792,740040732122⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199859113408,199859113472⟩ : DyadicInterval 40),(⟨-244441216896,-244441216832⟩ : DyadicInterval 40),(⟨740131181424,740131200754⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200094700864,200094700928⟩ : DyadicInterval 40),(⟨-244794206528,-244794206464⟩ : DyadicInterval 40),(⟨740074049989,740074069319⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨84720158,113086042⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨84716864,84716928⟩ : DyadicInterval 40),(⟨-84723456,-84723392⟩ : DyadicInterval 40),(⟨762123380319,762123399649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨113080192,113080256⟩ : DyadicInterval 40),(⟨-113091904,-113091840⟩ : DyadicInterval 40),(⟨762123377776,762123397106⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-11648,-6464⟩ : DyadicInterval 40),(⟨762123386848,762123408704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨219285549362,219540803429⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199950571328,199950571392⟩ : DyadicInterval 40),(⟨-244578229312,-244578229248⟩ : DyadicInterval 40),(⟨740109012735,740109032064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200163361920,200163361984⟩ : DyadicInterval 40),(⟨-244897119552,-244897119488⟩ : DyadicInterval 40),(⟨740057382710,740057402040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-44733757568,-44627657856⟩ : DyadicInterval 40),(⟨784437212544,784490281664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨200042028288,200232003072⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-245000018624,-244715268736⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1138_ok : ecellOkT e1138 = true := by decide +kernel
theorem e1138_pos {a z : ℝ} (ha1 : ((817311/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((10227/51200 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1138 e1138_ok ha1 ha2 hz1 hz2 hz

-- box ['408231/2048000', '817311/4096000', '3997/4000', '1999/2000']  interval_lower 487092669/1099511627776
noncomputable def e1139 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1318678977052,0,true,199852020800,199852020864⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨880344278500,0,false,-244430592640,-244430592576⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1318906878755,0,true,200042028288,200042028352⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨880116376797,0,false,-244715268800,-244715268736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1318514601540,0,true,199714956288,199714956352⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨880508654012,0,false,-244225313920,-244225313856⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1318797181130,0,true,199950574656,199950574720⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨880226074422,0,false,-244578234304,-244578234240⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568046039,0,true,56416768,56416832⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455209513,0,false,-56419712,-56419648⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099596349720,0,true,84718656,84718720⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099426905832,0,false,-84725248,-84725184⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621247,0,false,-6592,-6528⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624882,0,false,-2944,-2880⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1318596784617,0,true,199783486784,199783486848⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨880426470935,0,false,-244327942656,-244327942592⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1318852038868,0,true,199996309888,199996309952⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨880171216684,0,false,-244646760512,-244646760448⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1055755641279,0,false,-44650450624,-44650450560⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1055857422823,0,false,-44544455872,-44544455808⟩
    { al := (408231/2048000), au := (817311/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨219167349276,219395250979⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199852020800,199852020864⟩ : DyadicInterval 40),(⟨-244430592640,-244430592576⟩ : DyadicInterval 40),(⟨740132900046,740132919375⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨200042028288,200042028352⟩ : DyadicInterval 40),(⟨-244715268800,-244715268736⟩ : DyadicInterval 40),(⟨740086831048,740086850378⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199714956288,199714956352⟩ : DyadicInterval 40),(⟨-244225313920,-244225313856⟩ : DyadicInterval 40),(⟨740166097081,740166116411⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199950574656,199950574720⟩ : DyadicInterval 40),(⟨-244578234304,-244578234240⟩ : DyadicInterval 40),(⟨740109011930,740109031260⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨56418263,84721944⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56416768,56416832⟩ : DyadicInterval 40),(⟨-56419712,-56419648⟩ : DyadicInterval 40),(⟨762123382128,762123401458⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨84718656,84718720⟩ : DyadicInterval 40),(⟨-84725248,-84725184⟩ : DyadicInterval 40),(⟨762123380319,762123399649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6592,-2880⟩ : DyadicInterval 40),(⟨762123385056,762123406176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨219085156841,219340411092⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199783486784,199783486848⟩ : DyadicInterval 40),(⟨-244327942656,-244327942592⟩ : DyadicInterval 40),(⟨740149502708,740149522037⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨199996309888,199996309952⟩ : DyadicInterval 40),(⟨-244646760512,-244646760448⟩ : DyadicInterval 40),(⟨740097921073,740097940402⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-44650450624,-44544455808⟩ : DyadicInterval 40),(⟨784395611520,784448628192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨199852020800,200042028352⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-244715268800,-244430592576⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1139_ok : ecellOkT e1139 = true := by decide +kernel
theorem e1139_pos {a z : ℝ} (ha1 : ((408231/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((817311/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1139 e1139_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B018

end


