-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B010__2
-- name    : CK_CKLaneC2R_EpCells_B010__2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T15:06:17.356813+00:00
-- url     : https://prove2.me/theorems/afe996b7-82f9-4d86-b18b-7fc07dba7fe5
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B010 (+1 modules: CKLaneC2R.EpCells.B011)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B010 (+1 modules: CKLaneC2R.EpCells.B011)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B010 (+1 modules: CKLaneC2R.EpCells.B011)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B010 (+1 modules: CKLaneC2R.EpCells.B011) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B010 (+1 modules: CKLaneC2R/EpCells/B011).lean)

import Definitions.Def_CK_CKLaneC2R_EpCells_B010__2_q00

-- ===== source module CKLaneC2R.EpCells.B011 =====
section

namespace CKLaneC2R.EpCells.B011

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['715431/4096000', '17907/102400', '3997/4000', '1999/2000']  interval_lower 25335555/549755813888
noncomputable def e660 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1291558674497,0,true,177003403072,177003403136⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨907464581055,0,false,-211069782912,-211069782848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1291786576200,0,true,177197400064,177197400128⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨907236679352,0,false,-211345950208,-211345950144⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1291414639211,0,true,176880778176,176880778240⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨907608616341,0,false,-210895279232,-210895279168⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1291690438726,0,true,177115569024,177115569088⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨907332816826,0,false,-211229444032,-211229443968⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099560724498,0,true,49095616,49095680⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099462531054,0,false,-49097856,-49097792⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585365298,0,true,73735040,73735104⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437890254,0,false,-73740032,-73739968⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622830,0,false,-4992,-4928⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625584,0,false,-2240,-2176⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1291486652473,0,true,176942088576,176942088640⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨907536603079,0,false,-210982522304,-210982522240⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1291738516218,0,true,177156492736,177156492800⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨907284739334,0,false,-211287706176,-211287706112⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1065904728397,0,false,-34131213376,-34131213312⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1065992737047,0,false,-34040433664,-34040433600⟩
    { al := (715431/4096000), au := (17907/102400), zl := (3997/4000), zu := (1999/2000),
      A := ⟨192047046721,192274948424⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177003403072,177003403136⟩ : DyadicInterval 40),(⟨-211069782912,-211069782848⟩ : DyadicInterval 40),(⟨745265022260,745265041590⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177197400064,177197400128⟩ : DyadicInterval 40),(⟨-211345950208,-211345950144⟩ : DyadicInterval 40),(⟨745224778871,745224798200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176880778176,176880778240⟩ : DyadicInterval 40),(⟨-210895279232,-210895279168⟩ : DyadicInterval 40),(⟨745290431166,745290450495⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177115569024,177115569088⟩ : DyadicInterval 40),(⟨-211229444032,-211229443968⟩ : DyadicInterval 40),(⟨745241760988,745241780318⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨49096722,73737522⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨49095616,49095680⟩ : DyadicInterval 40),(⟨-49097856,-49097792⟩ : DyadicInterval 40),(⟨762123382479,762123401808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73735040,73735104⟩ : DyadicInterval 40),(⟨-73740032,-73739968⟩ : DyadicInterval 40),(⟨762123381102,762123400432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4992,-2176⟩ : DyadicInterval 40),(⟨762123384704,762123405376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨191975024697,192226888442⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176942088576,176942088640⟩ : DyadicInterval 40),(⟨-210982522304,-210982522240⟩ : DyadicInterval 40),(⟨745277729936,745277749265⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177156492736,177156492800⟩ : DyadicInterval 40),(⟨-211287706176,-211287706112⟩ : DyadicInterval 40),(⟨745233269475,745233288804⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34131213376,-34040433600⟩ : DyadicInterval 40),(⟨779143600416,779189009568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨177003403072,177197400128⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-211345950208,-211069782848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e660_ok : ecellOkT e660 = true := by decide +kernel
theorem e660_pos {a z : ℝ} (ha1 : ((715431/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((17907/102400 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e660 e660_ok ha1 ha2 hz1 hz2 hz

-- box ['178221/1024000', '713733/4096000', '1999/2000', '3999/4000']  interval_lower 41936611/1099511627776
noncomputable def e661 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1290874969391,0,true,176421206720,176421206784⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨908148286161,0,false,-210241696960,-210241696896⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1291102871094,0,true,176615306432,176615306496⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨907920384458,0,false,-210517656320,-210517656256⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1290779287720,0,true,176339706176,176339706240⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨908243967832,0,false,-210125859520,-210125859456⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1291054973284,0,true,176574515584,176574515648⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨907968282268,0,false,-210459652544,-210459652480⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536084802,0,true,24456704,24456768⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487170750,0,false,-24457344,-24457280⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099560603765,0,true,48974848,48974912⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099462651787,0,false,-48977088,-48977024⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625594,0,false,-2240,-2176⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627232,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1290827123852,0,true,176380453184,176380453248⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨908196131700,0,false,-210183771008,-210183770944⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1291078930742,0,true,176594918464,176594918528⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨907944324810,0,false,-210488664384,-210488664320⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1066134962501,0,false,-33893745856,-33893745792⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1066222649184,0,false,-33803317760,-33803317696⟩
    { al := (178221/1024000), au := (713733/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨191363341615,191591243318⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176421206720,176421206784⟩ : DyadicInterval 40),(⟨-210241696960,-210241696896⟩ : DyadicInterval 40),(⟨745385460040,745385479369⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176615306432,176615306496⟩ : DyadicInterval 40),(⟨-210517656320,-210517656256⟩ : DyadicInterval 40),(⟨745345362828,745345382158⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176339706176,176339706240⟩ : DyadicInterval 40),(⟨-210125859520,-210125859456⟩ : DyadicInterval 40),(⟨745402279830,745402299160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176574515584,176574515648⟩ : DyadicInterval 40),(⟨-210459652544,-210459652480⟩ : DyadicInterval 40),(⟨745353794053,745353813382⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨24457026,48975989⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24456704,24456768⟩ : DyadicInterval 40),(⟨-24457344,-24457280⟩ : DyadicInterval 40),(⟨762123383327,762123402656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨48974848,48974912⟩ : DyadicInterval 40),(⟨-48977088,-48977024⟩ : DyadicInterval 40),(⟨762123382490,762123401819⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2240,-512⟩ : DyadicInterval 40),(⟨762123383872,762123404000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨191315496076,191567302966⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176380453184,176380453248⟩ : DyadicInterval 40),(⟨-210183771008,-210183770944⟩ : DyadicInterval 40),(⟨745393871838,745393891167⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176594918464,176594918528⟩ : DyadicInterval 40),(⟨-210488664384,-210488664320⟩ : DyadicInterval 40),(⟨745349577204,745349596534⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33893745856,-33803317696⟩ : DyadicInterval 40),(⟨779025042464,779070275808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨176421206720,176615306496⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-210517656320,-210241696896⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e661_ok : ecellOkT e661 = true := by decide +kernel
theorem e661_pos {a z : ℝ} (ha1 : ((178221/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((713733/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e661 e661_ok ha1 ha2 hz1 hz2 hz

-- box ['713733/4096000', '357291/2048000', '1999/2000', '3999/4000']  interval_lower 44654043/1099511627776
noncomputable def e662 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1291102871093,0,true,176615306432,176615306496⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨907920384459,0,false,-210517656320,-210517656256⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1291330772796,0,true,176809371904,176809371968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨907692482756,0,false,-210793684928,-210793684864⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1291007075471,0,true,176533723264,176533723328⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨908016180081,0,false,-210401651840,-210401651776⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1291282818010,0,true,176768539712,176768539776⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨907740437542,0,false,-210735597568,-210735597504⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536115246,0,true,24487168,24487232⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487140306,0,false,-24487744,-24487680⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099560664665,0,true,49035776,49035840⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099462590887,0,false,-49038016,-49037952⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625589,0,false,-2240,-2176⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627231,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1291054968577,0,true,176574511552,176574511616⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨907968286975,0,false,-210459646848,-210459646784⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1291306803961,0,true,176788963264,176788963328⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨907716451591,0,false,-210764651264,-210764651200⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1066055510825,0,false,-33975687936,-33975687872⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1066143311809,0,false,-33885135232,-33885135168⟩
    { al := (713733/4096000), au := (357291/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨191591243317,191819145020⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176615306432,176615306496⟩ : DyadicInterval 40),(⟨-210517656320,-210517656256⟩ : DyadicInterval 40),(⟨745345362828,745345382158⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176809371904,176809371968⟩ : DyadicInterval 40),(⟨-210793684928,-210793684864⟩ : DyadicInterval 40),(⟨745305216875,745305236205⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176533723264,176533723328⟩ : DyadicInterval 40),(⟨-210401651840,-210401651776⟩ : DyadicInterval 40),(⟨745362223107,745362242437⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176768539712,176768539776⟩ : DyadicInterval 40),(⟨-210735597568,-210735597504⟩ : DyadicInterval 40),(⟨745313668393,745313687722⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨24487470,49036889⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24487168,24487232⟩ : DyadicInterval 40),(⟨-24487744,-24487680⟩ : DyadicInterval 40),(⟨762123383294,762123402623⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨49035776,49035840⟩ : DyadicInterval 40),(⟨-49038016,-49037952⟩ : DyadicInterval 40),(⟨762123382484,762123401814⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2240,-512⟩ : DyadicInterval 40),(⟨762123383872,762123404000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨191543340801,191795176185⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176574511552,176574511616⟩ : DyadicInterval 40),(⟨-210459646848,-210459646784⟩ : DyadicInterval 40),(⟨745353794897,745353814226⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176788963264,176788963328⟩ : DyadicInterval 40),(⟨-210764651264,-210764651200⟩ : DyadicInterval 40),(⟨745309441421,745309460750⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33975687936,-33885135168⟩ : DyadicInterval 40),(⟨779065951200,779111246848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨176615306432,176809371968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-210793684928,-210517656256⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e662_ok : ecellOkT e662 = true := by decide +kernel
theorem e662_pos {a z : ℝ} (ha1 : ((713733/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((357291/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e662 e662_ok ha1 ha2 hz1 hz2 hz

-- box ['178221/1024000', '713733/4096000', '3999/4000', '1']  interval_lower 20700929/549755813888
noncomputable def e663 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1290874969391,0,true,176421206720,176421206784⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨908148286161,0,false,-210241696960,-210241696896⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1291102871094,0,true,176615306432,176615306496⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨907920384458,0,false,-210517656320,-210517656256⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1290827128555,0,true,176380457216,176380457280⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨908196126997,0,false,-210183776704,-210183776640⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536116039,0,true,24487936,24488000⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487139513,0,false,-24488576,-24488512⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627230,0,false,-576,-512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1290851044073,0,true,176400827968,176400828032⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨908172211479,0,false,-210212730496,-210212730432⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1291102879580,0,true,176615313664,176615313728⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨907920375972,0,false,-210517666560,-210517666496⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1066126616794,0,false,-33902352896,-33902352832⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1066214324407,0,false,-33811902464,-33811902400⟩
    { al := (178221/1024000), au := (713733/4096000), zl := (3999/4000), zu := 1,
      A := ⟨191363341615,191591243318⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176421206720,176421206784⟩ : DyadicInterval 40),(⟨-210241696960,-210241696896⟩ : DyadicInterval 40),(⟨745385460040,745385479369⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176615306432,176615306496⟩ : DyadicInterval 40),(⟨-210517656320,-210517656256⟩ : DyadicInterval 40),(⟨745345362828,745345382158⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176380457216,176380457280⟩ : DyadicInterval 40),(⟨-210183776704,-210183776640⟩ : DyadicInterval 40),(⟨745393870997,745393890326⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176615306432,176615306496⟩ : DyadicInterval 40),(⟨-210517656320,-210517656256⟩ : DyadicInterval 40),(⟨745345362828,745345382158⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,24488263⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24487936,24488000⟩ : DyadicInterval 40),(⟨-24488576,-24488512⟩ : DyadicInterval 40),(⟨762123383326,762123402655⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,0⟩ : DyadicInterval 40),(⟨762123383616,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨191339416297,191591251804⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176400827968,176400828032⟩ : DyadicInterval 40),(⟨-210212730496,-210212730432⟩ : DyadicInterval 40),(⟨745389666648,745389685978⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176615313664,176615313728⟩ : DyadicInterval 40),(⟨-210517666560,-210517666496⟩ : DyadicInterval 40),(⟨745345361316,745345380645⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33902352896,-33811902400⟩ : DyadicInterval 40),(⟨779029334816,779074579328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨176421206720,176615306496⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-210517656320,-210241696896⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e663_ok : ecellOkT e663 = true := by decide +kernel
theorem e663_pos {a z : ℝ} (ha1 : ((178221/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((713733/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e663 e663_ok ha1 ha2 hz1 hz2 hz

-- box ['713733/4096000', '357291/2048000', '3999/4000', '1']  interval_lower 22058611/549755813888
noncomputable def e664 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1291102871093,0,true,176615306432,176615306496⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨907920384459,0,false,-210517656320,-210517656256⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1291330772796,0,true,176809371904,176809371968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨907692482756,0,false,-210793684928,-210793684864⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1291054973282,0,true,176574515584,176574515648⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨907968282270,0,false,-210459652544,-210459652480⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536146488,0,true,24518400,24518464⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487109064,0,false,-24519040,-24518976⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627229,0,false,-576,-512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1291078917280,0,true,176594907008,176594907072⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨907944338272,0,false,-210488648064,-210488648000⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1291330781289,0,true,176809379136,176809379200⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨907692474263,0,false,-210793695232,-210793695168⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1066047145250,0,false,-33984316096,-33984316032⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1066134967193,0,false,-33893741056,-33893740992⟩
    { al := (713733/4096000), au := (357291/2048000), zl := (3999/4000), zu := 1,
      A := ⟨191591243317,191819145020⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176615306432,176615306496⟩ : DyadicInterval 40),(⟨-210517656320,-210517656256⟩ : DyadicInterval 40),(⟨745345362828,745345382158⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176809371904,176809371968⟩ : DyadicInterval 40),(⟨-210793684928,-210793684864⟩ : DyadicInterval 40),(⟨745305216875,745305236205⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176574515584,176574515648⟩ : DyadicInterval 40),(⟨-210459652544,-210459652480⟩ : DyadicInterval 40),(⟨745353794053,745353813383⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176809371904,176809371968⟩ : DyadicInterval 40),(⟨-210793684928,-210793684864⟩ : DyadicInterval 40),(⟨745305216875,745305236205⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,24518712⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24518400,24518464⟩ : DyadicInterval 40),(⟨-24519040,-24518976⟩ : DyadicInterval 40),(⟨762123383325,762123402654⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,0⟩ : DyadicInterval 40),(⟨762123383616,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨191567289504,191819153513⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176594907008,176594907072⟩ : DyadicInterval 40),(⟨-210488648064,-210488648000⟩ : DyadicInterval 40),(⟨745349579562,745349598891⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176809379136,176809379200⟩ : DyadicInterval 40),(⟨-210793695232,-210793695168⟩ : DyadicInterval 40),(⟨745305215384,745305234714⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-33984316096,-33893740992⟩ : DyadicInterval 40),(⟨779070254112,779115560928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨176615306432,176809371968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-210793684928,-210517656256⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e664_ok : ecellOkT e664 = true := by decide +kernel
theorem e664_pos {a z : ℝ} (ha1 : ((713733/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((357291/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e664 e664_ok ha1 ha2 hz1 hz2 hz

-- box ['357291/2048000', '715431/4096000', '1999/2000', '3999/4000']  interval_lower 23692769/549755813888
noncomputable def e665 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1291330772795,0,true,176809371904,176809371968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨907692482757,0,false,-210793684928,-210793684864⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1291558674498,0,true,177003403072,177003403136⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨907464581054,0,false,-211069782912,-211069782848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1291234863222,0,true,176727706048,176727706112⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨907788392330,0,false,-210677513280,-210677513216⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1291510662737,0,true,176962529600,176962529664⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨907512592815,0,false,-211011611904,-211011611840⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536145695,0,true,24517632,24517696⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487109857,0,false,-24518208,-24518144⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099560725572,0,true,49096640,49096704⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099462529980,0,false,-49098944,-49098880⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625583,0,false,-2240,-2176⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627230,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1291282813302,0,true,176768535744,176768535808⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨907740442250,0,false,-210735591872,-210735591808⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1291534677171,0,true,176982973824,176982973888⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨907488578381,0,false,-211040707392,-211040707328⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1065975964698,0,false,-34057733504,-34057733440⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1066063880005,0,false,-33967056128,-33967056064⟩
    { al := (357291/2048000), au := (715431/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨191819145019,192047046722⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176809371904,176809371968⟩ : DyadicInterval 40),(⟨-210793684928,-210793684864⟩ : DyadicInterval 40),(⟨745305216875,745305236205⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177003403072,177003403136⟩ : DyadicInterval 40),(⟨-211069782912,-211069782848⟩ : DyadicInterval 40),(⟨745265022260,745265041589⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176727706048,176727706112⟩ : DyadicInterval 40),(⟨-210677513280,-210677513216⟩ : DyadicInterval 40),(⟨745322117729,745322137058⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176962529600,176962529664⟩ : DyadicInterval 40),(⟨-211011611904,-211011611840⟩ : DyadicInterval 40),(⟨745273494058,745273513387⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨24517919,49097796⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24517632,24517696⟩ : DyadicInterval 40),(⟨-24518208,-24518144⟩ : DyadicInterval 40),(⟨762123383293,762123402622⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨49096640,49096704⟩ : DyadicInterval 40),(⟨-49098944,-49098880⟩ : DyadicInterval 40),(⟨762123382511,762123401840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2240,-512⟩ : DyadicInterval 40),(⟨762123383872,762123404000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨191771185526,192023049395⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176768535744,176768535808⟩ : DyadicInterval 40),(⟨-210735591872,-210735591808⟩ : DyadicInterval 40),(⟨745313669201,745313688531⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176982973824,176982973888⟩ : DyadicInterval 40),(⟨-211040707392,-211040707328⟩ : DyadicInterval 40),(⟨745269256912,745269276242⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34057733504,-33967056064⟩ : DyadicInterval 40),(⟨779106911648,779152269632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨176809371904,177003403136⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-211069782912,-210793684864⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e665_ok : ecellOkT e665 = true := by decide +kernel
theorem e665_pos {a z : ℝ} (ha1 : ((357291/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((715431/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e665 e665_ok ha1 ha2 hz1 hz2 hz

-- box ['715431/4096000', '17907/102400', '1999/2000', '3999/4000']  interval_lower 50130261/1099511627776
noncomputable def e666 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1291558674497,0,true,177003403072,177003403136⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨907464581055,0,false,-211069782912,-211069782848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1291786576200,0,true,177197400064,177197400128⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨907236679352,0,false,-211345950208,-211345950144⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1291462650973,0,true,176921654656,176921654720⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨907560604579,0,false,-210953444032,-210953443968⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1291738507464,0,true,177156485312,177156485376⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨907284748088,0,false,-211287695552,-211287695488⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536176148,0,true,24548096,24548160⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487079404,0,false,-24548672,-24548608⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099560786490,0,true,49157568,49157632⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099462469062,0,false,-49159872,-49159808⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625578,0,false,-2240,-2176⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627228,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1291510658020,0,true,176962525632,176962525696⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨907512597532,0,false,-211011606208,-211011606144⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1291762550389,0,true,177176950144,177176950208⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨907260705163,0,false,-211316832832,-211316832768⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1065896324115,0,false,-34139882688,-34139882624⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1065984353773,0,false,-34049080576,-34049080512⟩
    { al := (715431/4096000), au := (17907/102400), zl := (1999/2000), zu := (3999/4000),
      A := ⟨192047046721,192274948424⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177003403072,177003403136⟩ : DyadicInterval 40),(⟨-211069782912,-211069782848⟩ : DyadicInterval 40),(⟨745265022260,745265041590⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177197400064,177197400128⟩ : DyadicInterval 40),(⟨-211345950208,-211345950144⟩ : DyadicInterval 40),(⟨745224778871,745224798200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176921654656,176921654720⟩ : DyadicInterval 40),(⟨-210953444032,-210953443968⟩ : DyadicInterval 40),(⟨745281963689,745281983019⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177156485312,177156485376⟩ : DyadicInterval 40),(⟨-211287695552,-211287695488⟩ : DyadicInterval 40),(⟨745233270999,745233290329⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨24548372,49158714⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24548096,24548160⟩ : DyadicInterval 40),(⟨-24548672,-24548608⟩ : DyadicInterval 40),(⟨762123383291,762123402620⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨49157568,49157632⟩ : DyadicInterval 40),(⟨-49159872,-49159808⟩ : DyadicInterval 40),(⟨762123382506,762123401835⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2240,-512⟩ : DyadicInterval 40),(⟨762123383872,762123404000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨191999030244,192250922613⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176962525632,176962525696⟩ : DyadicInterval 40),(⟨-211011606208,-211011606144⟩ : DyadicInterval 40),(⟨745273494869,745273514199⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177176950144,177176950208⟩ : DyadicInterval 40),(⟨-211316832832,-211316832768⟩ : DyadicInterval 40),(⟨745229023691,745229043021⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34139882688,-34049080512⟩ : DyadicInterval 40),(⟨779147923872,779193344224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨177003403072,177197400128⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-211345950208,-211069782848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e666_ok : ecellOkT e666 = true := by decide +kernel
theorem e666_pos {a z : ℝ} (ha1 : ((715431/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((17907/102400 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e666 e666_ok ha1 ha2 hz1 hz2 hz

-- box ['357291/2048000', '715431/4096000', '3999/4000', '1']  interval_lower 23423067/549755813888
noncomputable def e667 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1291330772795,0,true,176809371904,176809371968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨907692482757,0,false,-210793684928,-210793684864⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1291558674498,0,true,177003403072,177003403136⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨907464581054,0,false,-211069782912,-211069782848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1291282818008,0,true,176768539712,176768539776⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨907740437544,0,false,-210735597568,-210735597504⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536176942,0,true,24548864,24548928⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487078610,0,false,-24549504,-24549440⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627227,0,false,-576,-512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1291306790495,0,true,176788951808,176788951872⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨907716465057,0,false,-210764634944,-210764634880⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1291558682983,0,true,177003410304,177003410368⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨907464572569,0,false,-211069793152,-211069793088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1065967579234,0,false,-34066382848,-34066382784⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1066055515523,0,false,-33975683072,-33975683008⟩
    { al := (357291/2048000), au := (715431/4096000), zl := (3999/4000), zu := 1,
      A := ⟨191819145019,192047046722⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176809371904,176809371968⟩ : DyadicInterval 40),(⟨-210793684928,-210793684864⟩ : DyadicInterval 40),(⟨745305216875,745305236205⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177003403072,177003403136⟩ : DyadicInterval 40),(⟨-211069782912,-211069782848⟩ : DyadicInterval 40),(⟨745265022260,745265041589⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176768539712,176768539776⟩ : DyadicInterval 40),(⟨-210735597568,-210735597504⟩ : DyadicInterval 40),(⟨745313668393,745313687722⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177003403072,177003403136⟩ : DyadicInterval 40),(⟨-211069782912,-211069782848⟩ : DyadicInterval 40),(⟨745265022260,745265041589⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,24549166⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24548864,24548928⟩ : DyadicInterval 40),(⟨-24549504,-24549440⟩ : DyadicInterval 40),(⟨762123383323,762123402652⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,0⟩ : DyadicInterval 40),(⟨762123383616,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨191795162719,192047055207⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176788951808,176788951872⟩ : DyadicInterval 40),(⟨-210764634944,-210764634880⟩ : DyadicInterval 40),(⟨745309443785,745309463114⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177003410304,177003410368⟩ : DyadicInterval 40),(⟨-211069793152,-211069793088⟩ : DyadicInterval 40),(⟨745265020741,745265040070⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34066382848,-33975683008⟩ : DyadicInterval 40),(⟨779111225120,779156594304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨176809371904,177003403136⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-211069782912,-210793684864⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e667_ok : ecellOkT e667 = true := by decide +kernel
theorem e667_pos {a z : ℝ} (ha1 : ((357291/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((715431/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e667 e667_ok ha1 ha2 hz1 hz2 hz

-- box ['715431/4096000', '17907/102400', '3999/4000', '1']  interval_lower 6198571/137438953472
noncomputable def e668 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1291558674497,0,true,177003403072,177003403136⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨907464581055,0,false,-211069782912,-211069782848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1291786576200,0,true,177197400064,177197400128⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨907236679352,0,false,-211345950208,-211345950144⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1291510662735,0,true,176962529600,176962529664⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨907512592817,0,false,-211011611904,-211011611840⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536207402,0,true,24579328,24579392⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487048150,0,false,-24579904,-24579840⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627226,0,false,-576,-512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1291534663699,0,true,176982962368,176982962432⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨907488591853,0,false,-211040691072,-211040691008⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1291786584689,0,true,177197407296,177197407360⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨907236670863,0,false,-211345960448,-211345960384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1065887918738,0,false,-34148553152,-34148553088⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1065975969405,0,false,-34057728640,-34057728576⟩
    { al := (715431/4096000), au := (17907/102400), zl := (3999/4000), zu := 1,
      A := ⟨192047046721,192274948424⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177003403072,177003403136⟩ : DyadicInterval 40),(⟨-211069782912,-211069782848⟩ : DyadicInterval 40),(⟨745265022260,745265041590⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177197400064,177197400128⟩ : DyadicInterval 40),(⟨-211345950208,-211345950144⟩ : DyadicInterval 40),(⟨745224778871,745224798200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176962529600,176962529664⟩ : DyadicInterval 40),(⟨-211011611904,-211011611840⟩ : DyadicInterval 40),(⟨745273494058,745273513387⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177197400064,177197400128⟩ : DyadicInterval 40),(⟨-211345950208,-211345950144⟩ : DyadicInterval 40),(⟨745224778871,745224798200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,24579626⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24579328,24579392⟩ : DyadicInterval 40),(⟨-24579904,-24579840⟩ : DyadicInterval 40),(⟨762123383290,762123402619⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,0⟩ : DyadicInterval 40),(⟨762123383616,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨192023035923,192274956913⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨176982962368,176982962432⟩ : DyadicInterval 40),(⟨-211040691072,-211040691008⟩ : DyadicInterval 40),(⟨745269259283,745269278613⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177197407296,177197407360⟩ : DyadicInterval 40),(⟨-211345960448,-211345960384⟩ : DyadicInterval 40),(⟨745224777347,745224796676⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34148553152,-34057728576⟩ : DyadicInterval 40),(⟨779152247904,779197679456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨177003403072,177197400128⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-211345950208,-211069782848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e668_ok : ecellOkT e668 = true := by decide +kernel
theorem e668_pos {a z : ℝ} (ha1 : ((715431/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((17907/102400 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e668 e668_ok ha1 ha2 hz1 hz2 hz

-- box ['17907/102400', '717129/4096000', '999/1000', '3997/4000']  interval_lower 13493691/274877906944
noncomputable def e669 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1291786576199,0,true,177197400064,177197400128⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨907236679353,0,false,-211345950208,-211345950144⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1292014477902,0,true,177391362816,177391362880⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨907008777650,0,false,-211622186880,-211622186816⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1291594301250,0,true,177033731904,177033731968⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨907428954302,0,false,-211112950208,-211112950144⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1291870100765,0,true,177268490176,177268490240⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨907153154787,0,false,-211447181184,-211447181120⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585363942,0,true,73733632,73733696⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437891610,0,false,-73738688,-73738624⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099610065677,0,true,98433472,98433536⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099413189875,0,false,-98442368,-98442304⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618962,0,false,-8832,-8768⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622832,0,false,-4992,-4928⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1291690434807,0,true,177115565696,177115565760⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨907332820745,0,false,-211229439296,-211229439232⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1291942298428,0,true,177329935936,177329936000⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨907080957124,0,false,-211534691584,-211534691520⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1065833436411,0,false,-34204755584,-34204755520⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1065921538378,0,false,-34113873536,-34113873472⟩
    { al := (17907/102400), au := (717129/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨192274948423,192502850126⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177197400064,177197400128⟩ : DyadicInterval 40),(⟨-211345950208,-211345950144⟩ : DyadicInterval 40),(⟨745224778871,745224798200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177391362816,177391362880⟩ : DyadicInterval 40),(⟨-211622186880,-211622186816⟩ : DyadicInterval 40),(⟨745184486760,745184506090⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177033731904,177033731968⟩ : DyadicInterval 40),(⟨-211112950208,-211112950144⟩ : DyadicInterval 40),(⟨745258734432,745258753762⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177268490176,177268490240⟩ : DyadicInterval 40),(⟨-211447181184,-211447181120⟩ : DyadicInterval 40),(⟨745210017724,745210037053⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨73736166,98437901⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73733632,73733696⟩ : DyadicInterval 40),(⟨-73738688,-73738624⟩ : DyadicInterval 40),(⟨762123381134,762123400464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨98433472,98433536⟩ : DyadicInterval 40),(⟨-98442368,-98442304⟩ : DyadicInterval 40),(⟨762123379186,762123398516⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8832,-4928⟩ : DyadicInterval 40),(⟨762123386080,762123407296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨192178807031,192430670652⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177115565696,177115565760⟩ : DyadicInterval 40),(⟨-211229439296,-211229439232⟩ : DyadicInterval 40),(⟨745241761681,745241781011⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177329935936,177329936000⟩ : DyadicInterval 40),(⟨-211534691584,-211534691520⟩ : DyadicInterval 40),(⟨745197253092,745197272422⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34204755584,-34113873472⟩ : DyadicInterval 40),(⟨779180320352,779225780672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨177197400064,177391362880⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-211622186880,-211345950144⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e669_ok : ecellOkT e669 = true := by decide +kernel
theorem e669_pos {a z : ℝ} (ha1 : ((17907/102400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((717129/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e669 e669_ok ha1 ha2 hz1 hz2 hz

-- box ['717129/4096000', '358989/2048000', '999/1000', '3997/4000']  interval_lower 56751397/1099511627776
noncomputable def e670 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1292014477901,0,true,177391362816,177391362880⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨907008777651,0,false,-211622186880,-211622186816⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1292242379604,0,true,177585291328,177585291392⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨906780875948,0,false,-211898492992,-211898492928⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1291821975050,0,true,177227529600,177227529664⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨907201280502,0,false,-211388852096,-211388852032⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1292097831541,0,true,177462294912,177462294976⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨906925424011,0,false,-211723236096,-211723236032⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585455328,0,true,73825024,73825088⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437800224,0,false,-73830080,-73830016⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099610187547,0,true,98555328,98555392⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099413068005,0,false,-98564224,-98564160⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618941,0,false,-8896,-8832⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622819,0,false,-4992,-4928⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1291918222563,0,true,177309445888,177309445952⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨907105032989,0,false,-211505508544,-211505508480⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1292170114665,0,true,177523802560,177523802624⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨906853140887,0,false,-211810872064,-211810872000⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1065753646839,0,false,-34287069440,-34287069376⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1065841863144,0,false,-34196062592,-34196062528⟩
    { al := (717129/4096000), au := (358989/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨192502850125,192730751828⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177391362816,177391362880⟩ : DyadicInterval 40),(⟨-211622186880,-211622186816⟩ : DyadicInterval 40),(⟨745184486760,745184506090⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177585291328,177585291392⟩ : DyadicInterval 40),(⟨-211898492992,-211898492928⟩ : DyadicInterval 40),(⟨745144145943,745144165273⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177227529600,177227529664⟩ : DyadicInterval 40),(⟨-211388852096,-211388852032⟩ : DyadicInterval 40),(⟨745218523668,745218542997⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177462294912,177462294976⟩ : DyadicInterval 40),(⟨-211723236096,-211723236032⟩ : DyadicInterval 40),(⟨745169738030,745169757360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨73827552,98559771⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73825024,73825088⟩ : DyadicInterval 40),(⟨-73830080,-73830016⟩ : DyadicInterval 40),(⟨762123381122,762123400451⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨98555328,98555392⟩ : DyadicInterval 40),(⟨-98564224,-98564160⟩ : DyadicInterval 40),(⟨762123379164,762123398494⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8896,-4928⟩ : DyadicInterval 40),(⟨762123386080,762123407328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨192406594787,192658486889⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177309445888,177309445952⟩ : DyadicInterval 40),(⟨-211505508544,-211505508480⟩ : DyadicInterval 40),(⟨745201510271,745201529601⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177523802560,177523802624⟩ : DyadicInterval 40),(⟨-211810872064,-211810872000⟩ : DyadicInterval 40),(⟨745156942833,745156962162⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34287069440,-34196062528⟩ : DyadicInterval 40),(⟨779221414880,779266937600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨177391362816,177585291392⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-211898492992,-211622186816⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e670_ok : ecellOkT e670 = true := by decide +kernel
theorem e670_pos {a z : ℝ} (ha1 : ((717129/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((358989/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e670 e670_ok ha1 ha2 hz1 hz2 hz

-- box ['17907/102400', '717129/4096000', '3997/4000', '1999/2000']  interval_lower 53431849/1099511627776
noncomputable def e671 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1291786576199,0,true,177197400064,177197400128⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨907236679353,0,false,-211345950208,-211345950144⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1292014477902,0,true,177391362816,177391362880⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨907008777650,0,false,-211622186880,-211622186816⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1291642369987,0,true,177074651264,177074651328⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨907380885565,0,false,-211171195584,-211171195520⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1291918226478,0,true,177309449216,177309449280⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨907105029074,0,false,-211505513280,-211505513216⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099560785414,0,true,49156480,49156544⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099462470138,0,false,-49158784,-49158720⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585456688,0,true,73826432,73826496⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437798864,0,false,-73831424,-73831360⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622818,0,false,-4992,-4928⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625579,0,false,-2240,-2176⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1291714468710,0,true,177136023616,177136023680⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨907308786842,0,false,-211258564096,-211258564032⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1291966360949,0,true,177350414208,177350414272⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨907056894603,0,false,-211563859136,-211563859072⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1065825013296,0,false,-34213444864,-34213444800⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1065913136292,0,false,-34122540416,-34122540352⟩
    { al := (17907/102400), au := (717129/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨192274948423,192502850126⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177197400064,177197400128⟩ : DyadicInterval 40),(⟨-211345950208,-211345950144⟩ : DyadicInterval 40),(⟨745224778871,745224798200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177391362816,177391362880⟩ : DyadicInterval 40),(⟨-211622186880,-211622186816⟩ : DyadicInterval 40),(⟨745184486760,745184506090⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177074651264,177074651328⟩ : DyadicInterval 40),(⟨-211171195584,-211171195520⟩ : DyadicInterval 40),(⟨745250248775,745250268104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177309449216,177309449280⟩ : DyadicInterval 40),(⟨-211505513280,-211505513216⟩ : DyadicInterval 40),(⟨745201509577,745201528907⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨49157638,73828912⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨49156480,49156544⟩ : DyadicInterval 40),(⟨-49158784,-49158720⟩ : DyadicInterval 40),(⟨762123382506,762123401835⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73826432,73826496⟩ : DyadicInterval 40),(⟨-73831424,-73831360⟩ : DyadicInterval 40),(⟨762123381090,762123400419⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4992,-2176⟩ : DyadicInterval 40),(⟨762123384704,762123405376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨192202840934,192454733173⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177136023616,177136023680⟩ : DyadicInterval 40),(⟨-211258564096,-211258564032⟩ : DyadicInterval 40),(⟨745237517046,745237536376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177350414208,177350414272⟩ : DyadicInterval 40),(⟨-211563859136,-211563859072⟩ : DyadicInterval 40),(⟨745192997715,745193017045⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34213444864,-34122540352⟩ : DyadicInterval 40),(⟨779184653792,779230125312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨177197400064,177391362880⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-211622186880,-211345950144⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e671_ok : ecellOkT e671 = true := by decide +kernel
theorem e671_pos {a z : ℝ} (ha1 : ((17907/102400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((717129/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e671 e671_ok ha1 ha2 hz1 hz2 hz

-- box ['717129/4096000', '358989/2048000', '3997/4000', '1999/2000']  interval_lower 56206527/1099511627776
noncomputable def e672 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1292014477901,0,true,177391362816,177391362880⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨907008777651,0,false,-211622186880,-211622186816⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1292242379604,0,true,177585291328,177585291392⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨906780875948,0,false,-211898492992,-211898492928⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1291870100763,0,true,177268490176,177268490240⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨907153154789,0,false,-211447181184,-211447181120⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1292146014229,0,true,177503295232,177503295296⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨906877241323,0,false,-211781651904,-211781651840⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099560846339,0,true,49217408,49217472⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099462409213,0,false,-49219712,-49219648⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585548092,0,true,73917824,73917888⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437707460,0,false,-73922816,-73922752⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622806,0,false,-4992,-4928⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625573,0,false,-2240,-2176⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1291942284947,0,true,177329924480,177329924544⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨907080970605,0,false,-211534675200,-211534675136⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1292194205675,0,true,177544301504,177544301568⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨906829049877,0,false,-211840081536,-211840081472⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1065745203767,0,false,-34295779968,-34295779904⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1065833441131,0,false,-34204750720,-34204750656⟩
    { al := (717129/4096000), au := (358989/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨192502850125,192730751828⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177391362816,177391362880⟩ : DyadicInterval 40),(⟨-211622186880,-211622186816⟩ : DyadicInterval 40),(⟨745184486760,745184506090⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177585291328,177585291392⟩ : DyadicInterval 40),(⟨-211898492992,-211898492928⟩ : DyadicInterval 40),(⟨745144145943,745144165273⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177268490176,177268490240⟩ : DyadicInterval 40),(⟨-211447181184,-211447181120⟩ : DyadicInterval 40),(⟨745210017724,745210037053⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177503295232,177503295296⟩ : DyadicInterval 40),(⟨-211781651904,-211781651840⟩ : DyadicInterval 40),(⟨745161209499,745161228829⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨49218563,73920316⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨49217408,49217472⟩ : DyadicInterval 40),(⟨-49219712,-49219648⟩ : DyadicInterval 40),(⟨762123382500,762123401829⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73917824,73917888⟩ : DyadicInterval 40),(⟨-73922816,-73922752⟩ : DyadicInterval 40),(⟨762123381078,762123400407⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4992,-2176⟩ : DyadicInterval 40),(⟨762123384704,762123405376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨192430657171,192682577899⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177329924480,177329924544⟩ : DyadicInterval 40),(⟨-211534675200,-211534675136⟩ : DyadicInterval 40),(⟨745197255448,745197274778⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177544301504,177544301568⟩ : DyadicInterval 40),(⟨-211840081536,-211840081472⟩ : DyadicInterval 40),(⟨745152677264,745152696593⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34295779968,-34204750656⟩ : DyadicInterval 40),(⟨779225758944,779271292864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨177391362816,177585291392⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-211898492992,-211622186816⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e672_ok : ecellOkT e672 = true := by decide +kernel
theorem e672_pos {a z : ℝ} (ha1 : ((717129/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((358989/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e672 e672_ok ha1 ha2 hz1 hz2 hz

-- box ['358989/2048000', '718827/4096000', '999/1000', '3997/4000']  interval_lower 59542029/1099511627776
noncomputable def e673 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1292242379603,0,true,177585291328,177585291392⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨906780875949,0,false,-211898492992,-211898492928⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1292470281307,0,true,177779185664,177779185728⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨906552974245,0,false,-212174868544,-212174868480⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1292049648851,0,true,177421293056,177421293120⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨906973606701,0,false,-211664823296,-211664823232⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1292325562317,0,true,177656065536,177656065600⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨906697693235,0,false,-211999360320,-211999360256⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585546729,0,true,73916416,73916480⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437708823,0,false,-73921472,-73921408⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099610309437,0,true,98677184,98677248⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099412946115,0,false,-98686144,-98686080⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618919,0,false,-8896,-8832⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622807,0,false,-4992,-4928⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1292146010308,0,true,177503291904,177503291968⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨906877245244,0,false,-211781647168,-211781647104⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1292397930908,0,true,177717635072,177717635136⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨906625324644,0,false,-212087121920,-212087121856⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1065673762858,0,false,-34369486848,-34369486784⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1065762093532,0,false,-34278355200,-34278355136⟩
    { al := (358989/2048000), au := (718827/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨192730751827,192958653531⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177585291328,177585291392⟩ : DyadicInterval 40),(⟨-211898492992,-211898492928⟩ : DyadicInterval 40),(⟨745144145943,745144165273⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177779185664,177779185728⟩ : DyadicInterval 40),(⟨-212174868544,-212174868480⟩ : DyadicInterval 40),(⟨745103756373,745103775702⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177421293056,177421293120⟩ : DyadicInterval 40),(⟨-211664823296,-211664823232⟩ : DyadicInterval 40),(⟨745178264348,745178283678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177656065536,177656065600⟩ : DyadicInterval 40),(⟨-211999360320,-211999360256⟩ : DyadicInterval 40),(⟨745129409645,745129428975⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨73918953,98681661⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73916416,73916480⟩ : DyadicInterval 40),(⟨-73921472,-73921408⟩ : DyadicInterval 40),(⟨762123381110,762123400439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨98677184,98677248⟩ : DyadicInterval 40),(⟨-98686144,-98686080⟩ : DyadicInterval 40),(⟨762123379174,762123398504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8896,-4928⟩ : DyadicInterval 40),(⟨762123386080,762123407328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨192634382532,192886303132⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177503291904,177503291968⟩ : DyadicInterval 40),(⟨-211781647168,-211781647104⟩ : DyadicInterval 40),(⟨745161210196,745161229525⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177717635072,177717635136⟩ : DyadicInterval 40),(⟨-212087121920,-212087121856⟩ : DyadicInterval 40),(⟨745116583830,745116603159⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34369486848,-34278355136⟩ : DyadicInterval 40),(⟨779262561184,779308146304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨177585291328,177779185728⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-212174868544,-211898492928⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e673_ok : ecellOkT e673 = true := by decide +kernel
theorem e673_pos {a z : ℝ} (ha1 : ((358989/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((718827/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e673 e673_ok ha1 ha2 hz1 hz2 hz

-- box ['718827/4096000', '179919/1024000', '999/1000', '3997/4000']  interval_lower 31173195/549755813888
noncomputable def e674 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1292470281306,0,true,177779185664,177779185728⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨906552974246,0,false,-212174868544,-212174868480⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1292698183009,0,true,177973045824,177973045888⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨906325072543,0,false,-212451313536,-212451313472⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1292277322652,0,true,177615022400,177615022464⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨906745932900,0,false,-211940863744,-211940863680⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1292553293093,0,true,177849801984,177849802048⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨906469962459,0,false,-212275553856,-212275553792⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585638146,0,true,74007872,74007936⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437617406,0,false,-74012864,-74012800⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099610431347,0,true,98799104,98799168⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099412824205,0,false,-98808064,-98808000⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618897,0,false,-8896,-8832⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622795,0,false,-4992,-4928⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1292373798060,0,true,177697103744,177697103808⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨906649457492,0,false,-212057855168,-212057855104⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1292625747155,0,true,177911433344,177911433408⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨906397508397,0,false,-212363441280,-212363441216⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1065593784470,0,false,-34452007872,-34452007808⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1065682229535,0,false,-34360751360,-34360751296⟩
    { al := (718827/4096000), au := (179919/1024000), zl := (999/1000), zu := (3997/4000),
      A := ⟨192958653530,193186555233⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177779185664,177779185728⟩ : DyadicInterval 40),(⟨-212174868544,-212174868480⟩ : DyadicInterval 40),(⟨745103756373,745103775702⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177973045824,177973045888⟩ : DyadicInterval 40),(⟨-212451313536,-212451313472⟩ : DyadicInterval 40),(⟨745063318036,745063337366⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177615022400,177615022464⟩ : DyadicInterval 40),(⟨-211940863744,-211940863680⟩ : DyadicInterval 40),(⟨745137956362,745137975691⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177849801984,177849802048⟩ : DyadicInterval 40),(⟨-212275553856,-212275553792⟩ : DyadicInterval 40),(⟨745089032595,745089051925⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨74010370,98803571⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74007872,74007936⟩ : DyadicInterval 40),(⟨-74012864,-74012800⟩ : DyadicInterval 40),(⟨762123381066,762123400395⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨98799104,98799168⟩ : DyadicInterval 40),(⟨-98808064,-98808000⟩ : DyadicInterval 40),(⟨762123379152,762123398482⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8896,-4928⟩ : DyadicInterval 40),(⟨762123386080,762123407328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨192862170284,193114119379⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177697103744,177697103808⟩ : DyadicInterval 40),(⟨-212057855168,-212057855104⟩ : DyadicInterval 40),(⟨745120861441,745120880770⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177911433344,177911433408⟩ : DyadicInterval 40),(⟨-212363441280,-212363441216⟩ : DyadicInterval 40),(⟨745076176202,745076195532⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34452007872,-34360751296⟩ : DyadicInterval 40),(⟨779303759264,779349406816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨177779185664,177973045888⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-212451313536,-212174868480⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e674_ok : ecellOkT e674 = true := by decide +kernel
theorem e674_pos {a z : ℝ} (ha1 : ((718827/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((179919/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e674 e674_ok ha1 ha2 hz1 hz2 hz

-- box ['358989/2048000', '718827/4096000', '3997/4000', '1999/2000']  interval_lower 29497475/549755813888
noncomputable def e675 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1292242379603,0,true,177585291328,177585291392⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨906780875949,0,false,-211898492992,-211898492928⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1292470281307,0,true,177779185664,177779185728⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨906552974245,0,false,-212174868544,-212174868480⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1292097831539,0,true,177462294912,177462294976⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨906925424013,0,false,-211723236096,-211723236032⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1292373801981,0,true,177697107136,177697107200⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨906649453571,0,false,-212057859904,-212057859840⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099560907274,0,true,49278336,49278400⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099462348278,0,false,-49280640,-49280576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585639511,0,true,74009216,74009280⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437616041,0,false,-74014272,-74014208⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622794,0,false,-4992,-4928⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625568,0,false,-2240,-2176⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1292170101178,0,true,177523791104,177523791168⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨906853154374,0,false,-211810855680,-211810855616⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1292422050406,0,true,177738154624,177738154688⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨906601205146,0,false,-212116373312,-212116373248⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1065665299807,0,false,-34378218624,-34378218560⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1065753651566,0,false,-34287064576,-34287064512⟩
    { al := (358989/2048000), au := (718827/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨192730751827,192958653531⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177585291328,177585291392⟩ : DyadicInterval 40),(⟨-211898492992,-211898492928⟩ : DyadicInterval 40),(⟨745144145943,745144165273⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177779185664,177779185728⟩ : DyadicInterval 40),(⟨-212174868544,-212174868480⟩ : DyadicInterval 40),(⟨745103756373,745103775702⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177462294912,177462294976⟩ : DyadicInterval 40),(⟨-211723236096,-211723236032⟩ : DyadicInterval 40),(⟨745169738031,745169757360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177697107136,177697107200⟩ : DyadicInterval 40),(⟨-212057859904,-212057859840⟩ : DyadicInterval 40),(⟨745120860705,745120880034⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨49279498,74011735⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨49278336,49278400⟩ : DyadicInterval 40),(⟨-49280640,-49280576⟩ : DyadicInterval 40),(⟨762123382495,762123401824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74009216,74009280⟩ : DyadicInterval 40),(⟨-74014272,-74014208⟩ : DyadicInterval 40),(⟨762123381097,762123400427⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4992,-2176⟩ : DyadicInterval 40),(⟨762123384704,762123405376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨192658473402,192910422630⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177523791104,177523791168⟩ : DyadicInterval 40),(⟨-211810855680,-211810855616⟩ : DyadicInterval 40),(⟨745156945196,745156964525⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177738154624,177738154688⟩ : DyadicInterval 40),(⟨-212116373312,-212116373248⟩ : DyadicInterval 40),(⟨745112308082,745112327411⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34378218624,-34287064512⟩ : DyadicInterval 40),(⟨779266915872,779312512192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨177585291328,177779185728⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-212174868544,-211898492928⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e675_ok : ecellOkT e675 = true := by decide +kernel
theorem e675_pos {a z : ℝ} (ha1 : ((358989/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((718827/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e675 e675_ok ha1 ha2 hz1 hz2 hz

-- box ['718827/4096000', '179919/1024000', '3997/4000', '1999/2000']  interval_lower 61797019/1099511627776
noncomputable def e676 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1292470281306,0,true,177779185664,177779185728⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨906552974246,0,false,-212174868544,-212174868480⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1292698183009,0,true,177973045824,177973045888⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨906325072543,0,false,-212451313536,-212451313472⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1292325562315,0,true,177656065536,177656065600⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨906697693237,0,false,-211999360320,-211999360256⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1292601589732,0,true,177890884800,177890884864⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨906421665820,0,false,-212334137344,-212334137280⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099560968220,0,true,49339328,49339392⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099462287332,0,false,-49341568,-49341504⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585730945,0,true,74100608,74100672⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437524607,0,false,-74105728,-74105664⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622781,0,false,-5056,-4992⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625562,0,false,-2240,-2176⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1292397917416,0,true,177717623552,177717623616⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨906625338136,0,false,-212087105600,-212087105536⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1292649895134,0,true,177931973504,177931973568⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨906373360418,0,false,-212392734528,-212392734464⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1065585301418,0,false,-34460760960,-34460760896⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1065673767593,0,false,-34369481984,-34369481920⟩
    { al := (718827/4096000), au := (179919/1024000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨192958653530,193186555233⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177779185664,177779185728⟩ : DyadicInterval 40),(⟨-212174868544,-212174868480⟩ : DyadicInterval 40),(⟨745103756373,745103775702⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177973045824,177973045888⟩ : DyadicInterval 40),(⟨-212451313536,-212451313472⟩ : DyadicInterval 40),(⟨745063318036,745063337366⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177656065536,177656065600⟩ : DyadicInterval 40),(⟨-211999360320,-211999360256⟩ : DyadicInterval 40),(⟨745129409646,745129428975⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177890884800,177890884864⟩ : DyadicInterval 40),(⟨-212334137344,-212334137280⟩ : DyadicInterval 40),(⟨745080463285,745080482614⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨49340444,74103169⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨49339328,49339392⟩ : DyadicInterval 40),(⟨-49341568,-49341504⟩ : DyadicInterval 40),(⟨762123382457,762123401786⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74100608,74100672⟩ : DyadicInterval 40),(⟨-74105728,-74105664⟩ : DyadicInterval 40),(⟨762123381117,762123400446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5056,-2176⟩ : DyadicInterval 40),(⟨762123384704,762123405408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨192886289640,193138267358⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177717623552,177717623616⟩ : DyadicInterval 40),(⟨-212087105600,-212087105536⟩ : DyadicInterval 40),(⟨745116586264,745116605593⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177931973504,177931973568⟩ : DyadicInterval 40),(⟨-212392734528,-212392734464⟩ : DyadicInterval 40),(⟨745071890224,745071909553⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34460760960,-34369481920⟩ : DyadicInterval 40),(⟨779308124576,779353783360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨177779185664,177973045888⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-212451313536,-212174868480⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e676_ok : ecellOkT e676 = true := by decide +kernel
theorem e676_pos {a z : ℝ} (ha1 : ((718827/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((179919/1024000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e676 e676_ok ha1 ha2 hz1 hz2 hz

-- box ['17907/102400', '717129/4096000', '1999/2000', '3999/4000']  interval_lower 52888659/1099511627776
noncomputable def e677 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1291786576199,0,true,177197400064,177197400128⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨907236679353,0,false,-211345950208,-211345950144⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1292014477902,0,true,177391362816,177391362880⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨907008777650,0,false,-211622186880,-211622186816⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1291690438724,0,true,177115569024,177115569088⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨907332816828,0,false,-211229444032,-211229443968⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1291966352190,0,true,177350406784,177350406848⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨907056903362,0,false,-211563848576,-211563848512⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536206607,0,true,24578496,24578560⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487048945,0,false,-24579136,-24579072⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099560847417,0,true,49218496,49218560⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099462408135,0,false,-49220800,-49220736⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625572,0,false,-2240,-2176⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627227,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1291738502741,0,true,177156481280,177156481344⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨907284752811,0,false,-211287689856,-211287689792⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1291990423602,0,true,177370892288,177370892352⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨907032831950,0,false,-211593027712,-211593027648⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1065816589081,0,false,-34222135424,-34222135360⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1065904733110,0,false,-34131208512,-34131208448⟩
    { al := (17907/102400), au := (717129/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨192274948423,192502850126⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177197400064,177197400128⟩ : DyadicInterval 40),(⟨-211345950208,-211345950144⟩ : DyadicInterval 40),(⟨745224778871,745224798200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177391362816,177391362880⟩ : DyadicInterval 40),(⟨-211622186880,-211622186816⟩ : DyadicInterval 40),(⟨745184486760,745184506090⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177115569024,177115569088⟩ : DyadicInterval 40),(⟨-211229444032,-211229443968⟩ : DyadicInterval 40),(⟨745241760989,745241780318⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177350406784,177350406848⟩ : DyadicInterval 40),(⟨-211563848576,-211563848512⟩ : DyadicInterval 40),(⟨745192999270,745193018600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨24578831,49219641⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24578496,24578560⟩ : DyadicInterval 40),(⟨-24579136,-24579072⟩ : DyadicInterval 40),(⟨762123383322,762123402651⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨49218496,49218560⟩ : DyadicInterval 40),(⟨-49220800,-49220736⟩ : DyadicInterval 40),(⟨762123382500,762123401829⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2240,-512⟩ : DyadicInterval 40),(⟨762123383872,762123404000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨192226874965,192478795826⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177156481280,177156481344⟩ : DyadicInterval 40),(⟨-211287689856,-211287689792⟩ : DyadicInterval 40),(⟨745233271851,745233291181⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177370892288,177370892352⟩ : DyadicInterval 40),(⟨-211593027712,-211593027648⟩ : DyadicInterval 40),(⟨745188741764,745188761093⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34222135424,-34131208448⟩ : DyadicInterval 40),(⟨779188987840,779234470592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨177197400064,177391362880⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-211622186880,-211345950144⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e677_ok : ecellOkT e677 = true := by decide +kernel
theorem e677_pos {a z : ℝ} (ha1 : ((17907/102400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((717129/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e677 e677_ok ha1 ha2 hz1 hz2 hz

-- box ['717129/4096000', '358989/2048000', '1999/2000', '3999/4000']  interval_lower 55661021/1099511627776
noncomputable def e678 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1292014477901,0,true,177391362816,177391362880⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨907008777651,0,false,-211622186880,-211622186816⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1292242379604,0,true,177585291328,177585291392⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨906780875948,0,false,-211898492992,-211898492928⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1291918226475,0,true,177309449216,177309449280⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨907105029077,0,false,-211505513280,-211505513216⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1292194196917,0,true,177544294080,177544294144⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨906829058635,0,false,-211840070912,-211840070848⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536237070,0,true,24608960,24609024⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487018482,0,false,-24609600,-24609536⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099560908354,0,true,49279424,49279488⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099462347198,0,false,-49281728,-49281664⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625567,0,false,-2240,-2176⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627226,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1291966347467,0,true,177350402752,177350402816⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨907056908085,0,false,-211563842816,-211563842752⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1292218296818,0,true,177564800192,177564800256⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨906804958734,0,false,-211869291904,-211869291840⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1065736759593,0,false,-34304491712,-34304491648⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1065825018017,0,false,-34213440000,-34213439936⟩
    { al := (717129/4096000), au := (358989/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨192502850125,192730751828⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177391362816,177391362880⟩ : DyadicInterval 40),(⟨-211622186880,-211622186816⟩ : DyadicInterval 40),(⟨745184486760,745184506090⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177585291328,177585291392⟩ : DyadicInterval 40),(⟨-211898492992,-211898492928⟩ : DyadicInterval 40),(⟨745144145943,745144165273⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177309449216,177309449280⟩ : DyadicInterval 40),(⟨-211505513280,-211505513216⟩ : DyadicInterval 40),(⟨745201509578,745201528908⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177544294080,177544294144⟩ : DyadicInterval 40),(⟨-211840070912,-211840070848⟩ : DyadicInterval 40),(⟨745152678796,745152698126⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨24609294,49280578⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24608960,24609024⟩ : DyadicInterval 40),(⟨-24609600,-24609536⟩ : DyadicInterval 40),(⟨762123383321,762123402650⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨49279424,49279488⟩ : DyadicInterval 40),(⟨-49281728,-49281664⟩ : DyadicInterval 40),(⟨762123382495,762123401824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2240,-512⟩ : DyadicInterval 40),(⟨762123383872,762123404000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨192454719691,192706669042⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177350402752,177350402816⟩ : DyadicInterval 40),(⟨-211563842816,-211563842752⟩ : DyadicInterval 40),(⟨745193000099,745193019428⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177564800192,177564800256⟩ : DyadicInterval 40),(⟨-211869291904,-211869291840⟩ : DyadicInterval 40),(⟨745148411103,745148430432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34304491712,-34213439936⟩ : DyadicInterval 40),(⟨779230103584,779275648736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨177391362816,177585291392⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-211898492992,-211622186816⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e678_ok : ecellOkT e678 = true := by decide +kernel
theorem e678_pos {a z : ℝ} (ha1 : ((717129/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((358989/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e678 e678_ok ha1 ha2 hz1 hz2 hz

-- box ['17907/102400', '717129/4096000', '3999/4000', '1']  interval_lower 26172521/549755813888
noncomputable def e679 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1291786576199,0,true,177197400064,177197400128⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨907236679353,0,false,-211345950208,-211345950144⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1292014477902,0,true,177391362816,177391362880⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨907008777650,0,false,-211622186880,-211622186816⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1291738507461,0,true,177156485312,177156485376⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨907284748091,0,false,-211287695552,-211287695488⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536237866,0,true,24609792,24609856⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487017686,0,false,-24610368,-24610304⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627225,0,false,-576,-512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1291762536912,0,true,177176938688,177176938752⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨907260718640,0,false,-211316816512,-211316816448⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1292014486394,0,true,177391370048,177391370112⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨907008769158,0,false,-211622197184,-211622197120⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1065808163765,0,false,-34230827136,-34230827072⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1065896328829,0,false,-34139877824,-34139877760⟩
    { al := (17907/102400), au := (717129/4096000), zl := (3999/4000), zu := 1,
      A := ⟨192274948423,192502850126⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177197400064,177197400128⟩ : DyadicInterval 40),(⟨-211345950208,-211345950144⟩ : DyadicInterval 40),(⟨745224778871,745224798200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177391362816,177391362880⟩ : DyadicInterval 40),(⟨-211622186880,-211622186816⟩ : DyadicInterval 40),(⟨745184486760,745184506090⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177156485312,177156485376⟩ : DyadicInterval 40),(⟨-211287695552,-211287695488⟩ : DyadicInterval 40),(⟨745233270999,745233290329⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177391362816,177391362880⟩ : DyadicInterval 40),(⟨-211622186880,-211622186816⟩ : DyadicInterval 40),(⟨745184486760,745184506090⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,24610090⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24609792,24609856⟩ : DyadicInterval 40),(⟨-24610368,-24610304⟩ : DyadicInterval 40),(⟨762123383289,762123402618⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,0⟩ : DyadicInterval 40),(⟨762123383616,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨192250909136,192502858618⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177176938688,177176938752⟩ : DyadicInterval 40),(⟨-211316816512,-211316816448⟩ : DyadicInterval 40),(⟨745229026069,745229045398⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177391370048,177391370112⟩ : DyadicInterval 40),(⟨-211622197184,-211622197120⟩ : DyadicInterval 40),(⟨745184485259,745184504588⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34230827136,-34139877760⟩ : DyadicInterval 40),(⟨779193322496,779238816448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨177197400064,177391362880⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-211622186880,-211345950144⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e679_ok : ecellOkT e679 = true := by decide +kernel
theorem e679_pos {a z : ℝ} (ha1 : ((17907/102400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((717129/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e679 e679_ok ha1 ha2 hz1 hz2 hz

-- box ['717129/4096000', '358989/2048000', '3999/4000', '1']  interval_lower 55115355/1099511627776
noncomputable def e680 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1292014477901,0,true,177391362816,177391362880⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨907008777651,0,false,-211622186880,-211622186816⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1292242379604,0,true,177585291328,177585291392⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨906780875948,0,false,-211898492992,-211898492928⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1291966352188,0,true,177350406784,177350406848⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨907056903364,0,false,-211563848512,-211563848448⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536268335,0,true,24640256,24640320⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486987217,0,false,-24640896,-24640832⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627223,0,false,-576,-512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1291990410123,0,true,177370880768,177370880832⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨907032845429,0,false,-211593011328,-211593011264⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1292242388092,0,true,177585298560,177585298624⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨906780867460,0,false,-211898503296,-211898503232⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1065728314317,0,false,-34313204672,-34313204608⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1065816593802,0,false,-34222130560,-34222130496⟩
    { al := (717129/4096000), au := (358989/2048000), zl := (3999/4000), zu := 1,
      A := ⟨192502850125,192730751828⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177391362816,177391362880⟩ : DyadicInterval 40),(⟨-211622186880,-211622186816⟩ : DyadicInterval 40),(⟨745184486760,745184506090⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177585291328,177585291392⟩ : DyadicInterval 40),(⟨-211898492992,-211898492928⟩ : DyadicInterval 40),(⟨745144145943,745144165273⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177350406784,177350406848⟩ : DyadicInterval 40),(⟨-211563848512,-211563848448⟩ : DyadicInterval 40),(⟨745192999244,745193018574⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177585291328,177585291392⟩ : DyadicInterval 40),(⟨-211898492992,-211898492928⟩ : DyadicInterval 40),(⟨745144145943,745144165273⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,24640559⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24640256,24640320⟩ : DyadicInterval 40),(⟨-24640896,-24640832⟩ : DyadicInterval 40),(⟨762123383319,762123402648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,0⟩ : DyadicInterval 40),(⟨762123383616,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨192478782347,192730760316⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177370880768,177370880832⟩ : DyadicInterval 40),(⟨-211593011328,-211593011264⟩ : DyadicInterval 40),(⟨745188744158,745188763488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177585298560,177585298624⟩ : DyadicInterval 40),(⟨-211898503296,-211898503232⟩ : DyadicInterval 40),(⟨745144144439,745144163769⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34313204672,-34222130496⟩ : DyadicInterval 40),(⟨779234448864,779280005216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨177391362816,177585291392⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-211898492992,-211622186816⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e680_ok : ecellOkT e680 = true := by decide +kernel
theorem e680_pos {a z : ℝ} (ha1 : ((717129/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((358989/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e680 e680_ok ha1 ha2 hz1 hz2 hz

-- box ['358989/2048000', '718827/4096000', '1999/2000', '3999/4000']  interval_lower 58447153/1099511627776
noncomputable def e681 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1292242379603,0,true,177585291328,177585291392⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨906780875949,0,false,-211898492992,-211898492928⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1292470281307,0,true,177779185664,177779185728⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨906552974245,0,false,-212174868544,-212174868480⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1292146014227,0,true,177503295232,177503295296⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨906877241325,0,false,-211781651904,-211781651840⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1292422041644,0,true,177738147136,177738147200⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨906601213908,0,false,-212116362688,-212116362624⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536267537,0,true,24639424,24639488⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486988015,0,false,-24640064,-24640000⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099560969302,0,true,49340416,49340480⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099462286250,0,false,-49342656,-49342592⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625561,0,false,-2240,-2176⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627224,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1292194192187,0,true,177544290048,177544290112⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨906829063365,0,false,-211840065152,-211840065088⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1292446170031,0,true,177758673856,177758673920⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨906577085521,0,false,-212145625600,-212145625536⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1065656835653,0,false,-34386951680,-34386951616⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1065745208495,0,false,-34295775104,-34295775040⟩
    { al := (358989/2048000), au := (718827/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨192730751827,192958653531⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177585291328,177585291392⟩ : DyadicInterval 40),(⟨-211898492992,-211898492928⟩ : DyadicInterval 40),(⟨745144145943,745144165273⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177779185664,177779185728⟩ : DyadicInterval 40),(⟨-212174868544,-212174868480⟩ : DyadicInterval 40),(⟨745103756373,745103775702⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177503295232,177503295296⟩ : DyadicInterval 40),(⟨-211781651904,-211781651840⟩ : DyadicInterval 40),(⟨745161209499,745161228829⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177738147136,177738147200⟩ : DyadicInterval 40),(⟨-212116362688,-212116362624⟩ : DyadicInterval 40),(⟨745112309656,745112328986⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨24639761,49341526⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24639424,24639488⟩ : DyadicInterval 40),(⟨-24640064,-24640000⟩ : DyadicInterval 40),(⟨762123383319,762123402648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨49340416,49340480⟩ : DyadicInterval 40),(⟨-49342656,-49342592⟩ : DyadicInterval 40),(⟨762123382457,762123401786⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2240,-512⟩ : DyadicInterval 40),(⟨762123383872,762123404000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨192682564411,192934542255⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177544290048,177544290112⟩ : DyadicInterval 40),(⟨-211840065152,-211840065088⟩ : DyadicInterval 40),(⟨745152679628,745152698957⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177758673856,177758673920⟩ : DyadicInterval 40),(⟨-212145625600,-212145625536⟩ : DyadicInterval 40),(⟨745108031777,745108051107⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34386951680,-34295775040⟩ : DyadicInterval 40),(⟨779271271136,779316878720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨177585291328,177779185728⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-212174868544,-211898492928⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e681_ok : ecellOkT e681 = true := by decide +kernel
theorem e681_pos {a z : ℝ} (ha1 : ((358989/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((718827/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e681 e681_ok ha1 ha2 hz1 hz2 hz

-- box ['718827/4096000', '179919/1024000', '1999/2000', '3999/4000']  interval_lower 61247129/1099511627776
noncomputable def e682 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1292470281306,0,true,177779185664,177779185728⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨906552974246,0,false,-212174868544,-212174868480⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1292698183009,0,true,177973045824,177973045888⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨906325072543,0,false,-212451313536,-212451313472⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1292373801979,0,true,177697107136,177697107200⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨906649453573,0,false,-212057859904,-212057859840⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1292649886371,0,true,177931966080,177931966144⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨906373369181,0,false,-212392723904,-212392723840⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536298010,0,true,24669952,24670016⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486957542,0,false,-24670528,-24670464⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099561030259,0,true,49401344,49401408⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099462225293,0,false,-49403648,-49403584⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625556,0,false,-2240,-2176⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627223,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1292422036914,0,true,177738143104,177738143168⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨906601218638,0,false,-212116356928,-212116356864⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1292674043250,0,true,177952513408,177952513472⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨906349212302,0,false,-212422028736,-212422028672⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1065576817257,0,false,-34469515264,-34469515200⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1065665304542,0,false,-34378213760,-34378213696⟩
    { al := (718827/4096000), au := (179919/1024000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨192958653530,193186555233⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177779185664,177779185728⟩ : DyadicInterval 40),(⟨-212174868544,-212174868480⟩ : DyadicInterval 40),(⟨745103756373,745103775702⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177973045824,177973045888⟩ : DyadicInterval 40),(⟨-212451313536,-212451313472⟩ : DyadicInterval 40),(⟨745063318036,745063337366⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177697107136,177697107200⟩ : DyadicInterval 40),(⟨-212057859904,-212057859840⟩ : DyadicInterval 40),(⟨745120860705,745120880035⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177931966080,177931966144⟩ : DyadicInterval 40),(⟨-212392723904,-212392723840⟩ : DyadicInterval 40),(⟨745071891764,745071911094⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨24670234,49402483⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24669952,24670016⟩ : DyadicInterval 40),(⟨-24670528,-24670464⟩ : DyadicInterval 40),(⟨762123383286,762123402615⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨49401344,49401408⟩ : DyadicInterval 40),(⟨-49403648,-49403584⟩ : DyadicInterval 40),(⟨762123382484,762123401813⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2240,-512⟩ : DyadicInterval 40),(⟨762123383872,762123404000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨192910409138,193162415474⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177738143104,177738143168⟩ : DyadicInterval 40),(⟨-212116356928,-212116356864⟩ : DyadicInterval 40),(⟨745112310490,745112329819⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177952513408,177952513472⟩ : DyadicInterval 40),(⟨-212422028736,-212422028672⟩ : DyadicInterval 40),(⟨745067603673,745067623003⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34469515264,-34378213696⟩ : DyadicInterval 40),(⟨779312490464,779358160512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨177779185664,177973045888⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-212451313536,-212174868480⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e682_ok : ecellOkT e682 = true := by decide +kernel
theorem e682_pos {a z : ℝ} (ha1 : ((718827/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((179919/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e682 e682_ok ha1 ha2 hz1 hz2 hz

-- box ['358989/2048000', '718827/4096000', '3999/4000', '1']  interval_lower 28949569/549755813888
noncomputable def e683 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1292242379603,0,true,177585291328,177585291392⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨906780875949,0,false,-211898492992,-211898492928⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1292470281307,0,true,177779185664,177779185728⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨906552974245,0,false,-212174868544,-212174868480⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1292194196915,0,true,177544294080,177544294144⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨906829058637,0,false,-211840070912,-211840070848⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536298809,0,true,24670720,24670784⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486956743,0,false,-24671360,-24671296⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627222,0,false,-576,-512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1292218283330,0,true,177564788672,177564788736⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨906804972222,0,false,-211869275584,-211869275520⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1292470289795,0,true,177779192896,177779192960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨906552965757,0,false,-212174878848,-212174878784⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1065648370391,0,false,-34395685888,-34395685824⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1065736764322,0,false,-34304486848,-34304486784⟩
    { al := (358989/2048000), au := (718827/4096000), zl := (3999/4000), zu := 1,
      A := ⟨192730751827,192958653531⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177585291328,177585291392⟩ : DyadicInterval 40),(⟨-211898492992,-211898492928⟩ : DyadicInterval 40),(⟨745144145943,745144165273⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177779185664,177779185728⟩ : DyadicInterval 40),(⟨-212174868544,-212174868480⟩ : DyadicInterval 40),(⟨745103756373,745103775702⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177544294080,177544294144⟩ : DyadicInterval 40),(⟨-211840070912,-211840070848⟩ : DyadicInterval 40),(⟨745152678797,745152698126⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177779185664,177779185728⟩ : DyadicInterval 40),(⟨-212174868544,-212174868480⟩ : DyadicInterval 40),(⟨745103756373,745103775702⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,24671033⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24670720,24670784⟩ : DyadicInterval 40),(⟨-24671360,-24671296⟩ : DyadicInterval 40),(⟨762123383318,762123402647⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,0⟩ : DyadicInterval 40),(⟨762123383616,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨192706655554,192958662019⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177564788672,177564788736⟩ : DyadicInterval 40),(⟨-211869275584,-211869275520⟩ : DyadicInterval 40),(⟨745148413531,745148432860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177779192896,177779192960⟩ : DyadicInterval 40),(⟨-212174878848,-212174878784⟩ : DyadicInterval 40),(⟨745103754864,745103774194⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34395685888,-34304486784⟩ : DyadicInterval 40),(⟨779275627008,779321245824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨177585291328,177779185728⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-212174868544,-211898492928⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e683_ok : ecellOkT e683 = true := by decide +kernel
theorem e683_pos {a z : ℝ} (ha1 : ((358989/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((718827/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e683 e683_ok ha1 ha2 hz1 hz2 hz

-- box ['718827/4096000', '179919/1024000', '3999/4000', '1']  interval_lower 30348491/549755813888
noncomputable def e684 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1292470281306,0,true,177779185664,177779185728⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨906552974246,0,false,-212174868544,-212174868480⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1292698183009,0,true,177973045824,177973045888⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨906325072543,0,false,-212451313536,-212451313472⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1292422041642,0,true,177738147136,177738147200⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨906601213910,0,false,-212116362688,-212116362624⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536329288,0,true,24701184,24701248⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486926264,0,false,-24701824,-24701760⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627221,0,false,-576,-512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1292446156537,0,true,177758662400,177758662464⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨906577099015,0,false,-212145609216,-212145609152⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1292698191504,0,true,177973053056,177973053120⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨906325064048,0,false,-212451323904,-212451323840⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1065568331987,0,false,-34478270784,-34478270720⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1065656840389,0,false,-34386946816,-34386946752⟩
    { al := (718827/4096000), au := (179919/1024000), zl := (3999/4000), zu := 1,
      A := ⟨192958653530,193186555233⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177779185664,177779185728⟩ : DyadicInterval 40),(⟨-212174868544,-212174868480⟩ : DyadicInterval 40),(⟨745103756373,745103775702⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177973045824,177973045888⟩ : DyadicInterval 40),(⟨-212451313536,-212451313472⟩ : DyadicInterval 40),(⟨745063318036,745063337366⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177738147136,177738147200⟩ : DyadicInterval 40),(⟨-212116362688,-212116362624⟩ : DyadicInterval 40),(⟨745112309657,745112328986⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177973045824,177973045888⟩ : DyadicInterval 40),(⟨-212451313536,-212451313472⟩ : DyadicInterval 40),(⟨745063318036,745063337366⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,24701512⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24701184,24701248⟩ : DyadicInterval 40),(⟨-24701824,-24701760⟩ : DyadicInterval 40),(⟨762123383317,762123402646⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,0⟩ : DyadicInterval 40),(⟨762123383616,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨192934528761,193186563728⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177758662400,177758662464⟩ : DyadicInterval 40),(⟨-212145609216,-212145609152⟩ : DyadicInterval 40),(⟨745108034148,745108053478⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177973053056,177973053120⟩ : DyadicInterval 40),(⟨-212451323904,-212451323840⟩ : DyadicInterval 40),(⟨745063316550,745063335879⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34478270784,-34386946752⟩ : DyadicInterval 40),(⟨779316856992,779362538272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨177779185664,177973045888⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-212451313536,-212174868480⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e684_ok : ecellOkT e684 = true := by decide +kernel
theorem e684_pos {a z : ℝ} (ha1 : ((718827/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((179919/1024000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e684 e684_ok ha1 ha2 hz1 hz2 hz

-- box ['179919/1024000', '28821/163840', '999/1000', '3997/4000']  interval_lower 65164805/1099511627776
noncomputable def e685 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1292698183008,0,true,177973045824,177973045888⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨906325072544,0,false,-212451313536,-212451313472⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1292926084711,0,true,178166871808,178166871872⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨906097170841,0,false,-212727828160,-212727828096⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1292504996452,0,true,177808717632,177808717696⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨906518259100,0,false,-212216973568,-212216973504⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1292781023869,0,true,178043504320,178043504384⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨906242231683,0,false,-212551816832,-212551816768⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585729577,0,true,74099264,74099328⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437525975,0,false,-74104320,-74104256⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099610553277,0,true,98921024,98921088⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099412702275,0,false,-98929984,-98929920⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618875,0,false,-8960,-8896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622782,0,false,-5056,-4992⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1292601585811,0,true,177890881472,177890881536⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨906421669741,0,false,-212334132544,-212334132480⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1292853563395,0,true,178105197504,178105197568⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨906169692157,0,false,-212639830016,-212639829952⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1065513711678,0,false,-34534632448,-34534632384⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1065602271157,0,false,-34443251072,-34443251008⟩
    { al := (179919/1024000), au := (28821/163840), zl := (999/1000), zu := (3997/4000),
      A := ⟨193186555232,193414456935⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177973045824,177973045888⟩ : DyadicInterval 40),(⟨-212451313536,-212451313472⟩ : DyadicInterval 40),(⟨745063318036,745063337366⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178166871808,178166871872⟩ : DyadicInterval 40),(⟨-212727828160,-212727828096⟩ : DyadicInterval 40),(⟨745022831003,745022850332⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177808717632,177808717696⟩ : DyadicInterval 40),(⟨-212216973568,-212216973504⟩ : DyadicInterval 40),(⟨745097599750,745097619080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178043504320,178043504384⟩ : DyadicInterval 40),(⟨-212551816832,-212551816768⟩ : DyadicInterval 40),(⟨745048606884,745048626214⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨74101801,98925501⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74099264,74099328⟩ : DyadicInterval 40),(⟨-74104320,-74104256⟩ : DyadicInterval 40),(⟨762123381085,762123400415⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨98921024,98921088⟩ : DyadicInterval 40),(⟨-98929984,-98929920⟩ : DyadicInterval 40),(⟨762123379131,762123398460⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8960,-4992⟩ : DyadicInterval 40),(⟨762123386112,762123407360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨193089958035,193341935619⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177890881472,177890881536⟩ : DyadicInterval 40),(⟨-212334132544,-212334132480⟩ : DyadicInterval 40),(⟨745080463958,745080483287⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178105197504,178105197568⟩ : DyadicInterval 40),(⟨-212639830016,-212639829952⟩ : DyadicInterval 40),(⟨745035719812,745035739141⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34534632448,-34443251008⟩ : DyadicInterval 40),(⟨779345009120,779390719104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨177973045824,178166871872⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-212727828160,-212451313472⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e685_ok : ecellOkT e685 = true := by decide +kernel
theorem e685_pos {a z : ℝ} (ha1 : ((179919/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((28821/163840 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e685 e685_ok ha1 ha2 hz1 hz2 hz

-- box ['28821/163840', '360687/2048000', '999/1000', '3997/4000']  interval_lower 33998585/549755813888
noncomputable def e686 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1292926084710,0,true,178166871808,178166871872⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨906097170842,0,false,-212727828160,-212727828096⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1293153986413,0,true,178360663616,178360663680⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨905869269139,0,false,-213004412224,-213004412160⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1292732670253,0,true,178002378752,178002378816⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨906290585299,0,false,-212493152704,-212493152640⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1293008754645,0,true,178237172544,178237172608⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨906014500907,0,false,-212828149248,-212828149184⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585821022,0,true,74190720,74190784⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437434530,0,false,-74195776,-74195712⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099610675226,0,true,99042944,99043008⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099412580326,0,false,-99051968,-99051904⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618853,0,false,-8960,-8896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622770,0,false,-5056,-4992⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1292829373560,0,true,178084625024,178084625088⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨906193881992,0,false,-212610479360,-212610479296⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1293081379640,0,true,178298927552,178298927616⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨905941875912,0,false,-212916288256,-212916288192⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1065433544479,0,false,-34617360704,-34617360640⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1065522218396,0,false,-34525854336,-34525854272⟩
    { al := (28821/163840), au := (360687/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨193414456934,193642358637⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178166871808,178166871872⟩ : DyadicInterval 40),(⟨-212727828160,-212727828096⟩ : DyadicInterval 40),(⟨745022831003,745022850333⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178360663616,178360663680⟩ : DyadicInterval 40),(⟨-213004412224,-213004412160⟩ : DyadicInterval 40),(⟨744982295182,744982314511⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178002378752,178002378816⟩ : DyadicInterval 40),(⟨-212493152704,-212493152640⟩ : DyadicInterval 40),(⟨745057194476,745057213806⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178237172544,178237172608⟩ : DyadicInterval 40),(⟨-212828149248,-212828149184⟩ : DyadicInterval 40),(⟨745008132501,745008151831⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨74193246,99047450⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74190720,74190784⟩ : DyadicInterval 40),(⟨-74195776,-74195712⟩ : DyadicInterval 40),(⟨762123381073,762123400402⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨99042944,99043008⟩ : DyadicInterval 40),(⟨-99051968,-99051904⟩ : DyadicInterval 40),(⟨762123379141,762123398470⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8960,-4992⟩ : DyadicInterval 40),(⟨762123386112,762123407360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨193317745784,193569751864⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178084625024,178084625088⟩ : DyadicInterval 40),(⟨-212610479360,-212610479296⟩ : DyadicInterval 40),(⟨745040017802,745040037131⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178298927552,178298927616⟩ : DyadicInterval 40),(⟨-212916288256,-212916288192⟩ : DyadicInterval 40),(⟨744995214698,744995234028⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34617360704,-34525854272⟩ : DyadicInterval 40),(⟨779386310752,779432083232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨178166871808,178360663680⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-213004412224,-212727828096⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e686_ok : ecellOkT e686 = true := by decide +kernel
theorem e686_pos {a z : ℝ} (ha1 : ((28821/163840 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((360687/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e686 e686_ok ha1 ha2 hz1 hz2 hz

-- box ['179919/1024000', '28821/163840', '3997/4000', '1999/2000']  interval_lower 64613139/1099511627776
noncomputable def e687 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1292698183008,0,true,177973045824,177973045888⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨906325072544,0,false,-212451313536,-212451313472⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1292926084711,0,true,178166871808,178166871872⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨906097170841,0,false,-212727828160,-212727828096⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1292553293091,0,true,177849801984,177849802048⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨906469962461,0,false,-212275553856,-212275553792⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1292829377483,0,true,178084628352,178084628416⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨906193878069,0,false,-212610484160,-212610484096⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099561029174,0,true,49400256,49400320⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099462226378,0,false,-49402560,-49402496⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585822394,0,true,74192064,74192128⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437433158,0,false,-74197184,-74197120⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622769,0,false,-5056,-4992⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625557,0,false,-2240,-2176⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1292625733657,0,true,177911421888,177911421952⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨906397521895,0,false,-212363424896,-212363424832⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1292877739860,0,true,178125758272,178125758336⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨906145515692,0,false,-212669165184,-212669165120⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1065505208600,0,false,-34543406912,-34543406848⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1065593789212,0,false,-34452002944,-34452002880⟩
    { al := (179919/1024000), au := (28821/163840), zl := (3997/4000), zu := (1999/2000),
      A := ⟨193186555232,193414456935⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177973045824,177973045888⟩ : DyadicInterval 40),(⟨-212451313536,-212451313472⟩ : DyadicInterval 40),(⟨745063318036,745063337366⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178166871808,178166871872⟩ : DyadicInterval 40),(⟨-212727828160,-212727828096⟩ : DyadicInterval 40),(⟨745022831003,745022850332⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177849801984,177849802048⟩ : DyadicInterval 40),(⟨-212275553856,-212275553792⟩ : DyadicInterval 40),(⟨745089032596,745089051925⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178084628352,178084628416⟩ : DyadicInterval 40),(⟨-212610484160,-212610484096⟩ : DyadicInterval 40),(⟨745040017126,745040036455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨49401398,74194618⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨49400256,49400320⟩ : DyadicInterval 40),(⟨-49402560,-49402496⟩ : DyadicInterval 40),(⟨762123382484,762123401813⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74192064,74192128⟩ : DyadicInterval 40),(⟨-74197184,-74197120⟩ : DyadicInterval 40),(⟨762123381105,762123400434⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5056,-2176⟩ : DyadicInterval 40),(⟨762123384704,762123405408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨193114105881,193366112084⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177911421888,177911421952⟩ : DyadicInterval 40),(⟨-212363424896,-212363424832⟩ : DyadicInterval 40),(⟨745076178579,745076197908⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178125758272,178125758336⟩ : DyadicInterval 40),(⟨-212669165184,-212669165120⟩ : DyadicInterval 40),(⟨745031423604,745031442933⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34543406912,-34452002880⟩ : DyadicInterval 40),(⟨779349385056,779395106336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨177973045824,178166871872⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-212727828160,-212451313472⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e687_ok : ecellOkT e687 = true := by decide +kernel
theorem e687_pos {a z : ℝ} (ha1 : ((179919/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((28821/163840 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e687 e687_ok ha1 ha2 hz1 hz2 hz

-- box ['28821/163840', '360687/2048000', '3997/4000', '1999/2000']  interval_lower 67443339/1099511627776
noncomputable def e688 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1292926084710,0,true,178166871808,178166871872⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨906097170842,0,false,-212727828160,-212727828096⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1293153986413,0,true,178360663616,178360663680⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨905869269139,0,false,-213004412224,-213004412160⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1292781023867,0,true,178043504320,178043504384⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨906242231685,0,false,-212551816832,-212551816768⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1293057165234,0,true,178278337728,178278337792⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨905966090318,0,false,-212886900480,-212886900416⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099561090140,0,true,49461248,49461312⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099462165412,0,false,-49463488,-49463424⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585913857,0,true,74283520,74283584⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437341695,0,false,-74288640,-74288576⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622757,0,false,-5056,-4992⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625551,0,false,-2240,-2176⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1292853549892,0,true,178105186048,178105186112⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨906169705660,0,false,-212639813632,-212639813568⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1293105584588,0,true,178319508928,178319508992⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨905917670964,0,false,-212945665408,-212945665344⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1065425021352,0,false,-34626156480,-34626156416⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1065513716428,0,false,-34534627584,-34534627520⟩
    { al := (28821/163840), au := (360687/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨193414456934,193642358637⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178166871808,178166871872⟩ : DyadicInterval 40),(⟨-212727828160,-212727828096⟩ : DyadicInterval 40),(⟨745022831003,745022850333⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178360663616,178360663680⟩ : DyadicInterval 40),(⟨-213004412224,-213004412160⟩ : DyadicInterval 40),(⟨744982295182,744982314511⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178043504320,178043504384⟩ : DyadicInterval 40),(⟨-212551816832,-212551816768⟩ : DyadicInterval 40),(⟨745048606885,745048626214⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178278337728,178278337792⟩ : DyadicInterval 40),(⟨-212886900480,-212886900416⟩ : DyadicInterval 40),(⟨744999522308,744999541638⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨49462364,74286081⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨49461248,49461312⟩ : DyadicInterval 40),(⟨-49463488,-49463424⟩ : DyadicInterval 40),(⟨762123382446,762123401775⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74283520,74283584⟩ : DyadicInterval 40),(⟨-74288640,-74288576⟩ : DyadicInterval 40),(⟨762123381092,762123400422⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5056,-2176⟩ : DyadicInterval 40),(⟨762123384704,762123405408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨193341922116,193593956812⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178105186048,178105186112⟩ : DyadicInterval 40),(⟨-212639813632,-212639813568⟩ : DyadicInterval 40),(⟨745035722195,745035741524⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178319508928,178319508992⟩ : DyadicInterval 40),(⟨-212945665408,-212945665344⟩ : DyadicInterval 40),(⟨744990908262,744990927591⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34626156480,-34534627520⟩ : DyadicInterval 40),(⟨779390697376,779436481120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨178166871808,178360663680⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-213004412224,-212727828096⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e688_ok : ecellOkT e688 = true := by decide +kernel
theorem e688_pos {a z : ℝ} (ha1 : ((28821/163840 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((360687/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e688 e688_ok ha1 ha2 hz1 hz2 hz

-- box ['360687/2048000', '722223/4096000', '999/1000', '3997/4000']  interval_lower 35421651/549755813888
noncomputable def e689 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1293153986412,0,true,178360663616,178360663680⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨905869269140,0,false,-213004412224,-213004412160⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1293381888115,0,true,178554421248,178554421312⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨905641367437,0,false,-213281065984,-213281065920⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1292960344053,0,true,178196005760,178196005824⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨906062911499,0,false,-212769401216,-212769401152⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1293236485420,0,true,178430806656,178430806720⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨905786770132,0,false,-213104551168,-213104551104⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585912482,0,true,74282176,74282240⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437343070,0,false,-74287232,-74287168⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099610797195,0,true,99164928,99164992⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099412458357,0,false,-99173952,-99173888⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618831,0,false,-8960,-8896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622758,0,false,-5056,-4992⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1293057161314,0,true,178278334400,178278334464⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨905966094238,0,false,-212886895680,-212886895616⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1293309195875,0,true,178492623424,178492623488⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨905714059677,0,false,-213192816064,-213192816000⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1065353282877,0,false,-34700192640,-34700192576⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1065442071251,0,false,-34608561216,-34608561152⟩
    { al := (360687/2048000), au := (722223/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨193642358636,193870260339⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178360663616,178360663680⟩ : DyadicInterval 40),(⟨-213004412224,-213004412160⟩ : DyadicInterval 40),(⟨744982295182,744982314512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178554421248,178554421312⟩ : DyadicInterval 40),(⟨-213281065984,-213281065920⟩ : DyadicInterval 40),(⟨744941710669,744941729998⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178196005760,178196005824⟩ : DyadicInterval 40),(⟨-212769401216,-212769401152⟩ : DyadicInterval 40),(⟨745016740555,745016759885⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178430806656,178430806720⟩ : DyadicInterval 40),(⟨-213104551168,-213104551104⟩ : DyadicInterval 40),(⟨744967609463,744967628792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨74284706,99169419⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74282176,74282240⟩ : DyadicInterval 40),(⟨-74287232,-74287168⟩ : DyadicInterval 40),(⟨762123381061,762123400390⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨99164928,99164992⟩ : DyadicInterval 40),(⟨-99173952,-99173888⟩ : DyadicInterval 40),(⟨762123379119,762123398448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8960,-4992⟩ : DyadicInterval 40),(⟨762123386112,762123407360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨193545533538,193797568099⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178278334400,178278334464⟩ : DyadicInterval 40),(⟨-212886895680,-212886895616⟩ : DyadicInterval 40),(⟨744999522985,744999542315⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178492623424,178492623488⟩ : DyadicInterval 40),(⟨-213192816064,-213192816000⟩ : DyadicInterval 40),(⟨744954660918,744954680248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34700192640,-34608561152⟩ : DyadicInterval 40),(⟨779427664192,779473499200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨178360663616,178554421312⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-213281065984,-213004412160⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e689_ok : ecellOkT e689 = true := by decide +kernel
theorem e689_pos {a z : ℝ} (ha1 : ((360687/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((722223/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e689 e689_ok ha1 ha2 hz1 hz2 hz

-- box ['722223/4096000', '5649/32000', '999/1000', '3997/4000']  interval_lower 36851787/549755813888
noncomputable def e690 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1293381888114,0,true,178554421248,178554421312⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨905641367438,0,false,-213281065984,-213281065920⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1293609789817,0,true,178748144768,178748144832⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨905413465735,0,false,-213557789312,-213557789248⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1293188017853,0,true,178389598656,178389598720⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨905835237699,0,false,-213045719168,-213045719104⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1293464216196,0,true,178624406656,178624406720⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨905559039356,0,false,-213381022528,-213381022464⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586003957,0,true,74373632,74373696⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437251595,0,false,-74378752,-74378688⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099610919184,0,true,99286912,99286976⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099412336368,0,false,-99295936,-99295872⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618809,0,false,-9024,-8960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622745,0,false,-5056,-4992⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1293284949058,0,true,178472009728,178472009792⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨905738306494,0,false,-213163381504,-213163381440⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1293537012118,0,true,178686285184,178686285248⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨905486243434,0,false,-213469413440,-213469413376⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1065272926867,0,false,-34783128192,-34783128128⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1065361829728,0,false,-34691371776,-34691371712⟩
    { al := (722223/4096000), au := (5649/32000), zl := (999/1000), zu := (3997/4000),
      A := ⟨193870260338,194098162041⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178554421248,178554421312⟩ : DyadicInterval 40),(⟨-213281065984,-213281065920⟩ : DyadicInterval 40),(⟨744941710669,744941729998⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178748144768,178748144832⟩ : DyadicInterval 40),(⟨-213557789312,-213557789248⟩ : DyadicInterval 40),(⟨744901077360,744901096690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178389598656,178389598720⟩ : DyadicInterval 40),(⟨-213045719168,-213045719104⟩ : DyadicInterval 40),(⟨744976238003,744976257332⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178624406656,178624406720⟩ : DyadicInterval 40),(⟨-213381022528,-213381022464⟩ : DyadicInterval 40),(⟨744927037730,744927057059⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨74376181,99291408⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74373632,74373696⟩ : DyadicInterval 40),(⟨-74378752,-74378688⟩ : DyadicInterval 40),(⟨762123381080,762123400410⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨99286912,99286976⟩ : DyadicInterval 40),(⟨-99295936,-99295872⟩ : DyadicInterval 40),(⟨762123379097,762123398426⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9024,-4992⟩ : DyadicInterval 40),(⟨762123386112,762123407392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨193773321282,194025384342⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178472009728,178472009792⟩ : DyadicInterval 40),(⟨-213163381504,-213163381440⟩ : DyadicInterval 40),(⟨744958979426,744958998755⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178686285184,178686285248⟩ : DyadicInterval 40),(⟨-213469413440,-213469413376⟩ : DyadicInterval 40),(⟨744914058418,744914077748⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34783128192,-34691371712⟩ : DyadicInterval 40),(⟨779469069472,779514966976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨178554421248,178748144832⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-213557789312,-213281065920⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e690_ok : ecellOkT e690 = true := by decide +kernel
theorem e690_pos {a z : ℝ} (ha1 : ((722223/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((5649/32000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e690 e690_ok ha1 ha2 hz1 hz2 hz

-- box ['360687/2048000', '722223/4096000', '3997/4000', '1999/2000']  interval_lower 70287035/1099511627776
noncomputable def e691 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1293153986412,0,true,178360663616,178360663680⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨905869269140,0,false,-213004412224,-213004412160⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1293381888115,0,true,178554421248,178554421312⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨905641367437,0,false,-213281065984,-213281065920⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1293008754642,0,true,178237172544,178237172608⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨906014500910,0,false,-212828149248,-212828149184⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1293284952985,0,true,178472013056,178472013120⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨905738302567,0,false,-213163386240,-213163386176⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099561151114,0,true,49522176,49522240⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099462104438,0,false,-49524480,-49524416⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586005336,0,true,74375040,74375104⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437250216,0,false,-74380096,-74380032⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622744,0,false,-5056,-4992⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625546,0,false,-2240,-2176⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1293081366132,0,true,178298916032,178298916096⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨905941889420,0,false,-212916271872,-212916271808⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1293333429316,0,true,178513225408,178513225472⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨905689826236,0,false,-213222235200,-213222235136⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1065344739674,0,false,-34709009792,-34709009728⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1065433549236,0,false,-34617355776,-34617355712⟩
    { al := (360687/2048000), au := (722223/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨193642358636,193870260339⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178360663616,178360663680⟩ : DyadicInterval 40),(⟨-213004412224,-213004412160⟩ : DyadicInterval 40),(⟨744982295182,744982314512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178554421248,178554421312⟩ : DyadicInterval 40),(⟨-213281065984,-213281065920⟩ : DyadicInterval 40),(⟨744941710669,744941729998⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178237172544,178237172608⟩ : DyadicInterval 40),(⟨-212828149248,-212828149184⟩ : DyadicInterval 40),(⟨745008132502,745008151832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178472013056,178472013120⟩ : DyadicInterval 40),(⟨-213163386240,-213163386176⟩ : DyadicInterval 40),(⟨744958978720,744958998049⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨49523338,74377560⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨49522176,49522240⟩ : DyadicInterval 40),(⟨-49524480,-49524416⟩ : DyadicInterval 40),(⟨762123382473,762123401802⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74375040,74375104⟩ : DyadicInterval 40),(⟨-74380096,-74380032⟩ : DyadicInterval 40),(⟨762123381048,762123400377⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5056,-2176⟩ : DyadicInterval 40),(⟨762123384704,762123405408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨193569738356,193821801540⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178298916032,178298916096⟩ : DyadicInterval 40),(⟨-212916271872,-212916271808⟩ : DyadicInterval 40),(⟨744995217126,744995236455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178513225408,178513225472⟩ : DyadicInterval 40),(⟨-213222235200,-213222235136⟩ : DyadicInterval 40),(⟨744950344225,744950363554⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34709009792,-34617355712⟩ : DyadicInterval 40),(⟨779432061472,779477907776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨178360663616,178554421312⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-213281065984,-213004412160⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e691_ok : ecellOkT e691 = true := by decide +kernel
theorem e691_pos {a z : ℝ} (ha1 : ((360687/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((722223/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e691 e691_ok ha1 ha2 hz1 hz2 hz

-- box ['722223/4096000', '5649/32000', '3997/4000', '1999/2000']  interval_lower 9143145/137438953472
noncomputable def e692 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1293381888114,0,true,178554421248,178554421312⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨905641367438,0,false,-213281065984,-213281065920⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1293609789817,0,true,178748144768,178748144832⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨905413465735,0,false,-213557789312,-213557789248⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1293236485418,0,true,178430806592,178430806656⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨905786770134,0,false,-213104551168,-213104551104⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1293512740737,0,true,178665654208,178665654272⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨905510514815,0,false,-213439941632,-213439941568⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099561212099,0,true,49583168,49583232⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099462043453,0,false,-49585472,-49585408⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586096828,0,true,74466496,74466560⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437158724,0,false,-74471616,-74471552⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622732,0,false,-5056,-4992⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625540,0,false,-2240,-2176⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1293309182357,0,true,178492611904,178492611968⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨905714073195,0,false,-213192799680,-213192799616⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1293561274041,0,true,178706907712,178706907776⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨905461981511,0,false,-213498874560,-213498874496⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1065264363568,0,false,-34791966784,-34791966720⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1065353287644,0,false,-34700187712,-34700187648⟩
    { al := (722223/4096000), au := (5649/32000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨193870260338,194098162041⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178554421248,178554421312⟩ : DyadicInterval 40),(⟨-213281065984,-213281065920⟩ : DyadicInterval 40),(⟨744941710669,744941729998⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178748144768,178748144832⟩ : DyadicInterval 40),(⟨-213557789312,-213557789248⟩ : DyadicInterval 40),(⟨744901077360,744901096690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178430806592,178430806656⟩ : DyadicInterval 40),(⟨-213104551168,-213104551104⟩ : DyadicInterval 40),(⟨744967609501,744967628830⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178665654208,178665654272⟩ : DyadicInterval 40),(⟨-213439941632,-213439941568⟩ : DyadicInterval 40),(⟨744918386503,744918405833⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨49584323,74469052⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨49583168,49583232⟩ : DyadicInterval 40),(⟨-49585472,-49585408⟩ : DyadicInterval 40),(⟨762123382467,762123401796⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74466496,74466560⟩ : DyadicInterval 40),(⟨-74471616,-74471552⟩ : DyadicInterval 40),(⟨762123381068,762123400397⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5056,-2176⟩ : DyadicInterval 40),(⟨762123384704,762123405408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨193797554581,194049646265⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178492611904,178492611968⟩ : DyadicInterval 40),(⟨-213192799680,-213192799616⟩ : DyadicInterval 40),(⟨744954663353,744954682683⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178706907712,178706907776⟩ : DyadicInterval 40),(⟨-213498874560,-213498874496⟩ : DyadicInterval 40),(⟨744909731483,744909750813⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34791966784,-34700187648⟩ : DyadicInterval 40),(⟨779473477440,779519386272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨178554421248,178748144832⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-213557789312,-213281065920⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e692_ok : ecellOkT e692 = true := by decide +kernel
theorem e692_pos {a z : ℝ} (ha1 : ((722223/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((5649/32000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e692 e692_ok ha1 ha2 hz1 hz2 hz

-- box ['179919/1024000', '28821/163840', '1999/2000', '3999/4000']  interval_lower 32030421/549755813888
noncomputable def e693 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1292698183008,0,true,177973045824,177973045888⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨906325072544,0,false,-212451313536,-212451313472⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1292926084711,0,true,178166871808,178166871872⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨906097170841,0,false,-212727828160,-212727828096⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1292601589730,0,true,177890884800,177890884864⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨906421665822,0,false,-212334137344,-212334137280⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1292877731097,0,true,178125750848,178125750912⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨906145524455,0,false,-212669154560,-212669154496⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536328489,0,true,24700416,24700480⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486927063,0,false,-24700992,-24700928⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099561091226,0,true,49462336,49462400⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099462164326,0,false,-49464576,-49464512⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625550,0,false,-2240,-2176⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627222,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1292649881636,0,true,177931962048,177931962112⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨906373373916,0,false,-212392718144,-212392718080⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1292901916464,0,true,178146318784,178146318848⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨906121339088,0,false,-212698501376,-212698501312⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1065496704409,0,false,-34552182528,-34552182464⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1065585306161,0,false,-34460756032,-34460755968⟩
    { al := (179919/1024000), au := (28821/163840), zl := (1999/2000), zu := (3999/4000),
      A := ⟨193186555232,193414456935⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177973045824,177973045888⟩ : DyadicInterval 40),(⟨-212451313536,-212451313472⟩ : DyadicInterval 40),(⟨745063318036,745063337366⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178166871808,178166871872⟩ : DyadicInterval 40),(⟨-212727828160,-212727828096⟩ : DyadicInterval 40),(⟨745022831003,745022850332⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177890884800,177890884864⟩ : DyadicInterval 40),(⟨-212334137344,-212334137280⟩ : DyadicInterval 40),(⟨745080463285,745080482614⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178125750848,178125750912⟩ : DyadicInterval 40),(⟨-212669154560,-212669154496⟩ : DyadicInterval 40),(⟨745031425148,745031444477⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨24700713,49463450⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24700416,24700480⟩ : DyadicInterval 40),(⟨-24700992,-24700928⟩ : DyadicInterval 40),(⟨762123383285,762123402614⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨49462336,49462400⟩ : DyadicInterval 40),(⟨-49464576,-49464512⟩ : DyadicInterval 40),(⟨762123382446,762123401775⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2240,-512⟩ : DyadicInterval 40),(⟨762123383872,762123404000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨193138253860,193390288688⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177931962048,177931962112⟩ : DyadicInterval 40),(⟨-212392718144,-212392718080⟩ : DyadicInterval 40),(⟨745071892601,745071911931⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178146318784,178146318848⟩ : DyadicInterval 40),(⟨-212698501376,-212698501312⟩ : DyadicInterval 40),(⟨745027126846,745027146175⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34552182528,-34460755968⟩ : DyadicInterval 40),(⟨779353761600,779399494144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨177973045824,178166871872⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-212727828160,-212451313472⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e693_ok : ecellOkT e693 = true := by decide +kernel
theorem e693_pos {a z : ℝ} (ha1 : ((179919/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((28821/163840 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e693 e693_ok ha1 ha2 hz1 hz2 hz

-- box ['28821/163840', '360687/2048000', '1999/2000', '3999/4000']  interval_lower 66888931/1099511627776
noncomputable def e694 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1292926084710,0,true,178166871808,178166871872⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨906097170842,0,false,-212727828160,-212727828096⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1293153986413,0,true,178360663616,178360663680⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨905869269139,0,false,-213004412224,-213004412160⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1292829377481,0,true,178084628352,178084628416⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨906193878071,0,false,-212610484160,-212610484096⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1293105575824,0,true,178319501440,178319501504⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨905917679728,0,false,-212945654784,-212945654720⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536358972,0,true,24730880,24730944⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486896580,0,false,-24731520,-24731456⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099561152202,0,true,49523264,49523328⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099462103350,0,false,-49525568,-49525504⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625545,0,false,-2240,-2176⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627220,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1292877726356,0,true,178125746816,178125746880⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨906145529196,0,false,-212669148800,-212669148736⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1293129789680,0,true,178340089984,178340090048⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨905893465872,0,false,-212975043520,-212975043456⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1065416497108,0,false,-34634953472,-34634953408⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1065505213351,0,false,-34543401984,-34543401920⟩
    { al := (28821/163840), au := (360687/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨193414456934,193642358637⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178166871808,178166871872⟩ : DyadicInterval 40),(⟨-212727828160,-212727828096⟩ : DyadicInterval 40),(⟨745022831003,745022850333⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178360663616,178360663680⟩ : DyadicInterval 40),(⟨-213004412224,-213004412160⟩ : DyadicInterval 40),(⟨744982295182,744982314511⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178084628352,178084628416⟩ : DyadicInterval 40),(⟨-212610484160,-212610484096⟩ : DyadicInterval 40),(⟨745040017126,745040036456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178319501440,178319501504⟩ : DyadicInterval 40),(⟨-212945654784,-212945654720⟩ : DyadicInterval 40),(⟨744990909847,744990929177⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨24731196,49524426⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24730880,24730944⟩ : DyadicInterval 40),(⟨-24731520,-24731456⟩ : DyadicInterval 40),(⟨762123383315,762123402644⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨49523264,49523328⟩ : DyadicInterval 40),(⟨-49525568,-49525504⟩ : DyadicInterval 40),(⟨762123382473,762123401802⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2240,-512⟩ : DyadicInterval 40),(⟨762123383872,762123404000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨193366098580,193618161904⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178125746816,178125746880⟩ : DyadicInterval 40),(⟨-212669148800,-212669148736⟩ : DyadicInterval 40),(⟨745031425987,745031445317⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178340089984,178340090048⟩ : DyadicInterval 40),(⟨-212975043520,-212975043456⟩ : DyadicInterval 40),(⟨744986601283,744986620612⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34634953472,-34543401920⟩ : DyadicInterval 40),(⟨779395084576,779440879616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨178166871808,178360663680⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-213004412224,-212727828096⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e694_ok : ecellOkT e694 = true := by decide +kernel
theorem e694_pos {a z : ℝ} (ha1 : ((28821/163840 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((360687/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e694 e694_ok ha1 ha2 hz1 hz2 hz

-- box ['179919/1024000', '28821/163840', '3999/4000', '1']  interval_lower 63508567/1099511627776
noncomputable def e695 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1292698183008,0,true,177973045824,177973045888⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨906325072544,0,false,-212451313536,-212451313472⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1292926084711,0,true,178166871808,178166871872⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨906097170841,0,false,-212727828160,-212727828096⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1292649886369,0,true,177931966080,177931966144⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨906373369183,0,false,-212392723904,-212392723840⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536359773,0,true,24731712,24731776⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486895779,0,false,-24732288,-24732224⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627219,0,false,-576,-512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1292674029751,0,true,177952501952,177952502016⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨906349225801,0,false,-212422012352,-212422012288⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1292926093202,0,true,178166879040,178166879104⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨906097162350,0,false,-212727838464,-212727838400⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1065488199109,0,false,-34560959360,-34560959296⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1065576822001,0,false,-34469510400,-34469510336⟩
    { al := (179919/1024000), au := (28821/163840), zl := (3999/4000), zu := 1,
      A := ⟨193186555232,193414456935⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177973045824,177973045888⟩ : DyadicInterval 40),(⟨-212451313536,-212451313472⟩ : DyadicInterval 40),(⟨745063318036,745063337366⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178166871808,178166871872⟩ : DyadicInterval 40),(⟨-212727828160,-212727828096⟩ : DyadicInterval 40),(⟨745022831003,745022850332⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177931966080,177931966144⟩ : DyadicInterval 40),(⟨-212392723904,-212392723840⟩ : DyadicInterval 40),(⟨745071891765,745071911095⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178166871808,178166871872⟩ : DyadicInterval 40),(⟨-212727828160,-212727828096⟩ : DyadicInterval 40),(⟨745022831003,745022850332⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,24731997⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24731712,24731776⟩ : DyadicInterval 40),(⟨-24732288,-24732224⟩ : DyadicInterval 40),(⟨762123383283,762123402612⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,0⟩ : DyadicInterval 40),(⟨762123383616,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨193162401975,193414465426⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨177952501952,177952502016⟩ : DyadicInterval 40),(⟨-212422012352,-212422012288⟩ : DyadicInterval 40),(⟨745067606051,745067625380⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178166879040,178166879104⟩ : DyadicInterval 40),(⟨-212727838464,-212727838400⟩ : DyadicInterval 40),(⟨745022829487,745022848816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34560959360,-34469510336⟩ : DyadicInterval 40),(⟨779358138784,779403882560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨177973045824,178166871872⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-212727828160,-212451313472⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e695_ok : ecellOkT e695 = true := by decide +kernel
theorem e695_pos {a z : ℝ} (ha1 : ((179919/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((28821/163840 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e695 e695_ok ha1 ha2 hz1 hz2 hz

-- box ['28821/163840', '360687/2048000', '3999/4000', '1']  interval_lower 16583527/274877906944
noncomputable def e696 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1292926084710,0,true,178166871808,178166871872⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨906097170842,0,false,-212727828160,-212727828096⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1293153986413,0,true,178360663616,178360663680⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨905869269139,0,false,-213004412224,-213004412160⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1292877731095,0,true,178125750848,178125750912⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨906145524457,0,false,-212669154560,-212669154496⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536390261,0,true,24762176,24762240⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486865291,0,false,-24762816,-24762752⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627218,0,false,-576,-512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1292901902961,0,true,178146307328,178146307392⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨906121352591,0,false,-212698484992,-212698484928⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1293153994909,0,true,178360670848,178360670912⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨905869260643,0,false,-213004422592,-213004422528⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1065407971751,0,false,-34643751680,-34643751616⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1065496709161,0,false,-34552177600,-34552177536⟩
    { al := (28821/163840), au := (360687/2048000), zl := (3999/4000), zu := 1,
      A := ⟨193414456934,193642358637⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178166871808,178166871872⟩ : DyadicInterval 40),(⟨-212727828160,-212727828096⟩ : DyadicInterval 40),(⟨745022831003,745022850333⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178360663616,178360663680⟩ : DyadicInterval 40),(⟨-213004412224,-213004412160⟩ : DyadicInterval 40),(⟨744982295182,744982314511⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178125750848,178125750912⟩ : DyadicInterval 40),(⟨-212669154560,-212669154496⟩ : DyadicInterval 40),(⟨745031425148,745031444478⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178360663616,178360663680⟩ : DyadicInterval 40),(⟨-213004412224,-213004412160⟩ : DyadicInterval 40),(⟨744982295182,744982314511⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,24762485⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24762176,24762240⟩ : DyadicInterval 40),(⟨-24762816,-24762752⟩ : DyadicInterval 40),(⟨762123383314,762123402643⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,0⟩ : DyadicInterval 40),(⟨762123383616,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨193390275185,193642367133⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178146307328,178146307392⟩ : DyadicInterval 40),(⟨-212698484992,-212698484928⟩ : DyadicInterval 40),(⟨745027129230,745027148560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178360670848,178360670912⟩ : DyadicInterval 40),(⟨-213004422592,-213004422528⟩ : DyadicInterval 40),(⟨744982293688,744982313018⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34643751680,-34552177536⟩ : DyadicInterval 40),(⟨779399472384,779445278720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨178166871808,178360663680⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-213004412224,-212727828096⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e696_ok : ecellOkT e696 = true := by decide +kernel
theorem e696_pos {a z : ℝ} (ha1 : ((28821/163840 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((360687/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e696 e696_ok ha1 ha2 hz1 hz2 hz

-- box ['360687/2048000', '722223/4096000', '1999/2000', '3999/4000']  interval_lower 34865289/549755813888
noncomputable def e697 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1293153986412,0,true,178360663616,178360663680⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨905869269140,0,false,-213004412224,-213004412160⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1293381888115,0,true,178554421248,178554421312⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨905641367437,0,false,-213281065984,-213281065920⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1293057165232,0,true,178278337728,178278337792⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨905966090320,0,false,-212886900480,-212886900416⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1293333420551,0,true,178513217920,178513217984⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨905689835001,0,false,-213222224576,-213222224512⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536389459,0,true,24761344,24761408⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486866093,0,false,-24761984,-24761920⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099561213189,0,true,49584256,49584320⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099462042363,0,false,-49586560,-49586496⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625539,0,false,-2240,-2176⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627219,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1293105571079,0,true,178319497408,178319497472⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨905917684473,0,false,-212945649024,-212945648960⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1293357662889,0,true,178533827072,178533827136⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨905665592663,0,false,-213251655232,-213251655168⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1065336195356,0,false,-34717828160,-34717828096⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1065425026110,0,false,-34626151552,-34626151488⟩
    { al := (360687/2048000), au := (722223/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨193642358636,193870260339⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178360663616,178360663680⟩ : DyadicInterval 40),(⟨-213004412224,-213004412160⟩ : DyadicInterval 40),(⟨744982295182,744982314512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178554421248,178554421312⟩ : DyadicInterval 40),(⟨-213281065984,-213281065920⟩ : DyadicInterval 40),(⟨744941710669,744941729998⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178278337728,178278337792⟩ : DyadicInterval 40),(⟨-212886900480,-212886900416⟩ : DyadicInterval 40),(⟨744999522309,744999541638⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178513217920,178513217984⟩ : DyadicInterval 40),(⟨-213222224576,-213222224512⟩ : DyadicInterval 40),(⟨744950345815,744950365144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨24761683,49585413⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24761344,24761408⟩ : DyadicInterval 40),(⟨-24761984,-24761920⟩ : DyadicInterval 40),(⟨762123383314,762123402643⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨49584256,49584320⟩ : DyadicInterval 40),(⟨-49586560,-49586496⟩ : DyadicInterval 40),(⟨762123382467,762123401796⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2240,-512⟩ : DyadicInterval 40),(⟨762123383872,762123404000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨193593943303,193846035113⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178319497408,178319497472⟩ : DyadicInterval 40),(⟨-212945649024,-212945648960⟩ : DyadicInterval 40),(⟨744990910690,744990930019⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178533827072,178533827136⟩ : DyadicInterval 40),(⟨-213251655232,-213251655168⟩ : DyadicInterval 40),(⟨744946026963,744946046293⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34717828160,-34626151488⟩ : DyadicInterval 40),(⟨779436459360,779482316960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨178360663616,178554421312⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-213281065984,-213004412160⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e697_ok : ecellOkT e697 = true := by decide +kernel
theorem e697_pos {a z : ℝ} (ha1 : ((360687/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((722223/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e697 e697_ok ha1 ha2 hz1 hz2 hz

-- box ['722223/4096000', '5649/32000', '1999/2000', '3999/4000']  interval_lower 18146577/274877906944
noncomputable def e698 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1293381888114,0,true,178554421248,178554421312⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨905641367438,0,false,-213281065984,-213281065920⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1293609789817,0,true,178748144768,178748144832⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨905413465735,0,false,-213557789312,-213557789248⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1293284952983,0,true,178472013056,178472013120⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨905738302569,0,false,-213163386240,-213163386176⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1293561265277,0,true,178706900288,178706900352⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨905461990275,0,false,-213498863872,-213498863808⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536419952,0,true,24791872,24791936⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486835600,0,false,-24792512,-24792448⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099561274186,0,true,49645248,49645312⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099461981366,0,false,-49647552,-49647488⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625534,0,false,-2304,-2240⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627217,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1293333415801,0,true,178513213888,178513213952⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨905689839751,0,false,-213222218752,-213222218688⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1293585536108,0,true,178727529984,178727530048⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨905437719444,0,false,-213528336576,-213528336512⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1065255799148,0,false,-34800806592,-34800806528⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1065344744440,0,false,-34709004864,-34709004800⟩
    { al := (722223/4096000), au := (5649/32000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨193870260338,194098162041⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178554421248,178554421312⟩ : DyadicInterval 40),(⟨-213281065984,-213281065920⟩ : DyadicInterval 40),(⟨744941710669,744941729998⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178748144768,178748144832⟩ : DyadicInterval 40),(⟨-213557789312,-213557789248⟩ : DyadicInterval 40),(⟨744901077360,744901096690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178472013056,178472013120⟩ : DyadicInterval 40),(⟨-213163386240,-213163386176⟩ : DyadicInterval 40),(⟨744958978720,744958998050⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178706900288,178706900352⟩ : DyadicInterval 40),(⟨-213498863872,-213498863808⟩ : DyadicInterval 40),(⟨744909733013,744909752342⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨24792176,49646410⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24791872,24791936⟩ : DyadicInterval 40),(⟨-24792512,-24792448⟩ : DyadicInterval 40),(⟨762123383312,762123402641⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨49645248,49645312⟩ : DyadicInterval 40),(⟨-49647552,-49647488⟩ : DyadicInterval 40),(⟨762123382462,762123401791⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2304,-512⟩ : DyadicInterval 40),(⟨762123383872,762123404032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨193821788025,194073908332⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178513213888,178513213952⟩ : DyadicInterval 40),(⟨-213222218752,-213222218688⟩ : DyadicInterval 40),(⟨744950346634,744950365963⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178727529984,178727530048⟩ : DyadicInterval 40),(⟨-213528336576,-213528336512⟩ : DyadicInterval 40),(⟨744905403937,744905423267⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34800806592,-34709004800⟩ : DyadicInterval 40),(⟨779477886016,779523806176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨178554421248,178748144832⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-213557789312,-213281065920⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e698_ok : ecellOkT e698 = true := by decide +kernel
theorem e698_pos {a z : ℝ} (ha1 : ((722223/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((5649/32000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e698 e698_ok ha1 ha2 hz1 hz2 hz

-- box ['360687/2048000', '722223/4096000', '3999/4000', '1']  interval_lower 34586841/549755813888
noncomputable def e699 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1293153986412,0,true,178360663616,178360663680⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨905869269140,0,false,-213004412224,-213004412160⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1293381888115,0,true,178554421248,178554421312⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨905641367437,0,false,-213281065984,-213281065920⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1293105575822,0,true,178319501440,178319501504⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨905917679730,0,false,-212945654784,-212945654720⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536420755,0,true,24792640,24792704⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486834797,0,false,-24793280,-24793216⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627216,0,false,-576,-512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1293129776171,0,true,178340078528,178340078592⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨905893479381,0,false,-212975027136,-212975027072⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1293381896602,0,true,178554428480,178554428544⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨905641358950,0,false,-213281076288,-213281076224⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1065327649921,0,false,-34726647744,-34726647680⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1065416501867,0,false,-34634948544,-34634948480⟩
    { al := (360687/2048000), au := (722223/4096000), zl := (3999/4000), zu := 1,
      A := ⟨193642358636,193870260339⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178360663616,178360663680⟩ : DyadicInterval 40),(⟨-213004412224,-213004412160⟩ : DyadicInterval 40),(⟨744982295182,744982314512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178554421248,178554421312⟩ : DyadicInterval 40),(⟨-213281065984,-213281065920⟩ : DyadicInterval 40),(⟨744941710669,744941729998⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178319501440,178319501504⟩ : DyadicInterval 40),(⟨-212945654784,-212945654720⟩ : DyadicInterval 40),(⟨744990909848,744990929177⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178554421248,178554421312⟩ : DyadicInterval 40),(⟨-213281065984,-213281065920⟩ : DyadicInterval 40),(⟨744941710669,744941729998⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,24792979⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24792640,24792704⟩ : DyadicInterval 40),(⟨-24793280,-24793216⟩ : DyadicInterval 40),(⟨762123383312,762123402641⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,0⟩ : DyadicInterval 40),(⟨762123383616,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨193618148395,193870268826⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178340078528,178340078592⟩ : DyadicInterval 40),(⟨-212975027136,-212975027072⟩ : DyadicInterval 40),(⟨744986603674,744986623003⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178554428480,178554428544⟩ : DyadicInterval 40),(⟨-213281076288,-213281076224⟩ : DyadicInterval 40),(⟨744941709146,744941728476⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34726647744,-34634948480⟩ : DyadicInterval 40),(⟨779440857856,779486726752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨178360663616,178554421312⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-213281065984,-213004412160⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e699_ok : ecellOkT e699 = true := by decide +kernel
theorem e699_pos {a z : ℝ} (ha1 : ((360687/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((722223/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e699 e699_ok ha1 ha2 hz1 hz2 hz

-- box ['722223/4096000', '5649/32000', '3999/4000', '1']  interval_lower 2250849/34359738368
noncomputable def e700 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1293381888114,0,true,178554421248,178554421312⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨905641367438,0,false,-213281065984,-213281065920⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1293609789817,0,true,178748144768,178748144832⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨905413465735,0,false,-213557789312,-213557789248⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1293333420548,0,true,178513217920,178513217984⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨905689835004,0,false,-213222224512,-213222224448⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536451254,0,true,24823168,24823232⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486804298,0,false,-24823808,-24823744⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627215,0,false,-576,-512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1293357649377,0,true,178533815552,178533815616⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨905665606175,0,false,-213251638848,-213251638784⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1293609798306,0,true,178748152000,178748152064⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨905413457246,0,false,-213557799616,-213557799552⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1065247233611,0,false,-34809647552,-34809647488⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1065336200122,0,false,-34717823232,-34717823168⟩
    { al := (722223/4096000), au := (5649/32000), zl := (3999/4000), zu := 1,
      A := ⟨193870260338,194098162041⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178554421248,178554421312⟩ : DyadicInterval 40),(⟨-213281065984,-213281065920⟩ : DyadicInterval 40),(⟨744941710669,744941729998⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178748144768,178748144832⟩ : DyadicInterval 40),(⟨-213557789312,-213557789248⟩ : DyadicInterval 40),(⟨744901077360,744901096690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178513217920,178513217984⟩ : DyadicInterval 40),(⟨-213222224512,-213222224448⟩ : DyadicInterval 40),(⟨744950345789,744950365118⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178748144768,178748144832⟩ : DyadicInterval 40),(⟨-213557789312,-213557789248⟩ : DyadicInterval 40),(⟨744901077360,744901096690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,24823478⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24823168,24823232⟩ : DyadicInterval 40),(⟨-24823808,-24823744⟩ : DyadicInterval 40),(⟨762123383311,762123402640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,0⟩ : DyadicInterval 40),(⟨762123383616,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨193846021601,194098170530⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178533815552,178533815616⟩ : DyadicInterval 40),(⟨-213251638848,-213251638784⟩ : DyadicInterval 40),(⟨744946029398,744946048728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178748152000,178748152064⟩ : DyadicInterval 40),(⟨-213557799616,-213557799552⟩ : DyadicInterval 40),(⟨744901075834,744901095164⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34809647552,-34717823168⟩ : DyadicInterval 40),(⟨779482295200,779528226656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨178554421248,178748144832⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-213557789312,-213281065920⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e700_ok : ecellOkT e700 = true := by decide +kernel
theorem e700_pos {a z : ℝ} (ha1 : ((722223/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((5649/32000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e700 e700_ok ha1 ha2 hz1 hz2 hz

-- box ['5649/32000', '723921/4096000', '999/1000', '3997/4000']  interval_lower 76577893/1099511627776
noncomputable def e701 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1293609789816,0,true,178748144768,178748144832⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨905413465736,0,false,-213557789312,-213557789248⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1293837691519,0,true,178941834176,178941834240⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨905185564033,0,false,-213834582336,-213834582272⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1293415691653,0,true,178583157504,178583157568⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨905607563899,0,false,-213322106560,-213322106496⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1293691946972,0,true,178817972544,178817972608⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨905331308580,0,false,-213657563456,-213657563392⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586095447,0,true,74465088,74465152⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437160105,0,false,-74470208,-74470144⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099611041192,0,true,99408896,99408960⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099412214360,0,false,-99417920,-99417856⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618787,0,false,-9024,-8960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622733,0,false,-5056,-4992⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1293512736810,0,true,178665650880,178665650944⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨905510518742,0,false,-213439936832,-213439936768⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1293764828356,0,true,178879912832,178879912896⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨905258427196,0,false,-213746080384,-213746080320⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1065192476452,0,false,-34866167488,-34866167424⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1065281493819,0,false,-34774285952,-34774285888⟩
    { al := (5649/32000), au := (723921/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨194098162040,194326063743⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178748144768,178748144832⟩ : DyadicInterval 40),(⟨-213557789312,-213557789248⟩ : DyadicInterval 40),(⟨744901077360,744901096690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178941834176,178941834240⟩ : DyadicInterval 40),(⟨-213834582336,-213834582272⟩ : DyadicInterval 40),(⟨744860395300,744860414630⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178583157504,178583157568⟩ : DyadicInterval 40),(⟨-213322106560,-213322106496⟩ : DyadicInterval 40),(⟨744935686769,744935706099⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178817972544,178817972608⟩ : DyadicInterval 40),(⟨-213657563456,-213657563392⟩ : DyadicInterval 40),(⟨744886417345,744886436675⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨74467671,99413416⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74465088,74465152⟩ : DyadicInterval 40),(⟨-74470208,-74470144⟩ : DyadicInterval 40),(⟨762123381068,762123400397⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨99408896,99408960⟩ : DyadicInterval 40),(⟨-99417920,-99417856⟩ : DyadicInterval 40),(⟨762123379075,762123398404⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9024,-4992⟩ : DyadicInterval 40),(⟨762123386112,762123407392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨194001109034,194253200580⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178665650880,178665650944⟩ : DyadicInterval 40),(⟨-213439936832,-213439936768⟩ : DyadicInterval 40),(⟨744918387184,744918406514⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178879912832,178879912896⟩ : DyadicInterval 40),(⟨-213746080384,-213746080320⟩ : DyadicInterval 40),(⟨744873407191,744873426521⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34866167488,-34774285888⟩ : DyadicInterval 40),(⟨779510526560,779556486624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨178748144768,178941834240⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-213834582336,-213557789248⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e701_ok : ecellOkT e701 = true := by decide +kernel
theorem e701_pos {a z : ℝ} (ha1 : ((5649/32000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((723921/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e701 e701_ok ha1 ha2 hz1 hz2 hz

-- box ['723921/4096000', '72477/409600', '999/1000', '3997/4000']  interval_lower 79466431/1099511627776
noncomputable def e702 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1293837691518,0,true,178941834176,178941834240⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨905185564034,0,false,-213834582336,-213834582272⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1294065593222,0,true,179135489472,179135489536⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨904957662330,0,false,-214111444992,-214111444928⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1293643365454,0,true,178776682240,178776682304⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨905379890098,0,false,-213598563456,-213598563392⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1293919677749,0,true,179011504384,179011504448⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨905103577803,0,false,-213934173952,-213934173888⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586186952,0,true,74556608,74556672⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437068600,0,false,-74561728,-74561664⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099611163221,0,true,99530880,99530944⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099412092331,0,false,-99539968,-99539904⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618765,0,false,-9024,-8960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622721,0,false,-5056,-4992⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1293740524560,0,true,178859257984,178859258048⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨905282730992,0,false,-213716561792,-213716561728⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1293992644601,0,true,179073506432,179073506496⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨905030610951,0,false,-214022816960,-214022816896⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1065111931629,0,false,-34949310528,-34949310464⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1065201063529,0,false,-34857303808,-34857303744⟩
    { al := (723921/4096000), au := (72477/409600), zl := (999/1000), zu := (3997/4000),
      A := ⟨194326063742,194553965446⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178941834176,178941834240⟩ : DyadicInterval 40),(⟨-213834582336,-213834582272⟩ : DyadicInterval 40),(⟨744860395300,744860414630⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179135489472,179135489536⟩ : DyadicInterval 40),(⟨-214111444992,-214111444928⟩ : DyadicInterval 40),(⟨744819664449,744819683779⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178776682240,178776682304⟩ : DyadicInterval 40),(⟨-213598563456,-213598563392⟩ : DyadicInterval 40),(⟨744895086908,744895106238⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179011504384,179011504448⟩ : DyadicInterval 40),(⟨-213934173952,-213934173888⟩ : DyadicInterval 40),(⟨744845748259,744845767589⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨74559176,99535445⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74556608,74556672⟩ : DyadicInterval 40),(⟨-74561728,-74561664⟩ : DyadicInterval 40),(⟨762123381055,762123400385⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨99530880,99530944⟩ : DyadicInterval 40),(⟨-99539968,-99539904⟩ : DyadicInterval 40),(⟨762123379084,762123398414⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9024,-4992⟩ : DyadicInterval 40),(⟨762123386112,762123407392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨194228896784,194481016825⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178859257984,178859258048⟩ : DyadicInterval 40),(⟨-213716561792,-213716561728⟩ : DyadicInterval 40),(⟨744877746228,744877765558⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179073506432,179073506496⟩ : DyadicInterval 40),(⟨-214022816960,-214022816896⟩ : DyadicInterval 40),(⟨744832707211,744832726541⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34949310528,-34857303744⟩ : DyadicInterval 40),(⟨779552035488,779598058144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨178941834176,179135489536⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-214111444992,-213834582272⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e702_ok : ecellOkT e702 = true := by decide +kernel
theorem e702_pos {a z : ℝ} (ha1 : ((723921/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((72477/409600 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e702 e702_ok ha1 ha2 hz1 hz2 hz

-- box ['5649/32000', '723921/4096000', '3997/4000', '1999/2000']  interval_lower 76017307/1099511627776
noncomputable def e703 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1293609789816,0,true,178748144768,178748144832⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨905413465736,0,false,-213557789312,-213557789248⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1293837691519,0,true,178941834176,178941834240⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨905185564033,0,false,-213834582336,-213834582272⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1293464216194,0,true,178624406656,178624406720⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨905559039358,0,false,-213381022528,-213381022464⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1293740528488,0,true,178859261312,178859261376⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨905282727064,0,false,-213716566592,-213716566528⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099561273092,0,true,49644160,49644224⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099461982460,0,false,-49646464,-49646400⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586188336,0,true,74558016,74558080⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437067216,0,false,-74563136,-74563072⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622719,0,false,-5120,-5056⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625535,0,false,-2304,-2240⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1293536998599,0,true,178686273728,178686273792⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨905486256953,0,false,-213469396992,-213469396928⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1293789118769,0,true,178900555968,178900556032⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨905234136783,0,false,-213775583488,-213775583424⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1065183893031,0,false,-34875027520,-34875027456⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1065272931639,0,false,-34783123264,-34783123200⟩
    { al := (5649/32000), au := (723921/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨194098162040,194326063743⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178748144768,178748144832⟩ : DyadicInterval 40),(⟨-213557789312,-213557789248⟩ : DyadicInterval 40),(⟨744901077360,744901096690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178941834176,178941834240⟩ : DyadicInterval 40),(⟨-213834582336,-213834582272⟩ : DyadicInterval 40),(⟨744860395300,744860414630⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178624406656,178624406720⟩ : DyadicInterval 40),(⟨-213381022528,-213381022464⟩ : DyadicInterval 40),(⟨744927037730,744927057060⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178859261312,178859261376⟩ : DyadicInterval 40),(⟨-213716566592,-213716566528⟩ : DyadicInterval 40),(⟨744877745545,744877764875⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨49645316,74560560⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨49644160,49644224⟩ : DyadicInterval 40),(⟨-49646464,-49646400⟩ : DyadicInterval 40),(⟨762123382462,762123401791⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74558016,74558080⟩ : DyadicInterval 40),(⟨-74563136,-74563072⟩ : DyadicInterval 40),(⟨762123381055,762123400385⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5120,-2240⟩ : DyadicInterval 40),(⟨762123384736,762123405440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨194025370823,194277490993⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178686273728,178686273792⟩ : DyadicInterval 40),(⟨-213469396992,-213469396928⟩ : DyadicInterval 40),(⟨744914060795,744914080125⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178900555968,178900556032⟩ : DyadicInterval 40),(⟨-213775583488,-213775583424⟩ : DyadicInterval 40),(⟨744869069950,744869089279⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34875027520,-34783123200⟩ : DyadicInterval 40),(⟨779514945216,779560916640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨178748144768,178941834240⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-213834582336,-213557789248⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e703_ok : ecellOkT e703 = true := by decide +kernel
theorem e703_pos {a z : ℝ} (ha1 : ((5649/32000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((723921/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e703 e703_ok ha1 ha2 hz1 hz2 hz

-- box ['723921/4096000', '72477/409600', '3997/4000', '1999/2000']  interval_lower 78903417/1099511627776
noncomputable def e704 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1293837691518,0,true,178941834176,178941834240⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨905185564034,0,false,-213834582336,-213834582272⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1294065593222,0,true,179135489472,179135489536⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨904957662330,0,false,-214111444992,-214111444928⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1293691946970,0,true,178817972544,178817972608⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨905331308582,0,false,-213657563456,-213657563392⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1293968316240,0,true,179052834304,179052834368⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨905054939312,0,false,-213993261120,-213993261056⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099561334096,0,true,49705152,49705216⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099461921456,0,false,-49707456,-49707392⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586279860,0,true,74649536,74649600⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436975692,0,false,-74654656,-74654592⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622707,0,false,-5120,-5056⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625529,0,false,-2304,-2240⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1293764814832,0,true,178879901376,178879901440⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨905258440720,0,false,-213746063936,-213746063872⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1294016963501,0,true,179094170112,179094170176⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨905006292051,0,false,-214052362112,-214052362048⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1065103328063,0,false,-34958192000,-34958191936⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1065192481232,0,false,-34866162560,-34866162496⟩
    { al := (723921/4096000), au := (72477/409600), zl := (3997/4000), zu := (1999/2000),
      A := ⟨194326063742,194553965446⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178941834176,178941834240⟩ : DyadicInterval 40),(⟨-213834582336,-213834582272⟩ : DyadicInterval 40),(⟨744860395300,744860414630⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179135489472,179135489536⟩ : DyadicInterval 40),(⟨-214111444992,-214111444928⟩ : DyadicInterval 40),(⟨744819664449,744819683779⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178817972544,178817972608⟩ : DyadicInterval 40),(⟨-213657563456,-213657563392⟩ : DyadicInterval 40),(⟨744886417345,744886436675⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179052834304,179052834368⟩ : DyadicInterval 40),(⟨-213993261120,-213993261056⟩ : DyadicInterval 40),(⟨744837055873,744837075203⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨49706320,74652084⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨49705152,49705216⟩ : DyadicInterval 40),(⟨-49707456,-49707392⟩ : DyadicInterval 40),(⟨762123382456,762123401785⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74649536,74649600⟩ : DyadicInterval 40),(⟨-74654656,-74654592⟩ : DyadicInterval 40),(⟨762123381043,762123400372⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5120,-2240⟩ : DyadicInterval 40),(⟨762123384736,762123405440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨194253187056,194505335725⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178879901376,178879901440⟩ : DyadicInterval 40),(⟨-213746063936,-213746063872⟩ : DyadicInterval 40),(⟨744873409575,744873428904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179094170112,179094170176⟩ : DyadicInterval 40),(⟨-214052362112,-214052362048⟩ : DyadicInterval 40),(⟨744828359702,744828379032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34958192000,-34866162496⟩ : DyadicInterval 40),(⟨779556464864,779602498880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨178941834176,179135489536⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-214111444992,-213834582272⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e704_ok : ecellOkT e704 = true := by decide +kernel
theorem e704_pos {a z : ℝ} (ha1 : ((723921/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((72477/409600 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e704 e704_ok ha1 ha2 hz1 hz2 hz

-- box ['72477/409600', '725619/4096000', '999/1000', '3997/4000']  interval_lower 10296115/137438953472
noncomputable def e705 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1294065593221,0,true,179135489472,179135489536⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨904957662331,0,false,-214111444992,-214111444928⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1294293494924,0,true,179329110656,179329110720⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨904729760628,0,false,-214388377472,-214388377408⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1293871039255,0,true,178970172928,178970172992⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨905152216297,0,false,-213875089920,-213875089856⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1294147408524,0,true,179205002176,179205002240⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨904875847028,0,false,-214210854016,-214210853952⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586278471,0,true,74648128,74648192⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436977081,0,false,-74653248,-74653184⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099611285268,0,true,99652928,99652992⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099411970284,0,false,-99662016,-99661952⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618743,0,false,-9088,-9024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622708,0,false,-5120,-5056⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1293968312311,0,true,179052830976,179052831040⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨905054943241,0,false,-213993256320,-213993256256⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1294220460840,0,true,179267065920,179267065984⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨904802794712,0,false,-214299623232,-214299623168⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1065031292402,0,false,-35032557248,-35032557184⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1065120538856,0,false,-34940425344,-34940425280⟩
    { al := (72477/409600), au := (725619/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨194553965445,194781867148⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179135489472,179135489536⟩ : DyadicInterval 40),(⟨-214111444992,-214111444928⟩ : DyadicInterval 40),(⟨744819664449,744819683779⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179329110656,179329110720⟩ : DyadicInterval 40),(⟨-214388377472,-214388377408⟩ : DyadicInterval 40),(⟨744778884877,744778904207⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178970172928,178970172992⟩ : DyadicInterval 40),(⟨-213875089920,-213875089856⟩ : DyadicInterval 40),(⟨744854438398,744854457728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179205002176,179205002240⟩ : DyadicInterval 40),(⟨-214210854016,-214210853952⟩ : DyadicInterval 40),(⟨744805030462,744805049792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨74650695,99657492⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74648128,74648192⟩ : DyadicInterval 40),(⟨-74653248,-74653184⟩ : DyadicInterval 40),(⟨762123381043,762123400372⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨99652928,99652992⟩ : DyadicInterval 40),(⟨-99662016,-99661952⟩ : DyadicInterval 40),(⟨762123379062,762123398392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9088,-5056⟩ : DyadicInterval 40),(⟨762123386144,762123407424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨194456684535,194708833064⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179052830976,179052831040⟩ : DyadicInterval 40),(⟨-213993256320,-213993256256⟩ : DyadicInterval 40),(⟨744837056559,744837075888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179267065920,179267065984⟩ : DyadicInterval 40),(⟨-214299623232,-214299623168⟩ : DyadicInterval 40),(⟨744791958535,744791977865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35032557248,-34940425280⟩ : DyadicInterval 40),(⟨779593596256,779639681504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨179135489472,179329110720⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-214388377472,-214111444928⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e705_ok : ecellOkT e705 = true := by decide +kernel
theorem e705_pos {a z : ℝ} (ha1 : ((72477/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((725619/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e705 e705_ok ha1 ha2 hz1 hz2 hz

-- box ['725619/4096000', '181617/1024000', '999/1000', '3997/4000']  interval_lower 21321453/274877906944
noncomputable def e706 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1294293494923,0,true,179329110656,179329110720⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨904729760629,0,false,-214388377472,-214388377408⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1294521396626,0,true,179522697728,179522697792⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨904501858926,0,false,-214665379648,-214665379584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1294098713055,0,true,179163629632,179163629696⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨904924542497,0,false,-214151685888,-214151685824⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1294375139300,0,true,179398465920,179398465984⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨904648116252,0,false,-214487603776,-214487603712⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586370007,0,true,74739648,74739712⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436885545,0,false,-74744832,-74744768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099611407337,0,true,99774976,99775040⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099411848215,0,false,-99784128,-99784064⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618721,0,false,-9088,-9024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622696,0,false,-5120,-5056⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1294196100063,0,true,179246369920,179246369984⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨904827155489,0,false,-214270020544,-214270020480⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1294448277080,0,true,179460591360,179460591424⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨904574978472,0,false,-214576499200,-214576499136⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1064950558768,0,false,-35115907840,-35115907776⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1065039919800,0,false,-35023650624,-35023650560⟩
    { al := (725619/4096000), au := (181617/1024000), zl := (999/1000), zu := (3997/4000),
      A := ⟨194781867147,195009768850⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179329110656,179329110720⟩ : DyadicInterval 40),(⟨-214388377472,-214388377408⟩ : DyadicInterval 40),(⟨744778884877,744778904207⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179522697728,179522697792⟩ : DyadicInterval 40),(⟨-214665379648,-214665379584⟩ : DyadicInterval 40),(⟨744738056519,744738075848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179163629632,179163629696⟩ : DyadicInterval 40),(⟨-214151685888,-214151685824⟩ : DyadicInterval 40),(⟨744813741164,744813760493⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179398465920,179398465984⟩ : DyadicInterval 40),(⟨-214487603776,-214487603712⟩ : DyadicInterval 40),(⟨744764263995,744764283324⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨74742231,99779561⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74739648,74739712⟩ : DyadicInterval 40),(⟨-74744832,-74744768⟩ : DyadicInterval 40),(⟨762123381063,762123400392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨99774976,99775040⟩ : DyadicInterval 40),(⟨-99784128,-99784064⟩ : DyadicInterval 40),(⟨762123379072,762123398402⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9088,-5056⟩ : DyadicInterval 40),(⟨762123386144,762123407424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨194684472287,194936649304⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179246369920,179246369984⟩ : DyadicInterval 40),(⟨-214270020544,-214270020480⟩ : DyadicInterval 40),(⟨744796318178,744796337508⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179460591360,179460591424⟩ : DyadicInterval 40),(⟨-214576499200,-214576499136⟩ : DyadicInterval 40),(⟨744751161112,744751180441⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35115907840,-35023650560⟩ : DyadicInterval 40),(⟨779635208896,779681356800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨179329110656,179522697792⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-214665379648,-214388377408⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e706_ok : ecellOkT e706 = true := by decide +kernel
theorem e706_pos {a z : ℝ} (ha1 : ((725619/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((181617/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e706 e706_ok ha1 ha2 hz1 hz2 hz

-- box ['72477/409600', '725619/4096000', '3997/4000', '1999/2000']  interval_lower 81803595/1099511627776
noncomputable def e707 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1294065593221,0,true,179135489472,179135489536⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨904957662331,0,false,-214111444992,-214111444928⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1294293494924,0,true,179329110656,179329110720⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨904729760628,0,false,-214388377472,-214388377408⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1293919677746,0,true,179011504384,179011504448⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨905103577806,0,false,-213934173952,-213934173888⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1294196103991,0,true,179246373248,179246373312⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨904827151561,0,false,-214270025344,-214270025280⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099561395111,0,true,49766208,49766272⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099461860441,0,false,-49768512,-49768448⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586371398,0,true,74741056,74741120⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436884154,0,false,-74746176,-74746112⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622695,0,false,-5120,-5056⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625524,0,false,-2304,-2240⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1293992631070,0,true,179073494912,179073494976⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨905030624482,0,false,-214022800512,-214022800448⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1294244808227,0,true,179287750208,179287750272⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨904778447325,0,false,-214329210432,-214329210368⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1065022668668,0,false,-35041460224,-35041460160⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1065111936416,0,false,-34949305536,-34949305472⟩
    { al := (72477/409600), au := (725619/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨194553965445,194781867148⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179135489472,179135489536⟩ : DyadicInterval 40),(⟨-214111444992,-214111444928⟩ : DyadicInterval 40),(⟨744819664449,744819683779⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179329110656,179329110720⟩ : DyadicInterval 40),(⟨-214388377472,-214388377408⟩ : DyadicInterval 40),(⟨744778884877,744778904207⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179011504384,179011504448⟩ : DyadicInterval 40),(⟨-213934173952,-213934173888⟩ : DyadicInterval 40),(⟨744845748260,744845767590⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179246373248,179246373312⟩ : DyadicInterval 40),(⟨-214270025344,-214270025280⟩ : DyadicInterval 40),(⟨744796317492,744796336821⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨49767335,74743622⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨49766208,49766272⟩ : DyadicInterval 40),(⟨-49768512,-49768448⟩ : DyadicInterval 40),(⟨762123382451,762123401780⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74741056,74741120⟩ : DyadicInterval 40),(⟨-74746176,-74746112⟩ : DyadicInterval 40),(⟨762123381030,762123400360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5120,-2240⟩ : DyadicInterval 40),(⟨762123384736,762123405440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨194481003294,194733180451⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179073494912,179073494976⟩ : DyadicInterval 40),(⟨-214022800512,-214022800448⟩ : DyadicInterval 40),(⟨744832709640,744832728969⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179287750208,179287750272⟩ : DyadicInterval 40),(⟨-214329210432,-214329210368⟩ : DyadicInterval 40),(⟨744787600695,744787620024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35041460224,-34949305472⟩ : DyadicInterval 40),(⟨779598036352,779644132992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨179135489472,179329110720⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-214388377472,-214111444928⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e707_ok : ecellOkT e707 = true := by decide +kernel
theorem e707_pos {a z : ℝ} (ha1 : ((72477/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((725619/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e707 e707_ok ha1 ha2 hz1 hz2 hz

-- box ['725619/4096000', '181617/1024000', '3997/4000', '1999/2000']  interval_lower 10589775/137438953472
noncomputable def e708 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1294293494923,0,true,179329110656,179329110720⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨904729760629,0,false,-214388377472,-214388377408⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1294521396626,0,true,179522697728,179522697792⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨904501858926,0,false,-214665379648,-214665379584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1294147408522,0,true,179205002176,179205002240⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨904875847030,0,false,-214210854016,-214210853952⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1294423891742,0,true,179439878080,179439878144⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨904599363810,0,false,-214546859200,-214546859136⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099561456135,0,true,49827200,49827264⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099461799417,0,false,-49829504,-49829440⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586462950,0,true,74832576,74832640⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436792602,0,false,-74837760,-74837696⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622682,0,false,-5120,-5056⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625518,0,false,-2304,-2240⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1294220447305,0,true,179267054400,179267054464⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨904802808247,0,false,-214299606784,-214299606720⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1294472652953,0,true,179481296128,179481296192⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨904550602599,0,false,-214606128512,-214606128448⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1064941914843,0,false,-35124832320,-35124832256⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1065031297196,0,false,-35032552320,-35032552256⟩
    { al := (725619/4096000), au := (181617/1024000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨194781867147,195009768850⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179329110656,179329110720⟩ : DyadicInterval 40),(⟨-214388377472,-214388377408⟩ : DyadicInterval 40),(⟨744778884877,744778904207⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179522697728,179522697792⟩ : DyadicInterval 40),(⟨-214665379648,-214665379584⟩ : DyadicInterval 40),(⟨744738056519,744738075848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179205002176,179205002240⟩ : DyadicInterval 40),(⟨-214210854016,-214210853952⟩ : DyadicInterval 40),(⟨744805030463,744805049792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179439878080,179439878144⟩ : DyadicInterval 40),(⟨-214546859200,-214546859136⟩ : DyadicInterval 40),(⟨744755530400,744755549730⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨49828359,74835174⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨49827200,49827264⟩ : DyadicInterval 40),(⟨-49829504,-49829440⟩ : DyadicInterval 40),(⟨762123382445,762123401774⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74832576,74832640⟩ : DyadicInterval 40),(⟨-74837760,-74837696⟩ : DyadicInterval 40),(⟨762123381050,762123400379⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5120,-2240⟩ : DyadicInterval 40),(⟨762123384736,762123405440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨194708819529,194961025177⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179267054400,179267054464⟩ : DyadicInterval 40),(⟨-214299606784,-214299606720⟩ : DyadicInterval 40),(⟨744791960970,744791980299⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179481296128,179481296192⟩ : DyadicInterval 40),(⟨-214606128512,-214606128448⟩ : DyadicInterval 40),(⟨744746793017,744746812346⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35124832320,-35032552256⟩ : DyadicInterval 40),(⟨779639659744,779685819040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨179329110656,179522697792⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-214665379648,-214388377408⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e708_ok : ecellOkT e708 = true := by decide +kernel
theorem e708_pos {a z : ℝ} (ha1 : ((725619/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((181617/1024000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e708 e708_ok ha1 ha2 hz1 hz2 hz

-- box ['5649/32000', '723921/4096000', '1999/2000', '3999/4000']  interval_lower 75456145/1099511627776
noncomputable def e709 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1293609789816,0,true,178748144768,178748144832⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨905413465736,0,false,-213557789312,-213557789248⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1293837691519,0,true,178941834176,178941834240⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨905185564033,0,false,-213834582336,-213834582272⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1293512740734,0,true,178665654208,178665654272⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨905510514818,0,false,-213439941632,-213439941568⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1293789110004,0,true,178900548544,178900548608⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨905234145548,0,false,-213775572864,-213775572800⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536450450,0,true,24822336,24822400⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486805102,0,false,-24822976,-24822912⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099561335192,0,true,49706240,49706304⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099461920360,0,false,-49708544,-49708480⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625528,0,false,-2304,-2240⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627216,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1293561260521,0,true,178706896256,178706896320⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨905461995031,0,false,-213498858112,-213498858048⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1293813409322,0,true,178921198848,178921198912⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨905209846230,0,false,-213805087616,-213805087552⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1065175308488,0,false,-34883888704,-34883888640⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1065264368341,0,false,-34791961856,-34791961792⟩
    { al := (5649/32000), au := (723921/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨194098162040,194326063743⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178748144768,178748144832⟩ : DyadicInterval 40),(⟨-213557789312,-213557789248⟩ : DyadicInterval 40),(⟨744901077360,744901096690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178941834176,178941834240⟩ : DyadicInterval 40),(⟨-213834582336,-213834582272⟩ : DyadicInterval 40),(⟨744860395300,744860414630⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178665654208,178665654272⟩ : DyadicInterval 40),(⟨-213439941632,-213439941568⟩ : DyadicInterval 40),(⟨744918386504,744918405833⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178900548544,178900548608⟩ : DyadicInterval 40),(⟨-213775572864,-213775572800⟩ : DyadicInterval 40),(⟨744869071509,744869090839⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨24822674,49707416⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24822336,24822400⟩ : DyadicInterval 40),(⟨-24822976,-24822912⟩ : DyadicInterval 40),(⟨762123383311,762123402640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨49706240,49706304⟩ : DyadicInterval 40),(⟨-49708544,-49708480⟩ : DyadicInterval 40),(⟨762123382456,762123401785⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2304,-512⟩ : DyadicInterval 40),(⟨762123383872,762123404032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨194049632745,194301781546⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178706896256,178706896320⟩ : DyadicInterval 40),(⟨-213498858112,-213498858048⟩ : DyadicInterval 40),(⟨744909733861,744909753191⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178921198848,178921198912⟩ : DyadicInterval 40),(⟨-213805087616,-213805087552⟩ : DyadicInterval 40),(⟨744864732147,744864751476⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34883888704,-34791961792⟩ : DyadicInterval 40),(⟨779519364512,779565347232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨178748144768,178941834240⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-213834582336,-213557789248⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e709_ok : ecellOkT e709 = true := by decide +kernel
theorem e709_pos {a z : ℝ} (ha1 : ((5649/32000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((723921/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e709 e709_ok ha1 ha2 hz1 hz2 hz

-- box ['723921/4096000', '72477/409600', '1999/2000', '3999/4000']  interval_lower 78339875/1099511627776
noncomputable def e710 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1293837691518,0,true,178941834176,178941834240⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨905185564034,0,false,-213834582336,-213834582272⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1294065593222,0,true,179135489472,179135489536⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨904957662330,0,false,-214111444992,-214111444928⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1293740528486,0,true,178859261312,178859261376⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨905282727066,0,false,-213716566592,-213716566528⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1294016954731,0,true,179094162688,179094162752⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨905006300821,0,false,-214052351488,-214052351424⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536480952,0,true,24852864,24852928⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486774600,0,false,-24853504,-24853440⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099561396208,0,true,49767296,49767360⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099461859344,0,false,-49769600,-49769536⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625523,0,false,-2304,-2240⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627215,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1293789105244,0,true,178900544512,178900544576⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨905234150308,0,false,-213775567104,-213775567040⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1294041282541,0,true,179114833536,179114833600⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨904981973011,0,false,-214081908224,-214081908160⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1065094723373,0,false,-34967074688,-34967074624⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1065183897812,0,false,-34875022528,-34875022464⟩
    { al := (723921/4096000), au := (72477/409600), zl := (1999/2000), zu := (3999/4000),
      A := ⟨194326063742,194553965446⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178941834176,178941834240⟩ : DyadicInterval 40),(⟨-213834582336,-213834582272⟩ : DyadicInterval 40),(⟨744860395300,744860414630⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179135489472,179135489536⟩ : DyadicInterval 40),(⟨-214111444992,-214111444928⟩ : DyadicInterval 40),(⟨744819664449,744819683779⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178859261312,178859261376⟩ : DyadicInterval 40),(⟨-213716566592,-213716566528⟩ : DyadicInterval 40),(⟨744877745546,744877764875⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179094162688,179094162752⟩ : DyadicInterval 40),(⟨-214052351488,-214052351424⟩ : DyadicInterval 40),(⟨744828361267,744828380596⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨24853176,49768432⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24852864,24852928⟩ : DyadicInterval 40),(⟨-24853504,-24853440⟩ : DyadicInterval 40),(⟨762123383310,762123402639⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨49767296,49767360⟩ : DyadicInterval 40),(⟨-49769600,-49769536⟩ : DyadicInterval 40),(⟨762123382451,762123401780⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2304,-512⟩ : DyadicInterval 40),(⟨762123383872,762123404032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨194277477468,194529654765⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178900544512,178900544576⟩ : DyadicInterval 40),(⟨-213775567104,-213775567040⟩ : DyadicInterval 40),(⟨744869072360,744869091690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179114833536,179114833600⟩ : DyadicInterval 40),(⟨-214081908224,-214081908160⟩ : DyadicInterval 40),(⟨744824011603,744824030933⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34967074688,-34875022464⟩ : DyadicInterval 40),(⟨779560894848,779606940224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨178941834176,179135489536⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-214111444992,-213834582272⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e710_ok : ecellOkT e710 = true := by decide +kernel
theorem e710_pos {a z : ℝ} (ha1 : ((723921/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((72477/409600 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e710 e710_ok ha1 ha2 hz1 hz2 hz

-- box ['5649/32000', '723921/4096000', '3999/4000', '1']  interval_lower 74894743/1099511627776
noncomputable def e711 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1293609789816,0,true,178748144768,178748144832⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨905413465736,0,false,-213557789312,-213557789248⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1293837691519,0,true,178941834176,178941834240⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨905185564033,0,false,-213834582336,-213834582272⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1293561265275,0,true,178706900288,178706900352⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨905461990277,0,false,-213498863872,-213498863808⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536481757,0,true,24853696,24853760⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486773795,0,false,-24854272,-24854208⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627214,0,false,-576,-512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1293585522587,0,true,178727518528,178727518592⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨905437732965,0,false,-213528320192,-213528320128⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1293837700008,0,true,178941841408,178941841472⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨905185555544,0,false,-213834592640,-213834592576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1065166722824,0,false,-34892751168,-34892751104⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1065255803922,0,false,-34800801664,-34800801600⟩
    { al := (5649/32000), au := (723921/4096000), zl := (3999/4000), zu := 1,
      A := ⟨194098162040,194326063743⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178748144768,178748144832⟩ : DyadicInterval 40),(⟨-213557789312,-213557789248⟩ : DyadicInterval 40),(⟨744901077360,744901096690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178941834176,178941834240⟩ : DyadicInterval 40),(⟨-213834582336,-213834582272⟩ : DyadicInterval 40),(⟨744860395300,744860414630⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178706900288,178706900352⟩ : DyadicInterval 40),(⟨-213498863872,-213498863808⟩ : DyadicInterval 40),(⟨744909733013,744909752342⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178941834176,178941834240⟩ : DyadicInterval 40),(⟨-213834582336,-213834582272⟩ : DyadicInterval 40),(⟨744860395300,744860414630⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,24853981⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24853696,24853760⟩ : DyadicInterval 40),(⟨-24854272,-24854208⟩ : DyadicInterval 40),(⟨762123383278,762123402607⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,0⟩ : DyadicInterval 40),(⟨762123383616,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨194073894811,194326072232⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178727518528,178727518592⟩ : DyadicInterval 40),(⟨-213528320192,-213528320128⟩ : DyadicInterval 40),(⟨744905406342,744905425671⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178941841408,178941841472⟩ : DyadicInterval 40),(⟨-213834592640,-213834592576⟩ : DyadicInterval 40),(⟨744860393770,744860413100⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34892751168,-34800801600⟩ : DyadicInterval 40),(⟨779523784416,779569778464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨178748144768,178941834240⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-213834582336,-213557789248⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e711_ok : ecellOkT e711 = true := by decide +kernel
theorem e711_pos {a z : ℝ} (ha1 : ((5649/32000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((723921/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e711 e711_ok ha1 ha2 hz1 hz2 hz

-- box ['723921/4096000', '72477/409600', '3999/4000', '1']  interval_lower 38888155/549755813888
noncomputable def e712 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1293837691518,0,true,178941834176,178941834240⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨905185564034,0,false,-213834582336,-213834582272⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1294065593222,0,true,179135489472,179135489536⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨904957662330,0,false,-214111444992,-214111444928⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1293789110002,0,true,178900548544,178900548608⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨905234145550,0,false,-213775572864,-213775572800⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536512266,0,true,24884160,24884224⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486743286,0,false,-24884800,-24884736⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627212,0,false,-576,-512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1293813395797,0,true,178921187328,178921187392⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨905209859755,0,false,-213805071168,-213805071104⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1294065601717,0,true,179135496704,179135496768⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨904957653835,0,false,-214111455360,-214111455296⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1065086117558,0,false,-34975958592,-34975958528⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1065175313269,0,false,-34883883776,-34883883712⟩
    { al := (723921/4096000), au := (72477/409600), zl := (3999/4000), zu := 1,
      A := ⟨194326063742,194553965446⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178941834176,178941834240⟩ : DyadicInterval 40),(⟨-213834582336,-213834582272⟩ : DyadicInterval 40),(⟨744860395300,744860414630⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179135489472,179135489536⟩ : DyadicInterval 40),(⟨-214111444992,-214111444928⟩ : DyadicInterval 40),(⟨744819664449,744819683779⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178900548544,178900548608⟩ : DyadicInterval 40),(⟨-213775572864,-213775572800⟩ : DyadicInterval 40),(⟨744869071509,744869090839⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179135489472,179135489536⟩ : DyadicInterval 40),(⟨-214111444992,-214111444928⟩ : DyadicInterval 40),(⟨744819664449,744819683779⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,24884490⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24884160,24884224⟩ : DyadicInterval 40),(⟨-24884800,-24884736⟩ : DyadicInterval 40),(⟨762123383308,762123402637⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,0⟩ : DyadicInterval 40),(⟨762123383616,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨194301768021,194553973941⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨178921187328,178921187392⟩ : DyadicInterval 40),(⟨-213805071168,-213805071104⟩ : DyadicInterval 40),(⟨744864734570,744864753899⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179135496704,179135496768⟩ : DyadicInterval 40),(⟨-214111455360,-214111455296⟩ : DyadicInterval 40),(⟨744819662941,744819682271⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-34975958592,-34883883712⟩ : DyadicInterval 40),(⟨779565325472,779611382176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨178941834176,179135489536⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-214111444992,-213834582272⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e712_ok : ecellOkT e712 = true := by decide +kernel
theorem e712_pos {a z : ℝ} (ha1 : ((723921/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((72477/409600 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e712 e712_ok ha1 ha2 hz1 hz2 hz

-- box ['72477/409600', '725619/4096000', '1999/2000', '3999/4000']  interval_lower 40619043/549755813888
noncomputable def e713 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1294065593221,0,true,179135489472,179135489536⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨904957662331,0,false,-214111444992,-214111444928⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1294293494924,0,true,179329110656,179329110720⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨904729760628,0,false,-214388377472,-214388377408⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1293968316238,0,true,179052834304,179052834368⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨905054939314,0,false,-213993261120,-213993261056⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1294244799458,0,true,179287742720,179287742784⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨904778456094,0,false,-214329199808,-214329199744⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536511460,0,true,24883392,24883456⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486744092,0,false,-24883968,-24883904⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099561457234,0,true,49828288,49828352⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099461798318,0,false,-49830592,-49830528⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625517,0,false,-2304,-2240⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627213,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1294016949971,0,true,179094158656,179094158720⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨905006305581,0,false,-214052345664,-214052345600⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1294269155752,0,true,179308434176,179308434240⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨904754099800,0,false,-214358798656,-214358798592⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1065014043807,0,false,-35050364416,-35050364352⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1065103332851,0,false,-34958187008,-34958186944⟩
    { al := (72477/409600), au := (725619/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨194553965445,194781867148⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179135489472,179135489536⟩ : DyadicInterval 40),(⟨-214111444992,-214111444928⟩ : DyadicInterval 40),(⟨744819664449,744819683779⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179329110656,179329110720⟩ : DyadicInterval 40),(⟨-214388377472,-214388377408⟩ : DyadicInterval 40),(⟨744778884877,744778904207⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179052834304,179052834368⟩ : DyadicInterval 40),(⟨-213993261120,-213993261056⟩ : DyadicInterval 40),(⟨744837055874,744837075203⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179287742720,179287742784⟩ : DyadicInterval 40),(⟨-214329199808,-214329199744⟩ : DyadicInterval 40),(⟨744787602300,744787621630⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨24883684,49829458⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24883392,24883456⟩ : DyadicInterval 40),(⟨-24883968,-24883904⟩ : DyadicInterval 40),(⟨762123383276,762123402605⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨49828288,49828352⟩ : DyadicInterval 40),(⟨-49830592,-49830528⟩ : DyadicInterval 40),(⟨762123382445,762123401774⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2304,-512⟩ : DyadicInterval 40),(⟨762123383872,762123404032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨194505322195,194757527976⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179094158656,179094158720⟩ : DyadicInterval 40),(⟨-214052345664,-214052345600⟩ : DyadicInterval 40),(⟨744828362094,744828381423⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179308434176,179308434240⟩ : DyadicInterval 40),(⟨-214358798656,-214358798592⟩ : DyadicInterval 40),(⟨744783242326,744783261656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35050364416,-34958186944⟩ : DyadicInterval 40),(⟨779602477088,779648585088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨179135489472,179329110720⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-214388377472,-214111444928⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e713_ok : ecellOkT e713 = true := by decide +kernel
theorem e713_pos {a z : ℝ} (ha1 : ((72477/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((725619/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e713 e713_ok ha1 ha2 hz1 hz2 hz

-- box ['725619/4096000', '181617/1024000', '1999/2000', '3999/4000']  interval_lower 42075121/549755813888
noncomputable def e714 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1294293494923,0,true,179329110656,179329110720⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨904729760629,0,false,-214388377472,-214388377408⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1294521396626,0,true,179522697728,179522697792⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨904501858926,0,false,-214665379648,-214665379584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1294196103989,0,true,179246373248,179246373312⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨904827151563,0,false,-214270025344,-214270025280⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1294472644184,0,true,179481288704,179481288768⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨904550611368,0,false,-214606117824,-214606117760⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536541973,0,true,24913856,24913920⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486713579,0,false,-24914496,-24914432⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099561518270,0,true,49889344,49889408⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099461737282,0,false,-49891648,-49891584⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625512,0,false,-2304,-2240⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627212,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1294244794691,0,true,179287738688,179287738752⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨904778460861,0,false,-214329193984,-214329193920⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1294497028967,0,true,179502000704,179502000768⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨904526226585,0,false,-214635758720,-214635758656⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1064933269787,0,false,-35133758016,-35133757952⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1065022673464,0,false,-35041455296,-35041455232⟩
    { al := (725619/4096000), au := (181617/1024000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨194781867147,195009768850⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179329110656,179329110720⟩ : DyadicInterval 40),(⟨-214388377472,-214388377408⟩ : DyadicInterval 40),(⟨744778884877,744778904207⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179522697728,179522697792⟩ : DyadicInterval 40),(⟨-214665379648,-214665379584⟩ : DyadicInterval 40),(⟨744738056519,744738075848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179246373248,179246373312⟩ : DyadicInterval 40),(⟨-214270025344,-214270025280⟩ : DyadicInterval 40),(⟨744796317492,744796336822⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179481288704,179481288768⟩ : DyadicInterval 40),(⟨-214606117824,-214606117760⟩ : DyadicInterval 40),(⟨744746794562,744746813892⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨24914197,49890494⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24913856,24913920⟩ : DyadicInterval 40),(⟨-24914496,-24914432⟩ : DyadicInterval 40),(⟨762123383307,762123402636⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨49889344,49889408⟩ : DyadicInterval 40),(⟨-49891648,-49891584⟩ : DyadicInterval 40),(⟨762123382440,762123401769⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2304,-512⟩ : DyadicInterval 40),(⟨762123383872,762123404032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨194733166915,194985401191⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179287738688,179287738752⟩ : DyadicInterval 40),(⟨-214329193984,-214329193920⟩ : DyadicInterval 40),(⟨744787603130,744787622460⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179502000704,179502000768⟩ : DyadicInterval 40),(⟨-214635758720,-214635758656⟩ : DyadicInterval 40),(⟨744742424262,744742443592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35133758016,-35041455232⟩ : DyadicInterval 40),(⟨779644111232,779690281888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨179329110656,179522697792⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-214665379648,-214388377408⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e714_ok : ecellOkT e714 = true := by decide +kernel
theorem e714_pos {a z : ℝ} (ha1 : ((725619/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((181617/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e714 e714_ok ha1 ha2 hz1 hz2 hz

-- box ['72477/409600', '725619/4096000', '3999/4000', '1']  interval_lower 80672071/1099511627776
noncomputable def e715 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1294065593221,0,true,179135489472,179135489536⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨904957662331,0,false,-214111444992,-214111444928⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1294293494924,0,true,179329110656,179329110720⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨904729760628,0,false,-214388377472,-214388377408⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1294016954729,0,true,179094162688,179094162752⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨905006300823,0,false,-214052351488,-214052351424⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536542780,0,true,24914688,24914752⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486712772,0,false,-24915328,-24915264⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627211,0,false,-576,-512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1294041269010,0,true,179114822016,179114822080⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨904981986542,0,false,-214081891840,-214081891776⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1294293503415,0,true,179329117888,179329117952⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨904729752137,0,false,-214388387776,-214388387712⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1065005417819,0,false,-35059269888,-35059269824⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1065094728162,0,false,-34967069760,-34967069696⟩
    { al := (72477/409600), au := (725619/4096000), zl := (3999/4000), zu := 1,
      A := ⟨194553965445,194781867148⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179135489472,179135489536⟩ : DyadicInterval 40),(⟨-214111444992,-214111444928⟩ : DyadicInterval 40),(⟨744819664449,744819683779⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179329110656,179329110720⟩ : DyadicInterval 40),(⟨-214388377472,-214388377408⟩ : DyadicInterval 40),(⟨744778884877,744778904207⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179094162688,179094162752⟩ : DyadicInterval 40),(⟨-214052351488,-214052351424⟩ : DyadicInterval 40),(⟨744828361267,744828380597⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179329110656,179329110720⟩ : DyadicInterval 40),(⟨-214388377472,-214388377408⟩ : DyadicInterval 40),(⟨744778884877,744778904207⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,24915004⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24914688,24914752⟩ : DyadicInterval 40),(⟨-24915328,-24915264⟩ : DyadicInterval 40),(⟨762123383307,762123402636⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,0⟩ : DyadicInterval 40),(⟨762123383616,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨194529641234,194781875639⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179114822016,179114822080⟩ : DyadicInterval 40),(⟨-214081891840,-214081891776⟩ : DyadicInterval 40),(⟨744824014059,744824033388⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179329117888,179329117952⟩ : DyadicInterval 40),(⟨-214388387776,-214388387712⟩ : DyadicInterval 40),(⟨744778883339,744778902669⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35059269888,-34967069696⟩ : DyadicInterval 40),(⟨779606918464,779653037824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨179135489472,179329110720⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-214388377472,-214111444928⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e715_ok : ecellOkT e715 = true := by decide +kernel
theorem e715_pos {a z : ℝ} (ha1 : ((72477/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((725619/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e715 e715_ok ha1 ha2 hz1 hz2 hz

-- box ['725619/4096000', '181617/1024000', '3999/4000', '1']  interval_lower 83582085/1099511627776
noncomputable def e716 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1294293494923,0,true,179329110656,179329110720⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨904729760629,0,false,-214388377472,-214388377408⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1294521396626,0,true,179522697728,179522697792⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨904501858926,0,false,-214665379648,-214665379584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1294244799456,0,true,179287742720,179287742784⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨904778456096,0,false,-214329199808,-214329199744⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536573299,0,true,24945216,24945280⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486682253,0,false,-24945856,-24945792⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627210,0,false,-576,-512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1294269142215,0,true,179308422656,179308422720⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨904754113337,0,false,-214358782144,-214358782080⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1294521405118,0,true,179522704960,179522705024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨904501850434,0,false,-214665389952,-214665389888⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1064924623602,0,false,-35142684992,-35142684928⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1065014048604,0,false,-35050359488,-35050359424⟩
    { al := (725619/4096000), au := (181617/1024000), zl := (3999/4000), zu := 1,
      A := ⟨194781867147,195009768850⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179329110656,179329110720⟩ : DyadicInterval 40),(⟨-214388377472,-214388377408⟩ : DyadicInterval 40),(⟨744778884877,744778904207⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179522697728,179522697792⟩ : DyadicInterval 40),(⟨-214665379648,-214665379584⟩ : DyadicInterval 40),(⟨744738056519,744738075848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179287742720,179287742784⟩ : DyadicInterval 40),(⟨-214329199808,-214329199744⟩ : DyadicInterval 40),(⟨744787602301,744787621630⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179522697728,179522697792⟩ : DyadicInterval 40),(⟨-214665379648,-214665379584⟩ : DyadicInterval 40),(⟨744738056519,744738075848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,24945523⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24945216,24945280⟩ : DyadicInterval 40),(⟨-24945856,-24945792⟩ : DyadicInterval 40),(⟨762123383306,762123402635⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,0⟩ : DyadicInterval 40),(⟨762123383616,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨194757514439,195009777342⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179308422656,179308422720⟩ : DyadicInterval 40),(⟨-214358782144,-214358782080⟩ : DyadicInterval 40),(⟨744783244736,744783264066⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179522704960,179522705024⟩ : DyadicInterval 40),(⟨-214665389952,-214665389888⟩ : DyadicInterval 40),(⟨744738054977,744738074307⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35142684992,-35050359424⟩ : DyadicInterval 40),(⟨779648563328,779694745376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨179329110656,179522697792⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-214665379648,-214388377408⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e716_ok : ecellOkT e716 = true := by decide +kernel
theorem e716_pos {a z : ℝ} (ha1 : ((725619/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((181617/1024000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e716 e716_ok ha1 ha2 hz1 hz2 hz

-- box ['181617/1024000', '727317/4096000', '999/1000', '3997/4000']  interval_lower 88216531/1099511627776
noncomputable def e717 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1294521396625,0,true,179522697728,179522697792⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨904501858927,0,false,-214665379648,-214665379584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1294749298328,0,true,179716250752,179716250816⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨904273957224,0,false,-214942451648,-214942451584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1294326386856,0,true,179357052224,179357052288⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨904696868696,0,false,-214428351488,-214428351424⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1294602870076,0,true,179591895680,179591895744⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨904420385476,0,false,-214764423168,-214764423104⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586461556,0,true,74831232,74831296⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436793996,0,false,-74836352,-74836288⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099611529425,0,true,99897088,99897152⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099411726127,0,false,-99906240,-99906176⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618698,0,false,-9088,-9024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622683,0,false,-5120,-5056⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1294423887811,0,true,179439874752,179439874816⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨904599367741,0,false,-214546854400,-214546854336⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1294676093327,0,true,179654082688,179654082752⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨904347162225,0,false,-214853444928,-214853444864⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1064869730726,0,false,-35199362176,-35199362112⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1064959206363,0,false,-35106979584,-35106979520⟩
    { al := (181617/1024000), au := (727317/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨195009768849,195237670552⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179522697728,179522697792⟩ : DyadicInterval 40),(⟨-214665379648,-214665379584⟩ : DyadicInterval 40),(⟨744738056519,744738075848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179716250752,179716250816⟩ : DyadicInterval 40),(⟨-214942451648,-214942451584⟩ : DyadicInterval 40),(⟨744697179378,744697198708⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179357052224,179357052288⟩ : DyadicInterval 40),(⟨-214428351488,-214428351424⟩ : DyadicInterval 40),(⟨744772995321,744773014651⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179591895680,179591895744⟩ : DyadicInterval 40),(⟨-214764423168,-214764423104⟩ : DyadicInterval 40),(⟨744723448782,744723468112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨74833780,99901649⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74831232,74831296⟩ : DyadicInterval 40),(⟨-74836352,-74836288⟩ : DyadicInterval 40),(⟨762123381018,762123400347⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨99897088,99897152⟩ : DyadicInterval 40),(⟨-99906240,-99906176⟩ : DyadicInterval 40),(⟨762123379050,762123398380⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9088,-5056⟩ : DyadicInterval 40),(⟨762123386144,762123407424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨194912260035,195164465551⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179439874752,179439874816⟩ : DyadicInterval 40),(⟨-214546854400,-214546854336⟩ : DyadicInterval 40),(⟨744755531089,744755550418⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179654082688,179654082752⟩ : DyadicInterval 40),(⟨-214853444928,-214853444864⟩ : DyadicInterval 40),(⟨744710314993,744710334323⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35199362176,-35106979520⟩ : DyadicInterval 40),(⟨779676873376,779723083968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨179522697728,179716250816⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-214942451648,-214665379584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e717_ok : ecellOkT e717 = true := by decide +kernel
theorem e717_pos {a z : ℝ} (ha1 : ((181617/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((727317/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e717 e717_ok ha1 ha2 hz1 hz2 hz

-- box ['727317/4096000', '364083/2048000', '999/1000', '3997/4000']  interval_lower 22790443/274877906944
noncomputable def e718 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1294749298327,0,true,179716250752,179716250816⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨904273957225,0,false,-214942451648,-214942451584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1294977200030,0,true,179909769728,179909769792⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨904046055522,0,false,-215219593536,-215219593472⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1294554060656,0,true,179550440832,179550440896⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨904469194896,0,false,-214705086720,-214705086656⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1294830600851,0,true,179785291328,179785291392⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨904192654701,0,false,-215041312256,-215041312192⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586553120,0,true,74922752,74922816⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436702432,0,false,-74927936,-74927872⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099611651533,0,true,100019200,100019264⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099411604019,0,false,-100028352,-100028288⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618676,0,false,-9152,-9088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622671,0,false,-5120,-5056⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1294651675562,0,true,179633345600,179633345664⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨904371579990,0,false,-214823758016,-214823757952⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1294903909567,0,true,179847540032,179847540096⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨904119345985,0,false,-215130460352,-215130460288⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1064788808281,0,false,-35282920320,-35282920256⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1064878398543,0,false,-35190412416,-35190412352⟩
    { al := (727317/4096000), au := (364083/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨195237670551,195465572254⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179716250752,179716250816⟩ : DyadicInterval 40),(⟨-214942451648,-214942451584⟩ : DyadicInterval 40),(⟨744697179378,744697198708⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179909769728,179909769792⟩ : DyadicInterval 40),(⟨-215219593536,-215219593472⟩ : DyadicInterval 40),(⟨744656253471,744656272801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179550440832,179550440896⟩ : DyadicInterval 40),(⟨-214705086720,-214705086656⟩ : DyadicInterval 40),(⟨744732200784,744732220114⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179785291328,179785291392⟩ : DyadicInterval 40),(⟨-215041312256,-215041312192⟩ : DyadicInterval 40),(⟨744682584916,744682604245⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨74925344,100023757⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74922752,74922816⟩ : DyadicInterval 40),(⟨-74927936,-74927872⟩ : DyadicInterval 40),(⟨762123381038,762123400367⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨100019200,100019264⟩ : DyadicInterval 40),(⟨-100028352,-100028288⟩ : DyadicInterval 40),(⟨762123379028,762123398358⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9152,-5056⟩ : DyadicInterval 40),(⟨762123386144,762123407456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨195140047786,195392281791⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179633345600,179633345664⟩ : DyadicInterval 40),(⟨-214823758016,-214823757952⟩ : DyadicInterval 40),(⟨744714695255,744714714585⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179847540032,179847540096⟩ : DyadicInterval 40),(⟨-215130460352,-215130460288⟩ : DyadicInterval 40),(⟨744669420069,744669439399⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35282920320,-35190412352⟩ : DyadicInterval 40),(⟨779718589792,779764863040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨179716250752,179909769792⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-215219593536,-214942451584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e718_ok : ecellOkT e718 = true := by decide +kernel
theorem e718_pos {a z : ℝ} (ha1 : ((727317/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((364083/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e718 e718_ok ha1 ha2 hz1 hz2 hz

-- box ['181617/1024000', '727317/4096000', '3997/4000', '1999/2000']  interval_lower 43823435/549755813888
noncomputable def e719 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1294521396625,0,true,179522697728,179522697792⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨904501858927,0,false,-214665379648,-214665379584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1294749298328,0,true,179716250752,179716250816⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨904273957224,0,false,-214942451648,-214942451584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1294375139298,0,true,179398465920,179398465984⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨904648116254,0,false,-214487603776,-214487603712⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1294651679493,0,true,179633348928,179633348992⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨904371576059,0,false,-214823762816,-214823762752⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099561517170,0,true,49888256,49888320⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099461738382,0,false,-49890560,-49890496⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586554518,0,true,74924160,74924224⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436701034,0,false,-74929344,-74929280⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622670,0,false,-5120,-5056⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625513,0,false,-2304,-2240⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1294448263539,0,true,179460579840,179460579904⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨904574992013,0,false,-214576482752,-214576482688⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1294700497684,0,true,179674808064,179674808128⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨904322757868,0,false,-214883116288,-214883116224⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1064861066587,0,false,-35208308160,-35208308096⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1064950563571,0,false,-35115902848,-35115902784⟩
    { al := (181617/1024000), au := (727317/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨195009768849,195237670552⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179522697728,179522697792⟩ : DyadicInterval 40),(⟨-214665379648,-214665379584⟩ : DyadicInterval 40),(⟨744738056519,744738075848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179716250752,179716250816⟩ : DyadicInterval 40),(⟨-214942451648,-214942451584⟩ : DyadicInterval 40),(⟨744697179378,744697198708⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179398465920,179398465984⟩ : DyadicInterval 40),(⟨-214487603776,-214487603712⟩ : DyadicInterval 40),(⟨744764263995,744764283325⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179633348928,179633348992⟩ : DyadicInterval 40),(⟨-214823762816,-214823762752⟩ : DyadicInterval 40),(⟨744714694565,744714713894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨49889394,74926742⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨49888256,49888320⟩ : DyadicInterval 40),(⟨-49890560,-49890496⟩ : DyadicInterval 40),(⟨762123382440,762123401769⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74924160,74924224⟩ : DyadicInterval 40),(⟨-74929344,-74929280⟩ : DyadicInterval 40),(⟨762123381037,762123400367⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5120,-2240⟩ : DyadicInterval 40),(⟨762123384736,762123405440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨194936635763,195188869908⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179460579840,179460579904⟩ : DyadicInterval 40),(⟨-214576482752,-214576482688⟩ : DyadicInterval 40),(⟨744751163553,744751182883⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179674808064,179674808128⟩ : DyadicInterval 40),(⟨-214883116288,-214883116224⟩ : DyadicInterval 40),(⟨744705936517,744705955846⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35208308160,-35115902784⟩ : DyadicInterval 40),(⟨779681335008,779727556960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨179522697728,179716250816⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-214942451648,-214665379584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e719_ok : ecellOkT e719 = true := by decide +kernel
theorem e719_pos {a z : ℝ} (ha1 : ((181617/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((727317/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e719 e719_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B011

end


