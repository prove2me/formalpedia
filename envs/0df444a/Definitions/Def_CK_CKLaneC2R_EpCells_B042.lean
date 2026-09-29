-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B042
-- name    : CK_CKLaneC2R_EpCells_B042
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:29:42.309832+00:00
-- url     : https://prove2.me/theorems/1719afea-ba02-43e2-a7f6-1702e4025a49
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B042` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B042` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B042` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B042 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B042.lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheckT

-- ===== source module CKLaneC2R.EpCells.B042 =====
section

namespace CKLaneC2R.EpCells.B042

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['33267/204800', '1331529/8192000', '1999/2000', '7997/8000']  interval_lower 244720551/1099511627776
noncomputable def e2520 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278112474071,0,true,165496569856,165496569920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920910781481,0,false,-194897479808,-194897479744⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278226424923,0,true,165594593088,165594593152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920796830629,0,false,-195033538624,-195033538560⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278023173647,0,true,165419745408,165419745472⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921000081905,0,false,-194790865664,-194790865600⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278159406875,0,true,165536943616,165536943680⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920863848677,0,false,-194953516160,-194953516096⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545767531,0,true,34139200,34139264⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477488021,0,false,-34140288,-34140224⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557178343,0,true,45549568,45549632⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466077209,0,false,-45551552,-45551488⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625888,0,false,-1920,-1856⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626716,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278067819392,0,true,165458154496,165458154560⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920955436160,0,false,-194844166144,-194844166080⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278192924487,0,true,165565776128,165565776192⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920830331065,0,false,-194993536896,-194993536832⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070474185162,0,false,-29427760768,-29427760704⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070514832509,0,false,-29386011584,-29386011520⟩
    { al := (33267/204800), au := (1331529/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨178600846295,178714797147⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165496569856,165496569920⟩ : DyadicInterval 40),(⟨-194897479808,-194897479744⟩ : DyadicInterval 40),(⟨747553260280,747553279609⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165594593088,165594593152⟩ : DyadicInterval 40),(⟨-195033538624,-195033538560⟩ : DyadicInterval 40),(⟨747534579000,747534598330⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165419745408,165419745472⟩ : DyadicInterval 40),(⟨-194790865664,-194790865600⟩ : DyadicInterval 40),(⟨747567891835,747567911165⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165536943616,165536943680⟩ : DyadicInterval 40),(⟨-194953516160,-194953516096⟩ : DyadicInterval 40),(⟨747545567522,747545586851⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34139755,45550567⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34139200,34139264⟩ : DyadicInterval 40),(⟨-34140288,-34140224⟩ : DyadicInterval 40),(⟨762123383035,762123402364⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45549568,45549632⟩ : DyadicInterval 40),(⟨-45551552,-45551488⟩ : DyadicInterval 40),(⟨762123382656,762123401985⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1920,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178556191616,178681296711⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165458154496,165458154560⟩ : DyadicInterval 40),(⟨-194844166144,-194844166080⟩ : DyadicInterval 40),(⟨747560577714,747560597043⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165565776128,165565776192⟩ : DyadicInterval 40),(⟨-194993536896,-194993536832⟩ : DyadicInterval 40),(⟨747540072362,747540091691⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29427760768,-29386011520⟩ : DyadicInterval 40),(⟨776816389376,776837283264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165496569856,165594593152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195033538624,-194897479744⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2520_ok : ecellOkT e2520 = true := by decide +kernel
theorem e2520_pos {a z : ℝ} (ha1 : ((33267/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1331529/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2520 e2520_ok ha1 ha2 hz1 hz2 hz

-- box ['1331529/8192000', '666189/4096000', '1999/2000', '7997/8000']  interval_lower 245981167/1099511627776
noncomputable def e2521 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278226424922,0,true,165594593088,165594593152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920796830630,0,false,-195033538624,-195033538560⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278340375774,0,true,165692607552,165692607616⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920682879778,0,false,-195169614272,-195169614208⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278137067523,0,true,165517726464,165517726528⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920886188029,0,false,-194926843264,-194926843200⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278273314994,0,true,165634926528,165634926592⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920749940558,0,false,-195089530880,-195089530816⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545790166,0,true,34161856,34161920⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477465386,0,false,-34162944,-34162880⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557208526,0,true,45579776,45579840⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466047026,0,false,-45581696,-45581632⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625886,0,false,-1920,-1856⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626715,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278181741754,0,true,165556156608,165556156672⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920841513798,0,false,-194980184320,-194980184256⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278306853976,0,true,165663774784,165663774848⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920716401576,0,false,-195129582144,-195129582080⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070437144064,0,false,-29465807296,-29465807232⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070477819654,0,false,-29424027648,-29424027584⟩
    { al := (1331529/8192000), au := (666189/4096000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨178714797146,178828747998⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165594593088,165594593152⟩ : DyadicInterval 40),(⟨-195033538624,-195033538560⟩ : DyadicInterval 40),(⟨747534579001,747534598330⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165692607552,165692607616⟩ : DyadicInterval 40),(⟨-195169614272,-195169614208⟩ : DyadicInterval 40),(⟨747515885606,747515904935⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165517726464,165517726528⟩ : DyadicInterval 40),(⟨-194926843264,-194926843200⟩ : DyadicInterval 40),(⟨747549229409,747549248739⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165634926528,165634926592⟩ : DyadicInterval 40),(⟨-195089530880,-195089530816⟩ : DyadicInterval 40),(⟨747526888235,747526907564⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34162390,45580750⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34161856,34161920⟩ : DyadicInterval 40),(⟨-34162944,-34162880⟩ : DyadicInterval 40),(⟨762123383034,762123402363⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45579776,45579840⟩ : DyadicInterval 40),(⟨-45581696,-45581632⟩ : DyadicInterval 40),(⟨762123382622,762123401951⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1920,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178670113978,178795226200⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165556156608,165556156672⟩ : DyadicInterval 40),(⟨-194980184320,-194980184256⟩ : DyadicInterval 40),(⟨747541905870,747541925200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165663774784,165663774848⟩ : DyadicInterval 40),(⟨-195129582144,-195129582080⟩ : DyadicInterval 40),(⟨747521386065,747521405395⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29465807296,-29424027584⟩ : DyadicInterval 40),(⟨776835397408,776856306528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165594593088,165692607616⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195169614272,-195033538560⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2521_ok : ecellOkT e2521 = true := by decide +kernel
theorem e2521_pos {a z : ℝ} (ha1 : ((1331529/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((666189/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2521 e2521_ok ha1 ha2 hz1 hz2 hz

-- box ['33267/204800', '1331529/8192000', '7997/8000', '3999/4000']  interval_lower 122270239/549755813888
noncomputable def e2522 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278112474071,0,true,165496569856,165496569920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920910781481,0,false,-194897479808,-194897479744⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278226424923,0,true,165594593088,165594593152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920796830629,0,false,-195033538624,-195033538560⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278045498753,0,true,165438952064,165438952128⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920977756799,0,false,-194817518272,-194817518208⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278181746224,0,true,165556160448,165556160512⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920841509328,0,false,-194980189696,-194980189632⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534387582,0,true,22759552,22759616⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488867970,0,false,-22760064,-22760000⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545790849,0,true,34162496,34162560⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477464703,0,false,-34163648,-34163584⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626714,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627305,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278078981851,0,true,165467757440,165467757504⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920944273701,0,false,-194857492864,-194857492800⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278204094094,0,true,165575384256,165575384320⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920819161458,0,false,-195006873984,-195006873920⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070470554710,0,false,-29431489664,-29431489600⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070511206921,0,false,-29389735424,-29389735360⟩
    { al := (33267/204800), au := (1331529/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨178600846295,178714797147⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165496569856,165496569920⟩ : DyadicInterval 40),(⟨-194897479808,-194897479744⟩ : DyadicInterval 40),(⟨747553260280,747553279609⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165594593088,165594593152⟩ : DyadicInterval 40),(⟨-195033538624,-195033538560⟩ : DyadicInterval 40),(⟨747534579000,747534598330⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165438952064,165438952128⟩ : DyadicInterval 40),(⟨-194817518272,-194817518208⟩ : DyadicInterval 40),(⟨747564234638,747564253968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165556160448,165556160512⟩ : DyadicInterval 40),(⟨-194980189696,-194980189632⟩ : DyadicInterval 40),(⟨747541905156,747541924486⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22759806,34163073⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22759552,22759616⟩ : DyadicInterval 40),(⟨-22760064,-22760000⟩ : DyadicInterval 40),(⟨762123383336,762123402665⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34162496,34162560⟩ : DyadicInterval 40),(⟨-34163648,-34163584⟩ : DyadicInterval 40),(⟨762123383066,762123402395⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178567354075,178692466318⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165467757440,165467757504⟩ : DyadicInterval 40),(⟨-194857492864,-194857492800⟩ : DyadicInterval 40),(⟨747558748713,747558768043⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165575384256,165575384320⟩ : DyadicInterval 40),(⟨-195006873984,-195006873920⟩ : DyadicInterval 40),(⟨747538240908,747538260238⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29431489664,-29389735360⟩ : DyadicInterval 40),(⟨776818251296,776839147712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165496569856,165594593152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195033538624,-194897479744⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2522_ok : ecellOkT e2522 = true := by decide +kernel
theorem e2522_pos {a z : ℝ} (ha1 : ((33267/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1331529/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2522 e2522_ok ha1 ha2 hz1 hz2 hz

-- box ['1331529/8192000', '666189/4096000', '7997/8000', '3999/4000']  interval_lower 245800641/1099511627776
noncomputable def e2523 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278226424922,0,true,165594593088,165594593152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920796830630,0,false,-195033538624,-195033538560⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278340375774,0,true,165692607552,165692607616⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920682879778,0,false,-195169614272,-195169614208⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278159406872,0,true,165536943616,165536943680⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920863848680,0,false,-194953516160,-194953516096⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278295668588,0,true,165654153856,165654153920⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920727586964,0,false,-195116224704,-195116224640⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534402672,0,true,22774656,22774720⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488852880,0,false,-22775168,-22775104⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545813487,0,true,34185152,34185216⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477442065,0,false,-34186304,-34186240⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626713,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627305,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278192911333,0,true,165565764800,165565764864⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920830344219,0,false,-194993521216,-194993521152⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278318030703,0,true,165673388224,165673388288⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920705224849,0,false,-195142929344,-195142929280⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070433508982,0,false,-29469541120,-29469541056⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070474189438,0,false,-29427756352,-29427756288⟩
    { al := (1331529/8192000), au := (666189/4096000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨178714797146,178828747998⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165594593088,165594593152⟩ : DyadicInterval 40),(⟨-195033538624,-195033538560⟩ : DyadicInterval 40),(⟨747534579001,747534598330⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165692607552,165692607616⟩ : DyadicInterval 40),(⟨-195169614272,-195169614208⟩ : DyadicInterval 40),(⟨747515885606,747515904935⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165536943616,165536943680⟩ : DyadicInterval 40),(⟨-194953516160,-194953516096⟩ : DyadicInterval 40),(⟨747545567522,747545586852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165654153856,165654153920⟩ : DyadicInterval 40),(⟨-195116224704,-195116224640⟩ : DyadicInterval 40),(⟨747523221171,747523240501⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22774896,34185711⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22774656,22774720⟩ : DyadicInterval 40),(⟨-22775168,-22775104⟩ : DyadicInterval 40),(⟨762123383336,762123402665⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34185152,34185216⟩ : DyadicInterval 40),(⟨-34186304,-34186240⟩ : DyadicInterval 40),(⟨762123383065,762123402394⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178681283557,178806402927⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165565764800,165565764864⟩ : DyadicInterval 40),(⟨-194993521216,-194993521152⟩ : DyadicInterval 40),(⟨747540074537,747540093867⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165673388224,165673388288⟩ : DyadicInterval 40),(⟨-195142929344,-195142929280⟩ : DyadicInterval 40),(⟨747519552212,747519571541⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29469541120,-29427756288⟩ : DyadicInterval 40),(⟨776837261760,776858173440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165594593088,165692607616⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195169614272,-195033538560⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2523_ok : ecellOkT e2523 = true := by decide +kernel
theorem e2523_pos {a z : ℝ} (ha1 : ((1331529/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((666189/4096000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2523 e2523_ok ha1 ha2 hz1 hz2 hz

-- box ['666189/4096000', '1333227/8192000', '1999/2000', '7997/8000']  interval_lower 123622483/549755813888
noncomputable def e2524 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278340375773,0,true,165692607552,165692607616⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920682879779,0,false,-195169614272,-195169614208⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278454326625,0,true,165790613312,165790613376⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920568928927,0,false,-195305706816,-195305706752⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278250961398,0,true,165615698816,165615698880⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920772294154,0,false,-195062837696,-195062837632⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278387223113,0,true,165732900672,165732900736⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920636032439,0,false,-195225562432,-195225562368⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545812803,0,true,34184448,34184512⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477442749,0,false,-34185600,-34185536⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557238710,0,true,45609984,45610048⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466016842,0,false,-45611904,-45611840⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625883,0,false,-1920,-1856⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626714,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278295664115,0,true,165654150016,165654150080⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920727591437,0,false,-195116219392,-195116219328⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278420783460,0,true,165761764736,165761764800⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920602472092,0,false,-195265644160,-195265644096⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070400079358,0,false,-29503879360,-29503879296⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070440783192,0,false,-29462069312,-29462069248⟩
    { al := (666189/4096000), au := (1333227/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨178828747997,178942698849⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165692607552,165692607616⟩ : DyadicInterval 40),(⟨-195169614272,-195169614208⟩ : DyadicInterval 40),(⟨747515885606,747515904936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165790613312,165790613376⟩ : DyadicInterval 40),(⟨-195305706816,-195305706752⟩ : DyadicInterval 40),(⟨747497180084,747497199413⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165615698816,165615698880⟩ : DyadicInterval 40),(⟨-195062837696,-195062837632⟩ : DyadicInterval 40),(⟨747530554856,747530574186⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165732900672,165732900736⟩ : DyadicInterval 40),(⟨-195225562432,-195225562368⟩ : DyadicInterval 40),(⟨747508196850,747508216179⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34185027,45610934⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34184448,34184512⟩ : DyadicInterval 40),(⟨-34185600,-34185536⟩ : DyadicInterval 40),(⟨762123383065,762123402394⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45609984,45610048⟩ : DyadicInterval 40),(⟨-45611904,-45611840⟩ : DyadicInterval 40),(⟨762123382619,762123401948⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1920,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178784036339,178909155684⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165654150016,165654150080⟩ : DyadicInterval 40),(⟨-195116219392,-195116219328⟩ : DyadicInterval 40),(⟨747523221913,747523241243⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165761764736,165761764800⟩ : DyadicInterval 40),(⟨-195265644160,-195265644096⟩ : DyadicInterval 40),(⟨747502687598,747502706928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29503879360,-29462069248⟩ : DyadicInterval 40),(⟨776854418240,776875342560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165692607552,165790613376⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195305706816,-195169614208⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2524_ok : ecellOkT e2524 = true := by decide +kernel
theorem e2524_pos {a z : ℝ} (ha1 : ((666189/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1333227/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2524 e2524_ok ha1 ha2 hz1 hz2 hz

-- box ['1333227/8192000', '333519/2048000', '1999/2000', '7997/8000']  interval_lower 31063995/137438953472
noncomputable def e2525 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278454326624,0,true,165790613312,165790613376⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920568928928,0,false,-195305706816,-195305706752⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278568277476,0,true,165888610368,165888610432⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920454978076,0,false,-195441816128,-195441816064⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278364855274,0,true,165713662400,165713662464⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920658400278,0,false,-195198848960,-195198848896⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278501131233,0,true,165830866048,165830866112⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920522124319,0,false,-195361610816,-195361610752⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545835442,0,true,34207104,34207168⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477420110,0,false,-34208256,-34208192⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557268898,0,true,45640128,45640192⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465986654,0,false,-45642112,-45642048⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625881,0,false,-1920,-1856⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626712,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278409586475,0,true,165752134720,165752134784⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920613669077,0,false,-195252271232,-195252271168⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278534712950,0,true,165859745984,165859746048⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920488542602,0,false,-195401723008,-195401722944⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070362991039,0,false,-29541977024,-29541976960⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070403723123,0,false,-29500136512,-29500136448⟩
    { al := (1333227/8192000), au := (333519/2048000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨178942698848,179056649700⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165790613312,165790613376⟩ : DyadicInterval 40),(⟨-195305706816,-195305706752⟩ : DyadicInterval 40),(⟨747497180084,747497199413⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165888610368,165888610432⟩ : DyadicInterval 40),(⟨-195441816128,-195441816064⟩ : DyadicInterval 40),(⟨747478462380,747478481709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165713662400,165713662464⟩ : DyadicInterval 40),(⟨-195198848960,-195198848896⟩ : DyadicInterval 40),(⟨747511868212,747511887541⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165830866048,165830866112⟩ : DyadicInterval 40),(⟨-195361610816,-195361610752⟩ : DyadicInterval 40),(⟨747489493366,747489512695⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34207666,45641122⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34207104,34207168⟩ : DyadicInterval 40),(⟨-34208256,-34208192⟩ : DyadicInterval 40),(⟨762123383063,762123402392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45640128,45640192⟩ : DyadicInterval 40),(⟨-45642112,-45642048⟩ : DyadicInterval 40),(⟨762123382649,762123401978⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1920,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178897958699,179023085174⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165752134720,165752134784⟩ : DyadicInterval 40),(⟨-195252271232,-195252271168⟩ : DyadicInterval 40),(⟨747504525788,747504545118⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165859745984,165859746048⟩ : DyadicInterval 40),(⟨-195401723008,-195401722944⟩ : DyadicInterval 40),(⟨747483976984,747483996314⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29541977024,-29500136448⟩ : DyadicInterval 40),(⟨776873451840,776894391392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165790613312,165888610432⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195441816128,-195305706752⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2525_ok : ecellOkT e2525 = true := by decide +kernel
theorem e2525_pos {a z : ℝ} (ha1 : ((1333227/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((333519/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2525 e2525_ok ha1 ha2 hz1 hz2 hz

-- box ['666189/4096000', '1333227/8192000', '7997/8000', '3999/4000']  interval_lower 247064017/1099511627776
noncomputable def e2526 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278340375773,0,true,165692607552,165692607616⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920682879779,0,false,-195169614272,-195169614208⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278454326625,0,true,165790613312,165790613376⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920568928927,0,false,-195305706816,-195305706752⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278273314992,0,true,165634926528,165634926592⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920749940560,0,false,-195089530880,-195089530816⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278409590951,0,true,165752138560,165752138624⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920613664601,0,false,-195252276608,-195252276544⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534417764,0,true,22789696,22789760⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488837788,0,false,-22790272,-22790208⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545836125,0,true,34207808,34207872⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477419427,0,false,-34208896,-34208832⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626711,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627304,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278306840819,0,true,165663763520,165663763584⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920716414733,0,false,-195129566400,-195129566336⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278431967310,0,true,165771383424,165771383488⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920591288242,0,false,-195279001536,-195279001472⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070396439641,0,false,-29507618112,-29507618048⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070437148344,0,false,-29465802880,-29465802816⟩
    { al := (666189/4096000), au := (1333227/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨178828747997,178942698849⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165692607552,165692607616⟩ : DyadicInterval 40),(⟨-195169614272,-195169614208⟩ : DyadicInterval 40),(⟨747515885606,747515904936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165790613312,165790613376⟩ : DyadicInterval 40),(⟨-195305706816,-195305706752⟩ : DyadicInterval 40),(⟨747497180084,747497199413⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165634926528,165634926592⟩ : DyadicInterval 40),(⟨-195089530880,-195089530816⟩ : DyadicInterval 40),(⟨747526888235,747526907565⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165752138560,165752138624⟩ : DyadicInterval 40),(⟨-195252276608,-195252276544⟩ : DyadicInterval 40),(⟨747504525072,747504544401⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22789988,34208349⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22789696,22789760⟩ : DyadicInterval 40),(⟨-22790272,-22790208⟩ : DyadicInterval 40),(⟨762123383367,762123402696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34207808,34207872⟩ : DyadicInterval 40),(⟨-34208896,-34208832⟩ : DyadicInterval 40),(⟨762123383031,762123402360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178795213043,178920339534⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165663763520,165663763584⟩ : DyadicInterval 40),(⟨-195129566400,-195129566336⟩ : DyadicInterval 40),(⟨747521388180,747521407510⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165771383424,165771383488⟩ : DyadicInterval 40),(⟨-195279001536,-195279001472⟩ : DyadicInterval 40),(⟨747500851405,747500870735⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29507618112,-29465802816⟩ : DyadicInterval 40),(⟨776856285024,776877211936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165692607552,165790613376⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195305706816,-195169614208⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2526_ok : ecellOkT e2526 = true := by decide +kernel
theorem e2526_pos {a z : ℝ} (ha1 : ((666189/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1333227/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2526 e2526_ok ha1 ha2 hz1 hz2 hz

-- box ['1333227/8192000', '333519/2048000', '7997/8000', '3999/4000']  interval_lower 124165149/549755813888
noncomputable def e2527 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278454326624,0,true,165790613312,165790613376⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920568928928,0,false,-195305706816,-195305706752⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278568277476,0,true,165888610368,165888610432⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920454978076,0,false,-195441816128,-195441816064⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278387223111,0,true,165732900672,165732900736⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920636032441,0,false,-195225562432,-195225562368⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278523513314,0,true,165850114496,165850114560⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920499742238,0,false,-195388345280,-195388345216⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534432857,0,true,22804800,22804864⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488822695,0,false,-22805376,-22805312⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545858766,0,true,34230400,34230464⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477396786,0,false,-34231552,-34231488⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626710,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627303,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278420770301,0,true,165761753408,165761753472⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920602485251,0,false,-195265628416,-195265628352⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278545903924,0,true,165869369920,165869369984⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920477351628,0,false,-195415090560,-195415090496⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070359346684,0,false,-29545720640,-29545720576⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070400083641,0,false,-29503874944,-29503874880⟩
    { al := (1333227/8192000), au := (333519/2048000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨178942698848,179056649700⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165790613312,165790613376⟩ : DyadicInterval 40),(⟨-195305706816,-195305706752⟩ : DyadicInterval 40),(⟨747497180084,747497199413⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165888610368,165888610432⟩ : DyadicInterval 40),(⟨-195441816128,-195441816064⟩ : DyadicInterval 40),(⟨747478462380,747478481709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165732900672,165732900736⟩ : DyadicInterval 40),(⟨-195225562432,-195225562368⟩ : DyadicInterval 40),(⟨747508196850,747508216179⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165850114496,165850114560⟩ : DyadicInterval 40),(⟨-195388345280,-195388345216⟩ : DyadicInterval 40),(⟨747485816840,747485836170⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22805081,34230990⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22804800,22804864⟩ : DyadicInterval 40),(⟨-22805376,-22805312⟩ : DyadicInterval 40),(⟨762123383366,762123402696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34230400,34230464⟩ : DyadicInterval 40),(⟨-34231552,-34231488⟩ : DyadicInterval 40),(⟨762123383062,762123402391⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178909142525,179034276148⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165761753408,165761753472⟩ : DyadicInterval 40),(⟨-195265628416,-195265628352⟩ : DyadicInterval 40),(⟨747502689753,747502709083⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165869369920,165869369984⟩ : DyadicInterval 40),(⟨-195415090560,-195415090496⟩ : DyadicInterval 40),(⟨747482138448,747482157778⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29545720640,-29503874880⟩ : DyadicInterval 40),(⟨776875321056,776896263200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165790613312,165888610432⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195441816128,-195305706752⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2527_ok : ecellOkT e2527 = true := by decide +kernel
theorem e2527_pos {a z : ℝ} (ha1 : ((1333227/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((333519/2048000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2527 e2527_ok ha1 ha2 hz1 hz2 hz

-- box ['33267/204800', '1331529/8192000', '3999/4000', '7999/8000']  interval_lower 244359887/1099511627776
noncomputable def e2528 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278112474071,0,true,165496569856,165496569920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920910781481,0,false,-194897479808,-194897479744⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278226424923,0,true,165594593088,165594593152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920796830629,0,false,-195033538624,-195033538560⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278067823859,0,true,165458158336,165458158400⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920955431693,0,false,-194844171456,-194844171392⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278204085574,0,true,165575376960,165575377024⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920819169978,0,false,-195006863808,-195006863744⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523007578,0,true,11379712,11379776⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500247974,0,false,-11379904,-11379840⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534403300,0,true,22775232,22775296⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488852252,0,false,-22775808,-22775744⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627304,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627659,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278090144337,0,true,165477360256,165477360320⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920933111215,0,false,-194870819776,-194870819712⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278215263733,0,true,165584992384,165584992448⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920807991819,0,false,-195020211264,-195020211200⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070466924020,0,false,-29435218880,-29435218816⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070507581097,0,false,-29393459456,-29393459392⟩
    { al := (33267/204800), au := (1331529/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨178600846295,178714797147⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165496569856,165496569920⟩ : DyadicInterval 40),(⟨-194897479808,-194897479744⟩ : DyadicInterval 40),(⟨747553260280,747553279609⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165594593088,165594593152⟩ : DyadicInterval 40),(⟨-195033538624,-195033538560⟩ : DyadicInterval 40),(⟨747534579000,747534598330⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165458158336,165458158400⟩ : DyadicInterval 40),(⟨-194844171456,-194844171392⟩ : DyadicInterval 40),(⟨747560576975,747560596304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165575376960,165575377024⟩ : DyadicInterval 40),(⟨-195006863808,-195006863744⟩ : DyadicInterval 40),(⟨747538242285,747538261615⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11379802,22775524⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11379712,11379776⟩ : DyadicInterval 40),(⟨-11379904,-11379840⟩ : DyadicInterval 40),(⟨762123383530,762123402859⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22775232,22775296⟩ : DyadicInterval 40),(⟨-22775808,-22775744⟩ : DyadicInterval 40),(⟨762123383368,762123402697⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178578516561,178703635957⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165477360256,165477360320⟩ : DyadicInterval 40),(⟨-194870819776,-194870819712⟩ : DyadicInterval 40),(⟨747556919631,747556938960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165584992384,165584992448⟩ : DyadicInterval 40),(⟨-195020211264,-195020211200⟩ : DyadicInterval 40),(⟨747536409297,747536428627⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29435218880,-29393459392⟩ : DyadicInterval 40),(⟨776820113312,776841012320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165496569856,165594593152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195033538624,-194897479744⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2528_ok : ecellOkT e2528 = true := by decide +kernel
theorem e2528_pos {a z : ℝ} (ha1 : ((33267/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1331529/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2528 e2528_ok ha1 ha2 hz1 hz2 hz

-- box ['1331529/8192000', '666189/4096000', '3999/4000', '7999/8000']  interval_lower 245620023/1099511627776
noncomputable def e2529 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278226424922,0,true,165594593088,165594593152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920796830630,0,false,-195033538624,-195033538560⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278340375774,0,true,165692607552,165692607616⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920682879778,0,false,-195169614272,-195169614208⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278181746222,0,true,165556160448,165556160512⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920841509330,0,false,-194980189696,-194980189632⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278318022181,0,true,165673380864,165673380928⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920705233371,0,false,-195142919168,-195142919104⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523015123,0,true,11387264,11387328⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500240429,0,false,-11387456,-11387392⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534418392,0,true,22790336,22790400⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488837160,0,false,-22790912,-22790848⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627303,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627659,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278204080940,0,true,165575372992,165575373056⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920819174612,0,false,-195006858304,-195006858240⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278329207459,0,true,165683001600,165683001664⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920694048093,0,false,-195156276800,-195156276736⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070429873662,0,false,-29473275200,-29473275136⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070470558986,0,false,-29431485312,-29431485248⟩
    { al := (1331529/8192000), au := (666189/4096000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨178714797146,178828747998⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165594593088,165594593152⟩ : DyadicInterval 40),(⟨-195033538624,-195033538560⟩ : DyadicInterval 40),(⟨747534579001,747534598330⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165692607552,165692607616⟩ : DyadicInterval 40),(⟨-195169614272,-195169614208⟩ : DyadicInterval 40),(⟨747515885606,747515904935⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165556160448,165556160512⟩ : DyadicInterval 40),(⟨-194980189696,-194980189632⟩ : DyadicInterval 40),(⟨747541905157,747541924486⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165673380864,165673380928⟩ : DyadicInterval 40),(⟨-195142919168,-195142919104⟩ : DyadicInterval 40),(⟨747519553628,747519572958⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11387347,22790616⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11387264,11387328⟩ : DyadicInterval 40),(⟨-11387456,-11387392⟩ : DyadicInterval 40),(⟨762123383530,762123402859⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22790336,22790400⟩ : DyadicInterval 40),(⟨-22790912,-22790848⟩ : DyadicInterval 40),(⟨762123383367,762123402696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178692453164,178817579683⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165575372992,165575373056⟩ : DyadicInterval 40),(⟨-195006858304,-195006858240⟩ : DyadicInterval 40),(⟨747538243047,747538262376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165683001600,165683001664⟩ : DyadicInterval 40),(⟨-195156276800,-195156276736⟩ : DyadicInterval 40),(⟨747517718265,747517737595⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29473275200,-29431485248⟩ : DyadicInterval 40),(⟨776839126240,776860040480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165594593088,165692607616⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195169614272,-195033538560⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2529_ok : ecellOkT e2529 = true := by decide +kernel
theorem e2529_pos {a z : ℝ} (ha1 : ((1331529/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((666189/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2529 e2529_ok ha1 ha2 hz1 hz2 hz

-- box ['33267/204800', '1331529/8192000', '7999/8000', '1']  interval_lower 61044909/274877906944
noncomputable def e2530 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278112474071,0,true,165496569856,165496569920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920910781481,0,false,-194897479808,-194897479744⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278226424923,0,true,165594593088,165594593152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920796830629,0,false,-195033538624,-195033538560⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278090148965,0,true,165477364288,165477364352⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920933106587,0,false,-194870825280,-194870825216⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523015694,0,true,11387840,11387904⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500239858,0,false,-11388032,-11387968⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627658,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1278101306852,0,true,165486963072,165486963136⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨920921948700,0,false,-194884146880,-194884146816⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1278226433392,0,true,165594600384,165594600448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨920796822160,0,false,-195033548736,-195033548672⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1070463293097,0,false,-29438948352,-29438948288⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1070503955036,0,false,-29397183744,-29397183680⟩
    { al := (33267/204800), au := (1331529/8192000), zl := (7999/8000), zu := 1,
      A := ⟨178600846295,178714797147⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165496569856,165496569920⟩ : DyadicInterval 40),(⟨-194897479808,-194897479744⟩ : DyadicInterval 40),(⟨747553260280,747553279609⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165594593088,165594593152⟩ : DyadicInterval 40),(⟨-195033538624,-195033538560⟩ : DyadicInterval 40),(⟨747534579000,747534598330⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165477364288,165477364352⟩ : DyadicInterval 40),(⟨-194870825280,-194870825216⟩ : DyadicInterval 40),(⟨747556918834,747556938163⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165594593088,165594593152⟩ : DyadicInterval 40),(⟨-195033538624,-195033538560⟩ : DyadicInterval 40),(⟨747534579000,747534598330⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11387918⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11387840,11387904⟩ : DyadicInterval 40),(⟨-11388032,-11387968⟩ : DyadicInterval 40),(⟨762123383530,762123402859⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨178589679076,178714805616⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165486963072,165486963136⟩ : DyadicInterval 40),(⟨-194884146880,-194884146816⟩ : DyadicInterval 40),(⟨747555090391,747555109720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165594600384,165594600448⟩ : DyadicInterval 40),(⟨-195033548736,-195033548672⟩ : DyadicInterval 40),(⟨747534577605,747534596934⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29438948352,-29397183680⟩ : DyadicInterval 40),(⟨776821975456,776842877056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨165496569856,165594593152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195033538624,-194897479744⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2530_ok : ecellOkT e2530 = true := by decide +kernel
theorem e2530_pos {a z : ℝ} (ha1 : ((33267/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1331529/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2530 e2530_ok ha1 ha2 hz1 hz2 hz

-- box ['1331529/8192000', '666189/4096000', '7999/8000', '1']  interval_lower 30679901/137438953472
noncomputable def e2531 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278226424922,0,true,165594593088,165594593152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920796830630,0,false,-195033538624,-195033538560⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278340375774,0,true,165692607552,165692607616⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920682879778,0,false,-195169614272,-195169614208⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278204085572,0,true,165575376960,165575377024⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920819169980,0,false,-195006863808,-195006863744⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523023240,0,true,11395392,11395456⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500232312,0,false,-11395584,-11395520⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627657,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1278215250579,0,true,165584981056,165584981120⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨920808004973,0,false,-195020195584,-195020195520⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1278340384242,0,true,165692614848,165692614912⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨920682871310,0,false,-195169624384,-195169624320⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1070426238107,0,false,-29477009536,-29477009472⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1070466928297,0,false,-29435214464,-29435214400⟩
    { al := (1331529/8192000), au := (666189/4096000), zl := (7999/8000), zu := 1,
      A := ⟨178714797146,178828747998⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165594593088,165594593152⟩ : DyadicInterval 40),(⟨-195033538624,-195033538560⟩ : DyadicInterval 40),(⟨747534579001,747534598330⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165692607552,165692607616⟩ : DyadicInterval 40),(⟨-195169614272,-195169614208⟩ : DyadicInterval 40),(⟨747515885606,747515904935⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165575376960,165575377024⟩ : DyadicInterval 40),(⟨-195006863808,-195006863744⟩ : DyadicInterval 40),(⟨747538242286,747538261615⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165692607552,165692607616⟩ : DyadicInterval 40),(⟨-195169614272,-195169614208⟩ : DyadicInterval 40),(⟨747515885606,747515904935⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11395464⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11395392,11395456⟩ : DyadicInterval 40),(⟨-11395584,-11395520⟩ : DyadicInterval 40),(⟨762123383529,762123402858⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨178703622803,178828756466⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165584981056,165584981120⟩ : DyadicInterval 40),(⟨-195020195584,-195020195520⟩ : DyadicInterval 40),(⟨747536411473,747536430803⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165692614848,165692614912⟩ : DyadicInterval 40),(⟨-195169624384,-195169624320⟩ : DyadicInterval 40),(⟨747515884208,747515903538⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29477009536,-29435214400⟩ : DyadicInterval 40),(⟨776840990816,776861907648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨165594593088,165692607616⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195169614272,-195033538560⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2531_ok : ecellOkT e2531 = true := by decide +kernel
theorem e2531_pos {a z : ℝ} (ha1 : ((1331529/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((666189/4096000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2531 e2531_ok ha1 ha2 hz1 hz2 hz

-- box ['666189/4096000', '1333227/8192000', '3999/4000', '7999/8000']  interval_lower 123441323/549755813888
noncomputable def e2532 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278340375773,0,true,165692607552,165692607616⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920682879779,0,false,-195169614272,-195169614208⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278454326625,0,true,165790613312,165790613376⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920568928927,0,false,-195305706816,-195305706752⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278295668585,0,true,165654153856,165654153920⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920727586967,0,false,-195116224704,-195116224640⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278431958788,0,true,165771376128,165771376192⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920591296764,0,false,-195278991360,-195278991296⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523022669,0,true,11394816,11394880⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500232883,0,false,-11395008,-11394944⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534433484,0,true,22805440,22805504⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488822068,0,false,-22805952,-22805888⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627302,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627658,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278318017546,0,true,165673376896,165673376960⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920705238006,0,false,-195142913664,-195142913600⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278443151190,0,true,165781002048,165781002112⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920580104362,0,false,-195292359104,-195292359040⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070392799686,0,false,-29511357056,-29511356992⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070433513262,0,false,-29469536704,-29469536640⟩
    { al := (666189/4096000), au := (1333227/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨178828747997,178942698849⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165692607552,165692607616⟩ : DyadicInterval 40),(⟨-195169614272,-195169614208⟩ : DyadicInterval 40),(⟨747515885606,747515904936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165790613312,165790613376⟩ : DyadicInterval 40),(⟨-195305706816,-195305706752⟩ : DyadicInterval 40),(⟨747497180084,747497199413⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165654153856,165654153920⟩ : DyadicInterval 40),(⟨-195116224704,-195116224640⟩ : DyadicInterval 40),(⟨747523221172,747523240501⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165771376128,165771376192⟩ : DyadicInterval 40),(⟨-195278991360,-195278991296⟩ : DyadicInterval 40),(⟨747500852786,747500872116⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11394893,22805708⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11394816,11394880⟩ : DyadicInterval 40),(⟨-11395008,-11394944⟩ : DyadicInterval 40),(⟨762123383529,762123402858⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22805440,22805504⟩ : DyadicInterval 40),(⟨-22805952,-22805888⟩ : DyadicInterval 40),(⟨762123383334,762123402663⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178806389770,178931523414⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165673376896,165673376960⟩ : DyadicInterval 40),(⟨-195142913664,-195142913600⟩ : DyadicInterval 40),(⟨747519554391,747519573720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165781002048,165781002112⟩ : DyadicInterval 40),(⟨-195292359104,-195292359040⟩ : DyadicInterval 40),(⟨747499015091,747499034421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29511357056,-29469536640⟩ : DyadicInterval 40),(⟨776858151936,776879081408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165692607552,165790613376⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195305706816,-195169614208⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2532_ok : ecellOkT e2532 = true := by decide +kernel
theorem e2532_pos {a z : ℝ} (ha1 : ((666189/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1333227/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2532 e2532_ok ha1 ha2 hz1 hz2 hz

-- box ['1333227/8192000', '333519/2048000', '3999/4000', '7999/8000']  interval_lower 248148545/1099511627776
noncomputable def e2533 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278454326624,0,true,165790613312,165790613376⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920568928928,0,false,-195305706816,-195305706752⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278568277476,0,true,165888610368,165888610432⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920454978076,0,false,-195441816128,-195441816064⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278409590949,0,true,165752138560,165752138624⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920613664603,0,false,-195252276608,-195252276544⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278545895395,0,true,165869362560,165869362624⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920477360157,0,false,-195415080384,-195415080320⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523030216,0,true,11402368,11402432⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500225336,0,false,-11402560,-11402496⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534448578,0,true,22820544,22820608⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488806974,0,false,-22821056,-22820992⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627302,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627658,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278431954150,0,true,165771372096,165771372160⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920591301402,0,false,-195278985856,-195278985792⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278557094922,0,true,165878993792,165878993856⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920466160630,0,false,-195428458304,-195428458240⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070355702094,0,false,-29549464512,-29549464448⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070396443925,0,false,-29507613696,-29507613632⟩
    { al := (1333227/8192000), au := (333519/2048000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨178942698848,179056649700⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165790613312,165790613376⟩ : DyadicInterval 40),(⟨-195305706816,-195305706752⟩ : DyadicInterval 40),(⟨747497180084,747497199413⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165888610368,165888610432⟩ : DyadicInterval 40),(⟨-195441816128,-195441816064⟩ : DyadicInterval 40),(⟨747478462380,747478481709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165752138560,165752138624⟩ : DyadicInterval 40),(⟨-195252276608,-195252276544⟩ : DyadicInterval 40),(⟨747504525072,747504544402⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165869362560,165869362624⟩ : DyadicInterval 40),(⟨-195415080384,-195415080320⟩ : DyadicInterval 40),(⟨747482139870,747482159199⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11402440,22820802⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11402368,11402432⟩ : DyadicInterval 40),(⟨-11402560,-11402496⟩ : DyadicInterval 40),(⟨762123383529,762123402858⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22820544,22820608⟩ : DyadicInterval 40),(⟨-22821056,-22820992⟩ : DyadicInterval 40),(⟨762123383334,762123402663⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178920326374,179045467146⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165771372096,165771372160⟩ : DyadicInterval 40),(⟨-195278985856,-195278985792⟩ : DyadicInterval 40),(⟨747500853588,747500872917⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165878993792,165878993856⟩ : DyadicInterval 40),(⟨-195428458304,-195428458240⟩ : DyadicInterval 40),(⟨747480299793,747480319122⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29549464512,-29507613632⟩ : DyadicInterval 40),(⟨776877190432,776898135136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165790613312,165888610432⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195441816128,-195305706752⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2533_ok : ecellOkT e2533 = true := by decide +kernel
theorem e2533_pos {a z : ℝ} (ha1 : ((1333227/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((333519/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2533 e2533_ok ha1 ha2 hz1 hz2 hz

-- box ['666189/4096000', '1333227/8192000', '7999/8000', '1']  interval_lower 246701725/1099511627776
noncomputable def e2534 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278340375773,0,true,165692607552,165692607616⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920682879779,0,false,-195169614272,-195169614208⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278454326625,0,true,165790613312,165790613376⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920568928927,0,false,-195305706816,-195305706752⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278318022179,0,true,165673380864,165673380928⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920705233373,0,false,-195142919168,-195142919104⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523030787,0,true,11402944,11403008⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500224765,0,false,-11403072,-11403008⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627657,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1278329194302,0,true,165682990272,165682990336⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨920694061250,0,false,-195156261056,-195156260992⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1278454335091,0,true,165790620608,165790620672⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨920568920461,0,false,-195305716928,-195305716864⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1070389159497,0,false,-29515096256,-29515096192⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1070429877943,0,false,-29473270784,-29473270720⟩
    { al := (666189/4096000), au := (1333227/8192000), zl := (7999/8000), zu := 1,
      A := ⟨178828747997,178942698849⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165692607552,165692607616⟩ : DyadicInterval 40),(⟨-195169614272,-195169614208⟩ : DyadicInterval 40),(⟨747515885606,747515904936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165790613312,165790613376⟩ : DyadicInterval 40),(⟨-195305706816,-195305706752⟩ : DyadicInterval 40),(⟨747497180084,747497199413⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165673380864,165673380928⟩ : DyadicInterval 40),(⟨-195142919168,-195142919104⟩ : DyadicInterval 40),(⟨747519553628,747519572958⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165790613312,165790613376⟩ : DyadicInterval 40),(⟨-195305706816,-195305706752⟩ : DyadicInterval 40),(⟨747497180084,747497199413⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11403011⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11402944,11403008⟩ : DyadicInterval 40),(⟨-11403072,-11403008⟩ : DyadicInterval 40),(⟨762123383497,762123402826⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨178817566526,178942707315⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165682990272,165682990336⟩ : DyadicInterval 40),(⟨-195156261056,-195156260992⟩ : DyadicInterval 40),(⟨747517720417,747517739747⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165790620608,165790620672⟩ : DyadicInterval 40),(⟨-195305716928,-195305716864⟩ : DyadicInterval 40),(⟨747497178685,747497198014⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29515096256,-29473270720⟩ : DyadicInterval 40),(⟨776860018976,776880951008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨165692607552,165790613376⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195305706816,-195169614208⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2534_ok : ecellOkT e2534 = true := by decide +kernel
theorem e2534_pos {a z : ℝ} (ha1 : ((666189/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1333227/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2534 e2534_ok ha1 ha2 hz1 hz2 hz

-- box ['1333227/8192000', '333519/2048000', '7999/8000', '1']  interval_lower 61991749/274877906944
noncomputable def e2535 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278454326624,0,true,165790613312,165790613376⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920568928928,0,false,-195305706816,-195305706752⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278568277476,0,true,165888610368,165888610432⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920454978076,0,false,-195441816128,-195441816064⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278431958786,0,true,165771376128,165771376192⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920591296766,0,false,-195278991360,-195278991296⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523038334,0,true,11410496,11410560⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500217218,0,false,-11410624,-11410560⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627657,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1278443138031,0,true,165780990720,165780990784⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨920580117521,0,false,-195292343424,-195292343360⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1278568285953,0,true,165888617600,165888617664⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨920454969599,0,false,-195441826304,-195441826240⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1070352057265,0,false,-29553208640,-29553208576⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1070392803970,0,false,-29511352640,-29511352576⟩
    { al := (1333227/8192000), au := (333519/2048000), zl := (7999/8000), zu := 1,
      A := ⟨178942698848,179056649700⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165790613312,165790613376⟩ : DyadicInterval 40),(⟨-195305706816,-195305706752⟩ : DyadicInterval 40),(⟨747497180084,747497199413⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165888610368,165888610432⟩ : DyadicInterval 40),(⟨-195441816128,-195441816064⟩ : DyadicInterval 40),(⟨747478462380,747478481709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165771376128,165771376192⟩ : DyadicInterval 40),(⟨-195278991360,-195278991296⟩ : DyadicInterval 40),(⟨747500852787,747500872116⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165888610368,165888610432⟩ : DyadicInterval 40),(⟨-195441816128,-195441816064⟩ : DyadicInterval 40),(⟨747478462380,747478481709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11410558⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11410496,11410560⟩ : DyadicInterval 40),(⟨-11410624,-11410560⟩ : DyadicInterval 40),(⟨762123383497,762123402826⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨178931510255,179056658177⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165780990720,165780990784⟩ : DyadicInterval 40),(⟨-195292343424,-195292343360⟩ : DyadicInterval 40),(⟨747499017274,747499036603⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165888617600,165888617664⟩ : DyadicInterval 40),(⟨-195441826304,-195441826240⟩ : DyadicInterval 40),(⟨747478461041,747478480371⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29553208640,-29511352576⟩ : DyadicInterval 40),(⟨776879059904,776900007200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨165790613312,165888610432⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195441816128,-195305706752⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2535_ok : ecellOkT e2535 = true := by decide +kernel
theorem e2535_pos {a z : ℝ} (ha1 : ((1333227/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((333519/2048000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2535 e2535_ok ha1 ha2 hz1 hz2 hz

-- box ['333519/2048000', '53397/327680', '1999/2000', '7997/8000']  interval_lower 124890883/549755813888
noncomputable def e2536 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278568277475,0,true,165888610368,165888610432⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920454978077,0,false,-195441816128,-195441816064⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278682228327,0,true,165986598592,165986598656⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920341027225,0,false,-195577942336,-195577942272⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278478749150,0,true,165811617280,165811617344⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920544506402,0,false,-195334877056,-195334876992⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278615039352,0,true,165928822720,165928822784⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920408216200,0,false,-195497676032,-195497675968⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545858081,0,true,34229760,34229824⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477397471,0,false,-34230848,-34230784⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557299088,0,true,45670336,45670400⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465956464,0,false,-45672320,-45672256⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625878,0,false,-1920,-1856⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626711,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278523508840,0,true,165850110656,165850110720⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920499746712,0,false,-195388339968,-195388339904⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278648642433,0,true,165957718464,165957718528⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920374613119,0,false,-195537818752,-195537818688⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070325879113,0,false,-29580100288,-29580100224⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070366639445,0,false,-29538229312,-29538229248⟩
    { al := (333519/2048000), au := (53397/327680), zl := (1999/2000), zu := (7997/8000),
      A := ⟨179056649699,179170600551⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165888610368,165888610432⟩ : DyadicInterval 40),(⟨-195441816128,-195441816064⟩ : DyadicInterval 40),(⟨747478462380,747478481709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165986598592,165986598656⟩ : DyadicInterval 40),(⟨-195577942336,-195577942272⟩ : DyadicInterval 40),(⟨747459732621,747459751950⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165811617280,165811617344⟩ : DyadicInterval 40),(⟨-195334877056,-195334876992⟩ : DyadicInterval 40),(⟨747493169436,747493188766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165928822720,165928822784⟩ : DyadicInterval 40),(⟨-195497676032,-195497675968⟩ : DyadicInterval 40),(⟨747470777744,747470797074⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34230305,45671312⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34229760,34229824⟩ : DyadicInterval 40),(⟨-34230848,-34230784⟩ : DyadicInterval 40),(⟨762123383030,762123402359⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45670336,45670400⟩ : DyadicInterval 40),(⟨-45672320,-45672256⟩ : DyadicInterval 40),(⟨762123382646,762123401975⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1920,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179011881064,179137014657⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165850110656,165850110720⟩ : DyadicInterval 40),(⟨-195388339968,-195388339904⟩ : DyadicInterval 40),(⟨747485817584,747485836914⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165957718464,165957718528⟩ : DyadicInterval 40),(⟨-195537818752,-195537818688⟩ : DyadicInterval 40),(⟨747465254289,747465273618⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29580100288,-29538229248⟩ : DyadicInterval 40),(⟨776892498240,776913453024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165888610368,165986598656⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195577942336,-195441816064⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2536_ok : ecellOkT e2536 = true := by decide +kernel
theorem e2536_pos {a z : ℝ} (ha1 : ((333519/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((53397/327680 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2536 e2536_ok ha1 ha2 hz1 hz2 hz

-- box ['53397/327680', '667887/4096000', '1999/2000', '7997/8000']  interval_lower 31381787/137438953472
noncomputable def e2537 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278682228326,0,true,165986598592,165986598656⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920341027226,0,false,-195577942336,-195577942272⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278796179178,0,true,166084578176,166084578240⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920227076374,0,false,-195714085440,-195714085376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278592643025,0,true,165909563392,165909563456⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920430612527,0,false,-195470921920,-195470921856⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278728947472,0,true,166026770688,166026770752⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920294308080,0,false,-195633758144,-195633758080⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545880724,0,true,34252352,34252416⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477374828,0,false,-34253504,-34253440⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557329279,0,true,45700544,45700608⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465926273,0,false,-45702464,-45702400⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625876,0,false,-1920,-1856⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626709,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278637431197,0,true,165948077824,165948077888⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920385824355,0,false,-195524425472,-195524425408⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278762571917,0,true,166055682176,166055682240⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920260683635,0,false,-195673931328,-195673931264⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070288743575,0,false,-29618249088,-29618249024⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070329532162,0,false,-29576347648,-29576347584⟩
    { al := (53397/327680), au := (667887/4096000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨179170600550,179284551402⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165986598592,165986598656⟩ : DyadicInterval 40),(⟨-195577942336,-195577942272⟩ : DyadicInterval 40),(⟨747459732621,747459751950⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166084578176,166084578240⟩ : DyadicInterval 40),(⟨-195714085440,-195714085376⟩ : DyadicInterval 40),(⟨747440990693,747441010022⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165909563392,165909563456⟩ : DyadicInterval 40),(⟨-195470921920,-195470921856⟩ : DyadicInterval 40),(⟨747474458541,747474477871⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166026770688,166026770752⟩ : DyadicInterval 40),(⟨-195633758144,-195633758080⟩ : DyadicInterval 40),(⟨747452050011,747452069340⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34252948,45701503⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34252352,34252416⟩ : DyadicInterval 40),(⟨-34253504,-34253440⟩ : DyadicInterval 40),(⟨762123383060,762123402389⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45700544,45700608⟩ : DyadicInterval 40),(⟨-45702464,-45702400⟩ : DyadicInterval 40),(⟨762123382612,762123401941⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1920,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179125803421,179250944141⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165948077824,165948077888⟩ : DyadicInterval 40),(⟨-195524425472,-195524425408⟩ : DyadicInterval 40),(⟨747467097248,747467116577⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166055682176,166055682240⟩ : DyadicInterval 40),(⟨-195673931328,-195673931264⟩ : DyadicInterval 40),(⟨747446519482,747446538811⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29618249088,-29576347584⟩ : DyadicInterval 40),(⟨776911557408,776932527424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165986598592,166084578240⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195714085440,-195577942272⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2537_ok : ecellOkT e2537 = true := by decide +kernel
theorem e2537_pos {a z : ℝ} (ha1 : ((53397/327680 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((667887/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2537 e2537_ok ha1 ha2 hz1 hz2 hz

-- box ['333519/2048000', '53397/327680', '7997/8000', '3999/4000']  interval_lower 62399939/274877906944
noncomputable def e2538 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278568277475,0,true,165888610368,165888610432⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920454978077,0,false,-195441816128,-195441816064⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278682228327,0,true,165986598592,165986598656⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920341027225,0,false,-195577942336,-195577942272⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278501131231,0,true,165830866048,165830866112⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920522124321,0,false,-195361610816,-195361610752⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278637435678,0,true,165948081664,165948081728⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920385819874,0,false,-195524430848,-195524430784⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534447951,0,true,22819904,22819968⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488807601,0,false,-22820416,-22820352⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545881408,0,true,34253056,34253120⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477374144,0,false,-34254208,-34254144⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626708,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627303,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278534699788,0,true,165859734656,165859734720⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920488555764,0,false,-195401707328,-195401707264⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278659840524,0,true,165967347648,165967347712⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920363415028,0,false,-195551196480,-195551196416⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070322230119,0,false,-29583848768,-29583848704⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070362995326,0,false,-29541972608,-29541972544⟩
    { al := (333519/2048000), au := (53397/327680), zl := (7997/8000), zu := (3999/4000),
      A := ⟨179056649699,179170600551⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165888610368,165888610432⟩ : DyadicInterval 40),(⟨-195441816128,-195441816064⟩ : DyadicInterval 40),(⟨747478462380,747478481709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165986598592,165986598656⟩ : DyadicInterval 40),(⟨-195577942336,-195577942272⟩ : DyadicInterval 40),(⟨747459732621,747459751950⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165830866048,165830866112⟩ : DyadicInterval 40),(⟨-195361610816,-195361610752⟩ : DyadicInterval 40),(⟨747489493366,747489512696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165948081664,165948081728⟩ : DyadicInterval 40),(⟨-195524430848,-195524430784⟩ : DyadicInterval 40),(⟨747467096528,747467115858⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22820175,34253632⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22819904,22819968⟩ : DyadicInterval 40),(⟨-22820416,-22820352⟩ : DyadicInterval 40),(⟨762123383334,762123402663⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34253056,34253120⟩ : DyadicInterval 40),(⟨-34254208,-34254144⟩ : DyadicInterval 40),(⟨762123383060,762123402389⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179023072012,179148212748⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165859734656,165859734720⟩ : DyadicInterval 40),(⟨-195401707328,-195401707264⟩ : DyadicInterval 40),(⟨747483979169,747483998499⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165967347648,165967347712⟩ : DyadicInterval 40),(⟨-195551196480,-195551196416⟩ : DyadicInterval 40),(⟨747463413408,747463432737⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29583848768,-29541972544⟩ : DyadicInterval 40),(⟨776894369888,776915327264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165888610368,165986598656⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195577942336,-195441816064⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2538_ok : ecellOkT e2538 = true := by decide +kernel
theorem e2538_pos {a z : ℝ} (ha1 : ((333519/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((53397/327680 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2538 e2538_ok ha1 ha2 hz1 hz2 hz

-- box ['53397/327680', '667887/4096000', '7997/8000', '3999/4000']  interval_lower 250872117/1099511627776
noncomputable def e2539 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278682228326,0,true,165986598592,165986598656⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920341027226,0,false,-195577942336,-195577942272⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278796179178,0,true,166084578176,166084578240⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920227076374,0,false,-195714085440,-195714085376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278615039350,0,true,165928822720,165928822784⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920408216202,0,false,-195497676032,-195497675968⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278751358041,0,true,166046040192,166046040256⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920271897511,0,false,-195660533248,-195660533184⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534463045,0,true,22835008,22835072⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488792507,0,false,-22835520,-22835456⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545904052,0,true,34275712,34275776⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477351500,0,false,-34276864,-34276800⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626707,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627302,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278648629268,0,true,165957707136,165957707200⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920374626284,0,false,-195537803008,-195537802944⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278773777135,0,true,166065316672,166065316736⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920249478417,0,false,-195687319168,-195687319104⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070285089937,0,false,-29622002496,-29622002432⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070325883403,0,false,-29580095872,-29580095808⟩
    { al := (53397/327680), au := (667887/4096000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨179170600550,179284551402⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165986598592,165986598656⟩ : DyadicInterval 40),(⟨-195577942336,-195577942272⟩ : DyadicInterval 40),(⟨747459732621,747459751950⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166084578176,166084578240⟩ : DyadicInterval 40),(⟨-195714085440,-195714085376⟩ : DyadicInterval 40),(⟨747440990693,747441010022⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165928822720,165928822784⟩ : DyadicInterval 40),(⟨-195497676032,-195497675968⟩ : DyadicInterval 40),(⟨747470777745,747470797074⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166046040192,166046040256⟩ : DyadicInterval 40),(⟨-195660533248,-195660533184⟩ : DyadicInterval 40),(⟨747448364034,747448383364⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22835269,34276276⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22835008,22835072⟩ : DyadicInterval 40),(⟨-22835520,-22835456⟩ : DyadicInterval 40),(⟨762123383333,762123402662⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34275712,34275776⟩ : DyadicInterval 40),(⟨-34276864,-34276800⟩ : DyadicInterval 40),(⟨762123383059,762123402388⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179137001492,179262149359⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165957707136,165957707200⟩ : DyadicInterval 40),(⟨-195537803008,-195537802944⟩ : DyadicInterval 40),(⟨747465256450,747465275780⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166065316672,166065316736⟩ : DyadicInterval 40),(⟨-195687319168,-195687319104⟩ : DyadicInterval 40),(⟨747444676187,747444695517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29622002496,-29580095808⟩ : DyadicInterval 40),(⟨776913431520,776934404128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165986598592,166084578240⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195714085440,-195577942272⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2539_ok : ecellOkT e2539 = true := by decide +kernel
theorem e2539_pos {a z : ℝ} (ha1 : ((53397/327680 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((667887/4096000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2539 e2539_ok ha1 ha2 hz1 hz2 hz

-- box ['667887/4096000', '1336623/8192000', '1999/2000', '7997/8000']  interval_lower 252330197/1099511627776
noncomputable def e2540 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278796179177,0,true,166084578176,166084578240⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920227076375,0,false,-195714085440,-195714085376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278910130029,0,true,166182548992,166182549056⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920113125523,0,false,-195850245312,-195850245248⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278706536901,0,true,166007500864,166007500928⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920316718651,0,false,-195606983680,-195606983616⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278842855591,0,true,166124709888,166124709952⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920180399961,0,false,-195769857024,-195769856960⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545903368,0,true,34275008,34275072⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477352184,0,false,-34276160,-34276096⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557359473,0,true,45730688,45730752⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465896079,0,false,-45732672,-45732608⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625873,0,false,-1920,-1856⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626708,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278751353561,0,true,166046036352,166046036416⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920271901991,0,false,-195660527872,-195660527808⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278876501404,0,true,166153637184,166153637248⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920146754148,0,false,-195810060736,-195810060672⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070251584426,0,false,-29656423488,-29656423424⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070292401269,0,false,-29614491520,-29614491456⟩
    { al := (667887/4096000), au := (1336623/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨179284551401,179398502253⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166084578176,166084578240⟩ : DyadicInterval 40),(⟨-195714085440,-195714085376⟩ : DyadicInterval 40),(⟨747440990693,747441010023⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166182548992,166182549056⟩ : DyadicInterval 40),(⟨-195850245312,-195850245248⟩ : DyadicInterval 40),(⟨747422236617,747422255947⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166007500864,166007500928⟩ : DyadicInterval 40),(⟨-195606983680,-195606983616⟩ : DyadicInterval 40),(⟨747455735502,747455754832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166124709888,166124709952⟩ : DyadicInterval 40),(⟨-195769857024,-195769856960⟩ : DyadicInterval 40),(⟨747433310147,747433329477⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34275592,45731697⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34275008,34275072⟩ : DyadicInterval 40),(⟨-34276160,-34276096⟩ : DyadicInterval 40),(⟨762123383059,762123402388⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45730688,45730752⟩ : DyadicInterval 40),(⟨-45732672,-45732608⟩ : DyadicInterval 40),(⟨762123382641,762123401970⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1920,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179239725785,179364873628⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166046036352,166046036416⟩ : DyadicInterval 40),(⟨-195660527872,-195660527808⟩ : DyadicInterval 40),(⟨747448364755,747448384084⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166153637184,166153637248⟩ : DyadicInterval 40),(⟨-195810060736,-195810060672⟩ : DyadicInterval 40),(⟨747427772525,747427791854⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29656423488,-29614491456⟩ : DyadicInterval 40),(⟨776930629344,776951614624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166084578176,166182549056⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195850245312,-195714085376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2540_ok : ecellOkT e2540 = true := by decide +kernel
theorem e2540_pos {a z : ℝ} (ha1 : ((667887/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1336623/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2540 e2540_ok ha1 ha2 hz1 hz2 hz

-- box ['1336623/8192000', '10449/64000', '1999/2000', '7997/8000']  interval_lower 63402245/274877906944
noncomputable def e2541 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278910130028,0,true,166182548992,166182549056⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920113125524,0,false,-195850245312,-195850245248⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279024080880,0,true,166280511040,166280511104⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919999174672,0,false,-195986422144,-195986422080⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278820430776,0,true,166105429568,166105429632⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920202824776,0,false,-195743062272,-195743062208⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278956763711,0,true,166222640384,166222640448⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920066491841,0,false,-195905972800,-195905972736⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545926013,0,true,34297664,34297728⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477329539,0,false,-34298816,-34298752⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557389670,0,true,45760896,45760960⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465865882,0,false,-45762880,-45762816⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625871,0,false,-1920,-1856⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626707,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278865275925,0,true,166143986112,166143986176⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920157979627,0,false,-195796647104,-195796647040⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278990430884,0,true,166251583488,166251583552⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920032824668,0,false,-195946206976,-195946206912⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070214401670,0,false,-29694623488,-29694623424⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070255246769,0,false,-29652660992,-29652660928⟩
    { al := (1336623/8192000), au := (10449/64000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨179398502252,179512453104⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166182548992,166182549056⟩ : DyadicInterval 40),(⟨-195850245312,-195850245248⟩ : DyadicInterval 40),(⟨747422236617,747422255947⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166280511040,166280511104⟩ : DyadicInterval 40),(⟨-195986422144,-195986422080⟩ : DyadicInterval 40),(⟨747403470472,747403489801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166105429568,166105429632⟩ : DyadicInterval 40),(⟨-195743062272,-195743062208⟩ : DyadicInterval 40),(⟨747437000367,747437019697⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166222640384,166222640448⟩ : DyadicInterval 40),(⟨-195905972800,-195905972736⟩ : DyadicInterval 40),(⟨747414558170,747414577499⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34298237,45761894⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34297664,34297728⟩ : DyadicInterval 40),(⟨-34298816,-34298752⟩ : DyadicInterval 40),(⟨762123383058,762123402387⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45760896,45760960⟩ : DyadicInterval 40),(⟨-45762880,-45762816⟩ : DyadicInterval 40),(⟨762123382639,762123401968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1920,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179353648149,179478803108⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166143986112,166143986176⟩ : DyadicInterval 40),(⟨-195796647104,-195796647040⟩ : DyadicInterval 40),(⟨747429620153,747429639482⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166251583488,166251583552⟩ : DyadicInterval 40),(⟨-195946206976,-195946206912⟩ : DyadicInterval 40),(⟨747409013418,747409032747⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29694623488,-29652660928⟩ : DyadicInterval 40),(⟨776949714080,776970714624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166182548992,166280511104⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195986422144,-195850245248⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2541_ok : ecellOkT e2541 = true := by decide +kernel
theorem e2541_pos {a z : ℝ} (ha1 : ((1336623/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((10449/64000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2541 e2541_ok ha1 ha2 hz1 hz2 hz

-- box ['667887/4096000', '1336623/8192000', '7997/8000', '3999/4000']  interval_lower 126073643/549755813888
noncomputable def e2542 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278796179177,0,true,166084578176,166084578240⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920227076375,0,false,-195714085440,-195714085376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278910130029,0,true,166182548992,166182549056⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920113125523,0,false,-195850245312,-195850245248⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278728947470,0,true,166026770688,166026770752⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920294308082,0,false,-195633758144,-195633758080⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278865280404,0,true,166143989952,166143990016⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920157975148,0,false,-195796652480,-195796652416⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534478141,0,true,22850112,22850176⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488777411,0,false,-22850624,-22850560⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545926698,0,true,34298368,34298432⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477328854,0,false,-34299520,-34299456⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626706,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627302,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278762558750,0,true,166055670848,166055670912⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920260696802,0,false,-195673915584,-195673915520⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278887713746,0,true,166163276928,166163276992⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920135541806,0,false,-195823458752,-195823458688⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070247926142,0,false,-29660181760,-29660181696⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070288747869,0,false,-29618244672,-29618244608⟩
    { al := (667887/4096000), au := (1336623/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨179284551401,179398502253⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166084578176,166084578240⟩ : DyadicInterval 40),(⟨-195714085440,-195714085376⟩ : DyadicInterval 40),(⟨747440990693,747441010023⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166182548992,166182549056⟩ : DyadicInterval 40),(⟨-195850245312,-195850245248⟩ : DyadicInterval 40),(⟨747422236617,747422255947⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166026770688,166026770752⟩ : DyadicInterval 40),(⟨-195633758144,-195633758080⟩ : DyadicInterval 40),(⟨747452050011,747452069340⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166143989952,166143990016⟩ : DyadicInterval 40),(⟨-195796652480,-195796652416⟩ : DyadicInterval 40),(⟨747429619432,747429638761⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22850365,34298922⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22850112,22850176⟩ : DyadicInterval 40),(⟨-22850624,-22850560⟩ : DyadicInterval 40),(⟨762123383333,762123402662⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34298368,34298432⟩ : DyadicInterval 40),(⟨-34299520,-34299456⟩ : DyadicInterval 40),(⟨762123383058,762123402387⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179250930974,179376085970⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166055670848,166055670912⟩ : DyadicInterval 40),(⟨-195673915584,-195673915520⟩ : DyadicInterval 40),(⟨747446521646,747446540976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166163276928,166163276992⟩ : DyadicInterval 40),(⟨-195823458752,-195823458688⟩ : DyadicInterval 40),(⟨747425926878,747425946207⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29660181760,-29618244608⟩ : DyadicInterval 40),(⟨776932505920,776953493760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166084578176,166182549056⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195850245312,-195714085376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2542_ok : ecellOkT e2542 = true := by decide +kernel
theorem e2542_pos {a z : ℝ} (ha1 : ((667887/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1336623/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2542 e2542_ok ha1 ha2 hz1 hz2 hz

-- box ['1336623/8192000', '10449/64000', '7997/8000', '3999/4000']  interval_lower 126712749/549755813888
noncomputable def e2543 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278910130028,0,true,166182548992,166182549056⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920113125524,0,false,-195850245312,-195850245248⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279024080880,0,true,166280511040,166280511104⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919999174672,0,false,-195986422144,-195986422080⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278842855589,0,true,166124709888,166124709952⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920180399963,0,false,-195769857024,-195769856960⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278979202767,0,true,166241930944,166241931008⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920044052785,0,false,-195932788608,-195932788544⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534493238,0,true,22865216,22865280⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488762314,0,false,-22865728,-22865664⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545949346,0,true,34321024,34321088⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477306206,0,false,-34322112,-34322048⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626704,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627301,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278876488235,0,true,166153625856,166153625920⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920146767317,0,false,-195810044992,-195810044928⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279001650344,0,true,166261228480,166261228544⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920021605208,0,false,-195959615232,-195959615168⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070210738737,0,false,-29698386688,-29698386624⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070251588724,0,false,-29656419072,-29656419008⟩
    { al := (1336623/8192000), au := (10449/64000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨179398502252,179512453104⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166182548992,166182549056⟩ : DyadicInterval 40),(⟨-195850245312,-195850245248⟩ : DyadicInterval 40),(⟨747422236617,747422255947⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166280511040,166280511104⟩ : DyadicInterval 40),(⟨-195986422144,-195986422080⟩ : DyadicInterval 40),(⟨747403470472,747403489801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166124709888,166124709952⟩ : DyadicInterval 40),(⟨-195769857024,-195769856960⟩ : DyadicInterval 40),(⟨747433310148,747433329477⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166241930944,166241931008⟩ : DyadicInterval 40),(⟨-195932788608,-195932788544⟩ : DyadicInterval 40),(⟨747410862745,747410882075⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22865462,34321570⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22865216,22865280⟩ : DyadicInterval 40),(⟨-22865728,-22865664⟩ : DyadicInterval 40),(⟨762123383332,762123402661⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34321024,34321088⟩ : DyadicInterval 40),(⟨-34322112,-34322048⟩ : DyadicInterval 40),(⟨762123383024,762123402353⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179364860459,179490022568⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166153625856,166153625920⟩ : DyadicInterval 40),(⟨-195810044992,-195810044928⟩ : DyadicInterval 40),(⟨747427774692,747427794022⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166261228480,166261228544⟩ : DyadicInterval 40),(⟨-195959615232,-195959615168⟩ : DyadicInterval 40),(⟨747407165443,747407184773⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29698386688,-29656419008⟩ : DyadicInterval 40),(⟨776951593120,776972596224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166182548992,166280511104⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195986422144,-195850245248⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2543_ok : ecellOkT e2543 = true := by decide +kernel
theorem e2543_pos {a z : ℝ} (ha1 : ((1336623/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((10449/64000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2543 e2543_ok ha1 ha2 hz1 hz2 hz

-- box ['333519/2048000', '53397/327680', '3999/4000', '7999/8000']  interval_lower 62354391/274877906944
noncomputable def e2544 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278568277475,0,true,165888610368,165888610432⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920454978077,0,false,-195441816128,-195441816064⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278682228327,0,true,165986598592,165986598656⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920341027225,0,false,-195577942336,-195577942272⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278523513312,0,true,165850114496,165850114560⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920499742240,0,false,-195388345280,-195388345216⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278659832003,0,true,165967340352,165967340416⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920363423549,0,false,-195551186304,-195551186240⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523037763,0,true,11409920,11409984⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500217789,0,false,-11410048,-11409984⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534463673,0,true,22835648,22835712⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488791879,0,false,-22836160,-22836096⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627301,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627658,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278545890762,0,true,165869358592,165869358656⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920477364790,0,false,-195415074880,-195415074816⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278671038648,0,true,165976976832,165976976896⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920352216904,0,false,-195564574400,-195564574336⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070318580887,0,false,-29587597504,-29587597440⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070359350972,0,false,-29545716224,-29545716160⟩
    { al := (333519/2048000), au := (53397/327680), zl := (3999/4000), zu := (7999/8000),
      A := ⟨179056649699,179170600551⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165888610368,165888610432⟩ : DyadicInterval 40),(⟨-195441816128,-195441816064⟩ : DyadicInterval 40),(⟨747478462380,747478481709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165986598592,165986598656⟩ : DyadicInterval 40),(⟨-195577942336,-195577942272⟩ : DyadicInterval 40),(⟨747459732621,747459751950⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165850114496,165850114560⟩ : DyadicInterval 40),(⟨-195388345280,-195388345216⟩ : DyadicInterval 40),(⟨747485816841,747485836170⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165967340352,165967340416⟩ : DyadicInterval 40),(⟨-195551186304,-195551186240⟩ : DyadicInterval 40),(⟨747463414792,747463434122⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11409987,22835897⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11409920,11409984⟩ : DyadicInterval 40),(⟨-11410048,-11409984⟩ : DyadicInterval 40),(⟨762123383497,762123402826⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22835648,22835712⟩ : DyadicInterval 40),(⟨-22836160,-22836096⟩ : DyadicInterval 40),(⟨762123383333,762123402662⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179034262986,179159410872⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165869358592,165869358656⟩ : DyadicInterval 40),(⟨-195415074880,-195415074816⟩ : DyadicInterval 40),(⟨747482140634,747482159963⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165976976832,165976976896⟩ : DyadicInterval 40),(⟨-195564574400,-195564574336⟩ : DyadicInterval 40),(⟨747461572368,747461591697⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29587597504,-29545716160⟩ : DyadicInterval 40),(⟨776896241696,776917201632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165888610368,165986598656⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195577942336,-195441816064⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2544_ok : ecellOkT e2544 = true := by decide +kernel
theorem e2544_pos {a z : ℝ} (ha1 : ((333519/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((53397/327680 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2544 e2544_ok ha1 ha2 hz1 hz2 hz

-- box ['53397/327680', '667887/4096000', '3999/4000', '7999/8000']  interval_lower 250689347/1099511627776
noncomputable def e2545 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278682228326,0,true,165986598592,165986598656⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920341027226,0,false,-195577942336,-195577942272⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278796179178,0,true,166084578176,166084578240⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920227076374,0,false,-195714085440,-195714085376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278637435675,0,true,165948081664,165948081728⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920385819877,0,false,-195524430848,-195524430784⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278773768610,0,true,166065309312,166065309376⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920249486942,0,false,-195687308992,-195687308928⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523045310,0,true,11417472,11417536⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500210242,0,false,-11417600,-11417536⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534478769,0,true,22850752,22850816⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488776783,0,false,-22851264,-22851200⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627301,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627658,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278659827358,0,true,165967336320,165967336384⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920363428194,0,false,-195551180736,-195551180672⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278784982377,0,true,166074951104,166074951168⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920238273175,0,false,-195700707264,-195700707200⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070281436063,0,false,-29625756160,-29625756096⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070322234411,0,false,-29583844352,-29583844288⟩
    { al := (53397/327680), au := (667887/4096000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨179170600550,179284551402⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165986598592,165986598656⟩ : DyadicInterval 40),(⟨-195577942336,-195577942272⟩ : DyadicInterval 40),(⟨747459732621,747459751950⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166084578176,166084578240⟩ : DyadicInterval 40),(⟨-195714085440,-195714085376⟩ : DyadicInterval 40),(⟨747440990693,747441010022⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165948081664,165948081728⟩ : DyadicInterval 40),(⟨-195524430848,-195524430784⟩ : DyadicInterval 40),(⟨747467096529,747467115859⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166065309312,166065309376⟩ : DyadicInterval 40),(⟨-195687308992,-195687308928⟩ : DyadicInterval 40),(⟨747444677611,747444696941⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11417534,22850993⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11417472,11417536⟩ : DyadicInterval 40),(⟨-11417600,-11417536⟩ : DyadicInterval 40),(⟨762123383497,762123402826⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22850752,22850816⟩ : DyadicInterval 40),(⟨-22851264,-22851200⟩ : DyadicInterval 40),(⟨762123383333,762123402662⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179148199582,179273354601⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165967336320,165967336384⟩ : DyadicInterval 40),(⟨-195551180736,-195551180672⟩ : DyadicInterval 40),(⟨747463415570,747463434899⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166074951104,166074951168⟩ : DyadicInterval 40),(⟨-195700707264,-195700707200⟩ : DyadicInterval 40),(⟨747442832799,747442852128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29625756160,-29583844288⟩ : DyadicInterval 40),(⟨776915305760,776936280960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165986598592,166084578240⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195714085440,-195577942272⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2545_ok : ecellOkT e2545 = true := by decide +kernel
theorem e2545_pos {a z : ℝ} (ha1 : ((53397/327680 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((667887/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2545 e2545_ok ha1 ha2 hz1 hz2 hz

-- box ['333519/2048000', '53397/327680', '7999/8000', '1']  interval_lower 249235721/1099511627776
noncomputable def e2546 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278568277475,0,true,165888610368,165888610432⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920454978077,0,false,-195441816128,-195441816064⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278682228327,0,true,165986598592,165986598656⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920341027225,0,false,-195577942336,-195577942272⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278545895393,0,true,165869362560,165869362624⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920477360159,0,false,-195415080384,-195415080320⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523045881,0,true,11417984,11418048⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500209671,0,false,-11418176,-11418112⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627657,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1278557081760,0,true,165878982464,165878982528⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨920466173792,0,false,-195428442624,-195428442560⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1278682236796,0,true,165986605888,165986605952⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨920341018756,0,false,-195577952448,-195577952384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1070314931419,0,false,-29591346560,-29591346496⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1070355706381,0,false,-29549460096,-29549460032⟩
    { al := (333519/2048000), au := (53397/327680), zl := (7999/8000), zu := 1,
      A := ⟨179056649699,179170600551⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165888610368,165888610432⟩ : DyadicInterval 40),(⟨-195441816128,-195441816064⟩ : DyadicInterval 40),(⟨747478462380,747478481709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165986598592,165986598656⟩ : DyadicInterval 40),(⟨-195577942336,-195577942272⟩ : DyadicInterval 40),(⟨747459732621,747459751950⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165869362560,165869362624⟩ : DyadicInterval 40),(⟨-195415080384,-195415080320⟩ : DyadicInterval 40),(⟨747482139870,747482159199⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165986598592,165986598656⟩ : DyadicInterval 40),(⟨-195577942336,-195577942272⟩ : DyadicInterval 40),(⟨747459732621,747459751950⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11418105⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11417984,11418048⟩ : DyadicInterval 40),(⟨-11418176,-11418112⟩ : DyadicInterval 40),(⟨762123383529,762123402858⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨179045453984,179170609020⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165878982464,165878982528⟩ : DyadicInterval 40),(⟨-195428442624,-195428442560⟩ : DyadicInterval 40),(⟨747480301978,747480321307⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165986605888,165986605952⟩ : DyadicInterval 40),(⟨-195577952448,-195577952384⟩ : DyadicInterval 40),(⟨747459731217,747459750547⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29591346560,-29549460032⟩ : DyadicInterval 40),(⟨776898113632,776919076160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨165888610368,165986598656⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195577942336,-195441816064⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2546_ok : ecellOkT e2546 = true := by decide +kernel
theorem e2546_pos {a z : ℝ} (ha1 : ((333519/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((53397/327680 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2546 e2546_ok ha1 ha2 hz1 hz2 hz

-- box ['53397/327680', '667887/4096000', '7999/8000', '1']  interval_lower 125253659/549755813888
noncomputable def e2547 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278682228326,0,true,165986598592,165986598656⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920341027226,0,false,-195577942336,-195577942272⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278796179178,0,true,166084578176,166084578240⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920227076374,0,false,-195714085440,-195714085376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278659832000,0,true,165967340352,165967340416⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920363423552,0,false,-195551186240,-195551186176⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523053429,0,true,11425536,11425600⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500202123,0,false,-11425728,-11425664⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627657,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1278671025487,0,true,165976965504,165976965568⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨920352230065,0,false,-195564558656,-195564558592⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1278796187648,0,true,166084585472,166084585536⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨920227067904,0,false,-195714095552,-195714095488⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1070277781951,0,false,-29629510080,-29629510016⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1070318585177,0,false,-29587593152,-29587593088⟩
    { al := (53397/327680), au := (667887/4096000), zl := (7999/8000), zu := 1,
      A := ⟨179170600550,179284551402⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165986598592,165986598656⟩ : DyadicInterval 40),(⟨-195577942336,-195577942272⟩ : DyadicInterval 40),(⟨747459732621,747459751950⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166084578176,166084578240⟩ : DyadicInterval 40),(⟨-195714085440,-195714085376⟩ : DyadicInterval 40),(⟨747440990693,747441010022⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165967340352,165967340416⟩ : DyadicInterval 40),(⟨-195551186240,-195551186176⟩ : DyadicInterval 40),(⟨747463414766,747463434096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166084578176,166084578240⟩ : DyadicInterval 40),(⟨-195714085440,-195714085376⟩ : DyadicInterval 40),(⟨747440990693,747441010022⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11425653⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11425536,11425600⟩ : DyadicInterval 40),(⟨-11425728,-11425664⟩ : DyadicInterval 40),(⟨762123383529,762123402858⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨179159397711,179284559872⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165976965504,165976965568⟩ : DyadicInterval 40),(⟨-195564558656,-195564558592⟩ : DyadicInterval 40),(⟨747461574530,747461593859⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166084585472,166084585536⟩ : DyadicInterval 40),(⟨-195714095552,-195714095488⟩ : DyadicInterval 40),(⟨747440989288,747441008618⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29629510080,-29587593088⟩ : DyadicInterval 40),(⟨776917180160,776938157920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨165986598592,166084578240⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195714085440,-195577942272⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2547_ok : ecellOkT e2547 = true := by decide +kernel
theorem e2547_pos {a z : ℝ} (ha1 : ((53397/327680 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((667887/4096000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2547 e2547_ok ha1 ha2 hz1 hz2 hz

-- box ['667887/4096000', '1336623/8192000', '3999/4000', '7999/8000']  interval_lower 251964517/1099511627776
noncomputable def e2548 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278796179177,0,true,166084578176,166084578240⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920227076375,0,false,-195714085440,-195714085376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278910130029,0,true,166182548992,166182549056⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920113125523,0,false,-195850245312,-195850245248⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278751358039,0,true,166046040192,166046040256⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920271897513,0,false,-195660533248,-195660533184⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278887705217,0,true,166163269632,166163269696⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920135550335,0,false,-195823448576,-195823448512⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523052858,0,true,11424960,11425024⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500202694,0,false,-11425152,-11425088⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534493866,0,true,22865792,22865856⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488761686,0,false,-22866368,-22866304⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627300,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627658,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278773763967,0,true,166065305344,166065305408⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920249491585,0,false,-195687303424,-195687303360⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278898926110,0,true,166172916608,166172916672⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920124329442,0,false,-195836857024,-195836856960⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070244267622,0,false,-29663940352,-29663940288⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070285094232,0,false,-29621998080,-29621998016⟩
    { al := (667887/4096000), au := (1336623/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨179284551401,179398502253⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166084578176,166084578240⟩ : DyadicInterval 40),(⟨-195714085440,-195714085376⟩ : DyadicInterval 40),(⟨747440990693,747441010023⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166182548992,166182549056⟩ : DyadicInterval 40),(⟨-195850245312,-195850245248⟩ : DyadicInterval 40),(⟨747422236617,747422255947⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166046040192,166046040256⟩ : DyadicInterval 40),(⟨-195660533248,-195660533184⟩ : DyadicInterval 40),(⟨747448364035,747448383364⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166163269632,166163269696⟩ : DyadicInterval 40),(⟨-195823448576,-195823448512⟩ : DyadicInterval 40),(⟨747425928267,747425947597⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11425082,22866090⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11424960,11425024⟩ : DyadicInterval 40),(⟨-11425152,-11425088⟩ : DyadicInterval 40),(⟨762123383529,762123402858⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22865792,22865856⟩ : DyadicInterval 40),(⟨-22866368,-22866304⟩ : DyadicInterval 40),(⟨762123383364,762123402693⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179262136191,179387298334⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166065305344,166065305408⟩ : DyadicInterval 40),(⟨-195687303424,-195687303360⟩ : DyadicInterval 40),(⟨747444678352,747444697682⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166172916608,166172916672⟩ : DyadicInterval 40),(⟨-195836857024,-195836856960⟩ : DyadicInterval 40),(⟨747424081137,747424100467⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29663940352,-29621998016⟩ : DyadicInterval 40),(⟨776934382624,776955373056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166084578176,166182549056⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195850245312,-195714085376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2548_ok : ecellOkT e2548 = true := by decide +kernel
theorem e2548_pos {a z : ℝ} (ha1 : ((667887/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1336623/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2548 e2548_ok ha1 ha2 hz1 hz2 hz

-- box ['1336623/8192000', '10449/64000', '3999/4000', '7999/8000']  interval_lower 253242467/1099511627776
noncomputable def e2549 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278910130028,0,true,166182548992,166182549056⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920113125524,0,false,-195850245312,-195850245248⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279024080880,0,true,166280511040,166280511104⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919999174672,0,false,-195986422144,-195986422080⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278865280402,0,true,166143989952,166143990016⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920157975150,0,false,-195796652480,-195796652416⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279001641824,0,true,166261221184,166261221248⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920021613728,0,false,-195959604992,-195959604928⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523060407,0,true,11432512,11432576⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500195145,0,false,-11432704,-11432640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534508964,0,true,22880896,22880960⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488746588,0,false,-22881472,-22881408⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627299,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627658,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278887700575,0,true,166163265664,166163265728⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920135554977,0,false,-195823443008,-195823442944⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279012869835,0,true,166270873472,166270873536⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920010385717,0,false,-195973023616,-195973023552⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070207075566,0,false,-29702150144,-29702150080⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070247930440,0,false,-29660177344,-29660177280⟩
    { al := (1336623/8192000), au := (10449/64000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨179398502252,179512453104⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166182548992,166182549056⟩ : DyadicInterval 40),(⟨-195850245312,-195850245248⟩ : DyadicInterval 40),(⟨747422236617,747422255947⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166280511040,166280511104⟩ : DyadicInterval 40),(⟨-195986422144,-195986422080⟩ : DyadicInterval 40),(⟨747403470472,747403489801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166143989952,166143990016⟩ : DyadicInterval 40),(⟨-195796652480,-195796652416⟩ : DyadicInterval 40),(⟨747429619432,747429638761⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166261221184,166261221248⟩ : DyadicInterval 40),(⟨-195959604992,-195959604928⟩ : DyadicInterval 40),(⟨747407166806,747407186136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11432631,22881188⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11432512,11432576⟩ : DyadicInterval 40),(⟨-11432704,-11432640⟩ : DyadicInterval 40),(⟨762123383529,762123402858⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22880896,22880960⟩ : DyadicInterval 40),(⟨-22881472,-22881408⟩ : DyadicInterval 40),(⟨762123383363,762123402692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179376072799,179501242059⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166163265664,166163265728⟩ : DyadicInterval 40),(⟨-195823443008,-195823442944⟩ : DyadicInterval 40),(⟨747425929009,747425948339⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166270873472,166270873536⟩ : DyadicInterval 40),(⟨-195973023616,-195973023552⟩ : DyadicInterval 40),(⟨747405317282,747405336612⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29702150144,-29660177280⟩ : DyadicInterval 40),(⟨776953472256,776974477952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166182548992,166280511104⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195986422144,-195850245248⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2549_ok : ecellOkT e2549 = true := by decide +kernel
theorem e2549_pos {a z : ℝ} (ha1 : ((1336623/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((10449/64000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2549 e2549_ok ha1 ha2 hz1 hz2 hz

-- box ['667887/4096000', '1336623/8192000', '7999/8000', '1']  interval_lower 251781699/1099511627776
noncomputable def e2550 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278796179177,0,true,166084578176,166084578240⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920227076375,0,false,-195714085440,-195714085376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278910130029,0,true,166182548992,166182549056⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920113125523,0,false,-195850245312,-195850245248⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278773768607,0,true,166065309312,166065309376⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920249486945,0,false,-195687308992,-195687308928⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523060978,0,true,11433088,11433152⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500194574,0,false,-11433280,-11433216⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627657,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1278784969209,0,true,166074939776,166074939840⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨920238286343,0,false,-195700691520,-195700691456⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1278910138504,0,true,166182556288,166182556352⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨920113117048,0,false,-195850255488,-195850255424⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1070240608863,0,false,-29667699200,-29667699136⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1070281440358,0,false,-29625751744,-29625751680⟩
    { al := (667887/4096000), au := (1336623/8192000), zl := (7999/8000), zu := 1,
      A := ⟨179284551401,179398502253⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166084578176,166084578240⟩ : DyadicInterval 40),(⟨-195714085440,-195714085376⟩ : DyadicInterval 40),(⟨747440990693,747441010023⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166182548992,166182549056⟩ : DyadicInterval 40),(⟨-195850245312,-195850245248⟩ : DyadicInterval 40),(⟨747422236617,747422255947⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166065309312,166065309376⟩ : DyadicInterval 40),(⟨-195687308992,-195687308928⟩ : DyadicInterval 40),(⟨747444677612,747444696941⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166182548992,166182549056⟩ : DyadicInterval 40),(⟨-195850245312,-195850245248⟩ : DyadicInterval 40),(⟨747422236617,747422255947⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11433202⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11433088,11433152⟩ : DyadicInterval 40),(⟨-11433280,-11433216⟩ : DyadicInterval 40),(⟨762123383529,762123402858⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨179273341433,179398510728⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166074939776,166074939840⟩ : DyadicInterval 40),(⟨-195700691520,-195700691456⟩ : DyadicInterval 40),(⟨747442834964,747442854294⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166182556288,166182556352⟩ : DyadicInterval 40),(⟨-195850255488,-195850255424⟩ : DyadicInterval 40),(⟨747422235237,747422254566⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29667699200,-29625751680⟩ : DyadicInterval 40),(⟨776936259456,776957252480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨166084578176,166182549056⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195850245312,-195714085376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2550_ok : ecellOkT e2550 = true := by decide +kernel
theorem e2550_pos {a z : ℝ} (ha1 : ((667887/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1336623/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2550 e2550_ok ha1 ha2 hz1 hz2 hz

-- box ['1336623/8192000', '10449/64000', '7999/8000', '1']  interval_lower 126529657/549755813888
noncomputable def e2551 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1278910130028,0,true,166182548992,166182549056⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨920113125524,0,false,-195850245312,-195850245248⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279024080880,0,true,166280511040,166280511104⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919999174672,0,false,-195986422144,-195986422080⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278887705215,0,true,166163269632,166163269696⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920135550337,0,false,-195823448576,-195823448512⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523068527,0,true,11440640,11440704⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500187025,0,false,-11440832,-11440768⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627656,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1278898912940,0,true,166172905344,166172905408⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨920124342612,0,false,-195836841280,-195836841216⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1279024089345,0,true,166280518336,166280518400⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨919999166207,0,false,-195986432256,-195986432192⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1070203412160,0,false,-29705913856,-29705913792⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1070244271920,0,false,-29663935936,-29663935872⟩
    { al := (1336623/8192000), au := (10449/64000), zl := (7999/8000), zu := 1,
      A := ⟨179398502252,179512453104⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166182548992,166182549056⟩ : DyadicInterval 40),(⟨-195850245312,-195850245248⟩ : DyadicInterval 40),(⟨747422236617,747422255947⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166280511040,166280511104⟩ : DyadicInterval 40),(⟨-195986422144,-195986422080⟩ : DyadicInterval 40),(⟨747403470472,747403489801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166163269632,166163269696⟩ : DyadicInterval 40),(⟨-195823448576,-195823448512⟩ : DyadicInterval 40),(⟨747425928267,747425947597⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166280511040,166280511104⟩ : DyadicInterval 40),(⟨-195986422144,-195986422080⟩ : DyadicInterval 40),(⟨747403470472,747403489801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11440751⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11440640,11440704⟩ : DyadicInterval 40),(⟨-11440832,-11440768⟩ : DyadicInterval 40),(⟨762123383528,762123402857⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨179387285164,179512461569⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166172905344,166172905408⟩ : DyadicInterval 40),(⟨-195836841280,-195836841216⟩ : DyadicInterval 40),(⟨747424083268,747424102598⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166280518336,166280518400⟩ : DyadicInterval 40),(⟨-195986432256,-195986432192⟩ : DyadicInterval 40),(⟨747403469064,747403488394⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29705913856,-29663935872⟩ : DyadicInterval 40),(⟨776955351552,776976359808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨166182548992,166280511104⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-195986422144,-195850245248⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2551_ok : ecellOkT e2551 = true := by decide +kernel
theorem e2551_pos {a z : ℝ} (ha1 : ((1336623/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((10449/64000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2551 e2551_ok ha1 ha2 hz1 hz2 hz

-- box ['10449/64000', '1338321/8192000', '999/1000', '7993/8000']  interval_lower 1997063/8589934592
noncomputable def e2552 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279024080879,0,true,166280511040,166280511104⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919999174673,0,false,-195986422144,-195986422080⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279138031731,0,true,166378464448,166378464512⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919885223821,0,false,-196122615744,-196122615680⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278844568425,0,true,166126182528,166126182592⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920178687127,0,false,-195771903680,-195771903616⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278980858628,0,true,166243354496,166243354560⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920042396924,0,false,-195934767424,-195934767360⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591709391,0,true,80078656,80078720⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431546161,0,false,-80084544,-80084480⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099603210796,0,true,91579200,91579264⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099420044756,0,false,-91586880,-91586816⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620147,0,false,-7680,-7616⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621944,0,false,-5888,-5824⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278934320818,0,true,166203346240,166203346304⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920088934734,0,false,-195879153088,-195879153024⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279059454323,0,true,166310919360,166310919424⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919963801229,0,false,-196028698496,-196028698432⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070191863252,0,false,-29717779136,-29717779072⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070232717063,0,false,-29675806848,-29675806784⟩
    { al := (10449/64000), au := (1338321/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨179512453103,179626403955⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166280511040,166280511104⟩ : DyadicInterval 40),(⟨-195986422144,-195986422080⟩ : DyadicInterval 40),(⟨747403470472,747403489801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166378464448,166378464512⟩ : DyadicInterval 40),(⟨-196122615744,-196122615680⟩ : DyadicInterval 40),(⟨747384692101,747384711430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166126182528,166126182592⟩ : DyadicInterval 40),(⟨-195771903680,-195771903616⟩ : DyadicInterval 40),(⟨747433028271,747433047600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166243354496,166243354560⟩ : DyadicInterval 40),(⟨-195934767424,-195934767360⟩ : DyadicInterval 40),(⟨747410589982,747410609312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨80081615,91583020⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80078656,80078720⟩ : DyadicInterval 40),(⟨-80084544,-80084480⟩ : DyadicInterval 40),(⟨762123380663,762123399992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨91579200,91579264⟩ : DyadicInterval 40),(⟨-91586880,-91586816⟩ : DyadicInterval 40),(⟨762123379763,762123399092⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7680,-5824⟩ : DyadicInterval 40),(⟨762123386528,762123406720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179422693042,179547826547⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166203346240,166203346304⟩ : DyadicInterval 40),(⟨-195879153088,-195879153024⟩ : DyadicInterval 40),(⟨747418253736,747418273066⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166310919360,166310919424⟩ : DyadicInterval 40),(⟨-196028698496,-196028698432⟩ : DyadicInterval 40),(⟨747397642446,747397661775⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29717779136,-29675806784⟩ : DyadicInterval 40),(⟨776961287008,776982292448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166280511040,166378464512⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196122615744,-195986422080⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2552_ok : ecellOkT e2552 = true := by decide +kernel
theorem e2552_pos {a z : ℝ} (ha1 : ((10449/64000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1338321/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2552 e2552_ok ha1 ha2 hz1 hz2 hz

-- box ['1338321/8192000', '133917/819200', '999/1000', '7993/8000']  interval_lower 256910777/1099511627776
noncomputable def e2553 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279138031730,0,true,166378464448,166378464512⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919885223822,0,false,-196122615744,-196122615680⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279251982582,0,true,166476409024,166476409088⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919771272970,0,false,-196258826304,-196258826240⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278958405326,0,true,166224051712,166224051776⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920064850226,0,false,-195907934592,-195907934528⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279094709772,0,true,166341225408,166341225472⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919928545780,0,false,-196070835520,-196070835456⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591762236,0,true,80131520,80131584⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431493316,0,false,-80137408,-80137344⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099603271197,0,true,91639552,91639616⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099419984355,0,false,-91647296,-91647232⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620137,0,false,-7680,-7616⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621936,0,false,-5888,-5824⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279048214701,0,true,166301257472,166301257536⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919975040851,0,false,-196015265344,-196015265280⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279173355312,0,true,166408827200,166408827264⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919849900240,0,false,-196164837824,-196164837760⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070154651891,0,false,-29756010624,-29756010560⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070195533949,0,false,-29714007872,-29714007808⟩
    { al := (1338321/8192000), au := (133917/819200), zl := (999/1000), zu := (7993/8000),
      A := ⟨179626403954,179740354806⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166378464448,166378464512⟩ : DyadicInterval 40),(⟨-196122615744,-196122615680⟩ : DyadicInterval 40),(⟨747384692101,747384711430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166476409024,166476409088⟩ : DyadicInterval 40),(⟨-196258826304,-196258826240⟩ : DyadicInterval 40),(⟨747365901695,747365921024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166224051712,166224051776⟩ : DyadicInterval 40),(⟨-195907934592,-195907934528⟩ : DyadicInterval 40),(⟨747414287809,747414307138⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166341225408,166341225472⟩ : DyadicInterval 40),(⟨-196070835520,-196070835456⟩ : DyadicInterval 40),(⟨747391832730,747391852060⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨80134460,91643421⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80131520,80131584⟩ : DyadicInterval 40),(⟨-80137408,-80137344⟩ : DyadicInterval 40),(⟨762123380655,762123399984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨91639552,91639616⟩ : DyadicInterval 40),(⟨-91647296,-91647232⟩ : DyadicInterval 40),(⟨762123379785,762123399114⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7680,-5824⟩ : DyadicInterval 40),(⟨762123386528,762123406720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179536586925,179661727536⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166301257472,166301257536⟩ : DyadicInterval 40),(⟨-196015265344,-196015265280⟩ : DyadicInterval 40),(⟨747399494366,747399513696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166408827200,166408827264⟩ : DyadicInterval 40),(⟨-196164837824,-196164837760⟩ : DyadicInterval 40),(⟨747378868568,747378887897⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29756010624,-29714007808⟩ : DyadicInterval 40),(⟨776980387520,777001408192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166378464448,166476409088⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196258826304,-196122615680⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2553_ok : ecellOkT e2553 = true := by decide +kernel
theorem e2553_pos {a z : ℝ} (ha1 : ((1338321/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((133917/819200 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2553 e2553_ok ha1 ha2 hz1 hz2 hz

-- box ['10449/64000', '1338321/8192000', '7993/8000', '3997/4000']  interval_lower 31930105/137438953472
noncomputable def e2554 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279024080879,0,true,166280511040,166280511104⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919999174673,0,false,-195986422144,-195986422080⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279138031731,0,true,166378464448,166378464512⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919885223821,0,false,-196122615744,-196122615680⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278867007482,0,true,166145474816,166145474880⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920156248070,0,false,-195798716224,-195798716160⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279003311929,0,true,166262656896,166262656960⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨920019943623,0,false,-195961600960,-195961600896⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580269293,0,true,68639360,68639424⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442986259,0,false,-68643712,-68643648⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591763149,0,true,80132416,80132480⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431492403,0,false,-80138304,-80138240⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621935,0,false,-5888,-5824⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623491,0,false,-4288,-4224⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278945540144,0,true,166212991552,166212991616⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920077715408,0,false,-195892560320,-195892560256⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279070680792,0,true,166320569920,166320569984⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919952574760,0,false,-196042116096,-196042116032⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070188196622,0,false,-29721546176,-29721546112⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070229055319,0,false,-29679568768,-29679568704⟩
    { al := (10449/64000), au := (1338321/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨179512453103,179626403955⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166280511040,166280511104⟩ : DyadicInterval 40),(⟨-195986422144,-195986422080⟩ : DyadicInterval 40),(⟨747403470472,747403489801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166378464448,166378464512⟩ : DyadicInterval 40),(⟨-196122615744,-196122615680⟩ : DyadicInterval 40),(⟨747384692101,747384711430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166145474816,166145474880⟩ : DyadicInterval 40),(⟨-195798716224,-195798716160⟩ : DyadicInterval 40),(⟨747429335180,747429354509⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166262656896,166262656960⟩ : DyadicInterval 40),(⟨-195961600960,-195961600896⟩ : DyadicInterval 40),(⟨747406891731,747406911061⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨68641517,80135373⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68639360,68639424⟩ : DyadicInterval 40),(⟨-68643712,-68643648⟩ : DyadicInterval 40),(⟨762123381442,762123400771⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80132416,80132480⟩ : DyadicInterval 40),(⟨-80138304,-80138240⟩ : DyadicInterval 40),(⟨762123380655,762123399984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5888,-4224⟩ : DyadicInterval 40),(⟨762123385728,762123405824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179433912368,179559053016⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166212991552,166212991616⟩ : DyadicInterval 40),(⟨-195892560320,-195892560256⟩ : DyadicInterval 40),(⟨747416406345,747416425675⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166320569920,166320569984⟩ : DyadicInterval 40),(⟨-196042116096,-196042116032⟩ : DyadicInterval 40),(⟨747395792539,747395811869⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29721546176,-29679568704⟩ : DyadicInterval 40),(⟨776963167968,776984175968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166280511040,166378464512⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196122615744,-195986422080⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2554_ok : ecellOkT e2554 = true := by decide +kernel
theorem e2554_pos {a z : ℝ} (ha1 : ((10449/64000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1338321/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2554 e2554_ok ha1 ha2 hz1 hz2 hz

-- box ['1338321/8192000', '133917/819200', '7993/8000', '3997/4000']  interval_lower 256727001/1099511627776
noncomputable def e2555 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279138031730,0,true,166378464448,166378464512⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919885223822,0,false,-196122615744,-196122615680⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279251982582,0,true,166476409024,166476409088⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919771272970,0,false,-196258826304,-196258826240⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278980858626,0,true,166243354496,166243354560⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920042396926,0,false,-195934767424,-195934767360⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279117177317,0,true,166360538368,166360538432⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919906078235,0,false,-196097689408,-196097689344⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580314589,0,true,68684608,68684672⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442940963,0,false,-68688960,-68688896⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591816000,0,true,80185280,80185344⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431439552,0,false,-80191168,-80191104⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621927,0,false,-5888,-5824⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623486,0,false,-4352,-4288⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279059441149,0,true,166310908032,166310908096⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919963814403,0,false,-196028682752,-196028682688⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279184588906,0,true,166418482944,166418483008⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919838666646,0,false,-196178265600,-196178265536⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070150980607,0,false,-29759782592,-29759782528⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070191867555,0,false,-29717774720,-29717774656⟩
    { al := (1338321/8192000), au := (133917/819200), zl := (7993/8000), zu := (3997/4000),
      A := ⟨179626403954,179740354806⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166378464448,166378464512⟩ : DyadicInterval 40),(⟨-196122615744,-196122615680⟩ : DyadicInterval 40),(⟨747384692101,747384711430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166476409024,166476409088⟩ : DyadicInterval 40),(⟨-196258826304,-196258826240⟩ : DyadicInterval 40),(⟨747365901695,747365921024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166243354496,166243354560⟩ : DyadicInterval 40),(⟨-195934767424,-195934767360⟩ : DyadicInterval 40),(⟨747410589982,747410609312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166360538368,166360538432⟩ : DyadicInterval 40),(⟨-196097689408,-196097689344⟩ : DyadicInterval 40),(⟨747388129725,747388149055⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨68686813,80188224⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68684608,68684672⟩ : DyadicInterval 40),(⟨-68688960,-68688896⟩ : DyadicInterval 40),(⟨762123381436,762123400766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80185280,80185344⟩ : DyadicInterval 40),(⟨-80191168,-80191104⟩ : DyadicInterval 40),(⟨762123380647,762123399977⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5888,-4288⟩ : DyadicInterval 40),(⟨762123385760,762123405824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179547813373,179672961130⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166310908032,166310908096⟩ : DyadicInterval 40),(⟨-196028682752,-196028682688⟩ : DyadicInterval 40),(⟨747397644619,747397663948⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166418482944,166418483008⟩ : DyadicInterval 40),(⟨-196178265600,-196178265536⟩ : DyadicInterval 40),(⟨747377016338,747377035667⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29759782592,-29717774656⟩ : DyadicInterval 40),(⟨776982270944,777003294176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166378464448,166476409088⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196258826304,-196122615680⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2555_ok : ecellOkT e2555 = true := by decide +kernel
theorem e2555_pos {a z : ℝ} (ha1 : ((1338321/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((133917/819200 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2555 e2555_ok ha1 ha2 hz1 hz2 hz

-- box ['133917/819200', '1340019/8192000', '999/1000', '7993/8000']  interval_lower 129100001/549755813888
noncomputable def e2556 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279251982581,0,true,166476409024,166476409088⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919771272971,0,false,-196258826304,-196258826240⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279365933433,0,true,166574344960,166574345024⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919657322119,0,false,-196395053696,-196395053632⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279072242226,0,true,166321912128,166321912192⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919951013326,0,false,-196043982336,-196043982272⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279208560916,0,true,166439087680,166439087744⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919814694636,0,false,-196206920448,-196206920384⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591815086,0,true,80184384,80184448⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431440466,0,false,-80190272,-80190208⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099603331601,0,true,91699968,91700032⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099419923951,0,false,-91707712,-91707648⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620127,0,false,-7680,-7616⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621928,0,false,-5888,-5824⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279162108568,0,true,166399160000,166399160064⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919861146984,0,false,-196151394496,-196151394432⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279287256315,0,true,166506726272,166506726336⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919735999237,0,false,-196300993984,-196300993920⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070117416928,0,false,-29794267712,-29794267648⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070158327244,0,false,-29752234432,-29752234368⟩
    { al := (133917/819200), au := (1340019/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨179740354805,179854305657⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166476409024,166476409088⟩ : DyadicInterval 40),(⟨-196258826304,-196258826240⟩ : DyadicInterval 40),(⟨747365901695,747365921024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166574344960,166574345024⟩ : DyadicInterval 40),(⟨-196395053696,-196395053632⟩ : DyadicInterval 40),(⟨747347099088,747347118417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166321912128,166321912192⟩ : DyadicInterval 40),(⟨-196043982336,-196043982272⟩ : DyadicInterval 40),(⟨747395535272,747395554601⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166439087680,166439087744⟩ : DyadicInterval 40),(⟨-196206920448,-196206920384⟩ : DyadicInterval 40),(⟨747373063321,747373082650⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨80187310,91703825⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80184384,80184448⟩ : DyadicInterval 40),(⟨-80190272,-80190208⟩ : DyadicInterval 40),(⟨762123380647,762123399977⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨91699968,91700032⟩ : DyadicInterval 40),(⟨-91707712,-91707648⟩ : DyadicInterval 40),(⟨762123379775,762123399104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7680,-5824⟩ : DyadicInterval 40),(⟨762123386528,762123406720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179650480792,179775628539⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166399160000,166399160064⟩ : DyadicInterval 40),(⟨-196151394496,-196151394432⟩ : DyadicInterval 40),(⟨747380722889,747380742218⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166506726272,166506726336⟩ : DyadicInterval 40),(⟨-196300993984,-196300993920⟩ : DyadicInterval 40),(⟨747360082583,747360101912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29794267712,-29752234368⟩ : DyadicInterval 40),(⟨776999500800,777020536736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166476409024,166574345024⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196395053696,-196258826240⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2556_ok : ecellOkT e2556 = true := by decide +kernel
theorem e2556_pos {a z : ℝ} (ha1 : ((133917/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1340019/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2556 e2556_ok ha1 ha2 hz1 hz2 hz

-- box ['1340019/8192000', '335217/2048000', '999/1000', '7993/8000']  interval_lower 259492355/1099511627776
noncomputable def e2557 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279365933432,0,true,166574344960,166574345024⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919657322120,0,false,-196395053696,-196395053632⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279479884284,0,true,166672272128,166672272192⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919543371268,0,false,-196531297984,-196531297920⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279186079126,0,true,166419763840,166419763904⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919837176426,0,false,-196180046912,-196180046848⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279322412060,0,true,166536941248,166536941312⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919700843492,0,false,-196343022208,-196343022144⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591867939,0,true,80237184,80237248⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431387613,0,false,-80243136,-80243072⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099603392010,0,true,91760384,91760448⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099419863542,0,false,-91768064,-91768000⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620117,0,false,-7680,-7616⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621921,0,false,-5888,-5824⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279276002445,0,true,166497053824,166497053888⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919747253107,0,false,-196287540480,-196287540416⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279401157314,0,true,166604616640,166604616704⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919622098238,0,false,-196437166976,-196437166912⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070080158367,0,false,-29832550336,-29832550272⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070121096941,0,false,-29790486592,-29790486528⟩
    { al := (1340019/8192000), au := (335217/2048000), zl := (999/1000), zu := (7993/8000),
      A := ⟨179854305656,179968256508⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166574344960,166574345024⟩ : DyadicInterval 40),(⟨-196395053696,-196395053632⟩ : DyadicInterval 40),(⟨747347099088,747347118417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166672272128,166672272192⟩ : DyadicInterval 40),(⟨-196531297984,-196531297920⟩ : DyadicInterval 40),(⟨747328284379,747328303709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166419763840,166419763904⟩ : DyadicInterval 40),(⟨-196180046912,-196180046848⟩ : DyadicInterval 40),(⟨747376770622,747376789951⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166536941248,166536941312⟩ : DyadicInterval 40),(⟨-196343022208,-196343022144⟩ : DyadicInterval 40),(⟨747354281790,747354301120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨80240163,91764234⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80237184,80237248⟩ : DyadicInterval 40),(⟨-80243136,-80243072⟩ : DyadicInterval 40),(⟨762123380672,762123400001⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨91760384,91760448⟩ : DyadicInterval 40),(⟨-91768064,-91768000⟩ : DyadicInterval 40),(⟨762123379733,762123399062⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7680,-5824⟩ : DyadicInterval 40),(⟨762123386528,762123406720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179764374669,179889529538⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166497053824,166497053888⟩ : DyadicInterval 40),(⟨-196287540480,-196287540416⟩ : DyadicInterval 40),(⟨747361939271,747361958600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166604616640,166604616704⟩ : DyadicInterval 40),(⟨-196437166976,-196437166912⟩ : DyadicInterval 40),(⟨747341284456,747341303785⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29832550336,-29790486528⟩ : DyadicInterval 40),(⟨777018626880,777039678048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166574344960,166672272192⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196531297984,-196395053632⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2557_ok : ecellOkT e2557 = true := by decide +kernel
theorem e2557_pos {a z : ℝ} (ha1 : ((1340019/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((335217/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2557 e2557_ok ha1 ha2 hz1 hz2 hz

-- box ['133917/819200', '1340019/8192000', '7993/8000', '3997/4000']  interval_lower 129007941/549755813888
noncomputable def e2558 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279251982581,0,true,166476409024,166476409088⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919771272971,0,false,-196258826304,-196258826240⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279365933433,0,true,166574344960,166574345024⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919657322119,0,false,-196395053696,-196395053632⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279094709770,0,true,166341225408,166341225472⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919928545782,0,false,-196070835520,-196070835456⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279231042704,0,true,166458411200,166458411264⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919792212848,0,false,-196233794624,-196233794560⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580359889,0,true,68729920,68729984⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442895663,0,false,-68734272,-68734208⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591868854,0,true,80238144,80238208⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431386698,0,false,-80244032,-80243968⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621920,0,false,-5888,-5824⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623480,0,false,-4352,-4288⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279173342135,0,true,166408815872,166408815936⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919849913417,0,false,-196164822080,-196164822016⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279298497035,0,true,166516387328,166516387392⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919724758517,0,false,-196314431936,-196314431872⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070113740985,0,false,-29798044608,-29798044544⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070154656198,0,false,-29756006208,-29756006144⟩
    { al := (133917/819200), au := (1340019/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨179740354805,179854305657⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166476409024,166476409088⟩ : DyadicInterval 40),(⟨-196258826304,-196258826240⟩ : DyadicInterval 40),(⟨747365901695,747365921024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166574344960,166574345024⟩ : DyadicInterval 40),(⟨-196395053696,-196395053632⟩ : DyadicInterval 40),(⟨747347099088,747347118417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166341225408,166341225472⟩ : DyadicInterval 40),(⟨-196070835520,-196070835456⟩ : DyadicInterval 40),(⟨747391832730,747391852060⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166458411200,166458411264⟩ : DyadicInterval 40),(⟨-196233794624,-196233794560⟩ : DyadicInterval 40),(⟨747369355529,747369374859⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨68732113,80241078⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68729920,68729984⟩ : DyadicInterval 40),(⟨-68734272,-68734208⟩ : DyadicInterval 40),(⟨762123381431,762123400760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80238144,80238208⟩ : DyadicInterval 40),(⟨-80244032,-80243968⟩ : DyadicInterval 40),(⟨762123380639,762123399969⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5888,-4288⟩ : DyadicInterval 40),(⟨762123385760,762123405824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179661714359,179786869259⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166408815872,166408815936⟩ : DyadicInterval 40),(⟨-196164822080,-196164822016⟩ : DyadicInterval 40),(⟨747378870744,747378890074⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166516387328,166516387392⟩ : DyadicInterval 40),(⟨-196314431936,-196314431872⟩ : DyadicInterval 40),(⟨747358227952,747358247281⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29798044608,-29756006144⟩ : DyadicInterval 40),(⟨777001386688,777022425184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166476409024,166574345024⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196395053696,-196258826240⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2558_ok : ecellOkT e2558 = true := by decide +kernel
theorem e2558_pos {a z : ℝ} (ha1 : ((133917/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1340019/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2558 e2558_ok ha1 ha2 hz1 hz2 hz

-- box ['1340019/8192000', '335217/2048000', '7993/8000', '3997/4000']  interval_lower 129654007/549755813888
noncomputable def e2559 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279365933432,0,true,166574344960,166574345024⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919657322120,0,false,-196395053696,-196395053632⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279479884284,0,true,166672272128,166672272192⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919543371268,0,false,-196531297984,-196531297920⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279208560914,0,true,166439087680,166439087744⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919814694638,0,false,-196206920448,-196206920384⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279344908092,0,true,166556275264,166556275328⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919678347460,0,false,-196369916800,-196369916736⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580405192,0,true,68775232,68775296⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442850360,0,false,-68779584,-68779520⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591921713,0,true,80290944,80291008⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431333839,0,false,-80296896,-80296832⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621912,0,false,-5888,-5824⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623474,0,false,-4352,-4288⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279287243135,0,true,166506714944,166506715008⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919736012417,0,false,-196300978240,-196300978176⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279412405151,0,true,166614282944,166614283008⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919610850401,0,false,-196450615104,-196450615040⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070076477767,0,false,-29836332160,-29836332096⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070117421239,0,false,-29794263232,-29794263168⟩
    { al := (1340019/8192000), au := (335217/2048000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨179854305656,179968256508⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166574344960,166574345024⟩ : DyadicInterval 40),(⟨-196395053696,-196395053632⟩ : DyadicInterval 40),(⟨747347099088,747347118417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166672272128,166672272192⟩ : DyadicInterval 40),(⟨-196531297984,-196531297920⟩ : DyadicInterval 40),(⟨747328284379,747328303709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166439087680,166439087744⟩ : DyadicInterval 40),(⟨-196206920448,-196206920384⟩ : DyadicInterval 40),(⟨747373063321,747373082650⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166556275264,166556275328⟩ : DyadicInterval 40),(⟨-196369916800,-196369916736⟩ : DyadicInterval 40),(⟨747350569297,747350588626⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨68777416,80293937⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68775232,68775296⟩ : DyadicInterval 40),(⟨-68779584,-68779520⟩ : DyadicInterval 40),(⟨762123381425,762123400754⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80290944,80291008⟩ : DyadicInterval 40),(⟨-80296896,-80296832⟩ : DyadicInterval 40),(⟨762123380664,762123399993⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5888,-4288⟩ : DyadicInterval 40),(⟨762123385760,762123405824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179775615359,179900777375⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166506714944,166506715008⟩ : DyadicInterval 40),(⟨-196300978240,-196300978176⟩ : DyadicInterval 40),(⟨747360084763,747360104093⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166614282944,166614283008⟩ : DyadicInterval 40),(⟨-196450615104,-196450615040⟩ : DyadicInterval 40),(⟨747339427459,747339446788⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29836332160,-29794263168⟩ : DyadicInterval 40),(⟨777020515200,777041568960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166574344960,166672272192⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196531297984,-196395053632⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2559_ok : ecellOkT e2559 = true := by decide +kernel
theorem e2559_pos {a z : ℝ} (ha1 : ((1340019/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((335217/2048000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2559 e2559_ok ha1 ha2 hz1 hz2 hz

-- box ['10449/64000', '1338321/8192000', '3997/4000', '1599/1600']  interval_lower 255257481/1099511627776
noncomputable def e2560 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279024080879,0,true,166280511040,166280511104⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919999174673,0,false,-195986422144,-195986422080⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279138031731,0,true,166378464448,166378464512⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919885223821,0,false,-196122615744,-196122615680⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278889446539,0,true,166164766720,166164766784⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920133809013,0,false,-195825529344,-195825529280⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279025765229,0,true,166281959040,166281959104⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919997490323,0,false,-195988435136,-195988435072⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568829138,0,true,57199872,57199936⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454426414,0,false,-57202880,-57202816⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580315446,0,true,68685504,68685568⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442940106,0,false,-68689856,-68689792⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623485,0,false,-4352,-4288⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624801,0,false,-3008,-2944⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278956759498,0,true,166222636800,166222636864⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920066496054,0,false,-195905967744,-195905967680⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279081907295,0,true,166330220352,166330220416⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919941348257,0,false,-196055533952,-196055533888⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070184529751,0,false,-29725313536,-29725313472⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070225393338,0,false,-29683330944,-29683330880⟩
    { al := (10449/64000), au := (1338321/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨179512453103,179626403955⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166280511040,166280511104⟩ : DyadicInterval 40),(⟨-195986422144,-195986422080⟩ : DyadicInterval 40),(⟨747403470472,747403489801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166378464448,166378464512⟩ : DyadicInterval 40),(⟨-196122615744,-196122615680⟩ : DyadicInterval 40),(⟨747384692101,747384711430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166164766720,166164766784⟩ : DyadicInterval 40),(⟨-195825529344,-195825529280⟩ : DyadicInterval 40),(⟨747425641613,747425660942⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166281959040,166281959104⟩ : DyadicInterval 40),(⟨-195988435136,-195988435072⟩ : DyadicInterval 40),(⟨747403192955,747403212284⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57201362,68687670⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57199872,57199936⟩ : DyadicInterval 40),(⟨-57202880,-57202816⟩ : DyadicInterval 40),(⟨762123382080,762123401409⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68685504,68685568⟩ : DyadicInterval 40),(⟨-68689856,-68689792⟩ : DyadicInterval 40),(⟨762123381436,762123400766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4352,-2944⟩ : DyadicInterval 40),(⟨762123385088,762123405056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179445131722,179570279519⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166222636800,166222636864⟩ : DyadicInterval 40),(⟨-195905967744,-195905967680⟩ : DyadicInterval 40),(⟨747414558832,747414578162⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166330220352,166330220416⟩ : DyadicInterval 40),(⟨-196055533952,-196055533888⟩ : DyadicInterval 40),(⟨747393942573,747393961903⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29725313536,-29683330880⟩ : DyadicInterval 40),(⟨776965049056,776986059648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166280511040,166378464512⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196122615744,-195986422080⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2560_ok : ecellOkT e2560 = true := by decide +kernel
theorem e2560_pos {a z : ℝ} (ha1 : ((10449/64000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1338321/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2560 e2560_ok ha1 ha2 hz1 hz2 hz

-- box ['1338321/8192000', '133917/819200', '3997/4000', '1599/1600']  interval_lower 256543137/1099511627776
noncomputable def e2561 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279138031730,0,true,166378464448,166378464512⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919885223822,0,false,-196122615744,-196122615680⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279251982582,0,true,166476409024,166476409088⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919771272970,0,false,-196258826304,-196258826240⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279003311927,0,true,166262656896,166262656960⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920019943625,0,false,-195961600960,-195961600896⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279139644861,0,true,166379851008,166379851072⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919883610691,0,false,-196124543872,-196124543808⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568866886,0,true,57237568,57237632⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454388666,0,false,-57240640,-57240576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580360747,0,true,68730816,68730880⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442894805,0,false,-68735168,-68735104⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623479,0,false,-4352,-4288⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624797,0,false,-3008,-2944⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279070667618,0,true,166320558592,166320558656⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919952587934,0,false,-196042100352,-196042100288⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279195822532,0,true,166428138688,166428138752⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919827433020,0,false,-196191693568,-196191693504⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070147309082,0,false,-29763554880,-29763554816⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070188200925,0,false,-29721541760,-29721541696⟩
    { al := (1338321/8192000), au := (133917/819200), zl := (3997/4000), zu := (1599/1600),
      A := ⟨179626403954,179740354806⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166378464448,166378464512⟩ : DyadicInterval 40),(⟨-196122615744,-196122615680⟩ : DyadicInterval 40),(⟨747384692101,747384711430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166476409024,166476409088⟩ : DyadicInterval 40),(⟨-196258826304,-196258826240⟩ : DyadicInterval 40),(⟨747365901695,747365921024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166262656896,166262656960⟩ : DyadicInterval 40),(⟨-195961600960,-195961600896⟩ : DyadicInterval 40),(⟨747406891731,747406911061⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166379851008,166379851072⟩ : DyadicInterval 40),(⟨-196124543872,-196124543808⟩ : DyadicInterval 40),(⟨747384426204,747384445534⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57239110,68732971⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57237568,57237632⟩ : DyadicInterval 40),(⟨-57240640,-57240576⟩ : DyadicInterval 40),(⟨762123382108,762123401437⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68730816,68730880⟩ : DyadicInterval 40),(⟨-68735168,-68735104⟩ : DyadicInterval 40),(⟨762123381431,762123400760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4352,-2944⟩ : DyadicInterval 40),(⟨762123385088,762123405056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179559039842,179684194756⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166320558592,166320558656⟩ : DyadicInterval 40),(⟨-196042100352,-196042100288⟩ : DyadicInterval 40),(⟨747395794713,747395814042⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166428138688,166428138752⟩ : DyadicInterval 40),(⟨-196191693568,-196191693504⟩ : DyadicInterval 40),(⟨747375163948,747375183277⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29763554880,-29721541696⟩ : DyadicInterval 40),(⟨776984154464,777005180320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166378464448,166476409088⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196258826304,-196122615680⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2561_ok : ecellOkT e2561 = true := by decide +kernel
theorem e2561_pos {a z : ℝ} (ha1 : ((1338321/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((133917/819200 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2561 e2561_ok ha1 ha2 hz1 hz2 hz

-- box ['10449/64000', '1338321/8192000', '1599/1600', '1999/2000']  interval_lower 31884237/137438953472
noncomputable def e2562 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279024080879,0,true,166280511040,166280511104⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919999174673,0,false,-195986422144,-195986422080⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279138031731,0,true,166378464448,166378464512⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919885223821,0,false,-196122615744,-196122615680⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1278911885595,0,true,166184058304,166184058368⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨920111369957,0,false,-195852343168,-195852343104⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279048218530,0,true,166301260800,166301260864⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919975037022,0,false,-196015269952,-196015269888⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557388928,0,true,45760192,45760256⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465866624,0,false,-45762112,-45762048⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568867686,0,true,57238400,57238464⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454387866,0,false,-57241408,-57241344⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624796,0,false,-3008,-2944⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625872,0,false,-1920,-1856⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1278967978877,0,true,166232281984,166232282048⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨920055276675,0,false,-195919375424,-195919375360⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279093133824,0,true,166339870720,166339870784⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919930121728,0,false,-196068951936,-196068951872⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070180862643,0,false,-29729081152,-29729081088⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070221731120,0,false,-29687093376,-29687093312⟩
    { al := (10449/64000), au := (1338321/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨179512453103,179626403955⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166280511040,166280511104⟩ : DyadicInterval 40),(⟨-195986422144,-195986422080⟩ : DyadicInterval 40),(⟨747403470472,747403489801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166378464448,166378464512⟩ : DyadicInterval 40),(⟨-196122615744,-196122615680⟩ : DyadicInterval 40),(⟨747384692101,747384711430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166184058304,166184058368⟩ : DyadicInterval 40),(⟨-195852343168,-195852343104⟩ : DyadicInterval 40),(⟨747421947585,747421966915⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166301260800,166301260864⟩ : DyadicInterval 40),(⟨-196015269952,-196015269888⟩ : DyadicInterval 40),(⟨747399493728,747399513057⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨45761152,57239910⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45760192,45760256⟩ : DyadicInterval 40),(⟨-45762112,-45762048⟩ : DyadicInterval 40),(⟨762123382607,762123401936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57238400,57238464⟩ : DyadicInterval 40),(⟨-57241408,-57241344⟩ : DyadicInterval 40),(⟨762123382076,762123401405⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3008,-1856⟩ : DyadicInterval 40),(⟨762123384544,762123404384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179456351101,179581506048⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166232281984,166232282048⟩ : DyadicInterval 40),(⟨-195919375424,-195919375360⟩ : DyadicInterval 40),(⟨747412711225,747412730554⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166339870720,166339870784⟩ : DyadicInterval 40),(⟨-196068951936,-196068951872⟩ : DyadicInterval 40),(⟨747392092458,747392111788⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29729081152,-29687093312⟩ : DyadicInterval 40),(⟨776966930272,776987943456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166280511040,166378464512⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196122615744,-195986422080⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2562_ok : ecellOkT e2562 = true := by decide +kernel
theorem e2562_pos {a z : ℝ} (ha1 : ((10449/64000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1338321/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2562 e2562_ok ha1 ha2 hz1 hz2 hz

-- box ['1338321/8192000', '133917/819200', '1599/1600', '1999/2000']  interval_lower 128179567/549755813888
noncomputable def e2563 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279138031730,0,true,166378464448,166378464512⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919885223822,0,false,-196122615744,-196122615680⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279251982582,0,true,166476409024,166476409088⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919771272970,0,false,-196258826304,-196258826240⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279025765227,0,true,166281958976,166281959040⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919997490325,0,false,-195988435136,-195988435072⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279162112405,0,true,166399163328,166399163392⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919861143147,0,false,-196151399040,-196151398976⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557419126,0,true,45790336,45790400⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465836426,0,false,-45792320,-45792256⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568905436,0,true,57276160,57276224⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454350116,0,false,-57279168,-57279104⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624792,0,false,-3008,-2944⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625869,0,false,-1920,-1856⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279081894116,0,true,166330209024,166330209088⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919941361436,0,false,-196055518208,-196055518144⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279207056183,0,true,166437794304,166437794368⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919816199369,0,false,-196205121728,-196205121664⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070143637320,0,false,-29767327360,-29767327296⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070184534057,0,false,-29725309120,-29725309056⟩
    { al := (1338321/8192000), au := (133917/819200), zl := (1599/1600), zu := (1999/2000),
      A := ⟨179626403954,179740354806⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166378464448,166378464512⟩ : DyadicInterval 40),(⟨-196122615744,-196122615680⟩ : DyadicInterval 40),(⟨747384692101,747384711430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166476409024,166476409088⟩ : DyadicInterval 40),(⟨-196258826304,-196258826240⟩ : DyadicInterval 40),(⟨747365901695,747365921024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166281958976,166281959040⟩ : DyadicInterval 40),(⟨-195988435136,-195988435072⟩ : DyadicInterval 40),(⟨747403192992,747403212322⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166399163328,166399163392⟩ : DyadicInterval 40),(⟨-196151399040,-196151398976⟩ : DyadicInterval 40),(⟨747380722221,747380741551⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨45791350,57277660⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45790336,45790400⟩ : DyadicInterval 40),(⟨-45792320,-45792256⟩ : DyadicInterval 40),(⟨762123382636,762123401965⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57276160,57276224⟩ : DyadicInterval 40),(⟨-57279168,-57279104⟩ : DyadicInterval 40),(⟨762123382072,762123401401⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3008,-1856⟩ : DyadicInterval 40),(⟨762123384544,762123404384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179570266340,179695428407⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166330209024,166330209088⟩ : DyadicInterval 40),(⟨-196055518208,-196055518144⟩ : DyadicInterval 40),(⟨747393944748,747393964077⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166437794304,166437794368⟩ : DyadicInterval 40),(⟨-196205121728,-196205121664⟩ : DyadicInterval 40),(⟨747373311471,747373330801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29767327360,-29725309056⟩ : DyadicInterval 40),(⟨776986038144,777007066560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166378464448,166476409088⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196258826304,-196122615680⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2563_ok : ecellOkT e2563 = true := by decide +kernel
theorem e2563_pos {a z : ℝ} (ha1 : ((1338321/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((133917/819200 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2563 e2563_ok ha1 ha2 hz1 hz2 hz

-- box ['133917/819200', '1340019/8192000', '3997/4000', '1599/1600']  interval_lower 128915833/549755813888
noncomputable def e2564 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279251982581,0,true,166476409024,166476409088⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919771272971,0,false,-196258826304,-196258826240⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279365933433,0,true,166574344960,166574345024⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919657322119,0,false,-196395053696,-196395053632⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279117177314,0,true,166360538368,166360538432⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919906078238,0,false,-196097689408,-196097689344⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279253524493,0,true,166477734336,166477734400⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919769731059,0,false,-196260669504,-196260669440⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568904636,0,true,57275328,57275392⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454350916,0,false,-57278400,-57278336⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580406051,0,true,68776064,68776128⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442849501,0,false,-68780480,-68780416⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623473,0,false,-4352,-4288⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624793,0,false,-3008,-2944⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279184575727,0,true,166418471616,166418471680⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919838679825,0,false,-196178249856,-196178249792⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279309737777,0,true,166526048256,166526048320⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919713517775,0,false,-196327870080,-196327870016⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070110064806,0,false,-29801821760,-29801821696⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070150984915,0,false,-29759778176,-29759778112⟩
    { al := (133917/819200), au := (1340019/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨179740354805,179854305657⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166476409024,166476409088⟩ : DyadicInterval 40),(⟨-196258826304,-196258826240⟩ : DyadicInterval 40),(⟨747365901695,747365921024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166574344960,166574345024⟩ : DyadicInterval 40),(⟨-196395053696,-196395053632⟩ : DyadicInterval 40),(⟨747347099088,747347118417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166360538368,166360538432⟩ : DyadicInterval 40),(⟨-196097689408,-196097689344⟩ : DyadicInterval 40),(⟨747388129726,747388149055⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166477734336,166477734400⟩ : DyadicInterval 40),(⟨-196260669504,-196260669440⟩ : DyadicInterval 40),(⟨747365647311,747365666640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57276860,68778275⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57275328,57275392⟩ : DyadicInterval 40),(⟨-57278400,-57278336⟩ : DyadicInterval 40),(⟨762123382104,762123401433⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68776064,68776128⟩ : DyadicInterval 40),(⟨-68780480,-68780416⟩ : DyadicInterval 40),(⟨762123381457,762123400786⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4352,-2944⟩ : DyadicInterval 40),(⟨762123385088,762123405056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179672947951,179798110001⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166418471616,166418471680⟩ : DyadicInterval 40),(⟨-196178249856,-196178249792⟩ : DyadicInterval 40),(⟨747377018515,747377037845⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166526048256,166526048320⟩ : DyadicInterval 40),(⟨-196327870080,-196327870016⟩ : DyadicInterval 40),(⟨747356373235,747356392565⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29801821760,-29759778112⟩ : DyadicInterval 40),(⟨777003272672,777024313760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166476409024,166574345024⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196395053696,-196258826240⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2564_ok : ecellOkT e2564 = true := by decide +kernel
theorem e2564_pos {a z : ℝ} (ha1 : ((133917/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1340019/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2564 e2564_ok ha1 ha2 hz1 hz2 hz

-- box ['1340019/8192000', '335217/2048000', '3997/4000', '1599/1600']  interval_lower 259123519/1099511627776
noncomputable def e2565 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279365933432,0,true,166574344960,166574345024⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919657322120,0,false,-196395053696,-196395053632⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279479884284,0,true,166672272128,166672272192⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919543371268,0,false,-196531297984,-196531297920⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279231042702,0,true,166458411136,166458411200⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919792212850,0,false,-196233794624,-196233794560⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279367404124,0,true,166575608896,166575608960⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919655851428,0,false,-196396811968,-196396811904⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568942390,0,true,57313088,57313152⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454313162,0,false,-57316160,-57316096⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580451358,0,true,68821376,68821440⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442804194,0,false,-68825792,-68825728⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623468,0,false,-4352,-4288⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624789,0,false,-3008,-2944⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279298483850,0,true,166516376000,166516376064⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919724771702,0,false,-196314416192,-196314416128⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279423653016,0,true,166623949184,166623949248⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919599602536,0,false,-196464063488,-196464063424⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070072796927,0,false,-29840114240,-29840114176⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070113745298,0,false,-29798040192,-29798040128⟩
    { al := (1340019/8192000), au := (335217/2048000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨179854305656,179968256508⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166574344960,166574345024⟩ : DyadicInterval 40),(⟨-196395053696,-196395053632⟩ : DyadicInterval 40),(⟨747347099088,747347118417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166672272128,166672272192⟩ : DyadicInterval 40),(⟨-196531297984,-196531297920⟩ : DyadicInterval 40),(⟨747328284379,747328303709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166458411136,166458411200⟩ : DyadicInterval 40),(⟨-196233794624,-196233794560⟩ : DyadicInterval 40),(⟨747369355567,747369374896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166575608896,166575608960⟩ : DyadicInterval 40),(⟨-196396811968,-196396811904⟩ : DyadicInterval 40),(⟨747346856321,747346875651⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57314614,68823582⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57313088,57313152⟩ : DyadicInterval 40),(⟨-57316160,-57316096⟩ : DyadicInterval 40),(⟨762123382100,762123401429⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68821376,68821440⟩ : DyadicInterval 40),(⟨-68825792,-68825728⟩ : DyadicInterval 40),(⟨762123381451,762123400781⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4352,-2944⟩ : DyadicInterval 40),(⟨762123385088,762123405056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179786856074,179912025240⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166516376000,166516376064⟩ : DyadicInterval 40),(⟨-196314416192,-196314416128⟩ : DyadicInterval 40),(⟨747358230133,747358249462⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166623949184,166623949248⟩ : DyadicInterval 40),(⟨-196464063488,-196464063424⟩ : DyadicInterval 40),(⟨747337570365,747337589694⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29840114240,-29798040128⟩ : DyadicInterval 40),(⟨777022403680,777043460000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166574344960,166672272192⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196531297984,-196395053632⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2565_ok : ecellOkT e2565 = true := by decide +kernel
theorem e2565_pos {a z : ℝ} (ha1 : ((1340019/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((335217/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2565 e2565_ok ha1 ha2 hz1 hz2 hz

-- box ['133917/819200', '1340019/8192000', '1599/1600', '1999/2000']  interval_lower 257647373/1099511627776
noncomputable def e2566 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279251982581,0,true,166476409024,166476409088⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919771272971,0,false,-196258826304,-196258826240⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279365933433,0,true,166574344960,166574345024⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919657322119,0,false,-196395053696,-196395053632⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279139644859,0,true,166379851008,166379851072⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919883610693,0,false,-196124543872,-196124543808⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279276006281,0,true,166497057152,166497057216⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919747249271,0,false,-196287545024,-196287544960⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557449326,0,true,45820544,45820608⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465806226,0,false,-45822528,-45822464⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568943190,0,true,57313920,57313984⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454312362,0,false,-57316928,-57316864⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624788,0,false,-3008,-2944⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625867,0,false,-1920,-1856⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279195809354,0,true,166428127360,166428127424⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919827446198,0,false,-196191677824,-196191677760⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279320978549,0,true,166535709184,166535709248⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919702277003,0,false,-196341308416,-196341308352⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070106388387,0,false,-29805599232,-29805599168⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070147313390,0,false,-29763550464,-29763550400⟩
    { al := (133917/819200), au := (1340019/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨179740354805,179854305657⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166476409024,166476409088⟩ : DyadicInterval 40),(⟨-196258826304,-196258826240⟩ : DyadicInterval 40),(⟨747365901695,747365921024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166574344960,166574345024⟩ : DyadicInterval 40),(⟨-196395053696,-196395053632⟩ : DyadicInterval 40),(⟨747347099088,747347118417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166379851008,166379851072⟩ : DyadicInterval 40),(⟨-196124543872,-196124543808⟩ : DyadicInterval 40),(⟨747384426205,747384445534⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166497057152,166497057216⟩ : DyadicInterval 40),(⟨-196287545024,-196287544960⟩ : DyadicInterval 40),(⟨747361938602,747361957931⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨45821550,57315414⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45820544,45820608⟩ : DyadicInterval 40),(⟨-45822528,-45822464⟩ : DyadicInterval 40),(⟨762123382634,762123401963⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57313920,57313984⟩ : DyadicInterval 40),(⟨-57316928,-57316864⟩ : DyadicInterval 40),(⟨762123382068,762123401397⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3008,-1856⟩ : DyadicInterval 40),(⟨762123384544,762123404384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179684181578,179809350773⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166428127360,166428127424⟩ : DyadicInterval 40),(⟨-196191677824,-196191677760⟩ : DyadicInterval 40),(⟨747375166125,747375185454⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166535709184,166535709248⟩ : DyadicInterval 40),(⟨-196341308416,-196341308352⟩ : DyadicInterval 40),(⟨747354518359,747354537688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29805599232,-29763550400⟩ : DyadicInterval 40),(⟨777005158816,777026202496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166476409024,166574345024⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196395053696,-196258826240⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2566_ok : ecellOkT e2566 = true := by decide +kernel
theorem e2566_pos {a z : ℝ} (ha1 : ((133917/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1340019/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2566 e2566_ok ha1 ha2 hz1 hz2 hz

-- box ['1340019/8192000', '335217/2048000', '1599/1600', '1999/2000']  interval_lower 258938653/1099511627776
noncomputable def e2567 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279365933432,0,true,166574344960,166574345024⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919657322120,0,false,-196395053696,-196395053632⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279479884284,0,true,166672272128,166672272192⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919543371268,0,false,-196531297984,-196531297920⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279253524490,0,true,166477734336,166477734400⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919769731062,0,false,-196260669504,-196260669440⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279389900156,0,true,166594942208,166594942272⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919633355396,0,false,-196423707904,-196423707840⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557479529,0,true,45850752,45850816⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465776023,0,false,-45852736,-45852672⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568980947,0,true,57351616,57351680⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454274605,0,false,-57354688,-57354624⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624784,0,false,-3008,-2944⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625864,0,false,-1920,-1856⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279309724596,0,true,166526036928,166526036992⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919713530956,0,false,-196327854336,-196327854272⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279434900905,0,true,166633615360,166633615424⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919588354647,0,false,-196477512000,-196477511936⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070069115850,0,false,-29843896640,-29843896576⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070110069118,0,false,-29801817344,-29801817280⟩
    { al := (1340019/8192000), au := (335217/2048000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨179854305656,179968256508⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166574344960,166574345024⟩ : DyadicInterval 40),(⟨-196395053696,-196395053632⟩ : DyadicInterval 40),(⟨747347099088,747347118417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166672272128,166672272192⟩ : DyadicInterval 40),(⟨-196531297984,-196531297920⟩ : DyadicInterval 40),(⟨747328284379,747328303709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166477734336,166477734400⟩ : DyadicInterval 40),(⟨-196260669504,-196260669440⟩ : DyadicInterval 40),(⟨747365647311,747365666641⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166594942208,166594942272⟩ : DyadicInterval 40),(⟨-196423707904,-196423707840⟩ : DyadicInterval 40),(⟨747343142907,747343162237⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨45851753,57353171⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45850752,45850816⟩ : DyadicInterval 40),(⟨-45852736,-45852672⟩ : DyadicInterval 40),(⟨762123382631,762123401960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57351616,57351680⟩ : DyadicInterval 40),(⟨-57354688,-57354624⟩ : DyadicInterval 40),(⟨762123382096,762123401425⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3008,-1856⟩ : DyadicInterval 40),(⟨762123384544,762123404384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179798096820,179923273129⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166526036928,166526036992⟩ : DyadicInterval 40),(⟨-196327854336,-196327854272⟩ : DyadicInterval 40),(⟨747356375416,747356394746⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166633615360,166633615424⟩ : DyadicInterval 40),(⟨-196477512000,-196477511936⟩ : DyadicInterval 40),(⟨747335713121,747335732451⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29843896640,-29801817280⟩ : DyadicInterval 40),(⟨777024292256,777045351200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166574344960,166672272192⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196531297984,-196395053632⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2567_ok : ecellOkT e2567 = true := by decide +kernel
theorem e2567_pos {a z : ℝ} (ha1 : ((1340019/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((335217/2048000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2567 e2567_ok ha1 ha2 hz1 hz2 hz

-- box ['335217/2048000', '1341717/8192000', '999/1000', '7993/8000']  interval_lower 130393995/549755813888
noncomputable def e2568 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279479884283,0,true,166672272128,166672272192⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919543371269,0,false,-196531297984,-196531297920⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279593835135,0,true,166770190592,166770190656⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919429420417,0,false,-196667559104,-196667559040⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279299916026,0,true,166517606848,166517606912⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919723339526,0,false,-196316128320,-196316128256⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279436263204,0,true,166634786048,166634786112⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919586992348,0,false,-196479140800,-196479140736⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591920797,0,true,80290048,80290112⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431334755,0,false,-80296000,-80295936⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099603452423,0,true,91820800,91820864⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099419803129,0,false,-91828544,-91828480⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620107,0,false,-7680,-7616⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621913,0,false,-5888,-5824⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279389896316,0,true,166594938944,166594939008⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919633359236,0,false,-196423703296,-196423703232⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279515058314,0,true,166702498304,166702498368⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919508197238,0,false,-196573356864,-196573356800⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070042876207,0,false,-29870858560,-29870858496⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070083843044,0,false,-29828764288,-29828764224⟩
    { al := (335217/2048000), au := (1341717/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨179968256507,180082207359⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166672272128,166672272192⟩ : DyadicInterval 40),(⟨-196531297984,-196531297920⟩ : DyadicInterval 40),(⟨747328284379,747328303709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166770190592,166770190656⟩ : DyadicInterval 40),(⟨-196667559104,-196667559040⟩ : DyadicInterval 40),(⟨747309457504,747309476833⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166517606848,166517606912⟩ : DyadicInterval 40),(⟨-196316128320,-196316128256⟩ : DyadicInterval 40),(⟨747357993856,747358013186⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166634786048,166634786112⟩ : DyadicInterval 40),(⟨-196479140800,-196479140736⟩ : DyadicInterval 40),(⟨747335488175,747335507504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨80293021,91824647⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80290048,80290112⟩ : DyadicInterval 40),(⟨-80296000,-80295936⟩ : DyadicInterval 40),(⟨762123380664,762123399993⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨91820800,91820864⟩ : DyadicInterval 40),(⟨-91828544,-91828480⟩ : DyadicInterval 40),(⟨762123379755,762123399084⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7680,-5824⟩ : DyadicInterval 40),(⟨762123386528,762123406720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179878268540,180003430538⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166594938944,166594939008⟩ : DyadicInterval 40),(⟨-196423703296,-196423703232⟩ : DyadicInterval 40),(⟨747343143513,747343162842⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166702498304,166702498368⟩ : DyadicInterval 40),(⟨-196573356864,-196573356800⟩ : DyadicInterval 40),(⟨747322474211,747322493540⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29870858560,-29828764224⟩ : DyadicInterval 40),(⟨777037765728,777058832160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166672272128,166770190656⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196667559104,-196531297920⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2568_ok : ecellOkT e2568 = true := by decide +kernel
theorem e2568_pos {a z : ℝ} (ha1 : ((335217/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1341717/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2568 e2568_ok ha1 ha2 hz1 hz2 hz

-- box ['1341717/8192000', '671283/4096000', '999/1000', '7993/8000']  interval_lower 262086495/1099511627776
noncomputable def e2569 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279593835134,0,true,166770190592,166770190656⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919429420418,0,false,-196667559104,-196667559040⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279707785987,0,true,166868100352,166868100416⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919315469565,0,false,-196803837184,-196803837120⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279413752926,0,true,166615441152,166615441216⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919609502626,0,false,-196452226560,-196452226496⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279550114349,0,true,166732622208,166732622272⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919473141203,0,false,-196615276288,-196615276224⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591973658,0,true,80342912,80342976⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431281894,0,false,-80348864,-80348800⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099603512842,0,true,91881216,91881280⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099419742710,0,false,-91888960,-91888896⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620097,0,false,-7680,-7616⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621905,0,false,-5888,-5824⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279503790194,0,true,166692815296,166692815360⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919519465358,0,false,-196559883008,-196559882944⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279628959315,0,true,166800371200,166800371264⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919394296237,0,false,-196709563648,-196709563584⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070005570449,0,false,-29909192384,-29909192320⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070046565549,0,false,-29867067648,-29867067584⟩
    { al := (1341717/8192000), au := (671283/4096000), zl := (999/1000), zu := (7993/8000),
      A := ⟨180082207358,180196158211⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166770190592,166770190656⟩ : DyadicInterval 40),(⟨-196667559104,-196667559040⟩ : DyadicInterval 40),(⟨747309457504,747309476833⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166868100352,166868100416⟩ : DyadicInterval 40),(⟨-196803837184,-196803837120⟩ : DyadicInterval 40),(⟨747290618514,747290637844⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166615441152,166615441216⟩ : DyadicInterval 40),(⟨-196452226560,-196452226496⟩ : DyadicInterval 40),(⟨747339204975,747339224305⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166732622208,166732622272⟩ : DyadicInterval 40),(⟨-196615276288,-196615276224⟩ : DyadicInterval 40),(⟨747316682425,747316701754⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨80345882,91885066⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80342912,80342976⟩ : DyadicInterval 40),(⟨-80348864,-80348800⟩ : DyadicInterval 40),(⟨762123380656,762123399986⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨91881216,91881280⟩ : DyadicInterval 40),(⟨-91888960,-91888896⟩ : DyadicInterval 40),(⟨762123379744,762123399074⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7680,-5824⟩ : DyadicInterval 40),(⟨762123386528,762123406720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179992162418,180117331539⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166692815296,166692815360⟩ : DyadicInterval 40),(⟨-196559883008,-196559882944⟩ : DyadicInterval 40),(⟨747324335677,747324355007⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166800371200,166800371264⟩ : DyadicInterval 40),(⟨-196709563648,-196709563584⟩ : DyadicInterval 40),(⟨747303651883,747303671213⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29909192384,-29867067584⟩ : DyadicInterval 40),(⟨777056917408,777077999072⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166770190592,166868100416⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196803837184,-196667559040⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2569_ok : ecellOkT e2569 = true := by decide +kernel
theorem e2569_pos {a z : ℝ} (ha1 : ((1341717/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((671283/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2569 e2569_ok ha1 ha2 hz1 hz2 hz

-- box ['335217/2048000', '1341717/8192000', '7993/8000', '3997/4000']  interval_lower 130301619/549755813888
noncomputable def e2570 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279479884283,0,true,166672272128,166672272192⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919543371269,0,false,-196531297984,-196531297920⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279593835135,0,true,166770190592,166770190656⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919429420417,0,false,-196667559104,-196667559040⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279322412058,0,true,166536941248,166536941312⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919700843494,0,false,-196343022208,-196343022144⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279458773480,0,true,166654130560,166654130624⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919564482072,0,false,-196506055744,-196506055680⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580450500,0,true,68820544,68820608⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442805052,0,false,-68824896,-68824832⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591974574,0,true,80343808,80343872⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431280978,0,false,-80349760,-80349696⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621904,0,false,-5888,-5824⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623469,0,false,-4352,-4288⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279401144131,0,true,166604605312,166604605376⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919622111421,0,false,-196437151232,-196437151168⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279526313272,0,true,166712169856,166712169920⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919496942280,0,false,-196586815168,-196586815104⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070039190945,0,false,-29874645312,-29874645248⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070080162682,0,false,-29832545920,-29832545856⟩
    { al := (335217/2048000), au := (1341717/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨179968256507,180082207359⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166672272128,166672272192⟩ : DyadicInterval 40),(⟨-196531297984,-196531297920⟩ : DyadicInterval 40),(⟨747328284379,747328303709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166770190592,166770190656⟩ : DyadicInterval 40),(⟨-196667559104,-196667559040⟩ : DyadicInterval 40),(⟨747309457504,747309476833⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166536941248,166536941312⟩ : DyadicInterval 40),(⟨-196343022208,-196343022144⟩ : DyadicInterval 40),(⟨747354281791,747354301120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166654130560,166654130624⟩ : DyadicInterval 40),(⟨-196506055744,-196506055680⟩ : DyadicInterval 40),(⟨747331770945,747331790275⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨68822724,80346798⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68820544,68820608⟩ : DyadicInterval 40),(⟨-68824896,-68824832⟩ : DyadicInterval 40),(⟨762123381419,762123400749⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80343808,80343872⟩ : DyadicInterval 40),(⟨-80349760,-80349696⟩ : DyadicInterval 40),(⟨762123380656,762123399985⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5888,-4288⟩ : DyadicInterval 40),(⟨762123385760,762123405824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179889516355,180014685496⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166604605312,166604605376⟩ : DyadicInterval 40),(⟨-196437151232,-196437151168⟩ : DyadicInterval 40),(⟨747341286639,747341305968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166712169856,166712169920⟩ : DyadicInterval 40),(⟨-196586815168,-196586815104⟩ : DyadicInterval 40),(⟨747320614844,747320634173⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29874645312,-29832545856⟩ : DyadicInterval 40),(⟨777039656544,777060725536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166672272128,166770190656⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196667559104,-196531297920⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2570_ok : ecellOkT e2570 = true := by decide +kernel
theorem e2570_pos {a z : ℝ} (ha1 : ((335217/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1341717/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2570 e2570_ok ha1 ha2 hz1 hz2 hz

-- box ['1341717/8192000', '671283/4096000', '7993/8000', '3997/4000']  interval_lower 130950671/549755813888
noncomputable def e2571 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279593835134,0,true,166770190592,166770190656⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919429420418,0,false,-196667559104,-196667559040⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279707785987,0,true,166868100352,166868100416⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919315469565,0,false,-196803837184,-196803837120⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279436263202,0,true,166634786048,166634786112⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919586992350,0,false,-196479140800,-196479140736⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279572638869,0,true,166751977216,166751977280⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919450616683,0,false,-196642211584,-196642211520⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580495810,0,true,68865856,68865920⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442759742,0,false,-68870208,-68870144⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592027441,0,true,80396672,80396736⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431228111,0,false,-80402624,-80402560⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621896,0,false,-5888,-5824⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623463,0,false,-4352,-4288⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279515045129,0,true,166702486976,166702487040⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919508210423,0,false,-196573341120,-196573341056⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279640221393,0,true,166810048000,166810048064⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919383034159,0,false,-196723032128,-196723032064⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070001880522,0,false,-29912984064,-29912984000⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070042880525,0,false,-29870854144,-29870854080⟩
    { al := (1341717/8192000), au := (671283/4096000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨180082207358,180196158211⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166770190592,166770190656⟩ : DyadicInterval 40),(⟨-196667559104,-196667559040⟩ : DyadicInterval 40),(⟨747309457504,747309476833⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166868100352,166868100416⟩ : DyadicInterval 40),(⟨-196803837184,-196803837120⟩ : DyadicInterval 40),(⟨747290618514,747290637844⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166634786048,166634786112⟩ : DyadicInterval 40),(⟨-196479140800,-196479140736⟩ : DyadicInterval 40),(⟨747335488175,747335507505⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166751977216,166751977280⟩ : DyadicInterval 40),(⟨-196642211584,-196642211520⟩ : DyadicInterval 40),(⟨747312960454,747312979783⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨68868034,80399665⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68865856,68865920⟩ : DyadicInterval 40),(⟨-68870208,-68870144⟩ : DyadicInterval 40),(⟨762123381414,762123400743⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80396672,80396736⟩ : DyadicInterval 40),(⟨-80402624,-80402560⟩ : DyadicInterval 40),(⟨762123380648,762123399978⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5888,-4288⟩ : DyadicInterval 40),(⟨762123385760,762123405824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180003417353,180128593617⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166702486976,166702487040⟩ : DyadicInterval 40),(⟨-196573341120,-196573341056⟩ : DyadicInterval 40),(⟨747322476397,747322495726⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166810048000,166810048064⟩ : DyadicInterval 40),(⟨-196723032128,-196723032064⟩ : DyadicInterval 40),(⟨747301790144,747301809474⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29912984064,-29870854080⟩ : DyadicInterval 40),(⟨777058810656,777079894912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166770190592,166868100416⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196803837184,-196667559040⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2571_ok : ecellOkT e2571 = true := by decide +kernel
theorem e2571_pos {a z : ℝ} (ha1 : ((1341717/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((671283/4096000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2571 e2571_ok ha1 ha2 hz1 hz2 hz

-- box ['671283/4096000', '268683/1638400', '999/1000', '7993/8000']  interval_lower 16461753/68719476736
noncomputable def e2572 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279707785986,0,true,166868100352,166868100416⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919315469566,0,false,-196803837184,-196803837120⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279821736838,0,true,166966001408,166966001472⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919201518714,0,false,-196940132096,-196940132032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279527589827,0,true,166713266816,166713266880⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919495665725,0,false,-196588341696,-196588341632⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279663965493,0,true,166830449600,166830449664⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919359290059,0,false,-196751428608,-196751428544⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592026524,0,true,80395776,80395840⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431229028,0,false,-80401728,-80401664⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099603573265,0,true,91941632,91941696⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099419682287,0,false,-91949376,-91949312⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620087,0,false,-7744,-7680⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621898,0,false,-5888,-5824⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279617684070,0,true,166790683008,166790683072⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919405571482,0,false,-196696079552,-196696079488⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279742860316,0,true,166898235456,166898235520⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919280395236,0,false,-196845787264,-196845787200⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069968241092,0,false,-29947551808,-29947551744⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070009264460,0,false,-29905396544,-29905396480⟩
    { al := (671283/4096000), au := (268683/1638400), zl := (999/1000), zu := (7993/8000),
      A := ⟨180196158210,180310109062⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166868100352,166868100416⟩ : DyadicInterval 40),(⟨-196803837184,-196803837120⟩ : DyadicInterval 40),(⟨747290618514,747290637844⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166966001408,166966001472⟩ : DyadicInterval 40),(⟨-196940132096,-196940132032⟩ : DyadicInterval 40),(⟨747271767356,747271786685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166713266816,166713266880⟩ : DyadicInterval 40),(⟨-196588341696,-196588341632⟩ : DyadicInterval 40),(⟨747320403966,747320423295⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166830449600,166830449664⟩ : DyadicInterval 40),(⟨-196751428608,-196751428544⟩ : DyadicInterval 40),(⟨747297864587,747297883917⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨80398748,91945489⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80395776,80395840⟩ : DyadicInterval 40),(⟨-80401728,-80401664⟩ : DyadicInterval 40),(⟨762123380648,762123399978⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨91941632,91941696⟩ : DyadicInterval 40),(⟨-91949376,-91949312⟩ : DyadicInterval 40),(⟨762123379734,762123399064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7744,-5824⟩ : DyadicInterval 40),(⟨762123386528,762123406752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180106056294,180231232540⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166790683008,166790683072⟩ : DyadicInterval 40),(⟨-196696079552,-196696079488⟩ : DyadicInterval 40),(⟨747305515662,747305534991⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166898235456,166898235520⟩ : DyadicInterval 40),(⟨-196845787264,-196845787200⟩ : DyadicInterval 40),(⟨747284817372,747284836702⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29947551808,-29905396480⟩ : DyadicInterval 40),(⟨777076081856,777097178784⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166868100352,166966001472⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196940132096,-196803837120⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2572_ok : ecellOkT e2572 = true := by decide +kernel
theorem e2572_pos {a z : ℝ} (ha1 : ((671283/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((268683/1638400 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2572 e2572_ok ha1 ha2 hz1 hz2 hz

-- box ['268683/1638400', '168033/1024000', '999/1000', '7993/8000']  interval_lower 132346291/549755813888
noncomputable def e2573 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279821736837,0,true,166966001408,166966001472⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919201518715,0,false,-196940132096,-196940132032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279935687689,0,true,167063893696,167063893760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919087567863,0,false,-197076443968,-197076443904⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279641426727,0,true,166811083712,166811083776⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919381828825,0,false,-196724473600,-196724473536⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279777816637,0,true,166928268352,166928268416⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919245438915,0,false,-196887597824,-196887597760⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592079393,0,true,80448640,80448704⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431176159,0,false,-80454592,-80454528⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099603633691,0,true,92002048,92002112⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099419621861,0,false,-92009792,-92009728⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620077,0,false,-7744,-7680⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621890,0,false,-5888,-5824⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279731577951,0,true,166888541952,166888542016⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919291677601,0,false,-196832292992,-196832292928⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279856761312,0,true,166996090944,166996091008⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919166494240,0,false,-196982027776,-196982027712⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069930888138,0,false,-29985936768,-29985936704⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069971939773,0,false,-29943750976,-29943750912⟩
    { al := (268683/1638400), au := (168033/1024000), zl := (999/1000), zu := (7993/8000),
      A := ⟨180310109061,180424059913⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166966001408,166966001472⟩ : DyadicInterval 40),(⟨-196940132096,-196940132032⟩ : DyadicInterval 40),(⟨747271767356,747271786685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167063893696,167063893760⟩ : DyadicInterval 40),(⟨-197076443968,-197076443904⟩ : DyadicInterval 40),(⟨747252904117,747252923447⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166811083712,166811083776⟩ : DyadicInterval 40),(⟨-196724473600,-196724473536⟩ : DyadicInterval 40),(⟨747301590848,747301610178⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166928268352,166928268416⟩ : DyadicInterval 40),(⟨-196887597824,-196887597760⟩ : DyadicInterval 40),(⟨747279034614,747279053943⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨80451617,92005915⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80448640,80448704⟩ : DyadicInterval 40),(⟨-80454592,-80454528⟩ : DyadicInterval 40),(⟨762123380641,762123399970⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨92002048,92002112⟩ : DyadicInterval 40),(⟨-92009792,-92009728⟩ : DyadicInterval 40),(⟨762123379724,762123399054⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7744,-5824⟩ : DyadicInterval 40),(⟨762123386528,762123406752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180219950175,180345133536⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166888541952,166888542016⟩ : DyadicInterval 40),(⟨-196832292992,-196832292928⟩ : DyadicInterval 40),(⟨747286683566,747286702895⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166996090944,166996091008⟩ : DyadicInterval 40),(⟨-196982027776,-196982027712⟩ : DyadicInterval 40),(⟨747265970777,747265990107⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29985936768,-29943750912⟩ : DyadicInterval 40),(⟨777095259072,777116371264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166966001408,167063893760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197076443968,-196940132032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2573_ok : ecellOkT e2573 = true := by decide +kernel
theorem e2573_pos {a z : ℝ} (ha1 : ((268683/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((168033/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2573 e2573_ok ha1 ha2 hz1 hz2 hz

-- box ['671283/4096000', '268683/1638400', '7993/8000', '3997/4000']  interval_lower 263202389/1099511627776
noncomputable def e2574 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279707785986,0,true,166868100352,166868100416⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919315469566,0,false,-196803837184,-196803837120⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279821736838,0,true,166966001408,166966001472⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919201518714,0,false,-196940132096,-196940132032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279550114347,0,true,166732622208,166732622272⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919473141205,0,false,-196615276288,-196615276224⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279686504257,0,true,166849815168,166849815232⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919336751295,0,false,-196778384256,-196778384192⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580541123,0,true,68911168,68911232⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442714429,0,false,-68915520,-68915456⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592080311,0,true,80449536,80449600⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431175241,0,false,-80455488,-80455424⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621889,0,false,-5888,-5824⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623457,0,false,-4352,-4288⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279628946126,0,true,166800359872,166800359936⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919394309426,0,false,-196709547840,-196709547776⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279754129520,0,true,166907917504,166907917568⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919269126032,0,false,-196859265984,-196859265920⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069964546495,0,false,-29951348416,-29951348352⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070005574771,0,false,-29909187968,-29909187904⟩
    { al := (671283/4096000), au := (268683/1638400), zl := (7993/8000), zu := (3997/4000),
      A := ⟨180196158210,180310109062⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166868100352,166868100416⟩ : DyadicInterval 40),(⟨-196803837184,-196803837120⟩ : DyadicInterval 40),(⟨747290618514,747290637844⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166966001408,166966001472⟩ : DyadicInterval 40),(⟨-196940132096,-196940132032⟩ : DyadicInterval 40),(⟨747271767356,747271786685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166732622208,166732622272⟩ : DyadicInterval 40),(⟨-196615276288,-196615276224⟩ : DyadicInterval 40),(⟨747316682425,747316701755⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166849815168,166849815232⟩ : DyadicInterval 40),(⟨-196778384256,-196778384192⟩ : DyadicInterval 40),(⟨747294137831,747294157161⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨68913347,80452535⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68911168,68911232⟩ : DyadicInterval 40),(⟨-68915520,-68915456⟩ : DyadicInterval 40),(⟨762123381408,762123400737⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80449536,80449600⟩ : DyadicInterval 40),(⟨-80455488,-80455424⟩ : DyadicInterval 40),(⟨762123380640,762123399970⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5888,-4288⟩ : DyadicInterval 40),(⟨762123385760,762123405824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180117318350,180242501744⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166800359872,166800359936⟩ : DyadicInterval 40),(⟨-196709547840,-196709547776⟩ : DyadicInterval 40),(⟨747303654046,747303673376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166907917504,166907917568⟩ : DyadicInterval 40),(⟨-196859265984,-196859265920⟩ : DyadicInterval 40),(⟨747282953283,747282972612⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29951348416,-29909187904⟩ : DyadicInterval 40),(⟨777077977568,777099077088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166868100352,166966001472⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196940132096,-196803837120⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2574_ok : ecellOkT e2574 = true := by decide +kernel
theorem e2574_pos {a z : ℝ} (ha1 : ((671283/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((268683/1638400 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2574 e2574_ok ha1 ha2 hz1 hz2 hz

-- box ['268683/1638400', '168033/1024000', '7993/8000', '3997/4000']  interval_lower 264506471/1099511627776
noncomputable def e2575 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279821736837,0,true,166966001408,166966001472⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919201518715,0,false,-196940132096,-196940132032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279935687689,0,true,167063893696,167063893760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919087567863,0,false,-197076443968,-197076443904⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279663965491,0,true,166830449600,166830449664⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919359290061,0,false,-196751428608,-196751428544⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279800369645,0,true,166947644416,166947644480⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919222885907,0,false,-196914573824,-196914573760⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580586440,0,true,68956480,68956544⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442669112,0,false,-68960832,-68960768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592133186,0,true,80502400,80502464⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431122366,0,false,-80508416,-80508352⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621881,0,false,-5952,-5888⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623452,0,false,-4352,-4288⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279742847125,0,true,166898224128,166898224192⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919280408427,0,false,-196845771520,-196845771456⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279868037637,0,true,167005778304,167005778368⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919155217915,0,false,-196995516672,-196995516608⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069927188870,0,false,-29989738368,-29989738304⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069968245417,0,false,-29947547328,-29947547264⟩
    { al := (268683/1638400), au := (168033/1024000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨180310109061,180424059913⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166966001408,166966001472⟩ : DyadicInterval 40),(⟨-196940132096,-196940132032⟩ : DyadicInterval 40),(⟨747271767356,747271786685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167063893696,167063893760⟩ : DyadicInterval 40),(⟨-197076443968,-197076443904⟩ : DyadicInterval 40),(⟨747252904117,747252923447⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166830449600,166830449664⟩ : DyadicInterval 40),(⟨-196751428608,-196751428544⟩ : DyadicInterval 40),(⟨747297864588,747297883917⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166947644416,166947644480⟩ : DyadicInterval 40),(⟨-196914573824,-196914573760⟩ : DyadicInterval 40),(⟨747275303102,747275322432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨68958664,80505410⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68956480,68956544⟩ : DyadicInterval 40),(⟨-68960832,-68960768⟩ : DyadicInterval 40),(⟨762123381402,762123400732⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80502400,80502464⟩ : DyadicInterval 40),(⟨-80508416,-80508352⟩ : DyadicInterval 40),(⟨762123380665,762123399994⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5952,-4288⟩ : DyadicInterval 40),(⟨762123385760,762123405856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180231219349,180356409861⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166898224128,166898224192⟩ : DyadicInterval 40),(⟨-196845771520,-196845771456⟩ : DyadicInterval 40),(⟨747284819564,747284838894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167005778304,167005778368⟩ : DyadicInterval 40),(⟨-196995516672,-196995516608⟩ : DyadicInterval 40),(⟨747264104271,747264123601⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29989738368,-29947547264⟩ : DyadicInterval 40),(⟨777097157248,777118272064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166966001408,167063893760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-197076443968,-196940132032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2575_ok : ecellOkT e2575 = true := by decide +kernel
theorem e2575_pos {a z : ℝ} (ha1 : ((268683/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((168033/1024000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2575 e2575_ok ha1 ha2 hz1 hz2 hz

-- box ['335217/2048000', '1341717/8192000', '3997/4000', '1599/1600']  interval_lower 130209067/549755813888
noncomputable def e2576 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279479884283,0,true,166672272128,166672272192⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919543371269,0,false,-196531297984,-196531297920⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279593835135,0,true,166770190592,166770190656⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919429420417,0,false,-196667559104,-196667559040⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279344908090,0,true,166556275200,166556275264⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919678347462,0,false,-196369916800,-196369916736⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279481283756,0,true,166673474752,166673474816⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919541971796,0,false,-196532971328,-196532971264⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568980145,0,true,57350848,57350912⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454275407,0,false,-57353920,-57353856⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580496669,0,true,68866688,68866752⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442758883,0,false,-68871104,-68871040⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623462,0,false,-4352,-4288⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624785,0,false,-3008,-2944⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279412391963,0,true,166614271616,166614271680⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919610863589,0,false,-196450599360,-196450599296⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279537568259,0,true,166721841344,166721841408⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919485687293,0,false,-196600273728,-196600273664⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070035505443,0,false,-29878432320,-29878432256⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070076482083,0,false,-29836327744,-29836327680⟩
    { al := (335217/2048000), au := (1341717/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨179968256507,180082207359⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166672272128,166672272192⟩ : DyadicInterval 40),(⟨-196531297984,-196531297920⟩ : DyadicInterval 40),(⟨747328284379,747328303709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166770190592,166770190656⟩ : DyadicInterval 40),(⟨-196667559104,-196667559040⟩ : DyadicInterval 40),(⟨747309457504,747309476833⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166556275200,166556275264⟩ : DyadicInterval 40),(⟨-196369916800,-196369916736⟩ : DyadicInterval 40),(⟨747350569334,747350588664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166673474752,166673474816⟩ : DyadicInterval 40),(⟨-196532971328,-196532971264⟩ : DyadicInterval 40),(⟨747328053223,747328072552⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57352369,68868893⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57350848,57350912⟩ : DyadicInterval 40),(⟨-57353920,-57353856⟩ : DyadicInterval 40),(⟨762123382096,762123401425⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68866688,68866752⟩ : DyadicInterval 40),(⟨-68871104,-68871040⟩ : DyadicInterval 40),(⟨762123381446,762123400775⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4352,-2944⟩ : DyadicInterval 40),(⟨762123385088,762123405056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179900764187,180025940483⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166614271616,166614271680⟩ : DyadicInterval 40),(⟨-196450599360,-196450599296⟩ : DyadicInterval 40),(⟨747339429643,747339448972⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166721841344,166721841408⟩ : DyadicInterval 40),(⟨-196600273728,-196600273664⟩ : DyadicInterval 40),(⟨747318755380,747318774710⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29878432320,-29836327680⟩ : DyadicInterval 40),(⟨777041547456,777062619040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166672272128,166770190656⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196667559104,-196531297920⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2576_ok : ecellOkT e2576 = true := by decide +kernel
theorem e2576_pos {a z : ℝ} (ha1 : ((335217/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1341717/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2576 e2576_ok ha1 ha2 hz1 hz2 hz

-- box ['1341717/8192000', '671283/4096000', '3997/4000', '1599/1600']  interval_lower 261715789/1099511627776
noncomputable def e2577 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279593835134,0,true,166770190592,166770190656⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919429420418,0,false,-196667559104,-196667559040⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279707785987,0,true,166868100352,166868100416⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919315469565,0,false,-196803837184,-196803837120⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279458773478,0,true,166654130560,166654130624⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919564482074,0,false,-196506055744,-196506055680⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279595163389,0,true,166771331968,166771332032⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919428092163,0,false,-196669147520,-196669147456⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569017904,0,true,57388608,57388672⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454237648,0,false,-57391680,-57391616⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099580541983,0,true,68912000,68912064⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442713569,0,false,-68916416,-68916352⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623456,0,false,-4352,-4288⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624781,0,false,-3008,-2944⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279526300086,0,true,166712158528,166712158592⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919496955466,0,false,-196586799424,-196586799360⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279651483506,0,true,166819724800,166819724864⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919371772046,0,false,-196736500864,-196736500800⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069998190352,0,false,-29916776000,-29916775936⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070039195264,0,false,-29874640896,-29874640832⟩
    { al := (1341717/8192000), au := (671283/4096000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨180082207358,180196158211⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166770190592,166770190656⟩ : DyadicInterval 40),(⟨-196667559104,-196667559040⟩ : DyadicInterval 40),(⟨747309457504,747309476833⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166868100352,166868100416⟩ : DyadicInterval 40),(⟨-196803837184,-196803837120⟩ : DyadicInterval 40),(⟨747290618514,747290637844⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166654130560,166654130624⟩ : DyadicInterval 40),(⟨-196506055744,-196506055680⟩ : DyadicInterval 40),(⟨747331770946,747331790275⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166771331968,166771332032⟩ : DyadicInterval 40),(⟨-196669147520,-196669147456⟩ : DyadicInterval 40),(⟨747309237951,747309257280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57390128,68914207⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57388608,57388672⟩ : DyadicInterval 40),(⟨-57391680,-57391616⟩ : DyadicInterval 40),(⟨762123382092,762123401421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68912000,68912064⟩ : DyadicInterval 40),(⟨-68916416,-68916352⟩ : DyadicInterval 40),(⟨762123381440,762123400769⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4352,-2944⟩ : DyadicInterval 40),(⟨762123385088,762123405056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180014672310,180139855730⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166712158528,166712158592⟩ : DyadicInterval 40),(⟨-196586799424,-196586799360⟩ : DyadicInterval 40),(⟨747320617031,747320636360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166819724800,166819724864⟩ : DyadicInterval 40),(⟨-196736500864,-196736500800⟩ : DyadicInterval 40),(⟨747299928269,747299947599⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29916776000,-29874640832⟩ : DyadicInterval 40),(⟨777060704032,777081790880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166770190592,166868100416⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196803837184,-196667559040⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2577_ok : ecellOkT e2577 = true := by decide +kernel
theorem e2577_pos {a z : ℝ} (ha1 : ((1341717/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((671283/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2577 e2577_ok ha1 ha2 hz1 hz2 hz

-- box ['335217/2048000', '1341717/8192000', '1599/1600', '1999/2000']  interval_lower 1016535/4294967296
noncomputable def e2578 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279479884283,0,true,166672272128,166672272192⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919543371269,0,false,-196531297984,-196531297920⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279593835135,0,true,166770190592,166770190656⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919429420417,0,false,-196667559104,-196667559040⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279367404122,0,true,166575608896,166575608960⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919655851430,0,false,-196396811968,-196396811904⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279503794032,0,true,166692818624,166692818688⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919519461520,0,false,-196559887552,-196559887488⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557509734,0,true,45880960,45881024⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465745818,0,false,-45882944,-45882880⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569018705,0,true,57389376,57389440⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454236847,0,false,-57392448,-57392384⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624780,0,false,-3008,-2944⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625862,0,false,-1920,-1856⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279423639833,0,true,166623937856,166623937920⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919599615719,0,false,-196464047680,-196464047616⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279548823276,0,true,166731512768,166731512832⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919474432276,0,false,-196613732416,-196613732352⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070031819700,0,false,-29882219648,-29882219584⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070072801242,0,false,-29840109824,-29840109760⟩
    { al := (335217/2048000), au := (1341717/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨179968256507,180082207359⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166672272128,166672272192⟩ : DyadicInterval 40),(⟨-196531297984,-196531297920⟩ : DyadicInterval 40),(⟨747328284379,747328303709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166770190592,166770190656⟩ : DyadicInterval 40),(⟨-196667559104,-196667559040⟩ : DyadicInterval 40),(⟨747309457504,747309476833⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166575608896,166575608960⟩ : DyadicInterval 40),(⟨-196396811968,-196396811904⟩ : DyadicInterval 40),(⟨747346856321,747346875651⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166692818624,166692818688⟩ : DyadicInterval 40),(⟨-196559887552,-196559887488⟩ : DyadicInterval 40),(⟨747324335007,747324354337⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨45881958,57390929⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45880960,45881024⟩ : DyadicInterval 40),(⟨-45882944,-45882880⟩ : DyadicInterval 40),(⟨762123382629,762123401958⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57389376,57389440⟩ : DyadicInterval 40),(⟨-57392448,-57392384⟩ : DyadicInterval 40),(⟨762123382092,762123401421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3008,-1856⟩ : DyadicInterval 40),(⟨762123384544,762123404384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨179912012057,180037195500⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166623937856,166623937920⟩ : DyadicInterval 40),(⟨-196464047680,-196464047616⟩ : DyadicInterval 40),(⟨747337572522,747337591851⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166731512768,166731512832⟩ : DyadicInterval 40),(⟨-196613732416,-196613732352⟩ : DyadicInterval 40),(⟨747316895765,747316915095⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29882219648,-29840109760⟩ : DyadicInterval 40),(⟨777043438496,777064512704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166672272128,166770190656⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196667559104,-196531297920⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2578_ok : ecellOkT e2578 = true := by decide +kernel
theorem e2578_pos {a z : ℝ} (ha1 : ((335217/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1341717/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2578 e2578_ok ha1 ha2 hz1 hz2 hz

-- box ['1341717/8192000', '671283/4096000', '1599/1600', '1999/2000']  interval_lower 65382555/274877906944
noncomputable def e2579 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1279593835134,0,true,166770190592,166770190656⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨919429420418,0,false,-196667559104,-196667559040⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1279707785987,0,true,166868100352,166868100416⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨919315469565,0,false,-196803837184,-196803837120⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1279481283754,0,true,166673474752,166673474816⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨919541971798,0,false,-196532971328,-196532971264⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1279617687909,0,true,166790686272,166790686336⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨919405567643,0,false,-196696084160,-196696084096⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557539941,0,true,45911168,45911232⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465715611,0,false,-45913152,-45913088⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569056468,0,true,57427136,57427200⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454199084,0,false,-57430208,-57430144⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624776,0,false,-3008,-2944⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625859,0,false,-1920,-1856⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1279537555073,0,true,166721830016,166721830080⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨919485700479,0,false,-196600257920,-196600257856⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1279662745636,0,true,166829401472,166829401536⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨919360509916,0,false,-196749969728,-196749969664⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069994499947,0,false,-29920568256,-29920568192⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070035509762,0,false,-29878427904,-29878427840⟩
    { al := (1341717/8192000), au := (671283/4096000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨180082207358,180196158211⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166770190592,166770190656⟩ : DyadicInterval 40),(⟨-196667559104,-196667559040⟩ : DyadicInterval 40),(⟨747309457504,747309476833⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166868100352,166868100416⟩ : DyadicInterval 40),(⟨-196803837184,-196803837120⟩ : DyadicInterval 40),(⟨747290618514,747290637844⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166673474752,166673474816⟩ : DyadicInterval 40),(⟨-196532971328,-196532971264⟩ : DyadicInterval 40),(⟨747328053223,747328072552⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166790686272,166790686336⟩ : DyadicInterval 40),(⟨-196696084160,-196696084096⟩ : DyadicInterval 40),(⟨747305515055,747305534384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨45912165,57428692⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45911168,45911232⟩ : DyadicInterval 40),(⟨-45913152,-45913088⟩ : DyadicInterval 40),(⟨762123382626,762123401955⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57427136,57427200⟩ : DyadicInterval 40),(⟨-57430208,-57430144⟩ : DyadicInterval 40),(⟨762123382088,762123401417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3008,-1856⟩ : DyadicInterval 40),(⟨762123384544,762123404384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨180025927297,180151117860⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166721830016,166721830080⟩ : DyadicInterval 40),(⟨-196600257920,-196600257856⟩ : DyadicInterval 40),(⟨747318757540,747318776870⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨166829401472,166829401536⟩ : DyadicInterval 40),(⟨-196749969728,-196749969664⟩ : DyadicInterval 40),(⟨747298066282,747298085612⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29920568256,-29878427840⟩ : DyadicInterval 40),(⟨777062597536,777083687008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨166770190592,166868100416⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-196803837184,-196667559040⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2579_ok : ecellOkT e2579 = true := by decide +kernel
theorem e2579_pos {a z : ℝ} (ha1 : ((1341717/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((671283/4096000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2579 e2579_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B042

end


