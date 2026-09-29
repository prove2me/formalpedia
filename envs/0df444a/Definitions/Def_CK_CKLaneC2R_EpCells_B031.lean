-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B031
-- name    : CK_CKLaneC2R_EpCells_B031
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:33:00.885978+00:00
-- url     : https://prove2.me/theorems/a5716621-6fea-4159-9c64-7b59b96f6ab5
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B031` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B031` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B031` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B031 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B031.lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheckT

-- ===== source module CKLaneC2R.EpCells.B031 =====
section

namespace CKLaneC2R.EpCells.B031

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['632229/4096000', '1265307/8192000', '3997/4000', '1599/1600']  interval_lower 155512811/1099511627776
noncomputable def e1860 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269224307687,0,true,157823707776,157823707840⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929798947865,0,false,-184336431488,-184336431424⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269338258539,0,true,157922417408,157922417472⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929684997013,0,false,-184471189632,-184471189568⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269097023177,0,true,157713437376,157713437440⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929926232375,0,false,-184185924544,-184185924480⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269232116895,0,true,157830472768,157830472832⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929791138657,0,false,-184345666112,-184345666048⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565593199,0,true,53964096,53964160⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457662353,0,false,-53966784,-53966720⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576432008,0,true,64802304,64802368⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446823544,0,false,-64806144,-64806080⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623956,0,false,-3840,-3776⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625128,0,false,-2688,-2624⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269160661366,0,true,157768570432,157768570496⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929862594186,0,false,-184261170624,-184261170560⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269285192368,0,true,157876450048,157876450112⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929738063184,0,false,-184408431616,-184408431552⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073297204475,0,false,-26531981504,-26531981440⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073335647577,0,false,-26492600192,-26492600128⟩
    { al := (632229/4096000), au := (1265307/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨169712679911,169826630763⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157823707776,157823707840⟩ : DyadicInterval 40),(⟨-184336431488,-184336431424⟩ : DyadicInterval 40),(⟨748973060509,748973079839⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157922417408,157922417472⟩ : DyadicInterval 40),(⟨-184471189632,-184471189568⟩ : DyadicInterval 40),(⟨748955324122,748955343452⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157713437376,157713437440⟩ : DyadicInterval 40),(⟨-184185924544,-184185924480⟩ : DyadicInterval 40),(⟨748992858011,748992877340⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157830472768,157830472832⟩ : DyadicInterval 40),(⟨-184345666112,-184345666048⟩ : DyadicInterval 40),(⟨748971845391,748971864720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨53965423,64804232⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53964096,53964160⟩ : DyadicInterval 40),(⟨-53966784,-53966720⟩ : DyadicInterval 40),(⟨762123382247,762123401576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64802304,64802368⟩ : DyadicInterval 40),(⟨-64806144,-64806080⟩ : DyadicInterval 40),(⟨762123381652,762123400981⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3840,-2624⟩ : DyadicInterval 40),(⟨762123384928,762123404800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169649033590,169773564592⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157768570432,157768570496⟩ : DyadicInterval 40),(⟨-184261170624,-184261170560⟩ : DyadicInterval 40),(⟨748982961778,748982981107⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157876450048,157876450112⟩ : DyadicInterval 40),(⟨-184408431616,-184408431552⟩ : DyadicInterval 40),(⟨748963585377,748963604706⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26531981504,-26492600128⟩ : DyadicInterval 40),(⟨775369683680,775389393632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157823707776,157922417472⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184471189632,-184336431424⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1860_ok : ecellOkT e1860 = true := by decide +kernel
theorem e1860_pos {a z : ℝ} (ha1 : ((632229/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1265307/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1860 e1860_ok ha1 ha2 hz1 hz2 hz

-- box ['1265307/8192000', '316539/2048000', '3997/4000', '1599/1600']  interval_lower 156555287/1099511627776
noncomputable def e1861 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269338258538,0,true,157922417408,157922417472⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929684997014,0,false,-184471189632,-184471189568⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269452209390,0,true,158021118144,158021118208⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929571046162,0,false,-184605964288,-184605964224⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269210888564,0,true,157812082880,157812082944⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929812366988,0,false,-184320563136,-184320563072⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269345996527,0,true,157929120064,157929120128⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929677259025,0,false,-184480341184,-184480341120⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565630711,0,true,54001600,54001664⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457624841,0,false,-54004288,-54004224⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576477027,0,true,64847296,64847360⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446778525,0,false,-64851200,-64851136⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623951,0,false,-3840,-3776⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625124,0,false,-2688,-2624⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269274569484,0,true,157867248000,157867248064⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929748686068,0,false,-184395868992,-184395868928⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269399107604,0,true,157975124096,157975124160⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929624147948,0,false,-184543156416,-184543156352⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073262013789,0,false,-26568032256,-26568032192⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073300484893,0,false,-26528620992,-26528620928⟩
    { al := (1265307/8192000), au := (316539/2048000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨169826630762,169940581614⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157922417408,157922417472⟩ : DyadicInterval 40),(⟨-184471189632,-184471189568⟩ : DyadicInterval 40),(⟨748955324122,748955343452⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158021118144,158021118208⟩ : DyadicInterval 40),(⟨-184605964288,-184605964224⟩ : DyadicInterval 40),(⟨748937575655,748937594984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157812082880,157812082944⟩ : DyadicInterval 40),(⟨-184320563136,-184320563072⟩ : DyadicInterval 40),(⟨748975148411,748975167740⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157929120064,157929120128⟩ : DyadicInterval 40),(⟨-184480341184,-184480341120⟩ : DyadicInterval 40),(⟨748954119298,748954138627⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54002935,64849251⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54001600,54001664⟩ : DyadicInterval 40),(⟨-54004288,-54004224⟩ : DyadicInterval 40),(⟨762123382243,762123401572⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64847296,64847360⟩ : DyadicInterval 40),(⟨-64851200,-64851136⟩ : DyadicInterval 40),(⟨762123381679,762123401008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3840,-2624⟩ : DyadicInterval 40),(⟨762123384928,762123404800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169762941708,169887479828⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157867248000,157867248064⟩ : DyadicInterval 40),(⟨-184395868992,-184395868928⟩ : DyadicInterval 40),(⟨748965238790,748965258120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157975124096,157975124160⟩ : DyadicInterval 40),(⟨-184543156416,-184543156352⟩ : DyadicInterval 40),(⟨748945848055,748945867384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26568032256,-26528620928⟩ : DyadicInterval 40),(⟨775387694080,775407419008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157922417408,158021118208⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184605964288,-184471189568⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1861_ok : ecellOkT e1861 = true := by decide +kernel
theorem e1861_pos {a z : ℝ} (ha1 : ((1265307/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((316539/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1861 e1861_ok ha1 ha2 hz1 hz2 hz

-- box ['632229/4096000', '1265307/8192000', '1599/1600', '1999/2000']  interval_lower 77681435/549755813888
noncomputable def e1862 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269224307687,0,true,157823707776,157823707840⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929798947865,0,false,-184336431488,-184336431424⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269338258539,0,true,157922417408,157922417472⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929684997013,0,false,-184471189632,-184471189568⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269118237261,0,true,157731816576,157731816640⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929905018291,0,false,-184211007616,-184211007552⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269253345224,0,true,157848862272,157848862336⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929769910328,0,false,-184370769664,-184370769600⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554800157,0,true,43171520,43171584⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468455395,0,false,-43173248,-43173184⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565631465,0,true,54002304,54002368⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457624087,0,false,-54005056,-54004992⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625123,0,false,-2688,-2624⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626081,0,false,-1728,-1664⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269171268283,0,true,157777759488,157777759552⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929851987269,0,false,-184273712832,-184273712768⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269295806427,0,true,157885644416,157885644480⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929727449125,0,false,-184420983872,-184420983808⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073293926578,0,false,-26535339456,-26535339392⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073332374288,0,false,-26495953280,-26495953216⟩
    { al := (632229/4096000), au := (1265307/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨169712679911,169826630763⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157823707776,157823707840⟩ : DyadicInterval 40),(⟨-184336431488,-184336431424⟩ : DyadicInterval 40),(⟨748973060509,748973079839⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157922417408,157922417472⟩ : DyadicInterval 40),(⟨-184471189632,-184471189568⟩ : DyadicInterval 40),(⟨748955324122,748955343452⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157731816576,157731816640⟩ : DyadicInterval 40),(⟨-184211007616,-184211007552⟩ : DyadicInterval 40),(⟨748989559462,748989578792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157848862272,157848862336⟩ : DyadicInterval 40),(⟨-184370769664,-184370769600⟩ : DyadicInterval 40),(⟨748968541997,748968561326⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨43172381,54003689⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43171520,43171584⟩ : DyadicInterval 40),(⟨-43173248,-43173184⟩ : DyadicInterval 40),(⟨762123382720,762123402049⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54002304,54002368⟩ : DyadicInterval 40),(⟨-54005056,-54004992⟩ : DyadicInterval 40),(⟨762123382275,762123401604⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2688,-1664⟩ : DyadicInterval 40),(⟨762123384448,762123404224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169659640507,169784178651⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157777759488,157777759552⟩ : DyadicInterval 40),(⟨-184273712832,-184273712768⟩ : DyadicInterval 40),(⟨748981311968,748981331297⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157885644416,157885644480⟩ : DyadicInterval 40),(⟨-184420983872,-184420983808⟩ : DyadicInterval 40),(⟨748961933176,748961952506⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26535339456,-26495953216⟩ : DyadicInterval 40),(⟨775371360224,775391072608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157823707776,157922417472⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184471189632,-184336431424⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1862_ok : ecellOkT e1862 = true := by decide +kernel
theorem e1862_pos {a z : ℝ} (ha1 : ((632229/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1265307/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1862 e1862_ok ha1 ha2 hz1 hz2 hz

-- box ['1265307/8192000', '316539/2048000', '1599/1600', '1999/2000']  interval_lower 1221911/8589934592
noncomputable def e1863 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269338258538,0,true,157922417408,157922417472⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929684997014,0,false,-184471189632,-184471189568⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269452209390,0,true,158021118144,158021118208⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929571046162,0,false,-184605964288,-184605964224⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269232116893,0,true,157830472768,157830472832⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929791138659,0,false,-184345666112,-184345666048⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269367239100,0,true,157947520320,157947520384⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929656016452,0,false,-184505464640,-184505464576⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554830167,0,true,43201536,43201600⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468425385,0,false,-43203264,-43203200⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565668980,0,true,54039872,54039936⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457586572,0,false,-54042560,-54042496⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625119,0,false,-2688,-2624⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626079,0,false,-1728,-1664⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269285183524,0,true,157876442368,157876442432⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929738072028,0,false,-184408421120,-184408421056⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269409728789,0,true,157984323776,157984323840⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929613526763,0,false,-184555718656,-184555718592⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073258731491,0,false,-26571394880,-26571394816⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073297207207,0,false,-26531978688,-26531978624⟩
    { al := (1265307/8192000), au := (316539/2048000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨169826630762,169940581614⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157922417408,157922417472⟩ : DyadicInterval 40),(⟨-184471189632,-184471189568⟩ : DyadicInterval 40),(⟨748955324122,748955343452⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158021118144,158021118208⟩ : DyadicInterval 40),(⟨-184605964288,-184605964224⟩ : DyadicInterval 40),(⟨748937575655,748937594984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157830472768,157830472832⟩ : DyadicInterval 40),(⟨-184345666112,-184345666048⟩ : DyadicInterval 40),(⟨748971845391,748971864720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157947520320,157947520384⟩ : DyadicInterval 40),(⟨-184505464640,-184505464576⟩ : DyadicInterval 40),(⟨748950811389,748950830718⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨43202391,54041204⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43201536,43201600⟩ : DyadicInterval 40),(⟨-43203264,-43203200⟩ : DyadicInterval 40),(⟨762123382718,762123402047⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54039872,54039936⟩ : DyadicInterval 40),(⟨-54042560,-54042496⟩ : DyadicInterval 40),(⟨762123382239,762123401568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2688,-1664⟩ : DyadicInterval 40),(⟨762123384448,762123404224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169773555748,169898101013⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157876442368,157876442432⟩ : DyadicInterval 40),(⟨-184408421120,-184408421056⟩ : DyadicInterval 40),(⟨748963586749,748963606078⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157984323776,157984323840⟩ : DyadicInterval 40),(⟨-184555718656,-184555718592⟩ : DyadicInterval 40),(⟨748944193645,748944212974⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26571394880,-26531978624⟩ : DyadicInterval 40),(⟨775389372928,775409100320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157922417408,158021118208⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184605964288,-184471189568⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1863_ok : ecellOkT e1863 = true := by decide +kernel
theorem e1863_pos {a z : ℝ} (ha1 : ((1265307/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((316539/2048000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1863 e1863_ok ha1 ha2 hz1 hz2 hz

-- box ['316539/2048000', '253401/1638400', '999/1000', '7993/8000']  interval_lower 157901035/1099511627776
noncomputable def e1864 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269452209389,0,true,158021118144,158021118208⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929571046163,0,false,-184605964288,-184605964224⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269566160241,0,true,158119810048,158119810112⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929457095311,0,false,-184740755456,-184740755392⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269282268807,0,true,157873917568,157873917632⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929740986745,0,false,-184404974208,-184404974144⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269417362526,0,true,157990935808,157990935872⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929605893026,0,false,-184564747584,-184564747520⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587284174,0,true,75653760,75653824⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435971378,0,false,-75659008,-75658944⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099598153003,0,true,86521792,86521856⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099425102549,0,false,-86528640,-86528576⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620966,0,false,-6848,-6784⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622571,0,false,-5248,-5184⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269367235350,0,true,157947517056,157947517120⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929656020202,0,false,-184505460224,-184505460160⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269491766310,0,true,158055379072,158055379136⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929531489242,0,false,-184652753856,-184652753792⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073233372261,0,false,-26597374720,-26597374656⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073271862143,0,false,-26557943104,-26557943040⟩
    { al := (316539/2048000), au := (253401/1638400), zl := (999/1000), zu := (7993/8000),
      A := ⟨169940581613,170054532465⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158021118144,158021118208⟩ : DyadicInterval 40),(⟨-184605964288,-184605964224⟩ : DyadicInterval 40),(⟨748937575655,748937594984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158119810048,158119810112⟩ : DyadicInterval 40),(⟨-184740755456,-184740755392⟩ : DyadicInterval 40),(⟨748919815069,748919834398⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157873917568,157873917632⟩ : DyadicInterval 40),(⟨-184404974208,-184404974144⟩ : DyadicInterval 40),(⟨748964040410,748964059740⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157990935808,157990935872⟩ : DyadicInterval 40),(⟨-184564747584,-184564747520⟩ : DyadicInterval 40),(⟨748943004506,748943023835⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨75656398,86525227⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75653760,75653824⟩ : DyadicInterval 40),(⟨-75659008,-75658944⟩ : DyadicInterval 40),(⟨762123380969,762123400299⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨86521792,86521856⟩ : DyadicInterval 40),(⟨-86528640,-86528576⟩ : DyadicInterval 40),(⟨762123380166,762123399496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6848,-5184⟩ : DyadicInterval 40),(⟨762123386208,762123406304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169855607574,169980138534⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157947517056,157947517120⟩ : DyadicInterval 40),(⟨-184505460224,-184505460160⟩ : DyadicInterval 40),(⟨748950811990,748950831320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158055379072,158055379136⟩ : DyadicInterval 40),(⟨-184652753856,-184652753792⟩ : DyadicInterval 40),(⟨748931411618,748931430947⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26597374720,-26557943040⟩ : DyadicInterval 40),(⟨775402355136,775422090240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158021118144,158119810112⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184740755456,-184605964224⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1864_ok : ecellOkT e1864 = true := by decide +kernel
theorem e1864_pos {a z : ℝ} (ha1 : ((316539/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((253401/1638400 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1864 e1864_ok ha1 ha2 hz1 hz2 hz

-- box ['253401/1638400', '633927/4096000', '999/1000', '7993/8000']  interval_lower 79474635/549755813888
noncomputable def e1865 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269566160240,0,true,158119810048,158119810112⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929457095312,0,false,-184740755456,-184740755392⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269680111092,0,true,158218493120,158218493184⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929343144460,0,false,-184875563136,-184875563072⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269396105707,0,true,157972523968,157972524032⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929627149845,0,false,-184539605952,-184539605888⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269531213670,0,true,158089544064,158089544128⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929492041882,0,false,-184699415808,-184699415744⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587336697,0,true,75706304,75706368⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435918855,0,false,-75711552,-75711488⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099598213035,0,true,86581824,86581888⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099425042517,0,false,-86588672,-86588608⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620957,0,false,-6848,-6784⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622563,0,false,-5248,-5184⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269481129223,0,true,158046166208,158046166272⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929542126329,0,false,-184640171648,-184640171584⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269605667307,0,true,158154024768,158154024832⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929417588245,0,false,-184787491776,-184787491712⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073198143176,0,false,-26633467008,-26633466944⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073236661062,0,false,-26594005376,-26594005312⟩
    { al := (253401/1638400), au := (633927/4096000), zl := (999/1000), zu := (7993/8000),
      A := ⟨170054532464,170168483316⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158119810048,158119810112⟩ : DyadicInterval 40),(⟨-184740755456,-184740755392⟩ : DyadicInterval 40),(⟨748919815069,748919834399⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158218493120,158218493184⟩ : DyadicInterval 40),(⟨-184875563136,-184875563072⟩ : DyadicInterval 40),(⟨748902042363,748902061692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157972523968,157972524032⟩ : DyadicInterval 40),(⟨-184539605952,-184539605888⟩ : DyadicInterval 40),(⟨748946315621,748946334950⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158089544064,158089544128⟩ : DyadicInterval 40),(⟨-184699415808,-184699415744⟩ : DyadicInterval 40),(⟨748925263187,748925282517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨75708921,86585259⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75706304,75706368⟩ : DyadicInterval 40),(⟨-75711552,-75711488⟩ : DyadicInterval 40),(⟨762123380962,762123400292⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨86581824,86581888⟩ : DyadicInterval 40),(⟨-86588672,-86588608⟩ : DyadicInterval 40),(⟨762123380157,762123399486⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6848,-5184⟩ : DyadicInterval 40),(⟨762123386208,762123406304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169969501447,170094039531⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158046166208,158046166272⟩ : DyadicInterval 40),(⟨-184640171648,-184640171584⟩ : DyadicInterval 40),(⟨748933069300,748933088629⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158154024768,158154024832⟩ : DyadicInterval 40),(⟨-184787491776,-184787491712⟩ : DyadicInterval 40),(⟨748913654580,748913673909⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26633467008,-26594005312⟩ : DyadicInterval 40),(⟨775420386272,775440136384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158119810048,158218493184⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184875563136,-184740755392⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1865_ok : ecellOkT e1865 = true := by decide +kernel
theorem e1865_pos {a z : ℝ} (ha1 : ((253401/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((633927/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1865 e1865_ok ha1 ha2 hz1 hz2 hz

-- box ['316539/2048000', '253401/1638400', '7993/8000', '3997/4000']  interval_lower 78875323/549755813888
noncomputable def e1866 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269452209389,0,true,158021118144,158021118208⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929571046163,0,false,-184605964288,-184605964224⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269566160241,0,true,158119810048,158119810112⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929457095311,0,false,-184740755456,-184740755392⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269303511379,0,true,157892318720,157892318784⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929719744173,0,false,-184430095936,-184430095872⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269438619342,0,true,158009347328,158009347392⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929584636210,0,false,-184589889856,-184589889792⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576476224,0,true,64846528,64846592⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446779328,0,false,-64850368,-64850304⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587337550,0,true,75707136,75707200⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435918002,0,false,-75712384,-75712320⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622562,0,false,-5248,-5184⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623952,0,false,-3840,-3776⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269377856464,0,true,157956716928,157956716992⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929645399088,0,false,-184518021952,-184518021888⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269502394566,0,true,158064584256,158064584320⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929520860986,0,false,-184665325696,-184665325632⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073230085986,0,false,-26600741440,-26600741376⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073268580482,0,false,-26561305024,-26561304960⟩
    { al := (316539/2048000), au := (253401/1638400), zl := (7993/8000), zu := (3997/4000),
      A := ⟨169940581613,170054532465⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158021118144,158021118208⟩ : DyadicInterval 40),(⟨-184605964288,-184605964224⟩ : DyadicInterval 40),(⟨748937575655,748937594984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158119810048,158119810112⟩ : DyadicInterval 40),(⟨-184740755456,-184740755392⟩ : DyadicInterval 40),(⟨748919815069,748919834398⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157892318720,157892318784⟩ : DyadicInterval 40),(⟨-184430095936,-184430095872⟩ : DyadicInterval 40),(⟨748960733776,748960753106⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158009347328,158009347392⟩ : DyadicInterval 40),(⟨-184589889856,-184589889792⟩ : DyadicInterval 40),(⟨748939693005,748939712335⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨64848448,75709774⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64846528,64846592⟩ : DyadicInterval 40),(⟨-64850368,-64850304⟩ : DyadicInterval 40),(⟨762123381647,762123400976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75707136,75707200⟩ : DyadicInterval 40),(⟨-75712384,-75712320⟩ : DyadicInterval 40),(⟨762123380962,762123400291⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5248,-3776⟩ : DyadicInterval 40),(⟨762123385504,762123405504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169866228688,169990766790⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157956716928,157956716992⟩ : DyadicInterval 40),(⟨-184518021952,-184518021888⟩ : DyadicInterval 40),(⟨748949157895,748949177224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158064584256,158064584320⟩ : DyadicInterval 40),(⟨-184665325696,-184665325632⟩ : DyadicInterval 40),(⟨748929755153,748929774482⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26600741440,-26561304960⟩ : DyadicInterval 40),(⟨775404036096,775423773600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158021118144,158119810112⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184740755456,-184605964224⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1866_ok : ecellOkT e1866 = true := by decide +kernel
theorem e1866_pos {a z : ℝ} (ha1 : ((316539/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((253401/1638400 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1866 e1866_ok ha1 ha2 hz1 hz2 hz

-- box ['253401/1638400', '633927/4096000', '7993/8000', '3997/4000']  interval_lower 19849817/137438953472
noncomputable def e1867 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269566160240,0,true,158119810048,158119810112⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929457095312,0,false,-184740755456,-184740755392⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269680111092,0,true,158218493120,158218493184⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929343144460,0,false,-184875563136,-184875563072⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269417362523,0,true,157990935808,157990935872⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929605893029,0,false,-184564747584,-184564747520⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269552484730,0,true,158107966272,158107966336⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929470770822,0,false,-184724577984,-184724577920⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576521244,0,true,64891520,64891584⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446734308,0,false,-64895424,-64895360⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587390078,0,true,75759680,75759744⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435865474,0,false,-75764928,-75764864⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622555,0,false,-5248,-5184⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623946,0,false,-3840,-3776⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269491757459,0,true,158055371456,158055371520⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929531498093,0,false,-184652743360,-184652743296⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269616302686,0,true,158163235200,158163235264⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929406952866,0,false,-184800073600,-184800073536⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073194852495,0,false,-26636838336,-26636838272⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073233374998,0,false,-26597371904,-26597371840⟩
    { al := (253401/1638400), au := (633927/4096000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨170054532464,170168483316⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158119810048,158119810112⟩ : DyadicInterval 40),(⟨-184740755456,-184740755392⟩ : DyadicInterval 40),(⟨748919815069,748919834399⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158218493120,158218493184⟩ : DyadicInterval 40),(⟨-184875563136,-184875563072⟩ : DyadicInterval 40),(⟨748902042363,748902061692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157990935808,157990935872⟩ : DyadicInterval 40),(⟨-184564747584,-184564747520⟩ : DyadicInterval 40),(⟨748943004506,748943023836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158107966272,158107966336⟩ : DyadicInterval 40),(⟨-184724577984,-184724577920⟩ : DyadicInterval 40),(⟨748921947198,748921966527⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨64893468,75762302⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64891520,64891584⟩ : DyadicInterval 40),(⟨-64895424,-64895360⟩ : DyadicInterval 40),(⟨762123381673,762123401003⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75759680,75759744⟩ : DyadicInterval 40),(⟨-75764928,-75764864⟩ : DyadicInterval 40),(⟨762123380955,762123400284⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5248,-3776⟩ : DyadicInterval 40),(⟨762123385504,762123405504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169980129683,170104674910⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158055371456,158055371520⟩ : DyadicInterval 40),(⟨-184652743360,-184652743296⟩ : DyadicInterval 40),(⟨748931412957,748931432287⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158163235200,158163235264⟩ : DyadicInterval 40),(⟨-184800073600,-184800073536⟩ : DyadicInterval 40),(⟨748911995937,748912015267⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26636838336,-26597371840⟩ : DyadicInterval 40),(⟨775422069536,775441822048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158119810048,158218493184⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184875563136,-184740755392⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1867_ok : ecellOkT e1867 = true := by decide +kernel
theorem e1867_pos {a z : ℝ} (ha1 : ((253401/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((633927/4096000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1867 e1867_ok ha1 ha2 hz1 hz2 hz

-- box ['633927/4096000', '1268703/8192000', '999/1000', '7993/8000']  interval_lower 10000033/68719476736
noncomputable def e1868 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269680111091,0,true,158218493120,158218493184⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929343144461,0,false,-184875563136,-184875563072⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269794061943,0,true,158317167296,158317167360⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929229193609,0,false,-185010387328,-185010387264⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269509942607,0,true,158071121536,158071121600⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929513312945,0,false,-184674254144,-184674254080⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269645064814,0,true,158188143488,158188143552⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929378190738,0,false,-184834100416,-184834100352⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587389226,0,true,75758784,75758848⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435866326,0,false,-75764096,-75764032⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099598273072,0,true,86641856,86641920⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099424982480,0,false,-86648768,-86648704⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620948,0,false,-6848,-6784⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622556,0,false,-5248,-5184⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269595023101,0,true,158144806528,158144806592⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929428232451,0,false,-184774899584,-184774899520⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269719568309,0,true,158252661568,158252661632⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929303687243,0,false,-184922246208,-184922246144⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073162890492,0,false,-26669584576,-26669584512⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073201436384,0,false,-26630093056,-26630092992⟩
    { al := (633927/4096000), au := (1268703/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨170168483315,170282434167⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158218493120,158218493184⟩ : DyadicInterval 40),(⟨-184875563136,-184875563072⟩ : DyadicInterval 40),(⟨748902042363,748902061692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158317167296,158317167360⟩ : DyadicInterval 40),(⟨-185010387328,-185010387264⟩ : DyadicInterval 40),(⟨748884257573,748884276902⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158071121536,158071121600⟩ : DyadicInterval 40),(⟨-184674254144,-184674254080⟩ : DyadicInterval 40),(⟨748928578735,748928598064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158188143488,158188143552⟩ : DyadicInterval 40),(⟨-184834100416,-184834100352⟩ : DyadicInterval 40),(⟨748907509737,748907529066⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨75761450,86645296⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75758784,75758848⟩ : DyadicInterval 40),(⟨-75764096,-75764032⟩ : DyadicInterval 40),(⟨762123380987,762123400316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨86641856,86641920⟩ : DyadicInterval 40),(⟨-86648768,-86648704⟩ : DyadicInterval 40),(⟨762123380179,762123399509⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6848,-5184⟩ : DyadicInterval 40),(⟨762123386208,762123406304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170083395325,170207940533⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158144806528,158144806592⟩ : DyadicInterval 40),(⟨-184774899584,-184774899520⟩ : DyadicInterval 40),(⟨748915314513,748915333843⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158252661568,158252661632⟩ : DyadicInterval 40),(⟨-184922246208,-184922246144⟩ : DyadicInterval 40),(⟨748895885478,748895904808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26669584576,-26630092992⟩ : DyadicInterval 40),(⟨775438430112,775458195168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158218493120,158317167360⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185010387328,-184875563072⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1868_ok : ecellOkT e1868 = true := by decide +kernel
theorem e1868_pos {a z : ℝ} (ha1 : ((633927/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1268703/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1868 e1868_ok ha1 ha2 hz1 hz2 hz

-- box ['1268703/8192000', '79347/512000', '999/1000', '7993/8000']  interval_lower 161053957/1099511627776
noncomputable def e1869 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269794061942,0,true,158317167296,158317167360⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929229193610,0,false,-185010387328,-185010387264⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269908012794,0,true,158415832640,158415832704⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929115242758,0,false,-185145228096,-185145228032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269623779507,0,true,158169710272,158169710336⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929399476045,0,false,-184808918912,-184808918848⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269758915958,0,true,158286734080,158286734144⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929264339594,0,false,-184968801600,-184968801536⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587441756,0,true,75811328,75811392⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435813796,0,false,-75816640,-75816576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099598333111,0,true,86701888,86701952⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099424922441,0,false,-86708800,-86708736⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620938,0,false,-6848,-6784⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622549,0,false,-5248,-5184⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269708916974,0,true,158243438016,158243438080⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929314338578,0,false,-184909644096,-184909644032⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269833469307,0,true,158351289536,158351289600⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929189786245,0,false,-185057017152,-185057017088⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073127614210,0,false,-26705727616,-26705727552⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073166188112,0,false,-26666206016,-26666205952⟩
    { al := (1268703/8192000), au := (79347/512000), zl := (999/1000), zu := (7993/8000),
      A := ⟨170282434166,170396385018⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158317167296,158317167360⟩ : DyadicInterval 40),(⟨-185010387328,-185010387264⟩ : DyadicInterval 40),(⟨748884257573,748884276902⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158415832640,158415832704⟩ : DyadicInterval 40),(⟨-185145228096,-185145228032⟩ : DyadicInterval 40),(⟨748866460687,748866480017⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158169710272,158169710336⟩ : DyadicInterval 40),(⟨-184808918912,-184808918848⟩ : DyadicInterval 40),(⟨748910829805,748910849134⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158286734080,158286734144⟩ : DyadicInterval 40),(⟨-184968801600,-184968801536⟩ : DyadicInterval 40),(⟨748889744235,748889763565⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨75813980,86705335⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75811328,75811392⟩ : DyadicInterval 40),(⟨-75816640,-75816576⟩ : DyadicInterval 40),(⟨762123380980,762123400309⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨86701888,86701952⟩ : DyadicInterval 40),(⟨-86708800,-86708736⟩ : DyadicInterval 40),(⟨762123380170,762123399499⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6848,-5184⟩ : DyadicInterval 40),(⟨762123386208,762123406304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170197289198,170321841531⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158243438016,158243438080⟩ : DyadicInterval 40),(⟨-184909644096,-184909644032⟩ : DyadicInterval 40),(⟨748897547659,748897566988⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158351289536,158351289600⟩ : DyadicInterval 40),(⟨-185057017152,-185057017088⟩ : DyadicInterval 40),(⟨748878104277,748878123607⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26705727616,-26666205952⟩ : DyadicInterval 40),(⟨775456486592,775476266688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158317167296,158415832704⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185145228096,-185010387264⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1869_ok : ecellOkT e1869 = true := by decide +kernel
theorem e1869_pos {a z : ℝ} (ha1 : ((1268703/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((79347/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1869 e1869_ok ha1 ha2 hz1 hz2 hz

-- box ['633927/4096000', '1268703/8192000', '7993/8000', '3997/4000']  interval_lower 159849241/1099511627776
noncomputable def e1870 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269680111091,0,true,158218493120,158218493184⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929343144461,0,false,-184875563136,-184875563072⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269794061943,0,true,158317167296,158317167360⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929229193609,0,false,-185010387328,-185010387264⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269531213667,0,true,158089544064,158089544128⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929492041885,0,false,-184699415808,-184699415744⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269666350118,0,true,158206576384,158206576448⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929356905434,0,false,-184859282560,-184859282496⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576566269,0,true,64936512,64936576⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446689283,0,false,-64940416,-64940352⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587442610,0,true,75812160,75812224⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435812942,0,false,-75817472,-75817408⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622548,0,false,-5248,-5184⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623941,0,false,-3840,-3776⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269605658455,0,true,158154017088,158154017152⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929417597097,0,false,-184787481280,-184787481216⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269730210809,0,true,158261877376,158261877440⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929293044743,0,false,-184934838016,-184934837952⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073159595402,0,false,-26672960576,-26672960512⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073198145916,0,false,-26633464192,-26633464128⟩
    { al := (633927/4096000), au := (1268703/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨170168483315,170282434167⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158218493120,158218493184⟩ : DyadicInterval 40),(⟨-184875563136,-184875563072⟩ : DyadicInterval 40),(⟨748902042363,748902061692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158317167296,158317167360⟩ : DyadicInterval 40),(⟨-185010387328,-185010387264⟩ : DyadicInterval 40),(⟨748884257573,748884276902⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158089544064,158089544128⟩ : DyadicInterval 40),(⟨-184699415808,-184699415744⟩ : DyadicInterval 40),(⟨748925263187,748925282517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158206576384,158206576448⟩ : DyadicInterval 40),(⟨-184859282560,-184859282496⟩ : DyadicInterval 40),(⟨748904189280,748904208610⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨64938493,75814834⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64936512,64936576⟩ : DyadicInterval 40),(⟨-64940416,-64940352⟩ : DyadicInterval 40),(⟨762123381668,762123400997⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75812160,75812224⟩ : DyadicInterval 40),(⟨-75817472,-75817408⟩ : DyadicInterval 40),(⟨762123380980,762123400309⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5248,-3776⟩ : DyadicInterval 40),(⟨762123385504,762123405504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170094030679,170218583033⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158154017088,158154017152⟩ : DyadicInterval 40),(⟨-184787481280,-184787481216⟩ : DyadicInterval 40),(⟨748913655958,748913675287⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158261877376,158261877440⟩ : DyadicInterval 40),(⟨-184934838016,-184934837952⟩ : DyadicInterval 40),(⟨748894224582,748894243912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26672960576,-26633464128⟩ : DyadicInterval 40),(⟨775440115680,775459883168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158218493120,158317167360⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185010387328,-184875563072⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1870_ok : ecellOkT e1870 = true := by decide +kernel
theorem e1870_pos {a z : ℝ} (ha1 : ((633927/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1268703/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1870 e1870_ok ha1 ha2 hz1 hz2 hz

-- box ['1268703/8192000', '79347/512000', '7993/8000', '3997/4000']  interval_lower 160902497/1099511627776
noncomputable def e1871 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269794061942,0,true,158317167296,158317167360⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929229193610,0,false,-185010387328,-185010387264⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269908012794,0,true,158415832640,158415832704⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929115242758,0,false,-185145228096,-185145228032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269645064811,0,true,158188143488,158188143552⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929378190741,0,false,-184834100416,-184834100352⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269780215506,0,true,158305177664,158305177728⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929243040046,0,false,-184994003648,-184994003584⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576611295,0,true,64981568,64981632⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446644257,0,false,-64985472,-64985408⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587495145,0,true,75864704,75864768⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435760407,0,false,-75870016,-75869952⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622541,0,false,-5248,-5184⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623936,0,false,-3904,-3840⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269719559453,0,true,158252653888,158252653952⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929303696099,0,false,-184922235712,-184922235648⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269844118930,0,true,158360510656,158360510720⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929179136622,0,false,-185069618944,-185069618880⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073124314709,0,false,-26709108224,-26709108160⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073162893235,0,false,-26669581824,-26669581760⟩
    { al := (1268703/8192000), au := (79347/512000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨170282434166,170396385018⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158317167296,158317167360⟩ : DyadicInterval 40),(⟨-185010387328,-185010387264⟩ : DyadicInterval 40),(⟨748884257573,748884276902⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158415832640,158415832704⟩ : DyadicInterval 40),(⟨-185145228096,-185145228032⟩ : DyadicInterval 40),(⟨748866460687,748866480017⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158188143488,158188143552⟩ : DyadicInterval 40),(⟨-184834100416,-184834100352⟩ : DyadicInterval 40),(⟨748907509737,748907529067⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158305177664,158305177728⟩ : DyadicInterval 40),(⟨-184994003648,-184994003584⟩ : DyadicInterval 40),(⟨748886419278,748886438607⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨64983519,75867369⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64981568,64981632⟩ : DyadicInterval 40),(⟨-64985472,-64985408⟩ : DyadicInterval 40),(⟨762123381663,762123400992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75864704,75864768⟩ : DyadicInterval 40),(⟨-75870016,-75869952⟩ : DyadicInterval 40),(⟨762123380972,762123400302⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5248,-3840⟩ : DyadicInterval 40),(⟨762123385536,762123405504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170207931677,170332491154⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158252653888,158252653952⟩ : DyadicInterval 40),(⟨-184922235712,-184922235648⟩ : DyadicInterval 40),(⟨748895886859,748895906189⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158360510656,158360510720⟩ : DyadicInterval 40),(⟨-185069618944,-185069618880⟩ : DyadicInterval 40),(⟨748876441161,748876460490⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26709108224,-26669581760⟩ : DyadicInterval 40),(⟨775458174496,775477956992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158317167296,158415832704⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185145228096,-185010387264⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1871_ok : ecellOkT e1871 = true := by decide +kernel
theorem e1871_pos {a z : ℝ} (ha1 : ((1268703/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((79347/512000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1871 e1871_ok ha1 ha2 hz1 hz2 hz

-- box ['316539/2048000', '253401/1638400', '3997/4000', '1599/1600']  interval_lower 157600013/1099511627776
noncomputable def e1872 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269452209389,0,true,158021118144,158021118208⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929571046163,0,false,-184605964288,-184605964224⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269566160241,0,true,158119810048,158119810112⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929457095311,0,false,-184740755456,-184740755392⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269324753952,0,true,157910719552,157910719616⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929698501600,0,false,-184455218240,-184455218176⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269459876159,0,true,158027758592,158027758656⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929563379393,0,false,-184615032704,-184615032640⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565668225,0,true,54039104,54039168⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457587327,0,false,-54041792,-54041728⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576522048,0,true,64892352,64892416⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446733504,0,false,-64896192,-64896128⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623945,0,false,-3840,-3776⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625120,0,false,-2688,-2624⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269388477601,0,true,157965916736,157965916800⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929634777951,0,false,-184530583872,-184530583808⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269513022848,0,true,158073789312,158073789376⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929510232704,0,false,-184677897792,-184677897728⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073226799497,0,false,-26604108416,-26604108352⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073265298609,0,false,-26564667136,-26564667072⟩
    { al := (316539/2048000), au := (253401/1638400), zl := (3997/4000), zu := (1599/1600),
      A := ⟨169940581613,170054532465⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158021118144,158021118208⟩ : DyadicInterval 40),(⟨-184605964288,-184605964224⟩ : DyadicInterval 40),(⟨748937575655,748937594984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158119810048,158119810112⟩ : DyadicInterval 40),(⟨-184740755456,-184740755392⟩ : DyadicInterval 40),(⟨748919815069,748919834398⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157910719552,157910719616⟩ : DyadicInterval 40),(⟨-184455218240,-184455218176⟩ : DyadicInterval 40),(⟨748957426730,748957446060⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158027758592,158027758656⟩ : DyadicInterval 40),(⟨-184615032704,-184615032640⟩ : DyadicInterval 40),(⟨748936381053,748936400383⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54040449,64894272⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54039104,54039168⟩ : DyadicInterval 40),(⟨-54041792,-54041728⟩ : DyadicInterval 40),(⟨762123382239,762123401569⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64892352,64892416⟩ : DyadicInterval 40),(⟨-64896192,-64896128⟩ : DyadicInterval 40),(⟨762123381641,762123400970⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3840,-2624⟩ : DyadicInterval 40),(⟨762123384928,762123404800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169876849825,170001395072⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157965916736,157965916800⟩ : DyadicInterval 40),(⟨-184530583872,-184530583808⟩ : DyadicInterval 40),(⟨748947503705,748947523034⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158073789312,158073789376⟩ : DyadicInterval 40),(⟨-184677897792,-184677897728⟩ : DyadicInterval 40),(⟨748928098655,748928117984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26604108416,-26564667072⟩ : DyadicInterval 40),(⟨775405717152,775425457088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158021118144,158119810112⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184740755456,-184605964224⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1872_ok : ecellOkT e1872 = true := by decide +kernel
theorem e1872_pos {a z : ℝ} (ha1 : ((316539/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((253401/1638400 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1872 e1872_ok ha1 ha2 hz1 hz2 hz

-- box ['253401/1638400', '633927/4096000', '3997/4000', '1599/1600']  interval_lower 79323769/549755813888
noncomputable def e1873 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269566160240,0,true,158119810048,158119810112⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929457095312,0,false,-184740755456,-184740755392⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269680111092,0,true,158218493120,158218493184⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929343144460,0,false,-184875563136,-184875563072⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269438619340,0,true,158009347328,158009347392⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929584636212,0,false,-184589889856,-184589889792⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269573755790,0,true,158126388224,158126388288⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929449499762,0,false,-184749740736,-184749740672⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565705743,0,true,54076608,54076672⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457549809,0,false,-54079360,-54079296⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576567072,0,true,64937344,64937408⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446688480,0,false,-64941248,-64941184⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623940,0,false,-3840,-3776⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625117,0,false,-2688,-2624⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269502385716,0,true,158064576576,158064576640⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929520869836,0,false,-184665315264,-184665315200⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269626938091,0,true,158172445632,158172445696⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929396317461,0,false,-184812655616,-184812655552⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073191561600,0,false,-26640209920,-26640209856⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073230088723,0,false,-26600738624,-26600738560⟩
    { al := (253401/1638400), au := (633927/4096000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨170054532464,170168483316⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158119810048,158119810112⟩ : DyadicInterval 40),(⟨-184740755456,-184740755392⟩ : DyadicInterval 40),(⟨748919815069,748919834399⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158218493120,158218493184⟩ : DyadicInterval 40),(⟨-184875563136,-184875563072⟩ : DyadicInterval 40),(⟨748902042363,748902061692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158009347328,158009347392⟩ : DyadicInterval 40),(⟨-184589889856,-184589889792⟩ : DyadicInterval 40),(⟨748939693005,748939712335⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158126388224,158126388288⟩ : DyadicInterval 40),(⟨-184749740736,-184749740672⟩ : DyadicInterval 40),(⟨748918630757,748918650086⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54077967,64939296⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54076608,54076672⟩ : DyadicInterval 40),(⟨-54079360,-54079296⟩ : DyadicInterval 40),(⟨762123382268,762123401597⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64937344,64937408⟩ : DyadicInterval 40),(⟨-64941248,-64941184⟩ : DyadicInterval 40),(⟨762123381668,762123400997⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3840,-2624⟩ : DyadicInterval 40),(⟨762123384928,762123404800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169990757940,170115310315⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158064576576,158064576640⟩ : DyadicInterval 40),(⟨-184665315264,-184665315200⟩ : DyadicInterval 40),(⟨748929756556,748929775885⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158172445632,158172445696⟩ : DyadicInterval 40),(⟨-184812655616,-184812655552⟩ : DyadicInterval 40),(⟨748910337161,748910356491⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26640209920,-26600738560⟩ : DyadicInterval 40),(⟨775423752896,775443507840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158119810048,158218493184⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184875563136,-184740755392⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1873_ok : ecellOkT e1873 = true := by decide +kernel
theorem e1873_pos {a z : ℝ} (ha1 : ((253401/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((633927/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1873 e1873_ok ha1 ha2 hz1 hz2 hz

-- box ['316539/2048000', '253401/1638400', '1599/1600', '1999/2000']  interval_lower 157449107/1099511627776
noncomputable def e1874 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269452209389,0,true,158021118144,158021118208⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929571046163,0,false,-184605964288,-184605964224⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269566160241,0,true,158119810048,158119810112⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929457095311,0,false,-184740755456,-184740755392⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269345996525,0,true,157929120064,157929120128⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929677259027,0,false,-184480341184,-184480341120⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269481132975,0,true,158046169472,158046169536⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929542122577,0,false,-184640176064,-184640176000⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554860180,0,true,43231552,43231616⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468395372,0,false,-43233280,-43233216⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565706499,0,true,54077376,54077440⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457549053,0,false,-54080064,-54080000⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625116,0,false,-2688,-2624⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626077,0,false,-1728,-1664⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269399098757,0,true,157975116416,157975116480⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929624156795,0,false,-184543145984,-184543145920⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269523651152,0,true,158082994304,158082994368⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929499604400,0,false,-184690470016,-184690469952⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073223512796,0,false,-26607475648,-26607475584⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073262016524,0,false,-26568029504,-26568029440⟩
    { al := (316539/2048000), au := (253401/1638400), zl := (1599/1600), zu := (1999/2000),
      A := ⟨169940581613,170054532465⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158021118144,158021118208⟩ : DyadicInterval 40),(⟨-184605964288,-184605964224⟩ : DyadicInterval 40),(⟨748937575655,748937594984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158119810048,158119810112⟩ : DyadicInterval 40),(⟨-184740755456,-184740755392⟩ : DyadicInterval 40),(⟨748919815069,748919834398⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157929120064,157929120128⟩ : DyadicInterval 40),(⟨-184480341184,-184480341120⟩ : DyadicInterval 40),(⟨748954119298,748954138628⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158046169472,158046169536⟩ : DyadicInterval 40),(⟨-184640176064,-184640176000⟩ : DyadicInterval 40),(⟨748933068697,748933088027⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨43232404,54078723⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43231552,43231616⟩ : DyadicInterval 40),(⟨-43233280,-43233216⟩ : DyadicInterval 40),(⟨762123382716,762123402045⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54077376,54077440⟩ : DyadicInterval 40),(⟨-54080064,-54080000⟩ : DyadicInterval 40),(⟨762123382236,762123401565⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2688,-1664⟩ : DyadicInterval 40),(⟨762123384448,762123404224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169887470981,170012023376⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157975116416,157975116480⟩ : DyadicInterval 40),(⟨-184543145984,-184543145920⟩ : DyadicInterval 40),(⟨748945849456,748945868785⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158082994304,158082994368⟩ : DyadicInterval 40),(⟨-184690470016,-184690469952⟩ : DyadicInterval 40),(⟨748926442035,748926461364⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26607475648,-26568029440⟩ : DyadicInterval 40),(⟨775407398336,775427140704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158021118144,158119810112⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184740755456,-184605964224⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1874_ok : ecellOkT e1874 = true := by decide +kernel
theorem e1874_pos {a z : ℝ} (ha1 : ((316539/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((253401/1638400 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1874 e1874_ok ha1 ha2 hz1 hz2 hz

-- box ['253401/1638400', '633927/4096000', '1599/1600', '1999/2000']  interval_lower 158496471/1099511627776
noncomputable def e1875 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269566160240,0,true,158119810048,158119810112⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929457095312,0,false,-184740755456,-184740755392⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269680111092,0,true,158218493120,158218493184⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929343144460,0,false,-184875563136,-184875563072⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269459876157,0,true,158027758592,158027758656⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929563379395,0,false,-184615032704,-184615032640⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269595026851,0,true,158144809792,158144809856⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929428228701,0,false,-184774904064,-184774904000⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554890194,0,true,43261504,43261568⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468365358,0,false,-43263296,-43263232⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565744019,0,true,54114880,54114944⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457511533,0,false,-54117632,-54117568⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625112,0,false,-2688,-2624⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626074,0,false,-1728,-1664⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269513013998,0,true,158073781632,158073781696⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929510241554,0,false,-184677887296,-184677887232⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269637573516,0,true,158181656000,158181656064⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929385682036,0,false,-184825237824,-184825237760⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073188270493,0,false,-26643581760,-26643581696⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073226802235,0,false,-26604105600,-26604105536⟩
    { al := (253401/1638400), au := (633927/4096000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨170054532464,170168483316⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158119810048,158119810112⟩ : DyadicInterval 40),(⟨-184740755456,-184740755392⟩ : DyadicInterval 40),(⟨748919815069,748919834399⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158218493120,158218493184⟩ : DyadicInterval 40),(⟨-184875563136,-184875563072⟩ : DyadicInterval 40),(⟨748902042363,748902061692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158027758592,158027758656⟩ : DyadicInterval 40),(⟨-184615032704,-184615032640⟩ : DyadicInterval 40),(⟨748936381053,748936400383⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158144809792,158144809856⟩ : DyadicInterval 40),(⟨-184774904064,-184774904000⟩ : DyadicInterval 40),(⟨748915313938,748915333267⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨43262418,54116243⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43261504,43261568⟩ : DyadicInterval 40),(⟨-43263296,-43263232⟩ : DyadicInterval 40),(⟨762123382745,762123402074⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54114880,54114944⟩ : DyadicInterval 40),(⟨-54117632,-54117568⟩ : DyadicInterval 40),(⟨762123382264,762123401593⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2688,-1664⟩ : DyadicInterval 40),(⟨762123384448,762123404224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170001386222,170125945740⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158073781632,158073781696⟩ : DyadicInterval 40),(⟨-184677887296,-184677887232⟩ : DyadicInterval 40),(⟨748928100031,748928119361⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158181656000,158181656064⟩ : DyadicInterval 40),(⟨-184825237824,-184825237760⟩ : DyadicInterval 40),(⟨748908678290,748908697619⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26643581760,-26604105536⟩ : DyadicInterval 40),(⟨775425436384,775445193760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158119810048,158218493184⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184875563136,-184740755392⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1875_ok : ecellOkT e1875 = true := by decide +kernel
theorem e1875_pos {a z : ℝ} (ha1 : ((253401/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((633927/4096000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1875 e1875_ok ha1 ha2 hz1 hz2 hz

-- box ['633927/4096000', '1268703/8192000', '3997/4000', '1599/1600']  interval_lower 39924439/274877906944
noncomputable def e1876 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269680111091,0,true,158218493120,158218493184⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929343144461,0,false,-184875563136,-184875563072⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269794061943,0,true,158317167296,158317167360⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929229193609,0,false,-185010387328,-185010387264⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269552484728,0,true,158107966272,158107966336⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929470770824,0,false,-184724577984,-184724577920⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269687635422,0,true,158225008960,158225009024⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929335620130,0,false,-184884465280,-184884465216⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565743264,0,true,54114112,54114176⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457512288,0,false,-54116864,-54116800⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576612100,0,true,64982400,64982464⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446643452,0,false,-64986304,-64986240⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623935,0,false,-3904,-3840⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625113,0,false,-2688,-2624⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269616293834,0,true,158163227584,158163227648⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929406961718,0,false,-184800063104,-184800063040⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269740853331,0,true,158271093120,158271093184⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929282402221,0,false,-184947430016,-184947429952⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073156300100,0,false,-26676336832,-26676336768⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073194855235,0,false,-26636835520,-26636835456⟩
    { al := (633927/4096000), au := (1268703/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨170168483315,170282434167⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158218493120,158218493184⟩ : DyadicInterval 40),(⟨-184875563136,-184875563072⟩ : DyadicInterval 40),(⟨748902042363,748902061692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158317167296,158317167360⟩ : DyadicInterval 40),(⟨-185010387328,-185010387264⟩ : DyadicInterval 40),(⟨748884257573,748884276902⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158107966272,158107966336⟩ : DyadicInterval 40),(⟨-184724577984,-184724577920⟩ : DyadicInterval 40),(⟨748921947198,748921966528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158225008960,158225009024⟩ : DyadicInterval 40),(⟨-184884465280,-184884465216⟩ : DyadicInterval 40),(⟨748900868408,748900887737⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54115488,64984324⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54114112,54114176⟩ : DyadicInterval 40),(⟨-54116864,-54116800⟩ : DyadicInterval 40),(⟨762123382264,762123401593⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64982400,64982464⟩ : DyadicInterval 40),(⟨-64986304,-64986240⟩ : DyadicInterval 40),(⟨762123381663,762123400992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3904,-2624⟩ : DyadicInterval 40),(⟨762123384928,762123404832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170104666058,170229225555⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158163227584,158163227648⟩ : DyadicInterval 40),(⟨-184800063104,-184800063040⟩ : DyadicInterval 40),(⟨748911997279,748912016608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158271093120,158271093184⟩ : DyadicInterval 40),(⟨-184947430016,-184947429952⟩ : DyadicInterval 40),(⟨748892563589,748892582919⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26676336832,-26636835456⟩ : DyadicInterval 40),(⟨775441801344,775461571296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158218493120,158317167360⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185010387328,-184875563072⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1876_ok : ecellOkT e1876 = true := by decide +kernel
theorem e1876_pos {a z : ℝ} (ha1 : ((633927/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1268703/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1876 e1876_ok ha1 ha2 hz1 hz2 hz

-- box ['1268703/8192000', '79347/512000', '3997/4000', '1599/1600']  interval_lower 160750601/1099511627776
noncomputable def e1877 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269794061942,0,true,158317167296,158317167360⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929229193610,0,false,-185010387328,-185010387264⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269908012794,0,true,158415832640,158415832704⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929115242758,0,false,-185145228096,-185145228032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269666350116,0,true,158206576384,158206576448⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929356905436,0,false,-184859282560,-184859282496⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269801515054,0,true,158323620928,158323620992⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929221740498,0,false,-185019206272,-185019206208⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565780786,0,true,54151616,54151680⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457474766,0,false,-54154368,-54154304⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576657131,0,true,65027392,65027456⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446598421,0,false,-65031296,-65031232⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623929,0,false,-3904,-3840⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625109,0,false,-2688,-2624⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269730201954,0,true,158261869696,158261869760⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929293053598,0,false,-184934827520,-184934827456⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269854768576,0,true,158369731776,158369731840⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929168486976,0,false,-185082220928,-185082220864⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073121014994,0,false,-26712489088,-26712489024⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073159598145,0,false,-26672957824,-26672957760⟩
    { al := (1268703/8192000), au := (79347/512000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨170282434166,170396385018⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158317167296,158317167360⟩ : DyadicInterval 40),(⟨-185010387328,-185010387264⟩ : DyadicInterval 40),(⟨748884257573,748884276902⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158415832640,158415832704⟩ : DyadicInterval 40),(⟨-185145228096,-185145228032⟩ : DyadicInterval 40),(⟨748866460687,748866480017⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158206576384,158206576448⟩ : DyadicInterval 40),(⟨-184859282560,-184859282496⟩ : DyadicInterval 40),(⟨748904189281,748904208610⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158323620928,158323620992⟩ : DyadicInterval 40),(⟨-185019206272,-185019206208⟩ : DyadicInterval 40),(⟨748883093904,748883113233⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54153010,65029355⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54151616,54151680⟩ : DyadicInterval 40),(⟨-54154368,-54154304⟩ : DyadicInterval 40),(⟨762123382260,762123401589⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65027392,65027456⟩ : DyadicInterval 40),(⟨-65031296,-65031232⟩ : DyadicInterval 40),(⟨762123381657,762123400987⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3904,-2624⟩ : DyadicInterval 40),(⟨762123384928,762123404832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170218574178,170343140800⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158261869696,158261869760⟩ : DyadicInterval 40),(⟨-184934827520,-184934827456⟩ : DyadicInterval 40),(⟨748894225963,748894245292⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158369731776,158369731840⟩ : DyadicInterval 40),(⟨-185082220928,-185082220864⟩ : DyadicInterval 40),(⟨748874777910,748874797240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26712489088,-26672957760⟩ : DyadicInterval 40),(⟨775459862496,775479647424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158317167296,158415832704⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185145228096,-185010387264⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1877_ok : ecellOkT e1877 = true := by decide +kernel
theorem e1877_pos {a z : ℝ} (ha1 : ((1268703/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((79347/512000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1877 e1877_ok ha1 ha2 hz1 hz2 hz

-- box ['633927/4096000', '1268703/8192000', '1599/1600', '1999/2000']  interval_lower 159546325/1099511627776
noncomputable def e1878 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269680111091,0,true,158218493120,158218493184⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929343144461,0,false,-184875563136,-184875563072⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269794061943,0,true,158317167296,158317167360⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929229193609,0,false,-185010387328,-185010387264⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269573755788,0,true,158126388224,158126388288⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929449499764,0,false,-184749740736,-184749740672⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269708920727,0,true,158243441280,158243441344⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929314334825,0,false,-184909648512,-184909648448⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554920210,0,true,43291520,43291584⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468335342,0,false,-43293312,-43293248⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565781542,0,true,54152384,54152448⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457474010,0,false,-54155136,-54155072⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625108,0,false,-2688,-2624⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626072,0,false,-1728,-1664⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269626929239,0,true,158172437952,158172438016⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929396326313,0,false,-184812645184,-184812645120⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269751495883,0,true,158280308864,158280308928⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929271759669,0,false,-184960022144,-184960022080⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073153004582,0,false,-26679713280,-26679713216⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073191564340,0,false,-26640207168,-26640207104⟩
    { al := (633927/4096000), au := (1268703/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨170168483315,170282434167⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158218493120,158218493184⟩ : DyadicInterval 40),(⟨-184875563136,-184875563072⟩ : DyadicInterval 40),(⟨748902042363,748902061692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158317167296,158317167360⟩ : DyadicInterval 40),(⟨-185010387328,-185010387264⟩ : DyadicInterval 40),(⟨748884257573,748884276902⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158126388224,158126388288⟩ : DyadicInterval 40),(⟨-184749740736,-184749740672⟩ : DyadicInterval 40),(⟨748918630757,748918650086⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158243441280,158243441344⟩ : DyadicInterval 40),(⟨-184909648512,-184909648448⟩ : DyadicInterval 40),(⟨748897547055,748897566384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨43292434,54153766⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43291520,43291584⟩ : DyadicInterval 40),(⟨-43293312,-43293248⟩ : DyadicInterval 40),(⟨762123382743,762123402072⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54152384,54152448⟩ : DyadicInterval 40),(⟨-54155136,-54155072⟩ : DyadicInterval 40),(⟨762123382260,762123401589⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2688,-1664⟩ : DyadicInterval 40),(⟨762123384448,762123404224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170115301463,170239868107⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158172437952,158172438016⟩ : DyadicInterval 40),(⟨-184812645184,-184812645120⟩ : DyadicInterval 40),(⟨748910338567,748910357896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158280308864,158280308928⟩ : DyadicInterval 40),(⟨-184960022144,-184960022080⟩ : DyadicInterval 40),(⟨748890902435,748890921765⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26679713280,-26640207104⟩ : DyadicInterval 40),(⟨775443487168,775463259520⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158218493120,158317167360⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185010387328,-184875563072⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1878_ok : ecellOkT e1878 = true := by decide +kernel
theorem e1878_pos {a z : ℝ} (ha1 : ((633927/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1268703/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1878 e1878_ok ha1 ha2 hz1 hz2 hz

-- box ['1268703/8192000', '79347/512000', '1599/1600', '1999/2000']  interval_lower 160598845/1099511627776
noncomputable def e1879 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269794061942,0,true,158317167296,158317167360⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929229193610,0,false,-185010387328,-185010387264⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269908012794,0,true,158415832640,158415832704⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929115242758,0,false,-185145228096,-185145228032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269687635420,0,true,158225008960,158225009024⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929335620132,0,false,-184884465280,-184884465216⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269822814602,0,true,158342063872,158342063936⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929200440950,0,false,-185044409472,-185044409408⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554950229,0,true,43321536,43321600⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468305323,0,false,-43323328,-43323264⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565819068,0,true,54189952,54190016⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457436484,0,false,-54192640,-54192576⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625105,0,false,-2688,-2624⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626070,0,false,-1728,-1664⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269740844476,0,true,158271085504,158271085568⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929282411076,0,false,-184947419520,-184947419456⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269865418245,0,true,158378952832,158378952896⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929157837307,0,false,-185094823040,-185094822976⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073117715065,0,false,-26715870144,-26715870080⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073156302843,0,false,-26676334016,-26676333952⟩
    { al := (1268703/8192000), au := (79347/512000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨170282434166,170396385018⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158317167296,158317167360⟩ : DyadicInterval 40),(⟨-185010387328,-185010387264⟩ : DyadicInterval 40),(⟨748884257573,748884276902⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158415832640,158415832704⟩ : DyadicInterval 40),(⟨-185145228096,-185145228032⟩ : DyadicInterval 40),(⟨748866460687,748866480017⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158225008960,158225009024⟩ : DyadicInterval 40),(⟨-184884465280,-184884465216⟩ : DyadicInterval 40),(⟨748900868408,748900887737⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158342063872,158342063936⟩ : DyadicInterval 40),(⟨-185044409472,-185044409408⟩ : DyadicInterval 40),(⟨748879768112,748879787441⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨43322453,54191292⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43321536,43321600⟩ : DyadicInterval 40),(⟨-43323328,-43323264⟩ : DyadicInterval 40),(⟨762123382740,762123402070⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54189952,54190016⟩ : DyadicInterval 40),(⟨-54192640,-54192576⟩ : DyadicInterval 40),(⟨762123382225,762123401554⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2688,-1664⟩ : DyadicInterval 40),(⟨762123384448,762123404224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170229216700,170353790469⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158271085504,158271085568⟩ : DyadicInterval 40),(⟨-184947419520,-184947419456⟩ : DyadicInterval 40),(⟨748892564934,748892584263⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158378952832,158378952896⟩ : DyadicInterval 40),(⟨-185094823040,-185094822976⟩ : DyadicInterval 40),(⟨748873114536,748873133865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26715870144,-26676333952⟩ : DyadicInterval 40),(⟨775461550592,775481337952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158317167296,158415832704⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185145228096,-185010387264⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1879_ok : ecellOkT e1879 = true := by decide +kernel
theorem e1879_pos {a z : ℝ} (ha1 : ((1268703/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((79347/512000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1879 e1879_ok ha1 ha2 hz1 hz2 hz

-- box ['31569/204800', '1263609/8192000', '1999/2000', '7997/8000']  interval_lower 38284381/274877906944
noncomputable def e1880 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268996405985,0,true,157626261888,157626261952⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930026849567,0,false,-184066964800,-184066964736⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269110356837,0,true,157724989248,157724989312⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929912898715,0,false,-184201689920,-184201689856⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268911663595,0,true,157552835072,157552835136⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930111591957,0,false,-183966783808,-183966783744⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269046757314,0,true,157669887552,157669887616⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929976498238,0,false,-184126493568,-184126493504⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543962058,0,true,32333760,32333824⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479293494,0,false,-32334784,-32334720⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554770856,0,true,43142208,43142272⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468484696,0,false,-43143936,-43143872⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626083,0,false,-1728,-1664⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626826,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268954030494,0,true,157589545408,157589545472⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930069225058,0,false,-184016868096,-184016868032⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269078561538,0,true,157697442624,157697442688⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929944694014,0,false,-184164096384,-184164096320⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073360976614,0,false,-26466653696,-26466653632⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073399372923,0,false,-26427322624,-26427322560⟩
    { al := (31569/204800), au := (1263609/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨169484778209,169598729061⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157626261888,157626261952⟩ : DyadicInterval 40),(⟨-184066964800,-184066964736⟩ : DyadicInterval 40),(⟨749008497035,749008516365⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157724989248,157724989312⟩ : DyadicInterval 40),(⟨-184201689920,-184201689856⟩ : DyadicInterval 40),(⟨748990784843,748990804173⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157552835072,157552835136⟩ : DyadicInterval 40),(⟨-183966783808,-183966783744⟩ : DyadicInterval 40),(⟨749021661308,749021680638⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157669887552,157669887616⟩ : DyadicInterval 40),(⟨-184126493568,-184126493504⟩ : DyadicInterval 40),(⟨749000672034,749000691363⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32334282,43143080⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32333760,32333824⟩ : DyadicInterval 40),(⟨-32334784,-32334720⟩ : DyadicInterval 40),(⟨762123383113,762123402442⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43142208,43142272⟩ : DyadicInterval 40),(⟨-43143936,-43143872⟩ : DyadicInterval 40),(⟨762123382723,762123402052⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1728,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169442402718,169566933762⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157589545408,157589545472⟩ : DyadicInterval 40),(⟨-184016868096,-184016868032⟩ : DyadicInterval 40),(⟨749015080659,749015099988⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157697442624,157697442688⟩ : DyadicInterval 40),(⟨-184164096384,-184164096320⟩ : DyadicInterval 40),(⟨748995728211,748995747541⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26466653696,-26427322560⟩ : DyadicInterval 40),(⟨775337044896,775356729728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157626261888,157724989312⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184201689920,-184066964736⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1880_ok : ecellOkT e1880 = true := by decide +kernel
theorem e1880_pos {a z : ℝ} (ha1 : ((31569/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1263609/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1880 e1880_ok ha1 ha2 hz1 hz2 hz

-- box ['1263609/8192000', '632229/4096000', '1999/2000', '7997/8000']  interval_lower 154173889/1099511627776
noncomputable def e1881 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269110356836,0,true,157724989248,157724989312⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929912898716,0,false,-184201689920,-184201689856⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269224307688,0,true,157823707776,157823707840⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929798947864,0,false,-184336431488,-184336431424⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269025557471,0,true,157651519680,157651519744⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929997698081,0,false,-184101429248,-184101429184⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269160665434,0,true,157768573952,157768574016⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929862590118,0,false,-184261175424,-184261175360⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543984563,0,true,32356288,32356352⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479270989,0,false,-32357312,-32357248⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554800863,0,true,43172224,43172288⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468454689,0,false,-43173952,-43173888⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626080,0,false,-1728,-1664⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626824,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269067952858,0,true,157688251392,157688251456⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929955302694,0,false,-184151553344,-184151553280⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269192491026,0,true,157796145088,157796145152⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929830764526,0,false,-184298808128,-184298808064⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073325824346,0,false,-26502662976,-26502662912⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073364248659,0,false,-26463301952,-26463301888⟩
    { al := (1263609/8192000), au := (632229/4096000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨169598729060,169712679912⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157724989248,157724989312⟩ : DyadicInterval 40),(⟨-184201689920,-184201689856⟩ : DyadicInterval 40),(⟨748990784843,748990804173⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157823707776,157823707840⟩ : DyadicInterval 40),(⟨-184336431488,-184336431424⟩ : DyadicInterval 40),(⟨748973060509,748973079838⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157651519680,157651519744⟩ : DyadicInterval 40),(⟨-184101429248,-184101429184⟩ : DyadicInterval 40),(⟨749003966937,749003986266⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157768573952,157768574016⟩ : DyadicInterval 40),(⟨-184261175424,-184261175360⟩ : DyadicInterval 40),(⟨748982961143,748982980473⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32356787,43173087⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32356288,32356352⟩ : DyadicInterval 40),(⟨-32357312,-32357248⟩ : DyadicInterval 40),(⟨762123383111,762123402440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43172224,43172288⟩ : DyadicInterval 40),(⟨-43173952,-43173888⟩ : DyadicInterval 40),(⟨762123382720,762123402049⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1728,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169556325082,169680863250⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157688251392,157688251456⟩ : DyadicInterval 40),(⟨-184151553344,-184151553280⟩ : DyadicInterval 40),(⟨748997377367,748997396696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157796145088,157796145152⟩ : DyadicInterval 40),(⟨-184298808128,-184298808064⟩ : DyadicInterval 40),(⟨748978010612,748978029942⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26502662976,-26463301888⟩ : DyadicInterval 40),(⟨775355034560,775374734368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157724989248,157823707840⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184336431488,-184201689856⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1881_ok : ecellOkT e1881 = true := by decide +kernel
theorem e1881_pos {a z : ℝ} (ha1 : ((1263609/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((632229/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1881 e1881_ok ha1 ha2 hz1 hz2 hz

-- box ['31569/204800', '1263609/8192000', '7997/8000', '3999/4000']  interval_lower 76494197/549755813888
noncomputable def e1882 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268996405985,0,true,157626261888,157626261952⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930026849567,0,false,-184066964800,-184066964736⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269110356837,0,true,157724989248,157724989312⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929912898715,0,false,-184201689920,-184201689856⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268932849193,0,true,157571192256,157571192320⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930090406359,0,false,-183991828224,-183991828160⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269067957155,0,true,157688255104,157688255168⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929955298397,0,false,-184151558464,-184151558400⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533183926,0,true,21555904,21555968⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490071626,0,false,-21556416,-21556352⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543985221,0,true,32356928,32356992⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479270331,0,false,-32357952,-32357888⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626823,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627354,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268964623214,0,true,157598723648,157598723712⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930058632338,0,false,-184029390656,-184029390592⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269089161399,0,true,157706626176,157706626240⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929934094153,0,false,-184176629120,-184176629056⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073357707086,0,false,-26470002880,-26470002816⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073396107997,0,false,-26430667008,-26430666944⟩
    { al := (31569/204800), au := (1263609/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨169484778209,169598729061⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157626261888,157626261952⟩ : DyadicInterval 40),(⟨-184066964800,-184066964736⟩ : DyadicInterval 40),(⟨749008497035,749008516365⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157724989248,157724989312⟩ : DyadicInterval 40),(⟨-184201689920,-184201689856⟩ : DyadicInterval 40),(⟨748990784843,748990804173⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157571192256,157571192320⟩ : DyadicInterval 40),(⟨-183991828224,-183991828160⟩ : DyadicInterval 40),(⟨749018370865,749018390195⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157688255104,157688255168⟩ : DyadicInterval 40),(⟨-184151558464,-184151558400⟩ : DyadicInterval 40),(⟨748997376722,748997396051⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21556150,32357445⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21555904,21555968⟩ : DyadicInterval 40),(⟨-21556416,-21556352⟩ : DyadicInterval 40),(⟨762123383385,762123402714⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32356928,32356992⟩ : DyadicInterval 40),(⟨-32357952,-32357888⟩ : DyadicInterval 40),(⟨762123383111,762123402440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169452995438,169577533623⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157598723648,157598723712⟩ : DyadicInterval 40),(⟨-184029390656,-184029390592⟩ : DyadicInterval 40),(⟨749013435070,749013454399⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157706626176,157706626240⟩ : DyadicInterval 40),(⟨-184176629120,-184176629056⟩ : DyadicInterval 40),(⟨748994080292,748994099622⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26470002880,-26430666944⟩ : DyadicInterval 40),(⟨775338717088,775358404320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157626261888,157724989312⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184201689920,-184066964736⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1882_ok : ecellOkT e1882 = true := by decide +kernel
theorem e1882_pos {a z : ℝ} (ha1 : ((31569/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1263609/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1882 e1882_ok ha1 ha2 hz1 hz2 hz

-- box ['1263609/8192000', '632229/4096000', '7997/8000', '3999/4000']  interval_lower 9626513/68719476736
noncomputable def e1883 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269110356836,0,true,157724989248,157724989312⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929912898716,0,false,-184201689920,-184201689856⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269224307688,0,true,157823707776,157823707840⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929798947864,0,false,-184336431488,-184336431424⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269046757312,0,true,157669887552,157669887616⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929976498240,0,false,-184126493568,-184126493504⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269181879519,0,true,157786952192,157786952256⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929841376033,0,false,-184286260224,-184286260160⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533198929,0,true,21570880,21570944⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490056623,0,false,-21571392,-21571328⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544007727,0,true,32379456,32379520⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479247825,0,false,-32380480,-32380416⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626822,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627353,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269078552698,0,true,157697434944,157697435008⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929944702854,0,false,-184164085888,-184164085824⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269203098011,0,true,157805333952,157805334016⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929820157541,0,false,-184311350784,-184311350720⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073322550422,0,false,-26506016832,-26506016768⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073360979342,0,false,-26466650944,-26466650880⟩
    { al := (1263609/8192000), au := (632229/4096000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨169598729060,169712679912⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157724989248,157724989312⟩ : DyadicInterval 40),(⟨-184201689920,-184201689856⟩ : DyadicInterval 40),(⟨748990784843,748990804173⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157823707776,157823707840⟩ : DyadicInterval 40),(⟨-184336431488,-184336431424⟩ : DyadicInterval 40),(⟨748973060509,748973079838⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157669887552,157669887616⟩ : DyadicInterval 40),(⟨-184126493568,-184126493504⟩ : DyadicInterval 40),(⟨749000672034,749000691363⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157786952192,157786952256⟩ : DyadicInterval 40),(⟨-184286260224,-184286260160⟩ : DyadicInterval 40),(⟨748979661363,748979680693⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21571153,32379951⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21570880,21570944⟩ : DyadicInterval 40),(⟨-21571392,-21571328⟩ : DyadicInterval 40),(⟨762123383384,762123402713⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32379456,32379520⟩ : DyadicInterval 40),(⟨-32380480,-32380416⟩ : DyadicInterval 40),(⟨762123383110,762123402439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169566924922,169691470235⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157697434944,157697435008⟩ : DyadicInterval 40),(⟨-184164085888,-184164085824⟩ : DyadicInterval 40),(⟨748995729579,748995748909⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157805333952,157805334016⟩ : DyadicInterval 40),(⟨-184311350784,-184311350720⟩ : DyadicInterval 40),(⟨748976360463,748976379793⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26506016832,-26466650880⟩ : DyadicInterval 40),(⟨775356709056,775376411296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157724989248,157823707840⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184336431488,-184201689856⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1883_ok : ecellOkT e1883 = true := by decide +kernel
theorem e1883_pos {a z : ℝ} (ha1 : ((1263609/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((632229/4096000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1883 e1883_ok ha1 ha2 hz1 hz2 hz

-- box ['632229/4096000', '1265307/8192000', '1999/2000', '7997/8000']  interval_lower 155212603/1099511627776
noncomputable def e1884 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269224307687,0,true,157823707776,157823707840⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929798947865,0,false,-184336431488,-184336431424⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269338258539,0,true,157922417408,157922417472⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929684997013,0,false,-184471189632,-184471189568⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269139451347,0,true,157750195392,157750195456⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929883804205,0,false,-184236091264,-184236091200⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269274573553,0,true,157867251520,157867251584⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929748681999,0,false,-184395873792,-184395873728⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544007069,0,true,32378816,32378880⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479248483,0,false,-32379776,-32379712⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554830874,0,true,43202240,43202304⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468424678,0,false,-43203968,-43203904⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626078,0,false,-1728,-1664⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626823,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269181875220,0,true,157786948480,157786948544⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929841380332,0,false,-184286255168,-184286255104⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269306420511,0,true,157894838656,157894838720⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929716835041,0,false,-184433536384,-184433536320⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073290648468,0,false,-26538697664,-26538697600⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073329100789,0,false,-26499306624,-26499306560⟩
    { al := (632229/4096000), au := (1265307/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨169712679911,169826630763⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157823707776,157823707840⟩ : DyadicInterval 40),(⟨-184336431488,-184336431424⟩ : DyadicInterval 40),(⟨748973060509,748973079839⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157922417408,157922417472⟩ : DyadicInterval 40),(⟨-184471189632,-184471189568⟩ : DyadicInterval 40),(⟨748955324122,748955343452⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157750195392,157750195456⟩ : DyadicInterval 40),(⟨-184236091264,-184236091200⟩ : DyadicInterval 40),(⟨748986260540,748986279869⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157867251520,157867251584⟩ : DyadicInterval 40),(⟨-184395873792,-184395873728⟩ : DyadicInterval 40),(⟨748965238155,748965257484⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32379293,43203098⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32378816,32378880⟩ : DyadicInterval 40),(⟨-32379776,-32379712⟩ : DyadicInterval 40),(⟨762123383078,762123402407⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43202240,43202304⟩ : DyadicInterval 40),(⟨-43203968,-43203904⟩ : DyadicInterval 40),(⟨762123382718,762123402047⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1728,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169670247444,169794792735⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157786948480,157786948544⟩ : DyadicInterval 40),(⟨-184286255168,-184286255104⟩ : DyadicInterval 40),(⟨748979662036,748979681366⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157894838656,157894838720⟩ : DyadicInterval 40),(⟨-184433536384,-184433536320⟩ : DyadicInterval 40),(⟨748960280944,748960300273⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26538697664,-26499306560⟩ : DyadicInterval 40),(⟨775373036896,775392751712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157823707776,157922417472⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184471189632,-184336431424⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1884_ok : ecellOkT e1884 = true := by decide +kernel
theorem e1884_pos {a z : ℝ} (ha1 : ((632229/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1265307/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1884 e1884_ok ha1 ha2 hz1 hz2 hz

-- box ['1265307/8192000', '316539/2048000', '1999/2000', '7997/8000']  interval_lower 156254147/1099511627776
noncomputable def e1885 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269338258538,0,true,157922417408,157922417472⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929684997014,0,false,-184471189632,-184471189568⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269452209390,0,true,158021118144,158021118208⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929571046162,0,false,-184605964288,-184605964224⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269253345222,0,true,157848862272,157848862336⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929769910330,0,false,-184370769664,-184370769600⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269388481672,0,true,157965920256,157965920320⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929634773880,0,false,-184530588672,-184530588608⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544029577,0,true,32401280,32401344⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479225975,0,false,-32402304,-32402240⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554860886,0,true,43232256,43232320⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468394666,0,false,-43233984,-43233920⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626076,0,false,-1728,-1664⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626822,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269295797582,0,true,157885636736,157885636800⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929727457970,0,false,-184420973440,-184420973376⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269420349996,0,true,157993523392,157993523456⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929602905556,0,false,-184568281088,-184568281024⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073255448980,0,false,-26574757696,-26574757632⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073293929311,0,false,-26535336640,-26535336576⟩
    { al := (1265307/8192000), au := (316539/2048000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨169826630762,169940581614⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157922417408,157922417472⟩ : DyadicInterval 40),(⟨-184471189632,-184471189568⟩ : DyadicInterval 40),(⟨748955324122,748955343452⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158021118144,158021118208⟩ : DyadicInterval 40),(⟨-184605964288,-184605964224⟩ : DyadicInterval 40),(⟨748937575655,748937594984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157848862272,157848862336⟩ : DyadicInterval 40),(⟨-184370769664,-184370769600⟩ : DyadicInterval 40),(⟨748968541998,748968561327⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157965920256,157965920320⟩ : DyadicInterval 40),(⟨-184530588672,-184530588608⟩ : DyadicInterval 40),(⟨748947503068,748947522397⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32401801,43233110⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32401280,32401344⟩ : DyadicInterval 40),(⟨-32402304,-32402240⟩ : DyadicInterval 40),(⟨762123383109,762123402438⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43232256,43232320⟩ : DyadicInterval 40),(⟨-43233984,-43233920⟩ : DyadicInterval 40),(⟨762123382716,762123402045⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1728,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169784169806,169908722220⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157885636736,157885636800⟩ : DyadicInterval 40),(⟨-184420973440,-184420973376⟩ : DyadicInterval 40),(⟨748961934575,748961953905⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157993523392,157993523456⟩ : DyadicInterval 40),(⟨-184568281088,-184568281024⟩ : DyadicInterval 40),(⟨748942539140,748942558469⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26574757696,-26535336576⟩ : DyadicInterval 40),(⟨775391051904,775410781728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157922417408,158021118208⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184605964288,-184471189568⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1885_ok : ecellOkT e1885 = true := by decide +kernel
theorem e1885_pos {a z : ℝ} (ha1 : ((1265307/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((316539/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1885 e1885_ok ha1 ha2 hz1 hz2 hz

-- box ['632229/4096000', '1265307/8192000', '7997/8000', '3999/4000']  interval_lower 38765695/274877906944
noncomputable def e1886 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269224307687,0,true,157823707776,157823707840⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929798947865,0,false,-184336431488,-184336431424⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269338258539,0,true,157922417408,157922417472⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929684997013,0,false,-184471189632,-184471189568⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269160665431,0,true,157768573952,157768574016⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929862590121,0,false,-184261175424,-184261175360⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269295801882,0,true,157885640448,157885640512⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929727453670,0,false,-184420978496,-184420978432⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533213933,0,true,21585920,21585984⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490041619,0,false,-21586432,-21586368⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544030236,0,true,32401920,32401984⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479225316,0,false,-32402944,-32402880⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626821,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627353,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269192482184,0,true,157796137408,157796137472⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929830773368,0,false,-184298797632,-184298797568⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269317034619,0,true,157904032896,157904032960⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929706220933,0,false,-184446089024,-184446088960⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073287370146,0,false,-26542056064,-26542056000⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073325827076,0,false,-26502660224,-26502660160⟩
    { al := (632229/4096000), au := (1265307/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨169712679911,169826630763⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157823707776,157823707840⟩ : DyadicInterval 40),(⟨-184336431488,-184336431424⟩ : DyadicInterval 40),(⟨748973060509,748973079839⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157922417408,157922417472⟩ : DyadicInterval 40),(⟨-184471189632,-184471189568⟩ : DyadicInterval 40),(⟨748955324122,748955343452⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157768573952,157768574016⟩ : DyadicInterval 40),(⟨-184261175424,-184261175360⟩ : DyadicInterval 40),(⟨748982961143,748982980473⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157885640448,157885640512⟩ : DyadicInterval 40),(⟨-184420978496,-184420978432⟩ : DyadicInterval 40),(⟨748961933901,748961953230⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21586157,32402460⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21585920,21585984⟩ : DyadicInterval 40),(⟨-21586432,-21586368⟩ : DyadicInterval 40),(⟨762123383384,762123402713⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32401920,32401984⟩ : DyadicInterval 40),(⟨-32402944,-32402880⟩ : DyadicInterval 40),(⟨762123383109,762123402438⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169680854408,169805406843⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157796137408,157796137472⟩ : DyadicInterval 40),(⟨-184298797632,-184298797568⟩ : DyadicInterval 40),(⟨748978011982,748978031312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157904032896,157904032960⟩ : DyadicInterval 40),(⟨-184446089024,-184446088960⟩ : DyadicInterval 40),(⟨748958628552,748958647881⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26542056064,-26502660160⟩ : DyadicInterval 40),(⟨775374713696,775394430912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157823707776,157922417472⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184471189632,-184336431424⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1886_ok : ecellOkT e1886 = true := by decide +kernel
theorem e1886_pos {a z : ℝ} (ha1 : ((632229/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1265307/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1886 e1886_ok ha1 ha2 hz1 hz2 hz

-- box ['1265307/8192000', '316539/2048000', '7997/8000', '3999/4000']  interval_lower 4878249/34359738368
noncomputable def e1887 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269338258538,0,true,157922417408,157922417472⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929684997014,0,false,-184471189632,-184471189568⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269452209390,0,true,158021118144,158021118208⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929571046162,0,false,-184605964288,-184605964224⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269274573551,0,true,157867251520,157867251584⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929748682001,0,false,-184395873792,-184395873728⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269409724245,0,true,157984319872,157984319936⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929613531307,0,false,-184555713280,-184555713216⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533228938,0,true,21600896,21600960⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490026614,0,false,-21601408,-21601344⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544052745,0,true,32424448,32424512⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479202807,0,false,-32425472,-32425408⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626819,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627352,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269306411667,0,true,157894831040,157894831104⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929716843885,0,false,-184433525888,-184433525824⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269430971226,0,true,158002723008,158002723072⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929592284326,0,false,-184580843712,-184580843648⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073252166257,0,false,-26578120704,-26578120640⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073290651201,0,false,-26538694848,-26538694784⟩
    { al := (1265307/8192000), au := (316539/2048000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨169826630762,169940581614⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157922417408,157922417472⟩ : DyadicInterval 40),(⟨-184471189632,-184471189568⟩ : DyadicInterval 40),(⟨748955324122,748955343452⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158021118144,158021118208⟩ : DyadicInterval 40),(⟨-184605964288,-184605964224⟩ : DyadicInterval 40),(⟨748937575655,748937594984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157867251520,157867251584⟩ : DyadicInterval 40),(⟨-184395873792,-184395873728⟩ : DyadicInterval 40),(⟨748965238155,748965257485⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157984319872,157984319936⟩ : DyadicInterval 40),(⟨-184555713280,-184555713216⟩ : DyadicInterval 40),(⟨748944194334,748944213663⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21601162,32424969⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21600896,21600960⟩ : DyadicInterval 40),(⟨-21601408,-21601344⟩ : DyadicInterval 40),(⟨762123383383,762123402712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32424448,32424512⟩ : DyadicInterval 40),(⟨-32425472,-32425408⟩ : DyadicInterval 40),(⟨762123383107,762123402436⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169794783891,169919343450⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157894831040,157894831104⟩ : DyadicInterval 40),(⟨-184433525888,-184433525824⟩ : DyadicInterval 40),(⟨748960282279,748960301608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158002723008,158002723072⟩ : DyadicInterval 40),(⟨-184580843712,-184580843648⟩ : DyadicInterval 40),(⟨748940884502,748940903832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26578120704,-26538694784⟩ : DyadicInterval 40),(⟨775392731008,775412463232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157922417408,158021118208⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184605964288,-184471189568⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1887_ok : ecellOkT e1887 = true := by decide +kernel
theorem e1887_pos {a z : ℝ} (ha1 : ((1265307/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((316539/2048000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1887 e1887_ok ha1 ha2 hz1 hz2 hz

-- box ['31569/204800', '1263609/8192000', '3999/4000', '7999/8000']  interval_lower 152838763/1099511627776
noncomputable def e1888 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268996405985,0,true,157626261888,157626261952⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930026849567,0,false,-184066964800,-184066964736⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269110356837,0,true,157724989248,157724989312⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929912898715,0,false,-184201689920,-184201689856⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268954034790,0,true,157589549120,157589549184⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930069220762,0,false,-184016873152,-184016873088⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269089156996,0,true,157706622336,157706622400⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929934098556,0,false,-184176623872,-184176623808⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522405746,0,true,10777856,10777920⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500849806,0,false,-10778048,-10777984⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533199539,0,true,21571520,21571584⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490056013,0,false,-21572032,-21571968⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627352,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627671,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268975215957,0,true,157607901824,157607901888⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930048039595,0,false,-184041913472,-184041913408⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269099761286,0,true,157715809600,157715809664⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929923494266,0,false,-184189161984,-184189161920⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073354437346,0,false,-26473352320,-26473352256⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073392842860,0,false,-26434011584,-26434011520⟩
    { al := (31569/204800), au := (1263609/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨169484778209,169598729061⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157626261888,157626261952⟩ : DyadicInterval 40),(⟨-184066964800,-184066964736⟩ : DyadicInterval 40),(⟨749008497035,749008516365⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157724989248,157724989312⟩ : DyadicInterval 40),(⟨-184201689920,-184201689856⟩ : DyadicInterval 40),(⟨748990784843,748990804173⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157589549120,157589549184⟩ : DyadicInterval 40),(⟨-184016873152,-184016873088⟩ : DyadicInterval 40),(⟨749015079988,749015099317⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157706622336,157706622400⟩ : DyadicInterval 40),(⟨-184176623872,-184176623808⟩ : DyadicInterval 40),(⟨748994080973,748994100303⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10777970,21571763⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10777856,10777920⟩ : DyadicInterval 40),(⟨-10778048,-10777984⟩ : DyadicInterval 40),(⟨762123383542,762123402871⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21571520,21571584⟩ : DyadicInterval 40),(⟨-21572032,-21571968⟩ : DyadicInterval 40),(⟨762123383384,762123402713⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169463588181,169588133510⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157607901824,157607901888⟩ : DyadicInterval 40),(⟨-184041913472,-184041913408⟩ : DyadicInterval 40),(⟨749011789414,749011808743⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157715809600,157715809664⟩ : DyadicInterval 40),(⟨-184189161984,-184189161920⟩ : DyadicInterval 40),(⟨748992432287,748992451617⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26473352320,-26434011520⟩ : DyadicInterval 40),(⟨775340389376,775360079040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157626261888,157724989312⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184201689920,-184066964736⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1888_ok : ecellOkT e1888 = true := by decide +kernel
theorem e1888_pos {a z : ℝ} (ha1 : ((31569/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1263609/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1888 e1888_ok ha1 ha2 hz1 hz2 hz

-- box ['1263609/8192000', '632229/4096000', '3999/4000', '7999/8000']  interval_lower 76937201/549755813888
noncomputable def e1889 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269110356836,0,true,157724989248,157724989312⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929912898716,0,false,-184201689920,-184201689856⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269224307688,0,true,157823707776,157823707840⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929798947864,0,false,-184336431488,-184336431424⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269067957153,0,true,157688255104,157688255168⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929955298399,0,false,-184151558464,-184151558400⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269203093604,0,true,157805330112,157805330176⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929820161948,0,false,-184311345600,-184311345536⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522413247,0,true,10785408,10785472⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500842305,0,false,-10785536,-10785472⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533214543,0,true,21586496,21586560⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490041009,0,false,-21587008,-21586944⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627352,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627671,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269089152560,0,true,157706618496,157706618560⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929934102992,0,false,-184176618624,-184176618560⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269213705017,0,true,157814522752,157814522816⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929809550535,0,false,-184323893632,-184323893568⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073319276287,0,false,-26509370816,-26509370752⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073357709814,0,false,-26470000128,-26470000064⟩
    { al := (1263609/8192000), au := (632229/4096000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨169598729060,169712679912⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157724989248,157724989312⟩ : DyadicInterval 40),(⟨-184201689920,-184201689856⟩ : DyadicInterval 40),(⟨748990784843,748990804173⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157823707776,157823707840⟩ : DyadicInterval 40),(⟨-184336431488,-184336431424⟩ : DyadicInterval 40),(⟨748973060509,748973079838⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157688255104,157688255168⟩ : DyadicInterval 40),(⟨-184151558464,-184151558400⟩ : DyadicInterval 40),(⟨748997376722,748997396052⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157805330112,157805330176⟩ : DyadicInterval 40),(⟨-184311345600,-184311345536⟩ : DyadicInterval 40),(⟨748976361173,748976380503⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10785471,21586767⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10785408,10785472⟩ : DyadicInterval 40),(⟨-10785536,-10785472⟩ : DyadicInterval 40),(⟨762123383510,762123402839⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21586496,21586560⟩ : DyadicInterval 40),(⟨-21587008,-21586944⟩ : DyadicInterval 40),(⟨762123383384,762123402713⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169577524784,169702077241⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157706618496,157706618560⟩ : DyadicInterval 40),(⟨-184176618624,-184176618560⟩ : DyadicInterval 40),(⟨748994081660,748994100990⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157814522752,157814522816⟩ : DyadicInterval 40),(⟨-184323893632,-184323893568⟩ : DyadicInterval 40),(⟨748974710219,748974729549⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26509370816,-26470000064⟩ : DyadicInterval 40),(⟨775358383648,775378088288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157724989248,157823707840⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184336431488,-184201689856⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1889_ok : ecellOkT e1889 = true := by decide +kernel
theorem e1889_pos {a z : ℝ} (ha1 : ((1263609/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((632229/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1889 e1889_ok ha1 ha2 hz1 hz2 hz

-- box ['31569/204800', '1263609/8192000', '7999/8000', '1']  interval_lower 76344683/549755813888
noncomputable def e1890 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268996405985,0,true,157626261888,157626261952⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930026849567,0,false,-184066964800,-184066964736⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269110356837,0,true,157724989248,157724989312⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929912898715,0,false,-184201689920,-184201689856⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268975220387,0,true,157607905664,157607905728⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930048035165,0,false,-184041918720,-184041918656⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522413810,0,true,10785920,10785984⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500841742,0,false,-10786112,-10786048⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627670,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1268985808719,0,true,157617079936,157617080000⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨930037446833,0,false,-184054436416,-184054436352⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1269110361192,0,true,157724993024,157724993088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨929912894360,0,false,-184201695040,-184201694976⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1073351167395,0,false,-26476701952,-26476701888⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1073389577513,0,false,-26437356416,-26437356352⟩
    { al := (31569/204800), au := (1263609/8192000), zl := (7999/8000), zu := 1,
      A := ⟨169484778209,169598729061⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157626261888,157626261952⟩ : DyadicInterval 40),(⟨-184066964800,-184066964736⟩ : DyadicInterval 40),(⟨749008497035,749008516365⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157724989248,157724989312⟩ : DyadicInterval 40),(⟨-184201689920,-184201689856⟩ : DyadicInterval 40),(⟨748990784843,748990804173⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157607905664,157607905728⟩ : DyadicInterval 40),(⟨-184041918720,-184041918656⟩ : DyadicInterval 40),(⟨749011788729,749011808059⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157724989248,157724989312⟩ : DyadicInterval 40),(⟨-184201689920,-184201689856⟩ : DyadicInterval 40),(⟨748990784843,748990804173⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10786034⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10785920,10785984⟩ : DyadicInterval 40),(⟨-10786112,-10786048⟩ : DyadicInterval 40),(⟨762123383542,762123402871⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨169474180943,169598733416⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157617079936,157617080000⟩ : DyadicInterval 40),(⟨-184054436416,-184054436352⟩ : DyadicInterval 40),(⟨749010143637,749010162966⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157724993024,157724993088⟩ : DyadicInterval 40),(⟨-184201695040,-184201694976⟩ : DyadicInterval 40),(⟨748990784152,748990803482⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26476701952,-26437356352⟩ : DyadicInterval 40),(⟨775342061792,775361753856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨157626261888,157724989312⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184201689920,-184066964736⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1890_ok : ecellOkT e1890 = true := by decide +kernel
theorem e1890_pos {a z : ℝ} (ha1 : ((31569/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1263609/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1890 e1890_ok ha1 ha2 hz1 hz2 hz

-- box ['1263609/8192000', '632229/4096000', '7999/8000', '1']  interval_lower 153724311/1099511627776
noncomputable def e1891 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269110356836,0,true,157724989248,157724989312⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929912898716,0,false,-184201689920,-184201689856⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269224307688,0,true,157823707776,157823707840⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929798947864,0,false,-184336431488,-184336431424⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269089156994,0,true,157706622336,157706622400⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929934098558,0,false,-184176623872,-184176623808⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522421312,0,true,10793472,10793536⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500834240,0,false,-10793600,-10793536⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627670,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1269099752447,0,true,157715801984,157715802048⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨929923503105,0,false,-184189151552,-184189151488⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1269224312052,0,true,157823711552,157823711616⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨929798943500,0,false,-184336436672,-184336436608⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1073316001939,0,false,-26512725120,-26512725056⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1073354440073,0,false,-26473349504,-26473349440⟩
    { al := (1263609/8192000), au := (632229/4096000), zl := (7999/8000), zu := 1,
      A := ⟨169598729060,169712679912⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157724989248,157724989312⟩ : DyadicInterval 40),(⟨-184201689920,-184201689856⟩ : DyadicInterval 40),(⟨748990784843,748990804173⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157823707776,157823707840⟩ : DyadicInterval 40),(⟨-184336431488,-184336431424⟩ : DyadicInterval 40),(⟨748973060509,748973079838⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157706622336,157706622400⟩ : DyadicInterval 40),(⟨-184176623872,-184176623808⟩ : DyadicInterval 40),(⟨748994080974,748994100303⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157823707776,157823707840⟩ : DyadicInterval 40),(⟨-184336431488,-184336431424⟩ : DyadicInterval 40),(⟨748973060509,748973079838⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10793536⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10793472,10793536⟩ : DyadicInterval 40),(⟨-10793600,-10793536⟩ : DyadicInterval 40),(⟨762123383510,762123402839⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨169588124671,169712684276⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157715801984,157715802048⟩ : DyadicInterval 40),(⟨-184189151552,-184189151488⟩ : DyadicInterval 40),(⟨748992433646,748992452975⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157823711552,157823711616⟩ : DyadicInterval 40),(⟨-184336436672,-184336436608⟩ : DyadicInterval 40),(⟨748973059843,748973079172⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26512725120,-26473349440⟩ : DyadicInterval 40),(⟨775360058336,775379765440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨157724989248,157823707840⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184336431488,-184201689856⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1891_ok : ecellOkT e1891 = true := by decide +kernel
theorem e1891_pos {a z : ℝ} (ha1 : ((1263609/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((632229/4096000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1891 e1891_ok ha1 ha2 hz1 hz2 hz

-- box ['632229/4096000', '1265307/8192000', '3999/4000', '7999/8000']  interval_lower 38728109/274877906944
noncomputable def e1892 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269224307687,0,true,157823707776,157823707840⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929798947865,0,false,-184336431488,-184336431424⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269338258539,0,true,157922417408,157922417472⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929684997013,0,false,-184471189632,-184471189568⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269181879517,0,true,157786952192,157786952256⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929841376035,0,false,-184286260224,-184286260160⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269317030211,0,true,157904029056,157904029120⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929706225341,0,false,-184446083776,-184446083712⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522420750,0,true,10792896,10792960⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500834802,0,false,-10793088,-10793024⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533229548,0,true,21601536,21601600⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490026004,0,false,-21602048,-21601984⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627351,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627671,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269203089169,0,true,157805326272,157805326336⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929820166383,0,false,-184311340352,-184311340288⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269327648747,0,true,157913227072,157913227136⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929695606805,0,false,-184458641792,-184458641728⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073284091613,0,false,-26545414720,-26545414656⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073322553153,0,false,-26506014016,-26506013952⟩
    { al := (632229/4096000), au := (1265307/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨169712679911,169826630763⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157823707776,157823707840⟩ : DyadicInterval 40),(⟨-184336431488,-184336431424⟩ : DyadicInterval 40),(⟨748973060509,748973079839⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157922417408,157922417472⟩ : DyadicInterval 40),(⟨-184471189632,-184471189568⟩ : DyadicInterval 40),(⟨748955324122,748955343452⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157786952192,157786952256⟩ : DyadicInterval 40),(⟨-184286260224,-184286260160⟩ : DyadicInterval 40),(⟨748979661364,748979680693⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157904029056,157904029120⟩ : DyadicInterval 40),(⟨-184446083776,-184446083712⟩ : DyadicInterval 40),(⟨748958629236,748958648565⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10792974,21601772⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10792896,10792960⟩ : DyadicInterval 40),(⟨-10793088,-10793024⟩ : DyadicInterval 40),(⟨762123383542,762123402871⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21601536,21601600⟩ : DyadicInterval 40),(⟨-21602048,-21601984⟩ : DyadicInterval 40),(⟨762123383383,762123402712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169691461393,169816020971⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157805326272,157805326336⟩ : DyadicInterval 40),(⟨-184311340352,-184311340288⟩ : DyadicInterval 40),(⟨748976361860,748976381190⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157913227072,157913227136⟩ : DyadicInterval 40),(⟨-184458641792,-184458641728⟩ : DyadicInterval 40),(⟨748956976038,748956995367⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26545414720,-26506013952⟩ : DyadicInterval 40),(⟨775376390592,775396110240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157823707776,157922417472⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184471189632,-184336431424⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1892_ok : ecellOkT e1892 = true := by decide +kernel
theorem e1892_pos {a z : ℝ} (ha1 : ((632229/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1265307/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1892 e1892_ok ha1 ha2 hz1 hz2 hz

-- box ['1265307/8192000', '316539/2048000', '3999/4000', '7999/8000']  interval_lower 155953277/1099511627776
noncomputable def e1893 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269338258538,0,true,157922417408,157922417472⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929684997014,0,false,-184471189632,-184471189568⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269452209390,0,true,158021118144,158021118208⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929571046162,0,false,-184605964288,-184605964224⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269295801880,0,true,157885640448,157885640512⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929727453672,0,false,-184420978496,-184420978432⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269430966818,0,true,158002719168,158002719232⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929592288734,0,false,-184580838528,-184580838464⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522428253,0,true,10800384,10800448⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500827299,0,false,-10800576,-10800512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533244555,0,true,21616512,21616576⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490010997,0,false,-21617024,-21616960⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627351,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627670,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269317025774,0,true,157904025216,157904025280⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929706229778,0,false,-184446078528,-184446078464⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269441592474,0,true,158011922496,158011922560⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929581663078,0,false,-184593406464,-184593406400⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073248883324,0,false,-26581483968,-26581483904⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073287372879,0,false,-26542053248,-26542053184⟩
    { al := (1265307/8192000), au := (316539/2048000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨169826630762,169940581614⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157922417408,157922417472⟩ : DyadicInterval 40),(⟨-184471189632,-184471189568⟩ : DyadicInterval 40),(⟨748955324122,748955343452⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158021118144,158021118208⟩ : DyadicInterval 40),(⟨-184605964288,-184605964224⟩ : DyadicInterval 40),(⟨748937575655,748937594984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157885640448,157885640512⟩ : DyadicInterval 40),(⟨-184420978496,-184420978432⟩ : DyadicInterval 40),(⟨748961933902,748961953231⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158002719168,158002719232⟩ : DyadicInterval 40),(⟨-184580838528,-184580838464⟩ : DyadicInterval 40),(⟨748940885214,748940904543⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10800477,21616779⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10800384,10800448⟩ : DyadicInterval 40),(⟨-10800576,-10800512⟩ : DyadicInterval 40),(⟨762123383541,762123402870⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21616512,21616576⟩ : DyadicInterval 40),(⟨-21617024,-21616960⟩ : DyadicInterval 40),(⟨762123383383,762123402712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169805397998,169929964698⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157904025216,157904025280⟩ : DyadicInterval 40),(⟨-184446078528,-184446078464⟩ : DyadicInterval 40),(⟨748958629924,748958649254⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158011922496,158011922560⟩ : DyadicInterval 40),(⟨-184593406464,-184593406400⟩ : DyadicInterval 40),(⟨748939229779,748939249109⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26581483968,-26542053184⟩ : DyadicInterval 40),(⟨775394410208,775414144864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157922417408,158021118208⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184605964288,-184471189568⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1893_ok : ecellOkT e1893 = true := by decide +kernel
theorem e1893_pos {a z : ℝ} (ha1 : ((1265307/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((316539/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1893 e1893_ok ha1 ha2 hz1 hz2 hz

-- box ['632229/4096000', '1265307/8192000', '7999/8000', '1']  interval_lower 77381227/549755813888
noncomputable def e1894 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269224307687,0,true,157823707776,157823707840⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929798947865,0,false,-184336431488,-184336431424⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269338258539,0,true,157922417408,157922417472⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929684997013,0,false,-184471189632,-184471189568⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269203093601,0,true,157805330112,157805330176⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929820161951,0,false,-184311345600,-184311345536⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522428815,0,true,10800960,10801024⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500826737,0,false,-10801152,-10801088⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627669,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1269213696175,0,true,157814515136,157814515200⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨929809559377,0,false,-184323883200,-184323883136⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1269338262902,0,true,157922421184,157922421248⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨929684992650,0,false,-184471194816,-184471194752⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1073280812867,0,false,-26548773568,-26548773504⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1073319279018,0,false,-26509368064,-26509368000⟩
    { al := (632229/4096000), au := (1265307/8192000), zl := (7999/8000), zu := 1,
      A := ⟨169712679911,169826630763⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157823707776,157823707840⟩ : DyadicInterval 40),(⟨-184336431488,-184336431424⟩ : DyadicInterval 40),(⟨748973060509,748973079839⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157922417408,157922417472⟩ : DyadicInterval 40),(⟨-184471189632,-184471189568⟩ : DyadicInterval 40),(⟨748955324122,748955343452⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157805330112,157805330176⟩ : DyadicInterval 40),(⟨-184311345600,-184311345536⟩ : DyadicInterval 40),(⟨748976361173,748976380503⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157922417408,157922417472⟩ : DyadicInterval 40),(⟨-184471189632,-184471189568⟩ : DyadicInterval 40),(⟨748955324122,748955343452⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10801039⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10800960,10801024⟩ : DyadicInterval 40),(⟨-10801152,-10801088⟩ : DyadicInterval 40),(⟨762123383541,762123402870⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨169702068399,169826635126⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157814515136,157814515200⟩ : DyadicInterval 40),(⟨-184323883200,-184323883136⟩ : DyadicInterval 40),(⟨748974711580,748974730909⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157922421184,157922421248⟩ : DyadicInterval 40),(⟨-184471194816,-184471194752⟩ : DyadicInterval 40),(⟨748955323455,748955342784⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26548773568,-26509368000⟩ : DyadicInterval 40),(⟨775378067616,775397789664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨157823707776,157922417472⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184471189632,-184336431424⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1894_ok : ecellOkT e1894 = true := by decide +kernel
theorem e1894_pos {a z : ℝ} (ha1 : ((632229/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1265307/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1894 e1894_ok ha1 ha2 hz1 hz2 hz

-- box ['1265307/8192000', '316539/2048000', '7999/8000', '1']  interval_lower 155802783/1099511627776
noncomputable def e1895 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269338258538,0,true,157922417408,157922417472⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929684997014,0,false,-184471189632,-184471189568⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269452209390,0,true,158021118144,158021118208⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929571046162,0,false,-184605964288,-184605964224⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269317030209,0,true,157904029056,157904029120⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929706225343,0,false,-184446083776,-184446083712⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522436319,0,true,10808448,10808512⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500819233,0,false,-10808640,-10808576⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627669,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1269327639902,0,true,157913219392,157913219456⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨929695615650,0,false,-184458631360,-184458631296⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1269452213747,0,true,158021121920,158021121984⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨929571041805,0,false,-184605969408,-184605969344⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1073245600177,0,false,-26584847488,-26584847424⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1073284094346,0,false,-26545411904,-26545411840⟩
    { al := (1265307/8192000), au := (316539/2048000), zl := (7999/8000), zu := 1,
      A := ⟨169826630762,169940581614⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157922417408,157922417472⟩ : DyadicInterval 40),(⟨-184471189632,-184471189568⟩ : DyadicInterval 40),(⟨748955324122,748955343452⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158021118144,158021118208⟩ : DyadicInterval 40),(⟨-184605964288,-184605964224⟩ : DyadicInterval 40),(⟨748937575655,748937594984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157904029056,157904029120⟩ : DyadicInterval 40),(⟨-184446083776,-184446083712⟩ : DyadicInterval 40),(⟨748958629236,748958648566⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158021118144,158021118208⟩ : DyadicInterval 40),(⟨-184605964288,-184605964224⟩ : DyadicInterval 40),(⟨748937575655,748937594984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10808543⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10808448,10808512⟩ : DyadicInterval 40),(⟨-10808640,-10808576⟩ : DyadicInterval 40),(⟨762123383541,762123402870⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨169816012126,169940585971⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157913219392,157913219456⟩ : DyadicInterval 40),(⟨-184458631360,-184458631296⟩ : DyadicInterval 40),(⟨748956977437,748956996767⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158021121920,158021121984⟩ : DyadicInterval 40),(⟨-184605969408,-184605969344⟩ : DyadicInterval 40),(⟨748937574960,748937594290⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26584847488,-26545411840⟩ : DyadicInterval 40),(⟨775396089536,775415826624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨157922417408,158021118208⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184605964288,-184471189568⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1895_ok : ecellOkT e1895 = true := by decide +kernel
theorem e1895_pos {a z : ℝ} (ha1 : ((1265307/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((316539/2048000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1895 e1895_ok ha1 ha2 hz1 hz2 hz

-- box ['316539/2048000', '253401/1638400', '1999/2000', '7997/8000']  interval_lower 157298321/1099511627776
noncomputable def e1896 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269452209389,0,true,158021118144,158021118208⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929571046163,0,false,-184605964288,-184605964224⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269566160241,0,true,158119810048,158119810112⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929457095311,0,false,-184740755456,-184740755392⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269367239098,0,true,157947520320,157947520384⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929656016454,0,false,-184505464640,-184505464576⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269502389792,0,true,158064580096,158064580160⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929520865760,0,false,-184665320064,-184665320000⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544052086,0,true,32423808,32423872⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479203466,0,false,-32424832,-32424768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554890902,0,true,43262272,43262336⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468364650,0,false,-43264000,-43263936⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626073,0,false,-1728,-1664⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626820,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269409719941,0,true,157984316096,157984316160⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929613535611,0,false,-184555708224,-184555708160⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269534279480,0,true,158092199296,158092199360⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929488976072,0,false,-184703042368,-184703042304⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073220225882,0,false,-26610843072,-26610843008⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073258734226,0,false,-26571392064,-26571392000⟩
    { al := (316539/2048000), au := (253401/1638400), zl := (1999/2000), zu := (7997/8000),
      A := ⟨169940581613,170054532465⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158021118144,158021118208⟩ : DyadicInterval 40),(⟨-184605964288,-184605964224⟩ : DyadicInterval 40),(⟨748937575655,748937594984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158119810048,158119810112⟩ : DyadicInterval 40),(⟨-184740755456,-184740755392⟩ : DyadicInterval 40),(⟨748919815069,748919834398⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157947520320,157947520384⟩ : DyadicInterval 40),(⟨-184505464640,-184505464576⟩ : DyadicInterval 40),(⟨748950811389,748950830719⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158064580096,158064580160⟩ : DyadicInterval 40),(⟨-184665320064,-184665320000⟩ : DyadicInterval 40),(⟨748929755918,748929775247⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32424310,43263126⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32423808,32423872⟩ : DyadicInterval 40),(⟨-32424832,-32424768⟩ : DyadicInterval 40),(⟨762123383107,762123402436⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43262272,43262336⟩ : DyadicInterval 40),(⟨-43264000,-43263936⟩ : DyadicInterval 40),(⟨762123382713,762123402042⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1728,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169898092165,170022651704⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157984316096,157984316160⟩ : DyadicInterval 40),(⟨-184555708224,-184555708160⟩ : DyadicInterval 40),(⟨748944195047,748944214376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158092199296,158092199360⟩ : DyadicInterval 40),(⟨-184703042368,-184703042304⟩ : DyadicInterval 40),(⟨748924785254,748924804583⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26610843072,-26571392000⟩ : DyadicInterval 40),(⟨775409079616,775428824416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158021118144,158119810112⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184740755456,-184605964224⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1896_ok : ecellOkT e1896 = true := by decide +kernel
theorem e1896_pos {a z : ℝ} (ha1 : ((316539/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((253401/1638400 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1896 e1896_ok ha1 ha2 hz1 hz2 hz

-- box ['253401/1638400', '633927/4096000', '1999/2000', '7997/8000']  interval_lower 158345283/1099511627776
noncomputable def e1897 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269566160240,0,true,158119810048,158119810112⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929457095312,0,false,-184740755456,-184740755392⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269680111092,0,true,158218493120,158218493184⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929343144460,0,false,-184875563136,-184875563072⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269481132973,0,true,158046169472,158046169536⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929542122579,0,false,-184640176064,-184640176000⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269616297911,0,true,158163231104,158163231168⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929406957641,0,false,-184800067968,-184800067904⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544074596,0,true,32446336,32446400⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479180956,0,false,-32447360,-32447296⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554920918,0,true,43292288,43292352⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468334634,0,false,-43294016,-43293952⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626071,0,false,-1728,-1664⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626819,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269523642302,0,true,158082986688,158082986752⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929499613250,0,false,-184690459520,-184690459456⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269648208967,0,true,158190866304,158190866368⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929375046585,0,false,-184837820160,-184837820096⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073184979173,0,false,-26646953856,-26646953792⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073223515534,0,false,-26607472832,-26607472768⟩
    { al := (253401/1638400), au := (633927/4096000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨170054532464,170168483316⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158119810048,158119810112⟩ : DyadicInterval 40),(⟨-184740755456,-184740755392⟩ : DyadicInterval 40),(⟨748919815069,748919834399⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158218493120,158218493184⟩ : DyadicInterval 40),(⟨-184875563136,-184875563072⟩ : DyadicInterval 40),(⟨748902042363,748902061692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158046169472,158046169536⟩ : DyadicInterval 40),(⟨-184640176064,-184640176000⟩ : DyadicInterval 40),(⟨748933068697,748933088027⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158163231104,158163231168⟩ : DyadicInterval 40),(⟨-184800067968,-184800067904⟩ : DyadicInterval 40),(⟨748911996666,748912015996⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32446820,43293142⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32446336,32446400⟩ : DyadicInterval 40),(⟨-32447360,-32447296⟩ : DyadicInterval 40),(⟨762123383106,762123402435⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43292288,43292352⟩ : DyadicInterval 40),(⟨-43294016,-43293952⟩ : DyadicInterval 40),(⟨762123382711,762123402040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1728,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170012014526,170136581191⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158082986688,158082986752⟩ : DyadicInterval 40),(⟨-184690459520,-184690459456⟩ : DyadicInterval 40),(⟨748926443374,748926462704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158190866304,158190866368⟩ : DyadicInterval 40),(⟨-184837820160,-184837820096⟩ : DyadicInterval 40),(⟨748907019294,748907038623⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26646953856,-26607472768⟩ : DyadicInterval 40),(⟨775427120000,775446879808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158119810048,158218493184⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184875563136,-184740755392⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1897_ok : ecellOkT e1897 = true := by decide +kernel
theorem e1897_pos {a z : ℝ} (ha1 : ((253401/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((633927/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1897 e1897_ok ha1 ha2 hz1 hz2 hz

-- box ['316539/2048000', '253401/1638400', '7997/8000', '3999/4000']  interval_lower 157147787/1099511627776
noncomputable def e1898 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269452209389,0,true,158021118144,158021118208⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929571046163,0,false,-184605964288,-184605964224⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269566160241,0,true,158119810048,158119810112⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929457095311,0,false,-184740755456,-184740755392⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269388481670,0,true,157965920256,157965920320⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929634773882,0,false,-184530588672,-184530588608⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269523646609,0,true,158082990400,158082990464⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929499608943,0,false,-184690464640,-184690464576⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533243944,0,true,21615936,21616000⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490011608,0,false,-21616384,-21616320⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544075256,0,true,32446976,32447040⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479180296,0,false,-32448000,-32447936⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626818,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627352,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269420341148,0,true,157993515776,157993515840⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929602914404,0,false,-184568270656,-184568270592⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269544907829,0,true,158101404224,158101404288⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929478347723,0,false,-184715614976,-184715614912⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073216938756,0,false,-26614210752,-26614210688⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073255451716,0,false,-26574754880,-26574754816⟩
    { al := (316539/2048000), au := (253401/1638400), zl := (7997/8000), zu := (3999/4000),
      A := ⟨169940581613,170054532465⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158021118144,158021118208⟩ : DyadicInterval 40),(⟨-184605964288,-184605964224⟩ : DyadicInterval 40),(⟨748937575655,748937594984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158119810048,158119810112⟩ : DyadicInterval 40),(⟨-184740755456,-184740755392⟩ : DyadicInterval 40),(⟨748919815069,748919834398⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157965920256,157965920320⟩ : DyadicInterval 40),(⟨-184530588672,-184530588608⟩ : DyadicInterval 40),(⟨748947503068,748947522397⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158082990400,158082990464⟩ : DyadicInterval 40),(⟨-184690464640,-184690464576⟩ : DyadicInterval 40),(⟨748926442724,748926462053⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21616168,32447480⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21615936,21616000⟩ : DyadicInterval 40),(⟨-21616384,-21616320⟩ : DyadicInterval 40),(⟨762123383351,762123402680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32446976,32447040⟩ : DyadicInterval 40),(⟨-32448000,-32447936⟩ : DyadicInterval 40),(⟨762123383106,762123402435⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169908713372,170033280053⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157993515776,157993515840⟩ : DyadicInterval 40),(⟨-184568270656,-184568270592⟩ : DyadicInterval 40),(⟨748942540504,748942559834⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158101404224,158101404288⟩ : DyadicInterval 40),(⟨-184715614976,-184715614912⟩ : DyadicInterval 40),(⟨748923128405,748923147734⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26614210752,-26574754816⟩ : DyadicInterval 40),(⟨775410761024,775430508256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158021118144,158119810112⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184740755456,-184605964224⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1898_ok : ecellOkT e1898 = true := by decide +kernel
theorem e1898_pos {a z : ℝ} (ha1 : ((316539/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((253401/1638400 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1898 e1898_ok ha1 ha2 hz1 hz2 hz

-- box ['253401/1638400', '633927/4096000', '7997/8000', '3999/4000']  interval_lower 79097037/549755813888
noncomputable def e1899 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269566160240,0,true,158119810048,158119810112⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929457095312,0,false,-184740755456,-184740755392⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269680111092,0,true,158218493120,158218493184⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929343144460,0,false,-184875563136,-184875563072⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269502389790,0,true,158064580096,158064580160⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929520865762,0,false,-184665320064,-184665320000⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269637568972,0,true,158181652096,158181652160⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929385686580,0,false,-184825232448,-184825232384⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533258952,0,true,21630912,21630976⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489996600,0,false,-21631424,-21631360⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544097768,0,true,32469504,32469568⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479157784,0,false,-32470528,-32470464⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626817,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627351,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269534270630,0,true,158092191616,158092191680⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929488984922,0,false,-184703031936,-184703031872⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269658844440,0,true,158200076544,158200076608⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929364411112,0,false,-184850402688,-184850402624⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073181687639,0,false,-26650326144,-26650326080⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073220228620,0,false,-26610840256,-26610840192⟩
    { al := (253401/1638400), au := (633927/4096000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨170054532464,170168483316⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158119810048,158119810112⟩ : DyadicInterval 40),(⟨-184740755456,-184740755392⟩ : DyadicInterval 40),(⟨748919815069,748919834399⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158218493120,158218493184⟩ : DyadicInterval 40),(⟨-184875563136,-184875563072⟩ : DyadicInterval 40),(⟨748902042363,748902061692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158064580096,158064580160⟩ : DyadicInterval 40),(⟨-184665320064,-184665320000⟩ : DyadicInterval 40),(⟨748929755918,748929775247⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158181652096,158181652160⟩ : DyadicInterval 40),(⟨-184825232448,-184825232384⟩ : DyadicInterval 40),(⟨748908678980,748908698309⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21631176,32469992⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21630912,21630976⟩ : DyadicInterval 40),(⟨-21631424,-21631360⟩ : DyadicInterval 40),(⟨762123383382,762123402711⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32469504,32469568⟩ : DyadicInterval 40),(⟨-32470528,-32470464⟩ : DyadicInterval 40),(⟨762123383105,762123402434⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170022642854,170147216664⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158092191616,158092191680⟩ : DyadicInterval 40),(⟨-184703031936,-184703031872⟩ : DyadicInterval 40),(⟨748924786658,748924805987⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158200076544,158200076608⟩ : DyadicInterval 40),(⟨-184850402688,-184850402624⟩ : DyadicInterval 40),(⟨748905360202,748905379532⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26650326144,-26610840192⟩ : DyadicInterval 40),(⟨775428803712,775448565952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158119810048,158218493184⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184875563136,-184740755392⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1899_ok : ecellOkT e1899 = true := by decide +kernel
theorem e1899_pos {a z : ℝ} (ha1 : ((253401/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((633927/4096000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1899 e1899_ok ha1 ha2 hz1 hz2 hz

-- box ['633927/4096000', '1268703/8192000', '1999/2000', '7997/8000']  interval_lower 79697327/549755813888
noncomputable def e1900 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269680111091,0,true,158218493120,158218493184⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929343144461,0,false,-184875563136,-184875563072⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269794061943,0,true,158317167296,158317167360⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929229193609,0,false,-185010387328,-185010387264⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269595026849,0,true,158144809792,158144809856⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929428228703,0,false,-184774904064,-184774904000⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269730206031,0,true,158261873216,158261873280⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929293049521,0,false,-184934832384,-184934832320⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544097109,0,true,32468800,32468864⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479158443,0,false,-32469824,-32469760⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554950937,0,true,43322304,43322368⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468304615,0,false,-43324032,-43323968⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626068,0,false,-1728,-1664⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626818,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269637564664,0,true,158181648320,158181648384⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929385690888,0,false,-184825227328,-184825227264⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269762138449,0,true,158289524480,158289524544⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929261117103,0,false,-184972614464,-184972614400⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073149708854,0,false,-26683089984,-26683089920⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073188273234,0,false,-26643578944,-26643578880⟩
    { al := (633927/4096000), au := (1268703/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨170168483315,170282434167⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158218493120,158218493184⟩ : DyadicInterval 40),(⟨-184875563136,-184875563072⟩ : DyadicInterval 40),(⟨748902042363,748902061692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158317167296,158317167360⟩ : DyadicInterval 40),(⟨-185010387328,-185010387264⟩ : DyadicInterval 40),(⟨748884257573,748884276902⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158144809792,158144809856⟩ : DyadicInterval 40),(⟨-184774904064,-184774904000⟩ : DyadicInterval 40),(⟨748915313938,748915333267⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158261873216,158261873280⟩ : DyadicInterval 40),(⟨-184934832384,-184934832320⟩ : DyadicInterval 40),(⟨748894225349,748894244679⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32469333,43323161⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32468800,32468864⟩ : DyadicInterval 40),(⟨-32469824,-32469760⟩ : DyadicInterval 40),(⟨762123383105,762123402434⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43322304,43322368⟩ : DyadicInterval 40),(⟨-43324032,-43323968⟩ : DyadicInterval 40),(⟨762123382708,762123402038⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1728,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170125936888,170250510673⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158181648320,158181648384⟩ : DyadicInterval 40),(⟨-184825227328,-184825227264⟩ : DyadicInterval 40),(⟨748908679668,748908698998⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158289524480,158289524544⟩ : DyadicInterval 40),(⟨-184972614464,-184972614400⟩ : DyadicInterval 40),(⟨748889241223,748889260552⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26683089984,-26643578880⟩ : DyadicInterval 40),(⟨775445173056,775464947872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158218493120,158317167360⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185010387328,-184875563072⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1900_ok : ecellOkT e1900 = true := by decide +kernel
theorem e1900_pos {a z : ℝ} (ha1 : ((633927/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1268703/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1900 e1900_ok ha1 ha2 hz1 hz2 hz

-- box ['1268703/8192000', '79347/512000', '1999/2000', '7997/8000']  interval_lower 80223439/549755813888
noncomputable def e1901 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269794061942,0,true,158317167296,158317167360⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929229193610,0,false,-185010387328,-185010387264⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269908012794,0,true,158415832640,158415832704⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929115242758,0,false,-185145228096,-185145228032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269708920724,0,true,158243441280,158243441344⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929314334828,0,false,-184909648512,-184909648448⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269844114150,0,true,158360506560,158360506624⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929179141402,0,false,-185069613312,-185069613248⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544119623,0,true,32491328,32491392⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479135929,0,false,-32492352,-32492288⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554980958,0,true,43352320,43352384⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468274594,0,false,-43354048,-43353984⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626066,0,false,-1728,-1664⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626816,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269751487027,0,true,158280301184,158280301248⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929271768525,0,false,-184960011712,-184960011648⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269876067937,0,true,158388173824,158388173888⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929147187615,0,false,-185107425344,-185107425280⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073114414924,0,false,-26719251520,-26719251456⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073153007326,0,false,-26679710464,-26679710400⟩
    { al := (1268703/8192000), au := (79347/512000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨170282434166,170396385018⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158317167296,158317167360⟩ : DyadicInterval 40),(⟨-185010387328,-185010387264⟩ : DyadicInterval 40),(⟨748884257573,748884276902⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158415832640,158415832704⟩ : DyadicInterval 40),(⟨-185145228096,-185145228032⟩ : DyadicInterval 40),(⟨748866460687,748866480017⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158243441280,158243441344⟩ : DyadicInterval 40),(⟨-184909648512,-184909648448⟩ : DyadicInterval 40),(⟨748897547055,748897566385⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158360506560,158360506624⟩ : DyadicInterval 40),(⟨-185069613312,-185069613248⟩ : DyadicInterval 40),(⟨748876441893,748876461222⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32491847,43353182⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32491328,32491392⟩ : DyadicInterval 40),(⟨-32492352,-32492288⟩ : DyadicInterval 40),(⟨762123383103,762123402432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43352320,43352384⟩ : DyadicInterval 40),(⟨-43354048,-43353984⟩ : DyadicInterval 40),(⟨762123382706,762123402035⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1728,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170239859251,170364440161⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158280301184,158280301248⟩ : DyadicInterval 40),(⟨-184960011712,-184960011648⟩ : DyadicInterval 40),(⟨748890903844,748890923173⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158388173824,158388173888⟩ : DyadicInterval 40),(⟨-185107425344,-185107425280⟩ : DyadicInterval 40),(⟨748871451065,748871470395⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26719251520,-26679710400⟩ : DyadicInterval 40),(⟨775463238816,775483028640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158317167296,158415832704⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185145228096,-185010387264⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1901_ok : ecellOkT e1901 = true := by decide +kernel
theorem e1901_pos {a z : ℝ} (ha1 : ((1268703/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((79347/512000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1901 e1901_ok ha1 ha2 hz1 hz2 hz

-- box ['633927/4096000', '1268703/8192000', '7997/8000', '3999/4000']  interval_lower 39810779/274877906944
noncomputable def e1902 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269680111091,0,true,158218493120,158218493184⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929343144461,0,false,-184875563136,-184875563072⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269794061943,0,true,158317167296,158317167360⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929229193609,0,false,-185010387328,-185010387264⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269616297909,0,true,158163231104,158163231168⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929406957643,0,false,-184800067968,-184800067904⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269751491335,0,true,158280304896,158280304960⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929271764217,0,false,-184960016768,-184960016704⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533273960,0,true,21645952,21646016⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489981592,0,false,-21646400,-21646336⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544120283,0,true,32491968,32492032⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479135269,0,false,-32492992,-32492928⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626815,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627350,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269648200114,0,true,158190858624,158190858688⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929375055438,0,false,-184837809728,-184837809664⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269772781046,0,true,158298740096,158298740160⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929250474506,0,false,-184985206976,-184985206912⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073146412911,0,false,-26686466880,-26686466816⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073184981913,0,false,-26646951040,-26646950976⟩
    { al := (633927/4096000), au := (1268703/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨170168483315,170282434167⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158218493120,158218493184⟩ : DyadicInterval 40),(⟨-184875563136,-184875563072⟩ : DyadicInterval 40),(⟨748902042363,748902061692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158317167296,158317167360⟩ : DyadicInterval 40),(⟨-185010387328,-185010387264⟩ : DyadicInterval 40),(⟨748884257573,748884276902⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158163231104,158163231168⟩ : DyadicInterval 40),(⟨-184800067968,-184800067904⟩ : DyadicInterval 40),(⟨748911996667,748912015996⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158280304896,158280304960⟩ : DyadicInterval 40),(⟨-184960016768,-184960016704⟩ : DyadicInterval 40),(⟨748890903165,748890922494⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21646184,32492507⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21645952,21646016⟩ : DyadicInterval 40),(⟨-21646400,-21646336⟩ : DyadicInterval 40),(⟨762123383349,762123402678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32491968,32492032⟩ : DyadicInterval 40),(⟨-32492992,-32492928⟩ : DyadicInterval 40),(⟨762123383103,762123402432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170136572338,170261153270⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158190858624,158190858688⟩ : DyadicInterval 40),(⟨-184837809728,-184837809664⟩ : DyadicInterval 40),(⟨748907020700,748907040030⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158298740096,158298740160⟩ : DyadicInterval 40),(⟨-184985206976,-184985206912⟩ : DyadicInterval 40),(⟨748887579876,748887599205⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26686466880,-26646950976⟩ : DyadicInterval 40),(⟨775446859104,775466636320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158218493120,158317167360⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185010387328,-184875563072⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1902_ok : ecellOkT e1902 = true := by decide +kernel
theorem e1902_pos {a z : ℝ} (ha1 : ((633927/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1268703/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1902 e1902_ok ha1 ha2 hz1 hz2 hz

-- box ['1268703/8192000', '79347/512000', '7997/8000', '3999/4000']  interval_lower 160294917/1099511627776
noncomputable def e1903 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269794061942,0,true,158317167296,158317167360⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929229193610,0,false,-185010387328,-185010387264⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269908012794,0,true,158415832640,158415832704⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929115242758,0,false,-185145228096,-185145228032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269730206029,0,true,158261873216,158261873280⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929293049523,0,false,-184934832384,-184934832320⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269865413698,0,true,158378948864,158378948928⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929157841854,0,false,-185094817664,-185094817600⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533288970,0,true,21660928,21660992⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489966582,0,false,-21661440,-21661376⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544142799,0,true,32514496,32514560⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479112753,0,false,-32515520,-32515456⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626814,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627350,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269762129594,0,true,158289516800,158289516864⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929261125958,0,false,-184972604032,-184972603968⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269886717651,0,true,158397394752,158397394816⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929136537901,0,false,-185120027776,-185120027712⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073111114569,0,false,-26722633024,-26722632960⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073149711597,0,false,-26683087168,-26683087104⟩
    { al := (1268703/8192000), au := (79347/512000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨170282434166,170396385018⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158317167296,158317167360⟩ : DyadicInterval 40),(⟨-185010387328,-185010387264⟩ : DyadicInterval 40),(⟨748884257573,748884276902⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158415832640,158415832704⟩ : DyadicInterval 40),(⟨-185145228096,-185145228032⟩ : DyadicInterval 40),(⟨748866460687,748866480017⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158261873216,158261873280⟩ : DyadicInterval 40),(⟨-184934832384,-184934832320⟩ : DyadicInterval 40),(⟨748894225350,748894244680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158378948864,158378948928⟩ : DyadicInterval 40),(⟨-185094817664,-185094817600⟩ : DyadicInterval 40),(⟨748873115266,748873134596⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21661194,32515023⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21660928,21660992⟩ : DyadicInterval 40),(⟨-21661440,-21661376⟩ : DyadicInterval 40),(⟨762123383381,762123402710⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32514496,32514560⟩ : DyadicInterval 40),(⟨-32515520,-32515456⟩ : DyadicInterval 40),(⟨762123383102,762123402431⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170250501818,170375089875⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158289516800,158289516864⟩ : DyadicInterval 40),(⟨-184972604032,-184972603968⟩ : DyadicInterval 40),(⟨748889242631,748889261961⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158397394752,158397394816⟩ : DyadicInterval 40),(⟨-185120027776,-185120027712⟩ : DyadicInterval 40),(⟨748869787470,748869806800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26722633024,-26683087104⟩ : DyadicInterval 40),(⟨775464927168,775484719392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158317167296,158415832704⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185145228096,-185010387264⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1903_ok : ecellOkT e1903 = true := by decide +kernel
theorem e1903_pos {a z : ℝ} (ha1 : ((1268703/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((79347/512000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1903 e1903_ok ha1 ha2 hz1 hz2 hz

-- box ['316539/2048000', '253401/1638400', '3999/4000', '7999/8000']  interval_lower 156996595/1099511627776
noncomputable def e1904 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269452209389,0,true,158021118144,158021118208⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929571046163,0,false,-184605964288,-184605964224⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269566160241,0,true,158119810048,158119810112⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929457095311,0,false,-184740755456,-184740755392⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269409724243,0,true,157984319872,157984319936⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929613531309,0,false,-184555713280,-184555713216⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269544903425,0,true,158101400384,158101400448⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929478352127,0,false,-184715609728,-184715609664⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522435756,0,true,10807872,10807936⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500819796,0,false,-10808064,-10808000⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533259563,0,true,21631552,21631616⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489995989,0,false,-21632000,-21631936⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627350,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627670,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269430962378,0,true,158002715328,158002715392⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929592293174,0,false,-184580833280,-184580833216⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269555536204,0,true,158110609024,158110609088⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929467719348,0,false,-184728187712,-184728187648⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073213651417,0,false,-26617578624,-26617578560⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073252168993,0,false,-26578117888,-26578117824⟩
    { al := (316539/2048000), au := (253401/1638400), zl := (3999/4000), zu := (7999/8000),
      A := ⟨169940581613,170054532465⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158021118144,158021118208⟩ : DyadicInterval 40),(⟨-184605964288,-184605964224⟩ : DyadicInterval 40),(⟨748937575655,748937594984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158119810048,158119810112⟩ : DyadicInterval 40),(⟨-184740755456,-184740755392⟩ : DyadicInterval 40),(⟨748919815069,748919834398⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157984319872,157984319936⟩ : DyadicInterval 40),(⟨-184555713280,-184555713216⟩ : DyadicInterval 40),(⟨748944194334,748944213664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158101400384,158101400448⟩ : DyadicInterval 40),(⟨-184715609728,-184715609664⟩ : DyadicInterval 40),(⟨748923129090,748923148419⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10807980,21631787⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10807872,10807936⟩ : DyadicInterval 40),(⟨-10808064,-10808000⟩ : DyadicInterval 40),(⟨762123383541,762123402870⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21631552,21631616⟩ : DyadicInterval 40),(⟨-21632000,-21631936⟩ : DyadicInterval 40),(⟨762123383350,762123402679⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169919334602,170043908428⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158002715328,158002715392⟩ : DyadicInterval 40),(⟨-184580833280,-184580833216⟩ : DyadicInterval 40),(⟨748940885904,748940905234⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158110609024,158110609088⟩ : DyadicInterval 40),(⟨-184728187712,-184728187648⟩ : DyadicInterval 40),(⟨748921471469,748921490798⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26617578624,-26578117824⟩ : DyadicInterval 40),(⟨775412442528,775432192192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158021118144,158119810112⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184740755456,-184605964224⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1904_ok : ecellOkT e1904 = true := by decide +kernel
theorem e1904_pos {a z : ℝ} (ha1 : ((316539/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((253401/1638400 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1904 e1904_ok ha1 ha2 hz1 hz2 hz

-- box ['253401/1638400', '633927/4096000', '3999/4000', '7999/8000']  interval_lower 79021471/549755813888
noncomputable def e1905 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269566160240,0,true,158119810048,158119810112⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929457095312,0,false,-184740755456,-184740755392⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269680111092,0,true,158218493120,158218493184⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929343144460,0,false,-184875563136,-184875563072⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269523646606,0,true,158082990400,158082990464⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929499608946,0,false,-184690464640,-184690464576⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269658840032,0,true,158200072768,158200072832⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929364415520,0,false,-184850397504,-184850397440⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522443259,0,true,10815424,10815488⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500812293,0,false,-10815552,-10815488⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533274572,0,true,21646528,21646592⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489980980,0,false,-21647040,-21646976⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627349,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627670,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269544898979,0,true,158101396544,158101396608⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929478356573,0,false,-184715604480,-184715604416⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269669479935,0,true,158209286784,158209286848⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929353775617,0,false,-184862985408,-184862985344⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073178395893,0,false,-26653698624,-26653698560⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073216941494,0,false,-26614207936,-26614207872⟩
    { al := (253401/1638400), au := (633927/4096000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨170054532464,170168483316⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158119810048,158119810112⟩ : DyadicInterval 40),(⟨-184740755456,-184740755392⟩ : DyadicInterval 40),(⟨748919815069,748919834399⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158218493120,158218493184⟩ : DyadicInterval 40),(⟨-184875563136,-184875563072⟩ : DyadicInterval 40),(⟨748902042363,748902061692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158082990400,158082990464⟩ : DyadicInterval 40),(⟨-184690464640,-184690464576⟩ : DyadicInterval 40),(⟨748926442725,748926462054⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158200072768,158200072832⟩ : DyadicInterval 40),(⟨-184850397504,-184850397440⟩ : DyadicInterval 40),(⟨748905360879,748905380208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10815483,21646796⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10815424,10815488⟩ : DyadicInterval 40),(⟨-10815552,-10815488⟩ : DyadicInterval 40),(⟨762123383509,762123402838⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21646528,21646592⟩ : DyadicInterval 40),(⟨-21647040,-21646976⟩ : DyadicInterval 40),(⟨762123383381,762123402710⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170033271203,170157852159⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158101396544,158101396608⟩ : DyadicInterval 40),(⟨-184715604480,-184715604416⟩ : DyadicInterval 40),(⟨748923129782,748923149111⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158209286784,158209286848⟩ : DyadicInterval 40),(⟨-184862985408,-184862985344⟩ : DyadicInterval 40),(⟨748903700977,748903720307⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26653698624,-26614207872⟩ : DyadicInterval 40),(⟨775430487552,775450252192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158119810048,158218493184⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184875563136,-184740755392⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1905_ok : ecellOkT e1905 = true := by decide +kernel
theorem e1905_pos {a z : ℝ} (ha1 : ((253401/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((633927/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1905 e1905_ok ha1 ha2 hz1 hz2 hz

-- box ['316539/2048000', '253401/1638400', '7999/8000', '1']  interval_lower 9802867/68719476736
noncomputable def e1906 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269452209389,0,true,158021118144,158021118208⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929571046163,0,false,-184605964288,-184605964224⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269566160241,0,true,158119810048,158119810112⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929457095311,0,false,-184740755456,-184740755392⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269430966816,0,true,158002719168,158002719232⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929592288736,0,false,-184580838528,-184580838464⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522443822,0,true,10815936,10816000⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500811730,0,false,-10816128,-10816064⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627669,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1269441583626,0,true,158011914816,158011914880⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨929581671926,0,false,-184593396032,-184593395968⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1269566164598,0,true,158119813824,158119813888⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨929457090954,0,false,-184740760576,-184740760512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1073210363866,0,false,-26620946752,-26620946688⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1073248886059,0,false,-26581481152,-26581481088⟩
    { al := (316539/2048000), au := (253401/1638400), zl := (7999/8000), zu := 1,
      A := ⟨169940581613,170054532465⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158021118144,158021118208⟩ : DyadicInterval 40),(⟨-184605964288,-184605964224⟩ : DyadicInterval 40),(⟨748937575655,748937594984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158119810048,158119810112⟩ : DyadicInterval 40),(⟨-184740755456,-184740755392⟩ : DyadicInterval 40),(⟨748919815069,748919834398⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158002719168,158002719232⟩ : DyadicInterval 40),(⟨-184580838528,-184580838464⟩ : DyadicInterval 40),(⟨748940885215,748940904544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158119810048,158119810112⟩ : DyadicInterval 40),(⟨-184740755456,-184740755392⟩ : DyadicInterval 40),(⟨748919815069,748919834398⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10816046⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10815936,10816000⟩ : DyadicInterval 40),(⟨-10816128,-10816064⟩ : DyadicInterval 40),(⟨762123383541,762123402870⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨169929955850,170054536822⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158011914816,158011914880⟩ : DyadicInterval 40),(⟨-184593396032,-184593395968⟩ : DyadicInterval 40),(⟨748939231181,748939250511⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158119813824,158119813888⟩ : DyadicInterval 40),(⟨-184740760576,-184740760512⟩ : DyadicInterval 40),(⟨748919814373,748919833703⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26620946752,-26581481088⟩ : DyadicInterval 40),(⟨775414124160,775433876256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨158021118144,158119810112⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184740755456,-184605964224⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1906_ok : ecellOkT e1906 = true := by decide +kernel
theorem e1906_pos {a z : ℝ} (ha1 : ((316539/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((253401/1638400 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1906 e1906_ok ha1 ha2 hz1 hz2 hz

-- box ['253401/1638400', '633927/4096000', '7999/8000', '1']  interval_lower 78945815/549755813888
noncomputable def e1907 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269566160240,0,true,158119810048,158119810112⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929457095312,0,false,-184740755456,-184740755392⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269680111092,0,true,158218493120,158218493184⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929343144460,0,false,-184875563136,-184875563072⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269544903423,0,true,158101400384,158101400448⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929478352129,0,false,-184715609728,-184715609664⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522451327,0,true,10823488,10823552⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500804225,0,false,-10823616,-10823552⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627669,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1269555527353,0,true,158110601408,158110601472⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨929467728199,0,false,-184728177216,-184728177152⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1269680115452,0,true,158218496896,158218496960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨929343140100,0,false,-184875568320,-184875568256⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1073175103935,0,false,-26657071360,-26657071296⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1073213654155,0,false,-26617575808,-26617575744⟩
    { al := (253401/1638400), au := (633927/4096000), zl := (7999/8000), zu := 1,
      A := ⟨170054532464,170168483316⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158119810048,158119810112⟩ : DyadicInterval 40),(⟨-184740755456,-184740755392⟩ : DyadicInterval 40),(⟨748919815069,748919834399⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158218493120,158218493184⟩ : DyadicInterval 40),(⟨-184875563136,-184875563072⟩ : DyadicInterval 40),(⟨748902042363,748902061692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158101400384,158101400448⟩ : DyadicInterval 40),(⟨-184715609728,-184715609664⟩ : DyadicInterval 40),(⟨748923129090,748923148420⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158218493120,158218493184⟩ : DyadicInterval 40),(⟨-184875563136,-184875563072⟩ : DyadicInterval 40),(⟨748902042363,748902061692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10823551⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10823488,10823552⟩ : DyadicInterval 40),(⟨-10823616,-10823552⟩ : DyadicInterval 40),(⟨762123383509,762123402838⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨170043899577,170168487676⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158110601408,158110601472⟩ : DyadicInterval 40),(⟨-184728177216,-184728177152⟩ : DyadicInterval 40),(⟨748921472809,748921492139⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158218496896,158218496960⟩ : DyadicInterval 40),(⟨-184875568320,-184875568256⟩ : DyadicInterval 40),(⟨748902041694,748902061023⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26657071360,-26617575744⟩ : DyadicInterval 40),(⟨775432171488,775451938560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨158119810048,158218493184⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184875563136,-184740755392⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1907_ok : ecellOkT e1907 = true := by decide +kernel
theorem e1907_pos {a z : ℝ} (ha1 : ((253401/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((633927/4096000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1907 e1907_ok ha1 ha2 hz1 hz2 hz

-- box ['633927/4096000', '1268703/8192000', '3999/4000', '7999/8000']  interval_lower 39772945/274877906944
noncomputable def e1908 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269680111091,0,true,158218493120,158218493184⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929343144461,0,false,-184875563136,-184875563072⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269794061943,0,true,158317167296,158317167360⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929229193609,0,false,-185010387328,-185010387264⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269637568970,0,true,158181652096,158181652160⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929385686582,0,false,-184825232448,-184825232384⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269772776639,0,true,158298736256,158298736320⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929250478913,0,false,-184985201792,-184985201728⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522450764,0,true,10822912,10822976⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500804788,0,false,-10823104,-10823040⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533289581,0,true,21661568,21661632⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489965971,0,false,-21662080,-21662016⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627349,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627670,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269658835587,0,true,158200068928,158200068992⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929364419965,0,false,-184850392256,-184850392192⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269783423663,0,true,158307955584,158307955648⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929239831889,0,false,-184997799680,-184997799616⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073143116755,0,false,-26689844032,-26689843968⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073181690380,0,false,-26650323328,-26650323264⟩
    { al := (633927/4096000), au := (1268703/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨170168483315,170282434167⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158218493120,158218493184⟩ : DyadicInterval 40),(⟨-184875563136,-184875563072⟩ : DyadicInterval 40),(⟨748902042363,748902061692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158317167296,158317167360⟩ : DyadicInterval 40),(⟨-185010387328,-185010387264⟩ : DyadicInterval 40),(⟨748884257573,748884276902⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158181652096,158181652160⟩ : DyadicInterval 40),(⟨-184825232448,-184825232384⟩ : DyadicInterval 40),(⟨748908678981,748908698310⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158298736256,158298736320⟩ : DyadicInterval 40),(⟨-184985201792,-184985201728⟩ : DyadicInterval 40),(⟨748887580590,748887599920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10822988,21661805⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10822912,10822976⟩ : DyadicInterval 40),(⟨-10823104,-10823040⟩ : DyadicInterval 40),(⟨762123383541,762123402870⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21661568,21661632⟩ : DyadicInterval 40),(⟨-21662080,-21662016⟩ : DyadicInterval 40),(⟨762123383381,762123402710⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170147207811,170271795887⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158200068928,158200068992⟩ : DyadicInterval 40),(⟨-184850392256,-184850392192⟩ : DyadicInterval 40),(⟨748905361571,748905380901⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158307955584,158307955648⟩ : DyadicInterval 40),(⟨-184997799680,-184997799616⟩ : DyadicInterval 40),(⟨748885918469,748885937799⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26689844032,-26650323264⟩ : DyadicInterval 40),(⟨775448545248,775468324896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158218493120,158317167360⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185010387328,-184875563072⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1908_ok : ecellOkT e1908 = true := by decide +kernel
theorem e1908_pos {a z : ℝ} (ha1 : ((633927/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1268703/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1908 e1908_ok ha1 ha2 hz1 hz2 hz

-- box ['1268703/8192000', '79347/512000', '3999/4000', '7999/8000']  interval_lower 10008943/68719476736
noncomputable def e1909 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269794061942,0,true,158317167296,158317167360⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929229193610,0,false,-185010387328,-185010387264⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269908012794,0,true,158415832640,158415832704⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929115242758,0,false,-185145228096,-185145228032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269751491333,0,true,158280304896,158280304960⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929271764219,0,false,-184960016768,-184960016704⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269886713246,0,true,158397390912,158397390976⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929136542306,0,false,-185120022592,-185120022528⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522458269,0,true,10830400,10830464⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500797283,0,false,-10830592,-10830528⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533304592,0,true,21676544,21676608⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489950960,0,false,-21677056,-21676992⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627348,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627670,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269772772191,0,true,158298732416,158298732480⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929250483361,0,false,-184985196544,-184985196480⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269897367391,0,true,158406615616,158406615680⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929125888161,0,false,-185132630464,-185132630400⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073107814000,0,false,-26726014784,-26726014720⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073146415654,0,false,-26686464064,-26686464000⟩
    { al := (1268703/8192000), au := (79347/512000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨170282434166,170396385018⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158317167296,158317167360⟩ : DyadicInterval 40),(⟨-185010387328,-185010387264⟩ : DyadicInterval 40),(⟨748884257573,748884276902⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158415832640,158415832704⟩ : DyadicInterval 40),(⟨-185145228096,-185145228032⟩ : DyadicInterval 40),(⟨748866460687,748866480017⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158280304896,158280304960⟩ : DyadicInterval 40),(⟨-184960016768,-184960016704⟩ : DyadicInterval 40),(⟨748890903165,748890922494⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158397390912,158397390976⟩ : DyadicInterval 40),(⟨-185120022592,-185120022528⟩ : DyadicInterval 40),(⟨748869788186,748869807515⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10830493,21676816⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10830400,10830464⟩ : DyadicInterval 40),(⟨-10830592,-10830528⟩ : DyadicInterval 40),(⟨762123383541,762123402870⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21676544,21676608⟩ : DyadicInterval 40),(⟨-21677056,-21676992⟩ : DyadicInterval 40),(⟨762123383380,762123402709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170261144415,170385739615⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158298732416,158298732480⟩ : DyadicInterval 40),(⟨-184985196544,-184985196480⟩ : DyadicInterval 40),(⟨748887581284,748887600614⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158406615616,158406615680⟩ : DyadicInterval 40),(⟨-185132630464,-185132630400⟩ : DyadicInterval 40),(⟨748868123805,748868143134⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26726014784,-26686464000⟩ : DyadicInterval 40),(⟨775466615616,775486410272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158317167296,158415832704⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185145228096,-185010387264⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1909_ok : ecellOkT e1909 = true := by decide +kernel
theorem e1909_pos {a z : ℝ} (ha1 : ((1268703/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((79347/512000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1909 e1909_ok ha1 ha2 hz1 hz2 hz

-- box ['633927/4096000', '1268703/8192000', '7999/8000', '1']  interval_lower 158940089/1099511627776
noncomputable def e1910 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269680111091,0,true,158218493120,158218493184⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929343144461,0,false,-184875563136,-184875563072⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269794061943,0,true,158317167296,158317167360⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929229193609,0,false,-185010387328,-185010387264⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269658840030,0,true,158200072768,158200072832⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929364415522,0,false,-184850397504,-184850397440⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522458831,0,true,10830976,10831040⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500796721,0,false,-10831168,-10831104⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627669,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1269669471082,0,true,158209279104,158209279168⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨929353784470,0,false,-184862974976,-184862974912⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1269794066304,0,true,158317171072,158317171136⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨929229189248,0,false,-185010392512,-185010392448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1073139820385,0,false,-26693221376,-26693221312⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1073178398634,0,false,-26653695808,-26653695744⟩
    { al := (633927/4096000), au := (1268703/8192000), zl := (7999/8000), zu := 1,
      A := ⟨170168483315,170282434167⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158218493120,158218493184⟩ : DyadicInterval 40),(⟨-184875563136,-184875563072⟩ : DyadicInterval 40),(⟨748902042363,748902061692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158317167296,158317167360⟩ : DyadicInterval 40),(⟨-185010387328,-185010387264⟩ : DyadicInterval 40),(⟨748884257573,748884276902⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158200072768,158200072832⟩ : DyadicInterval 40),(⟨-184850397504,-184850397440⟩ : DyadicInterval 40),(⟨748905360879,748905380209⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158317167296,158317167360⟩ : DyadicInterval 40),(⟨-185010387328,-185010387264⟩ : DyadicInterval 40),(⟨748884257573,748884276902⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10831055⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10830976,10831040⟩ : DyadicInterval 40),(⟨-10831168,-10831104⟩ : DyadicInterval 40),(⟨762123383541,762123402870⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨170157843306,170282438528⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158209279104,158209279168⟩ : DyadicInterval 40),(⟨-184862974976,-184862974912⟩ : DyadicInterval 40),(⟨748903702384,748903721713⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158317171072,158317171136⟩ : DyadicInterval 40),(⟨-185010392512,-185010392448⟩ : DyadicInterval 40),(⟨748884256902,748884276231⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26693221376,-26653695744⟩ : DyadicInterval 40),(⟨775450231488,775470013568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨158218493120,158317167360⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185010387328,-184875563072⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1910_ok : ecellOkT e1910 = true := by decide +kernel
theorem e1910_pos {a z : ℝ} (ha1 : ((633927/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1268703/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1910 e1910_ok ha1 ha2 hz1 hz2 hz

-- box ['1268703/8192000', '79347/512000', '7999/8000', '1']  interval_lower 9999455/68719476736
noncomputable def e1911 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269794061942,0,true,158317167296,158317167360⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929229193610,0,false,-185010387328,-185010387264⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269908012794,0,true,158415832640,158415832704⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929115242758,0,false,-185145228096,-185145228032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269772776637,0,true,158298736256,158298736320⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929250478915,0,false,-184985201792,-184985201728⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522466337,0,true,10838464,10838528⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500789215,0,false,-10838656,-10838592⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627669,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1269783414806,0,true,158307947968,158307948032⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨929239840746,0,false,-184997789184,-184997789120⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1269908017155,0,true,158415836416,158415836480⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨929115238397,0,false,-185145233280,-185145233216⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1073104513217,0,false,-26729396800,-26729396736⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1073143119499,0,false,-26689841216,-26689841152⟩
    { al := (1268703/8192000), au := (79347/512000), zl := (7999/8000), zu := 1,
      A := ⟨170282434166,170396385018⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158317167296,158317167360⟩ : DyadicInterval 40),(⟨-185010387328,-185010387264⟩ : DyadicInterval 40),(⟨748884257573,748884276902⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158415832640,158415832704⟩ : DyadicInterval 40),(⟨-185145228096,-185145228032⟩ : DyadicInterval 40),(⟨748866460687,748866480017⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158298736256,158298736320⟩ : DyadicInterval 40),(⟨-184985201792,-184985201728⟩ : DyadicInterval 40),(⟨748887580591,748887599920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158415832640,158415832704⟩ : DyadicInterval 40),(⟨-185145228096,-185145228032⟩ : DyadicInterval 40),(⟨748866460687,748866480017⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10838561⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10838464,10838528⟩ : DyadicInterval 40),(⟨-10838656,-10838592⟩ : DyadicInterval 40),(⟨762123383541,762123402870⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨170271787030,170396389379⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158307947968,158307948032⟩ : DyadicInterval 40),(⟨-184997789184,-184997789120⟩ : DyadicInterval 40),(⟨748885919814,748885939144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158415836416,158415836480⟩ : DyadicInterval 40),(⟨-185145233280,-185145233216⟩ : DyadicInterval 40),(⟨748866460016,748866479345⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26729396800,-26689841152⟩ : DyadicInterval 40),(⟨775468304192,775488101280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨158317167296,158415832704⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185145228096,-185010387264⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1911_ok : ecellOkT e1911 = true := by decide +kernel
theorem e1911_pos {a z : ℝ} (ha1 : ((1268703/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((79347/512000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1911 e1911_ok ha1 ha2 hz1 hz2 hz

-- box ['79347/512000', '1270401/8192000', '999/1000', '7993/8000']  interval_lower 162110385/1099511627776
noncomputable def e1912 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269908012793,0,true,158415832640,158415832704⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929115242759,0,false,-185145228096,-185145228032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270021963645,0,true,158514489152,158514489216⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929001291907,0,false,-185280085440,-185280085376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269737616407,0,true,158268290176,158268290240⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929285639145,0,false,-184943600128,-184943600064⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269872767102,0,true,158385315840,158385315904⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929150488450,0,false,-185103519296,-185103519232⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587494292,0,true,75863872,75863936⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435761260,0,false,-75869184,-75869120⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099598393156,0,true,86761920,86761984⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099424862396,0,false,-86768832,-86768768⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620929,0,false,-6848,-6784⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622542,0,false,-5248,-5184⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269822810849,0,true,158342060672,158342060736⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929200444703,0,false,-185044405056,-185044404992⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269947370306,0,true,158449908672,158449908736⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929075885246,0,false,-185191804608,-185191804544⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073092314329,0,false,-26741895936,-26741895872⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073130916243,0,false,-26702344384,-26702344320⟩
    { al := (79347/512000), au := (1270401/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨170396385017,170510335869⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158415832640,158415832704⟩ : DyadicInterval 40),(⟨-185145228096,-185145228032⟩ : DyadicInterval 40),(⟨748866460688,748866480017⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158514489152,158514489216⟩ : DyadicInterval 40),(⟨-185280085440,-185280085376⟩ : DyadicInterval 40),(⟨748848651705,748848671035⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158268290176,158268290240⟩ : DyadicInterval 40),(⟨-184943600128,-184943600064⟩ : DyadicInterval 40),(⟨748893068776,748893088105⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158385315840,158385315904⟩ : DyadicInterval 40),(⟨-185103519296,-185103519232⟩ : DyadicInterval 40),(⟨748871966654,748871985984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨75866516,86765380⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75863872,75863936⟩ : DyadicInterval 40),(⟨-75869184,-75869120⟩ : DyadicInterval 40),(⟨762123380973,762123400302⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨86761920,86761984⟩ : DyadicInterval 40),(⟨-86768832,-86768768⟩ : DyadicInterval 40),(⟨762123380160,762123399490⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6848,-5184⟩ : DyadicInterval 40),(⟨762123386208,762123406304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170311183073,170435742530⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158342060672,158342060736⟩ : DyadicInterval 40),(⟨-185044405056,-185044404992⟩ : DyadicInterval 40),(⟨748879768680,748879788009⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158449908672,158449908736⟩ : DyadicInterval 40),(⟨-185191804608,-185191804544⟩ : DyadicInterval 40),(⟨748860310974,748860330304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26741895936,-26702344320⟩ : DyadicInterval 40),(⟨775474555776,775494350848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158415832640,158514489216⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185280085440,-185145228032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1912_ok : ecellOkT e1912 = true := by decide +kernel
theorem e1912_pos {a z : ℝ} (ha1 : ((79347/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1270401/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1912 e1912_ok ha1 ha2 hz1 hz2 hz

-- box ['1270401/8192000', '5085/32768', '999/1000', '7993/8000']  interval_lower 81584533/549755813888
noncomputable def e1913 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270021963644,0,true,158514489152,158514489216⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929001291908,0,false,-185280085440,-185280085376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270135914496,0,true,158613136768,158613136832⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928887341056,0,false,-185414959232,-185414959168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269851453308,0,true,158366861248,158366861312⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929171802244,0,false,-185078297856,-185078297792⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269986618246,0,true,158483888704,158483888768⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929036637306,0,false,-185238253440,-185238253376⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587546830,0,true,75916416,75916480⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435708722,0,false,-75921728,-75921664⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099598453205,0,true,86821952,86822016⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099424802347,0,false,-86828864,-86828800⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620919,0,false,-6912,-6848⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622534,0,false,-5248,-5184⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269936704723,0,true,158440674432,158440674496⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929086550829,0,false,-185179182592,-185179182528⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270061271304,0,true,158548518912,158548518976⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928961984248,0,false,-185326608640,-185326608576⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073056990851,0,false,-26778089664,-26778089600⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073095620780,0,false,-26738508096,-26738508032⟩
    { al := (1270401/8192000), au := (5085/32768), zl := (999/1000), zu := (7993/8000),
      A := ⟨170510335868,170624286720⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158514489152,158514489216⟩ : DyadicInterval 40),(⟨-185280085440,-185280085376⟩ : DyadicInterval 40),(⟨748848651706,748848671035⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158613136768,158613136832⟩ : DyadicInterval 40),(⟨-185414959232,-185414959168⟩ : DyadicInterval 40),(⟨748830830608,748830849938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158366861248,158366861312⟩ : DyadicInterval 40),(⟨-185078297856,-185078297792⟩ : DyadicInterval 40),(⟨748875295673,748875315002⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158483888704,158483888768⟩ : DyadicInterval 40),(⟨-185238253440,-185238253376⟩ : DyadicInterval 40),(⟨748854177001,748854196331⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨75919054,86825429⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75916416,75916480⟩ : DyadicInterval 40),(⟨-75921728,-75921664⟩ : DyadicInterval 40),(⟨762123380965,762123400295⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨86821952,86822016⟩ : DyadicInterval 40),(⟨-86828864,-86828800⟩ : DyadicInterval 40),(⟨762123380151,762123399480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6912,-5184⟩ : DyadicInterval 40),(⟨762123386208,762123406336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170425076947,170549643528⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158440674432,158440674496⟩ : DyadicInterval 40),(⟨-185179182592,-185179182528⟩ : DyadicInterval 40),(⟨748861977666,748861996996⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158548518912,158548518976⟩ : DyadicInterval 40),(⟨-185326608640,-185326608576⟩ : DyadicInterval 40),(⟨748842505633,748842524962⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26778089664,-26738508032⟩ : DyadicInterval 40),(⟨775492637632,775512447712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158514489152,158613136832⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185414959232,-185280085376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1913_ok : ecellOkT e1913 = true := by decide +kernel
theorem e1913_pos {a z : ℝ} (ha1 : ((1270401/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((5085/32768 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1913 e1913_ok ha1 ha2 hz1 hz2 hz

-- box ['79347/512000', '1270401/8192000', '7993/8000', '3997/4000']  interval_lower 80979205/549755813888
noncomputable def e1914 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269908012793,0,true,158415832640,158415832704⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929115242759,0,false,-185145228096,-185145228032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270021963645,0,true,158514489152,158514489216⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929001291907,0,false,-185280085440,-185280085376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269758915956,0,true,158286734080,158286734144⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929264339596,0,false,-184968801600,-184968801536⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269894080894,0,true,158403770048,158403770112⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929129174658,0,false,-185128741248,-185128741184⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576656326,0,true,65026624,65026688⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446599226,0,false,-65030528,-65030464⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587547685,0,true,75917248,75917312⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435707867,0,false,-75922560,-75922496⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622533,0,false,-5248,-5184⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623931,0,false,-3904,-3840⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269833460449,0,true,158351281856,158351281920⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929189795103,0,false,-185057006656,-185057006592⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269958027048,0,true,158459135168,158459135232⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929065228504,0,false,-185204416384,-185204416320⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073089010414,0,false,-26745281216,-26745281152⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073127616955,0,false,-26705724800,-26705724736⟩
    { al := (79347/512000), au := (1270401/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨170396385017,170510335869⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158415832640,158415832704⟩ : DyadicInterval 40),(⟨-185145228096,-185145228032⟩ : DyadicInterval 40),(⟨748866460688,748866480017⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158514489152,158514489216⟩ : DyadicInterval 40),(⟨-185280085440,-185280085376⟩ : DyadicInterval 40),(⟨748848651705,748848671035⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158286734080,158286734144⟩ : DyadicInterval 40),(⟨-184968801600,-184968801536⟩ : DyadicInterval 40),(⟨748889744235,748889763565⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158403770048,158403770112⟩ : DyadicInterval 40),(⟨-185128741248,-185128741184⟩ : DyadicInterval 40),(⟨748868637227,748868656556⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨65028550,75919909⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65026624,65026688⟩ : DyadicInterval 40),(⟨-65030528,-65030464⟩ : DyadicInterval 40),(⟨762123381657,762123400987⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75917248,75917312⟩ : DyadicInterval 40),(⟨-75922560,-75922496⟩ : DyadicInterval 40),(⟨762123380965,762123400295⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5248,-3840⟩ : DyadicInterval 40),(⟨762123385536,762123405504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170321832673,170446399272⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158351281856,158351281920⟩ : DyadicInterval 40),(⟨-185057006656,-185057006592⟩ : DyadicInterval 40),(⟨748878105660,748878124990⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158459135168,158459135232⟩ : DyadicInterval 40),(⟨-185204416384,-185204416320⟩ : DyadicInterval 40),(⟨748858645598,748858664927⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26745281216,-26705724736⟩ : DyadicInterval 40),(⟨775476245984,775496043488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158415832640,158514489216⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185280085440,-185145228032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1914_ok : ecellOkT e1914 = true := by decide +kernel
theorem e1914_pos {a z : ℝ} (ha1 : ((79347/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1270401/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1914 e1914_ok ha1 ha2 hz1 hz2 hz

-- box ['1270401/8192000', '5085/32768', '7993/8000', '3997/4000']  interval_lower 163016711/1099511627776
noncomputable def e1915 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270021963644,0,true,158514489152,158514489216⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929001291908,0,false,-185280085440,-185280085376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270135914496,0,true,158613136768,158613136832⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928887341056,0,false,-185414959232,-185414959168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269872767100,0,true,158385315840,158385315904⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929150488452,0,false,-185103519296,-185103519232⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270007946282,0,true,158502353664,158502353728⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929015309270,0,false,-185263495424,-185263495360⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576701359,0,true,65071616,65071680⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446554193,0,false,-65075520,-65075456⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587600228,0,true,75969792,75969856⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435655324,0,false,-75975104,-75975040⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622526,0,false,-5312,-5248⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623925,0,false,-3904,-3840⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269947361445,0,true,158449900992,158449901056⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929075894107,0,false,-185191794176,-185191794112⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270071935169,0,true,158557750720,158557750784⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928951320383,0,false,-185339230400,-185339230336⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073053682518,0,false,-26781479616,-26781479552⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073092317078,0,false,-26741893120,-26741893056⟩
    { al := (1270401/8192000), au := (5085/32768), zl := (7993/8000), zu := (3997/4000),
      A := ⟨170510335868,170624286720⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158514489152,158514489216⟩ : DyadicInterval 40),(⟨-185280085440,-185280085376⟩ : DyadicInterval 40),(⟨748848651706,748848671035⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158613136768,158613136832⟩ : DyadicInterval 40),(⟨-185414959232,-185414959168⟩ : DyadicInterval 40),(⟨748830830608,748830849938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158385315840,158385315904⟩ : DyadicInterval 40),(⟨-185103519296,-185103519232⟩ : DyadicInterval 40),(⟨748871966654,748871985984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158502353664,158502353728⟩ : DyadicInterval 40),(⟨-185263495424,-185263495360⟩ : DyadicInterval 40),(⟨748850843079,748850862408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨65073583,75972452⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65071616,65071680⟩ : DyadicInterval 40),(⟨-65075520,-65075456⟩ : DyadicInterval 40),(⟨762123381652,762123400981⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75969792,75969856⟩ : DyadicInterval 40),(⟨-75975104,-75975040⟩ : DyadicInterval 40),(⟨762123380958,762123400287⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5312,-3840⟩ : DyadicInterval 40),(⟨762123385536,762123405536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170435733669,170560307393⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158449900992,158449901056⟩ : DyadicInterval 40),(⟨-185191794176,-185191794112⟩ : DyadicInterval 40),(⟨748860312387,748860331716⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158557750720,158557750784⟩ : DyadicInterval 40),(⟨-185339230400,-185339230336⟩ : DyadicInterval 40),(⟨748840838030,748840857359⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26781479616,-26741893056⟩ : DyadicInterval 40),(⟨775494330144,775514142688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158514489152,158613136832⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185414959232,-185280085376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1915_ok : ecellOkT e1915 = true := by decide +kernel
theorem e1915_pos {a z : ℝ} (ha1 : ((1270401/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((5085/32768 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1915 e1915_ok ha1 ha2 hz1 hz2 hz

-- box ['5085/32768', '1272099/8192000', '999/1000', '7993/8000']  interval_lower 82115423/549755813888
noncomputable def e1916 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270135914496,0,true,158613136768,158613136832⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928887341056,0,false,-185414959232,-185414959168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270249865348,0,true,158711775552,158711775616⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928773390204,0,false,-185549849664,-185549849600⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269965290209,0,true,158465423488,158465423552⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929057965343,0,false,-185213012096,-185213012032⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270100469391,0,true,158582452800,158582452864⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928922786161,0,false,-185373004160,-185373004096⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587599373,0,true,75968960,75969024⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435656179,0,false,-75974272,-75974208⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099598513258,0,true,86882048,86882112⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099424742294,0,false,-86888960,-86888896⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620910,0,false,-6912,-6848⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622527,0,false,-5312,-5248⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270050598600,0,true,158539279360,158539279424⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928972656952,0,false,-185313976576,-185313976512⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270175172302,0,true,158647120320,158647120384⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928848083250,0,false,-185461429184,-185461429120⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073021643773,0,false,-26814308800,-26814308736⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073060301720,0,false,-26774697216,-26774697152⟩
    { al := (5085/32768), au := (1272099/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨170624286720,170738237572⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158613136768,158613136832⟩ : DyadicInterval 40),(⟨-185414959232,-185414959168⟩ : DyadicInterval 40),(⟨748830830608,748830849938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158711775552,158711775616⟩ : DyadicInterval 40),(⟨-185549849664,-185549849600⟩ : DyadicInterval 40),(⟨748812997440,748813016769⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158465423488,158465423552⟩ : DyadicInterval 40),(⟨-185213012096,-185213012032⟩ : DyadicInterval 40),(⟨748857510496,748857529825⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158582452800,158582452864⟩ : DyadicInterval 40),(⟨-185373004160,-185373004096⟩ : DyadicInterval 40),(⟨748836375257,748836394587⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨75971597,86885482⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75968960,75969024⟩ : DyadicInterval 40),(⟨-75974272,-75974208⟩ : DyadicInterval 40),(⟨762123380958,762123400287⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨86882048,86882112⟩ : DyadicInterval 40),(⟨-86888960,-86888896⟩ : DyadicInterval 40),(⟨762123380141,762123399471⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6912,-5248⟩ : DyadicInterval 40),(⟨762123386240,762123406336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170538970824,170663544526⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158539279360,158539279424⟩ : DyadicInterval 40),(⟨-185313976576,-185313976512⟩ : DyadicInterval 40),(⟨748844174526,748844193855⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158647120320,158647120384⟩ : DyadicInterval 40),(⟨-185461429184,-185461429120⟩ : DyadicInterval 40),(⟨748824688187,748824707517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26814308800,-26774697152⟩ : DyadicInterval 40),(⟨775510732192,775530557280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158613136768,158711775616⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185549849664,-185414959168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1916_ok : ecellOkT e1916 = true := by decide +kernel
theorem e1916_pos {a z : ℝ} (ha1 : ((5085/32768 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1272099/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1916 e1916_ok ha1 ha2 hz1 hz2 hz

-- box ['1272099/8192000', '318237/2048000', '999/1000', '7993/8000']  interval_lower 165295093/1099511627776
noncomputable def e1917 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270249865347,0,true,158711775552,158711775616⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928773390205,0,false,-185549849664,-185549849600⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270363816199,0,true,158810405504,158810405568⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928659439353,0,false,-185684756544,-185684756480⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270079127109,0,true,158563976832,158563976896⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928944128443,0,false,-185347742848,-185347742784⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270214320535,0,true,158681008000,158681008064⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928808935017,0,false,-185507771328,-185507771264⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587651919,0,true,76021504,76021568⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435603633,0,false,-76026816,-76026752⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099598573316,0,true,86942080,86942144⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099424682236,0,false,-86948992,-86948928⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620900,0,false,-6912,-6848⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622520,0,false,-5312,-5248⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270164492469,0,true,158637875456,158637875520⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928858763083,0,false,-185448787136,-185448787072⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270289073303,0,true,158745712960,158745713024⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928734182249,0,false,-185596266240,-185596266176⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072986273096,0,false,-26850553280,-26850553216⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073024959066,0,false,-26810911680,-26810911616⟩
    { al := (1272099/8192000), au := (318237/2048000), zl := (999/1000), zu := (7993/8000),
      A := ⟨170738237571,170852188423⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158711775552,158711775616⟩ : DyadicInterval 40),(⟨-185549849664,-185549849600⟩ : DyadicInterval 40),(⟨748812997440,748813016769⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158810405504,158810405568⟩ : DyadicInterval 40),(⟨-185684756544,-185684756480⟩ : DyadicInterval 40),(⟨748795152117,748795171446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158563976832,158563976896⟩ : DyadicInterval 40),(⟨-185347742848,-185347742784⟩ : DyadicInterval 40),(⟨748839713279,748839732609⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158681008000,158681008064⟩ : DyadicInterval 40),(⟨-185507771328,-185507771264⟩ : DyadicInterval 40),(⟨748818561440,748818580769⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨76024143,86945540⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76021504,76021568⟩ : DyadicInterval 40),(⟨-76026816,-76026752⟩ : DyadicInterval 40),(⟨762123380951,762123400280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨86942080,86942144⟩ : DyadicInterval 40),(⟨-86948992,-86948928⟩ : DyadicInterval 40),(⟨762123380132,762123399461⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6912,-5248⟩ : DyadicInterval 40),(⟨762123386240,762123406336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170652864693,170777445527⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158637875456,158637875520⟩ : DyadicInterval 40),(⟨-185448787136,-185448787072⟩ : DyadicInterval 40),(⟨748826359312,748826378642⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158745712960,158745713024⟩ : DyadicInterval 40),(⟨-185596266240,-185596266176⟩ : DyadicInterval 40),(⟨748806858600,748806877929⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26850553280,-26810911616⟩ : DyadicInterval 40),(⟨775528839424,775548679520⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158711775552,158810405568⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185684756544,-185549849600⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1917_ok : ecellOkT e1917 = true := by decide +kernel
theorem e1917_pos {a z : ℝ} (ha1 : ((1272099/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((318237/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1917 e1917_ok ha1 ha2 hz1 hz2 hz

-- box ['5085/32768', '1272099/8192000', '7993/8000', '3997/4000']  interval_lower 20509745/137438953472
noncomputable def e1918 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270135914496,0,true,158613136768,158613136832⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928887341056,0,false,-185414959232,-185414959168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270249865348,0,true,158711775552,158711775616⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928773390204,0,false,-185549849664,-185549849600⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269986618245,0,true,158483888704,158483888768⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929036637307,0,false,-185238253440,-185238253376⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270121811670,0,true,158600928384,158600928448⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928901443882,0,false,-185398266048,-185398265984⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576746396,0,true,65116672,65116736⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446509156,0,false,-65120576,-65120512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587652775,0,true,76022336,76022400⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435602777,0,false,-76027648,-76027584⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622519,0,false,-5312,-5248⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623920,0,false,-3904,-3840⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270061262442,0,true,158548511232,158548511296⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928961993110,0,false,-185326598144,-185326598080⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270185843288,0,true,158656357504,158656357568⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928837412264,0,false,-185474060864,-185474060800⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073018331020,0,false,-26817703360,-26817703296⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073056993601,0,false,-26778086848,-26778086784⟩
    { al := (5085/32768), au := (1272099/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨170624286720,170738237572⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158613136768,158613136832⟩ : DyadicInterval 40),(⟨-185414959232,-185414959168⟩ : DyadicInterval 40),(⟨748830830608,748830849938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158711775552,158711775616⟩ : DyadicInterval 40),(⟨-185549849664,-185549849600⟩ : DyadicInterval 40),(⟨748812997440,748813016769⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158483888704,158483888768⟩ : DyadicInterval 40),(⟨-185238253440,-185238253376⟩ : DyadicInterval 40),(⟨748854177002,748854196331⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158600928384,158600928448⟩ : DyadicInterval 40),(⟨-185398266048,-185398265984⟩ : DyadicInterval 40),(⟨748833036852,748833056181⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨65118620,76024999⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65116672,65116736⟩ : DyadicInterval 40),(⟨-65120576,-65120512⟩ : DyadicInterval 40),(⟨762123381647,762123400976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76022336,76022400⟩ : DyadicInterval 40),(⟨-76027648,-76027584⟩ : DyadicInterval 40),(⟨762123380951,762123400280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5312,-3840⟩ : DyadicInterval 40),(⟨762123385536,762123405536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170549634666,170674215512⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158548511232,158548511296⟩ : DyadicInterval 40),(⟨-185326598144,-185326598080⟩ : DyadicInterval 40),(⟨748842507021,748842526350⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158656357504,158656357568⟩ : DyadicInterval 40),(⟨-185474060864,-185474060800⟩ : DyadicInterval 40),(⟨748823018291,748823037621⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26817703360,-26778086784⟩ : DyadicInterval 40),(⟨775512427008,775532254560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158613136768,158711775616⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185549849664,-185414959168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1918_ok : ecellOkT e1918 = true := by decide +kernel
theorem e1918_pos {a z : ℝ} (ha1 : ((5085/32768 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1272099/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1918 e1918_ok ha1 ha2 hz1 hz2 hz

-- box ['1272099/8192000', '318237/2048000', '7993/8000', '3997/4000']  interval_lower 82571025/549755813888
noncomputable def e1919 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270249865347,0,true,158711775552,158711775616⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928773390205,0,false,-185549849664,-185549849600⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270363816199,0,true,158810405504,158810405568⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928659439353,0,false,-185684756544,-185684756480⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270100469389,0,true,158582452800,158582452864⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928922786163,0,false,-185373004160,-185373004096⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270235677058,0,true,158699494272,158699494336⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928787578494,0,false,-185533053184,-185533053120⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576791436,0,true,65161728,65161792⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446464116,0,false,-65165632,-65165568⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587705326,0,true,76074880,76074944⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435550226,0,false,-76080192,-76080128⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622512,0,false,-5312,-5248⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623915,0,false,-3904,-3840⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270175163437,0,true,158647112704,158647112768⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928848092115,0,false,-185461418688,-185461418624⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270299751413,0,true,158754955456,158754955520⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928723504139,0,false,-185608907968,-185608907904⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072982955919,0,false,-26853952448,-26853952384⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073021646526,0,false,-26814305984,-26814305920⟩
    { al := (1272099/8192000), au := (318237/2048000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨170738237571,170852188423⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158711775552,158711775616⟩ : DyadicInterval 40),(⟨-185549849664,-185549849600⟩ : DyadicInterval 40),(⟨748812997440,748813016769⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158810405504,158810405568⟩ : DyadicInterval 40),(⟨-185684756544,-185684756480⟩ : DyadicInterval 40),(⟨748795152117,748795171446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158582452800,158582452864⟩ : DyadicInterval 40),(⟨-185373004160,-185373004096⟩ : DyadicInterval 40),(⟨748836375258,748836394587⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158699494272,158699494336⟩ : DyadicInterval 40),(⟨-185533053184,-185533053120⟩ : DyadicInterval 40),(⟨748815218536,748815237865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨65163660,76077550⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65161728,65161792⟩ : DyadicInterval 40),(⟨-65165632,-65165568⟩ : DyadicInterval 40),(⟨762123381641,762123400971⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76074880,76074944⟩ : DyadicInterval 40),(⟨-76080192,-76080128⟩ : DyadicInterval 40),(⟨762123380943,762123400273⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5312,-3840⟩ : DyadicInterval 40),(⟨762123385536,762123405536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170663535661,170788123637⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158647112704,158647112768⟩ : DyadicInterval 40),(⟨-185461418688,-185461418624⟩ : DyadicInterval 40),(⟨748824689541,748824708870⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158754955456,158754955520⟩ : DyadicInterval 40),(⟨-185608907968,-185608907904⟩ : DyadicInterval 40),(⟨748805186497,748805205827⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26853952448,-26814305920⟩ : DyadicInterval 40),(⟨775530536576,775550379104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158711775552,158810405568⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185684756544,-185549849600⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1919_ok : ecellOkT e1919 = true := by decide +kernel
theorem e1919_pos {a z : ℝ} (ha1 : ((1272099/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((318237/2048000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1919 e1919_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B031

end


