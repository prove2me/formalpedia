-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B014
-- name    : CK_CKLaneC2R_EpCells_B014
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:29:12.145819+00:00
-- url     : https://prove2.me/theorems/cb953a77-d077-45a1-881f-2d2060c02b69
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B014` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B014` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B014` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B014 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B014.lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheckT

-- ===== source module CKLaneC2R.EpCells.B014 =====
section

namespace CKLaneC2R.EpCells.B014

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['751089/4096000', '375969/2048000', '3999/4000', '1']  interval_lower 88828419/549755813888
noncomputable def e840 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1301130545987,0,true,185121947904,185121947968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨897892709565,0,false,-222728951616,-222728951552⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1301358447690,0,true,185314517824,185314517888⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨897664807862,0,false,-223008063296,-223008063232⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1301080141257,0,true,185079352896,185079352960⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨897943114295,0,false,-222667230400,-222667230336⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537491205,0,true,25863104,25863168⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485764347,0,false,-25863744,-25863680⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627167,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1301105338505,0,true,185100646272,185100646336⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨897917917047,0,false,-222698084288,-222698084224⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1301358456194,0,true,185314525056,185314525120⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨897664799358,0,false,-223008073728,-223008073664⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1062456865358,0,false,-37693548672,-37693548608⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1062549741082,0,false,-37597437952,-37597437888⟩
    { al := (751089/4096000), au := (375969/2048000), zl := (3999/4000), zu := 1,
      A := ⟨201618918211,201846819914⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185121947904,185121947968⟩ : DyadicInterval 40),(⟨-222728951616,-222728951552⟩ : DyadicInterval 40),(⟨743532802855,743532822185⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185314517824,185314517888⟩ : DyadicInterval 40),(⟨-223008063296,-223008063232⟩ : DyadicInterval 40),(⟨743490509681,743490529010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185079352896,185079352960⟩ : DyadicInterval 40),(⟨-222667230400,-222667230336⟩ : DyadicInterval 40),(⟨743542150184,743542169513⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185314517824,185314517888⟩ : DyadicInterval 40),(⟨-223008063296,-223008063232⟩ : DyadicInterval 40),(⟨743490509681,743490529010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,25863429⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25863104,25863168⟩ : DyadicInterval 40),(⟨-25863744,-25863680⟩ : DyadicInterval 40),(⟨762123383263,762123402592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨201593710729,201846828418⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185100646272,185100646336⟩ : DyadicInterval 40),(⟨-222698084288,-222698084224⟩ : DyadicInterval 40),(⟨743537477764,743537497094⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185314525056,185314525120⟩ : DyadicInterval 40),(⟨-223008073728,-223008073664⟩ : DyadicInterval 40),(⟨743490508080,743490527410⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37693548672,-37597437888⟩ : DyadicInterval 40),(⟨780922102560,780970177216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨185121947904,185314517888⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-223008063296,-222728951552⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e840_ok : ecellOkT e840 = true := by decide +kernel
theorem e840_pos {a z : ℝ} (ha1 : ((751089/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((375969/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e840 e840_ok ha1 ha2 hz1 hz2 hz

-- box ['375969/2048000', '752787/4096000', '1999/2000', '3999/4000']  interval_lower 22708559/137438953472
noncomputable def e841 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1301358447689,0,true,185314517824,185314517888⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨897664807863,0,false,-223008063296,-223008063232⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1301586349392,0,true,185507054080,185507054144⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨897436906160,0,false,-223287245888,-223287245824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1301257524279,0,true,185229244800,185229244864⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨897765731273,0,false,-222884453440,-222884453376⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1301535830712,0,true,185464377728,185464377792⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨897487424840,0,false,-223225353728,-223225353664⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537490364,0,true,25862272,25862336⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485765188,0,false,-25862912,-25862848⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099563415403,0,true,51786368,51786432⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459840149,0,false,-51788864,-51788800⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625336,0,false,-2496,-2432⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627168,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1301307981096,0,true,185271878016,185271878080⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨897715274456,0,false,-222946250688,-222946250624⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1301561098639,0,true,185485723328,185485723392⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨897462156913,0,false,-223256309888,-223256309824⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1062382426369,0,false,-37770586560,-37770586496⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1062475395340,0,false,-37674372608,-37674372544⟩
    { al := (375969/2048000), au := (752787/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨201846819913,202074721616⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185314517824,185314517888⟩ : DyadicInterval 40),(⟨-223008063296,-223008063232⟩ : DyadicInterval 40),(⟨743490509681,743490529010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185507054080,185507054144⟩ : DyadicInterval 40),(⟨-223287245888,-223287245824⟩ : DyadicInterval 40),(⟨743448167604,743448186933⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185229244800,185229244864⟩ : DyadicInterval 40),(⟨-222884453440,-222884453376⟩ : DyadicInterval 40),(⟨743509244716,743509264046⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185464377728,185464377792⟩ : DyadicInterval 40),(⟨-223225353728,-223225353664⟩ : DyadicInterval 40),(⟨743457557734,743457577063⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨25862588,51787627⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25862272,25862336⟩ : DyadicInterval 40),(⟨-25862912,-25862848⟩ : DyadicInterval 40),(⟨762123383263,762123402592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨51786368,51786432⟩ : DyadicInterval 40),(⟨-51788864,-51788800⟩ : DyadicInterval 40),(⟨762123382360,762123401689⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2496,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨201796353320,202049470863⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185271878016,185271878080⟩ : DyadicInterval 40),(⟨-222946250688,-222946250624⟩ : DyadicInterval 40),(⟨743499879318,743499898647⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185485723328,185485723392⟩ : DyadicInterval 40),(⟨-223256309888,-223256309824⟩ : DyadicInterval 40),(⟨743452861393,743452880722⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37770586560,-37674372544⟩ : DyadicInterval 40),(⟨780960569888,781008696160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨185314517824,185507054144⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-223287245888,-223008063232⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e841_ok : ecellOkT e841 = true := by decide +kernel
theorem e841_pos {a z : ℝ} (ha1 : ((375969/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((752787/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e841 e841_ok ha1 ha2 hz1 hz2 hz

-- box ['752787/4096000', '188409/1024000', '1999/2000', '3999/4000']  interval_lower 185055033/1099511627776
noncomputable def e842 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1301586349391,0,true,185507054080,185507054144⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨897436906161,0,false,-223287245888,-223287245824⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1301814251095,0,true,185699556544,185699556608⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨897209004457,0,false,-223566499392,-223566499328⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1301485312030,0,true,185421699712,185421699776⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨897537943522,0,false,-223163465088,-223163465024⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1301763675440,0,true,185656839552,185656839616⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨897259580112,0,false,-223504521728,-223504521664⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537521040,0,true,25892928,25892992⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485734512,0,false,-25893632,-25893568⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099563476764,0,true,51847744,51847808⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459778788,0,false,-51850240,-51850176⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625330,0,false,-2496,-2432⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627167,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1301535825821,0,true,185464373568,185464373632⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨897487429731,0,false,-223225347776,-223225347712⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1301788971847,0,true,185678205504,185678205568⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨897234283705,0,false,-223535520640,-223535520576⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1062298629849,0,false,-37857315072,-37857315008⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1062391714203,0,false,-37760974144,-37760974080⟩
    { al := (752787/4096000), au := (188409/1024000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨202074721615,202302623319⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185507054080,185507054144⟩ : DyadicInterval 40),(⟨-223287245888,-223287245824⟩ : DyadicInterval 40),(⟨743448167604,743448186933⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185699556544,185699556608⟩ : DyadicInterval 40),(⟨-223566499392,-223566499328⟩ : DyadicInterval 40),(⟨743405776688,743405796017⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185421699712,185421699776⟩ : DyadicInterval 40),(⟨-223163465088,-223163465024⟩ : DyadicInterval 40),(⟨743466945481,743466964810⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185656839552,185656839616⟩ : DyadicInterval 40),(⟨-223504521728,-223504521664⟩ : DyadicInterval 40),(⟨743415188264,743415207593⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨25893264,51848988⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25892928,25892992⟩ : DyadicInterval 40),(⟨-25893632,-25893568⟩ : DyadicInterval 40),(⟨762123383294,762123402623⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨51847744,51847808⟩ : DyadicInterval 40),(⟨-51850240,-51850176⟩ : DyadicInterval 40),(⟨762123382354,762123401684⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2496,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨202024198045,202277344071⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185464373568,185464373632⟩ : DyadicInterval 40),(⟨-223225347776,-223225347712⟩ : DyadicInterval 40),(⟨743457558675,743457578005⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185678205504,185678205568⟩ : DyadicInterval 40),(⟨-223535520640,-223535520576⟩ : DyadicInterval 40),(⟨743410481180,743410500509⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37857315072,-37760974080⟩ : DyadicInterval 40),(⟨781003870656,781052060416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨185507054080,185699556608⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-223566499392,-223287245824⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e842_ok : ecellOkT e842 = true := by decide +kernel
theorem e842_pos {a z : ℝ} (ha1 : ((752787/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((188409/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e842 e842_ok ha1 ha2 hz1 hz2 hz

-- box ['375969/2048000', '752787/4096000', '3999/4000', '1']  interval_lower 181025539/1099511627776
noncomputable def e843 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1301358447689,0,true,185314517824,185314517888⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨897664807863,0,false,-223008063296,-223008063232⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1301586349392,0,true,185507054080,185507054144⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨897436906160,0,false,-223287245888,-223287245824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1301307985984,0,true,185271882176,185271882240⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨897715269568,0,false,-222946256640,-222946256576⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537521882,0,true,25893760,25893824⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485733670,0,false,-25894464,-25894400⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627166,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1301333211718,0,true,185293195904,185293195968⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨897690043834,0,false,-222977153280,-222977153216⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1301586357902,0,true,185507061248,185507061312⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨897436897650,0,false,-223287256320,-223287256256⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1062373142357,0,false,-37780195072,-37780195008⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1062466133472,0,false,-37683957376,-37683957312⟩
    { al := (375969/2048000), au := (752787/4096000), zl := (3999/4000), zu := 1,
      A := ⟨201846819913,202074721616⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185314517824,185314517888⟩ : DyadicInterval 40),(⟨-223008063296,-223008063232⟩ : DyadicInterval 40),(⟨743490509681,743490529010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185507054080,185507054144⟩ : DyadicInterval 40),(⟨-223287245888,-223287245824⟩ : DyadicInterval 40),(⟨743448167604,743448186933⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185271882176,185271882240⟩ : DyadicInterval 40),(⟨-222946256640,-222946256576⟩ : DyadicInterval 40),(⟨743499878378,743499897708⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185507054080,185507054144⟩ : DyadicInterval 40),(⟨-223287245888,-223287245824⟩ : DyadicInterval 40),(⟨743448167604,743448186933⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,25894106⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25893760,25893824⟩ : DyadicInterval 40),(⟨-25894464,-25894400⟩ : DyadicInterval 40),(⟨762123383294,762123402623⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨201821583942,202074730126⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185293195904,185293195968⟩ : DyadicInterval 40),(⟨-222977153280,-222977153216⟩ : DyadicInterval 40),(⟨743495195272,743495214602⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185507061248,185507061312⟩ : DyadicInterval 40),(⟨-223287256320,-223287256256⟩ : DyadicInterval 40),(⟨743448166036,743448185365⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37780195072,-37683957312⟩ : DyadicInterval 40),(⟨780965362272,781013500416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨185314517824,185507054144⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-223287245888,-223008063232⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e843_ok : ecellOkT e843 = true := by decide +kernel
theorem e843_pos {a z : ℝ} (ha1 : ((375969/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((752787/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e843 e843_ok ha1 ha2 hz1 hz2 hz

-- box ['752787/4096000', '188409/1024000', '3999/4000', '1']  interval_lower 92204613/549755813888
noncomputable def e844 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1301586349391,0,true,185507054080,185507054144⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨897436906161,0,false,-223287245888,-223287245824⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1301814251095,0,true,185699556544,185699556608⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨897209004457,0,false,-223566499392,-223566499328⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1301535830710,0,true,185464377728,185464377792⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨897487424842,0,false,-223225353728,-223225353664⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537552563,0,true,25924480,25924544⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485702989,0,false,-25925120,-25925056⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627164,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1301561084931,0,true,185485711744,185485711808⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨897462170621,0,false,-223256293120,-223256293056⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1301814259598,0,true,185699563776,185699563840⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨897208995954,0,false,-223566509824,-223566509760⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1062289324884,0,false,-37866946048,-37866945984⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1062382431408,0,false,-37770581312,-37770581248⟩
    { al := (752787/4096000), au := (188409/1024000), zl := (3999/4000), zu := 1,
      A := ⟨202074721615,202302623319⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185507054080,185507054144⟩ : DyadicInterval 40),(⟨-223287245888,-223287245824⟩ : DyadicInterval 40),(⟨743448167604,743448186933⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185699556544,185699556608⟩ : DyadicInterval 40),(⟨-223566499392,-223566499328⟩ : DyadicInterval 40),(⟨743405776688,743405796017⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185464377728,185464377792⟩ : DyadicInterval 40),(⟨-223225353728,-223225353664⟩ : DyadicInterval 40),(⟨743457557734,743457577063⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185699556544,185699556608⟩ : DyadicInterval 40),(⟨-223566499392,-223566499328⟩ : DyadicInterval 40),(⟨743405776688,743405796017⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,25924787⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25924480,25924544⟩ : DyadicInterval 40),(⟨-25925120,-25925056⟩ : DyadicInterval 40),(⟨762123383260,762123402589⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨202049457155,202302631822⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185485711744,185485711808⟩ : DyadicInterval 40),(⟨-223256293120,-223256293056⟩ : DyadicInterval 40),(⟨743452863954,743452883283⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185699563776,185699563840⟩ : DyadicInterval 40),(⟨-223566509824,-223566509760⟩ : DyadicInterval 40),(⟨743405775080,743405794409⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37866946048,-37770581248⟩ : DyadicInterval 40),(⟨781008674240,781056875904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨185507054080,185699556608⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-223566499392,-223287245824⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e844_ok : ecellOkT e844 = true := by decide +kernel
theorem e844_pos {a z : ℝ} (ha1 : ((752787/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((188409/1024000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e844 e844_ok ha1 ha2 hz1 hz2 hz

-- box ['188409/1024000', '150897/819200', '999/1000', '3997/4000']  interval_lower 47438033/274877906944
noncomputable def e845 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1301814251094,0,true,185699556544,185699556608⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨897209004458,0,false,-223566499392,-223566499328⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1302042152797,0,true,185892025408,185892025472⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨896981102755,0,false,-223845823872,-223845823808⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1301611948470,0,true,185528678592,185528678656⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨897411307082,0,false,-223318609536,-223318609472⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1301890254904,0,true,185763747456,185763747520⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨897133000648,0,false,-223659644480,-223659644416⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589399136,0,true,77768576,77768640⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433856416,0,false,-77774144,-77774080⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099615446922,0,true,103814208,103814272⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099407808630,0,false,-103824064,-103824000⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511617973,0,false,-9856,-9792⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622276,0,false,-5504,-5440⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1301713095822,0,true,185614117568,185614117632⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨897310159730,0,false,-223442542656,-223442542592⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1301966213060,0,true,185827896064,185827896128⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨897057042492,0,false,-223752741504,-223752741440⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1062233387085,0,false,-37924845440,-37924845376⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1062326542465,0,false,-37828425024,-37828424960⟩
    { al := (188409/1024000), au := (150897/819200), zl := (999/1000), zu := (3997/4000),
      A := ⟨202302623318,202530525021⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185699556544,185699556608⟩ : DyadicInterval 40),(⟨-223566499392,-223566499328⟩ : DyadicInterval 40),(⟨743405776688,743405796017⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185892025408,185892025472⟩ : DyadicInterval 40),(⟨-223845823872,-223845823808⟩ : DyadicInterval 40),(⟨743363336834,743363356163⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185528678592,185528678656⟩ : DyadicInterval 40),(⟨-223318609536,-223318609472⟩ : DyadicInterval 40),(⟨743443408496,743443427826⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185763747456,185763747520⟩ : DyadicInterval 40),(⟨-223659644480,-223659644416⟩ : DyadicInterval 40),(⟨743391628693,743391648022⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨77771360,103819146⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77768576,77768640⟩ : DyadicInterval 40),(⟨-77774144,-77774080⟩ : DyadicInterval 40),(⟨762123380834,762123400164⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨103814208,103814272⟩ : DyadicInterval 40),(⟨-103824064,-103824000⟩ : DyadicInterval 40),(⟨762123378676,762123398006⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9856,-5440⟩ : DyadicInterval 40),(⟨762123386336,762123407808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨202201468046,202454585284⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185614117568,185614117632⟩ : DyadicInterval 40),(⟨-223442542656,-223442542592⟩ : DyadicInterval 40),(⟨743424598142,743424617471⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185827896064,185827896128⟩ : DyadicInterval 40),(⟨-223752741504,-223752741440⟩ : DyadicInterval 40),(⟨743377483765,743377503095⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37924845440,-37828424960⟩ : DyadicInterval 40),(⟨781037596096,781085825600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨185699556544,185892025472⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-223845823872,-223566499328⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e845_ok : ecellOkT e845 = true := by decide +kernel
theorem e845_pos {a z : ℝ} (ha1 : ((188409/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((150897/819200 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e845 e845_ok ha1 ha2 hz1 hz2 hz

-- box ['150897/819200', '377667/2048000', '999/1000', '3997/4000']  interval_lower 193174943/1099511627776
noncomputable def e846 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1302042152796,0,true,185892025408,185892025472⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨896981102756,0,false,-223845823872,-223845823808⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1302270054499,0,true,186084460480,186084460544⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨896753201053,0,false,-224125219264,-224125219200⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1301839622270,0,true,185720984832,185720984896⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨897183633282,0,false,-223597591744,-223597591680⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1302117985680,0,true,185956060736,185956060800⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨896905269872,0,false,-223938783040,-223938782976⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589491190,0,true,77860608,77860672⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433764362,0,false,-77866176,-77866112⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099615569683,0,true,103936960,103937024⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099407685869,0,false,-103946880,-103946816⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511617949,0,false,-9856,-9792⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622262,0,false,-5568,-5504⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1301940883572,0,true,185806505088,185806505152⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨897082371980,0,false,-223721695936,-223721695872⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1302194029303,0,true,186020270272,186020270336⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨896829226249,0,false,-224032008512,-224032008448⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1062149443647,0,false,-38011738240,-38011738176⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1062242714409,0,false,-37915190784,-37915190720⟩
    { al := (150897/819200), au := (377667/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨202530525020,202758426723⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185892025408,185892025472⟩ : DyadicInterval 40),(⟨-223845823872,-223845823808⟩ : DyadicInterval 40),(⟨743363336834,743363356164⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186084460480,186084460544⟩ : DyadicInterval 40),(⟨-224125219264,-224125219200⟩ : DyadicInterval 40),(⟨743320848119,743320867448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185720984832,185720984896⟩ : DyadicInterval 40),(⟨-223597591744,-223597591680⟩ : DyadicInterval 40),(⟨743401054497,743401073827⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185956060736,185956060800⟩ : DyadicInterval 40),(⟨-223938783040,-223938782976⟩ : DyadicInterval 40),(⟨743349204384,743349223713⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨77863414,103941907⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77860608,77860672⟩ : DyadicInterval 40),(⟨-77866176,-77866112⟩ : DyadicInterval 40),(⟨762123380821,762123400151⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨103936960,103937024⟩ : DyadicInterval 40),(⟨-103946880,-103946816⟩ : DyadicInterval 40),(⟨762123378685,762123398015⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9856,-5504⟩ : DyadicInterval 40),(⟨762123386368,762123407808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨202429255796,202682401527⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185806505088,185806505152⟩ : DyadicInterval 40),(⟨-223721695936,-223721695872⟩ : DyadicInterval 40),(⟨743382201233,743382220562⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186020270272,186020270336⟩ : DyadicInterval 40),(⟨-224032008512,-224032008448⟩ : DyadicInterval 40),(⟨743335027255,743335046585⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38011738240,-37915190720⟩ : DyadicInterval 40),(⟨781080978976,781129272000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨185892025408,186084460544⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-224125219264,-223845823808⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e846_ok : ecellOkT e846 = true := by decide +kernel
theorem e846_pos {a z : ℝ} (ha1 : ((150897/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((377667/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e846 e846_ok ha1 ha2 hz1 hz2 hz

-- box ['188409/1024000', '150897/819200', '3997/4000', '1999/2000']  interval_lower 94552431/549755813888
noncomputable def e847 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1301814251094,0,true,185699556544,185699556608⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨897209004458,0,false,-223566499392,-223566499328⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1302042152797,0,true,185892025408,185892025472⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨896981102755,0,false,-223845823872,-223845823808⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1301662524126,0,true,185571400576,185571400640⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨897360731426,0,false,-223380576768,-223380576704⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1301940887535,0,true,185806508416,185806508480⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨897082368017,0,false,-223721700800,-223721700736⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099563475592,0,true,51846592,51846656⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459779960,0,false,-51849088,-51849024⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589492694,0,true,77862144,77862208⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433762858,0,false,-77867712,-77867648⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622261,0,false,-5568,-5504⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625332,0,false,-2496,-2432⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1301738383104,0,true,185635476608,185635476672⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨897284872448,0,false,-223473528640,-223473528576⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1301991528982,0,true,185849275200,185849275264⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨897031726570,0,false,-223783771392,-223783771328⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1062224063591,0,false,-37934496128,-37934496064⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1062317241162,0,false,-37838051968,-37838051904⟩
    { al := (188409/1024000), au := (150897/819200), zl := (3997/4000), zu := (1999/2000),
      A := ⟨202302623318,202530525021⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185699556544,185699556608⟩ : DyadicInterval 40),(⟨-223566499392,-223566499328⟩ : DyadicInterval 40),(⟨743405776688,743405796017⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185892025408,185892025472⟩ : DyadicInterval 40),(⟨-223845823872,-223845823808⟩ : DyadicInterval 40),(⟨743363336834,743363356163⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185571400576,185571400640⟩ : DyadicInterval 40),(⟨-223380576768,-223380576704⟩ : DyadicInterval 40),(⟨743434004155,743434023484⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185806508416,185806508480⟩ : DyadicInterval 40),(⟨-223721700800,-223721700736⟩ : DyadicInterval 40),(⟨743382200509,743382219838⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨51847816,77864918⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨51846592,51846656⟩ : DyadicInterval 40),(⟨-51849088,-51849024⟩ : DyadicInterval 40),(⟨762123382355,762123401684⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77862144,77862208⟩ : DyadicInterval 40),(⟨-77867712,-77867648⟩ : DyadicInterval 40),(⟨762123380821,762123400150⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5568,-2432⟩ : DyadicInterval 40),(⟨762123384832,762123405664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨202226755328,202479901206⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185635476608,185635476672⟩ : DyadicInterval 40),(⟨-223473528640,-223473528576⟩ : DyadicInterval 40),(⟨743419893981,743419913310⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185849275200,185849275264⟩ : DyadicInterval 40),(⟨-223783771392,-223783771328⟩ : DyadicInterval 40),(⟨743372768230,743372787559⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37934496128,-37838051904⟩ : DyadicInterval 40),(⟨781042409568,781090650944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨185699556544,185892025472⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-223845823872,-223566499328⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e847_ok : ecellOkT e847 = true := by decide +kernel
theorem e847_pos {a z : ℝ} (ha1 : ((188409/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((150897/819200 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e847 e847_ok ha1 ha2 hz1 hz2 hz

-- box ['150897/819200', '377667/2048000', '3997/4000', '1999/2000']  interval_lower 192525047/1099511627776
noncomputable def e848 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1302042152796,0,true,185892025408,185892025472⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨896981102756,0,false,-223845823872,-223845823808⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1302270054499,0,true,186084460480,186084460544⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨896753201053,0,false,-224125219264,-224125219200⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1301890254902,0,true,185763747456,185763747520⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨897133000650,0,false,-223659644480,-223659644416⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1302168675286,0,true,185998862336,185998862400⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨896854580266,0,false,-224000924928,-224000924864⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099563536962,0,true,51907904,51907968⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459718590,0,false,-51910464,-51910400⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589584767,0,true,77954176,77954240⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433670785,0,false,-77959808,-77959744⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622248,0,false,-5568,-5504⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625326,0,false,-2496,-2432⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1301966199342,0,true,185827884480,185827884544⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨897057056210,0,false,-223752724736,-223752724672⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1302219373714,0,true,186041669696,186041669760⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨896803881838,0,false,-224063081152,-224063081088⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1062140099157,0,false,-38021411456,-38021411392⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1062233392138,0,false,-37924840192,-37924840128⟩
    { al := (150897/819200), au := (377667/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨202530525020,202758426723⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185892025408,185892025472⟩ : DyadicInterval 40),(⟨-223845823872,-223845823808⟩ : DyadicInterval 40),(⟨743363336834,743363356164⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186084460480,186084460544⟩ : DyadicInterval 40),(⟨-224125219264,-224125219200⟩ : DyadicInterval 40),(⟨743320848119,743320867448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185763747456,185763747520⟩ : DyadicInterval 40),(⟨-223659644480,-223659644416⟩ : DyadicInterval 40),(⟨743391628693,743391648023⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185998862336,185998862400⟩ : DyadicInterval 40),(⟨-224000924928,-224000924864⟩ : DyadicInterval 40),(⟨743339754700,743339774030⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨51909186,77956991⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨51907904,51907968⟩ : DyadicInterval 40),(⟨-51910464,-51910400⟩ : DyadicInterval 40),(⟨762123382381,762123401710⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77954176,77954240⟩ : DyadicInterval 40),(⟨-77959808,-77959744⟩ : DyadicInterval 40),(⟨762123380840,762123400169⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5568,-2432⟩ : DyadicInterval 40),(⟨762123384832,762123405664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨202454571566,202707745938⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185827884480,185827884544⟩ : DyadicInterval 40),(⟨-223752724736,-223752724672⟩ : DyadicInterval 40),(⟨743377486338,743377505668⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186041669696,186041669760⟩ : DyadicInterval 40),(⟨-224063081152,-224063081088⟩ : DyadicInterval 40),(⟨743330300969,743330320298⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38021411456,-37924840128⟩ : DyadicInterval 40),(⟨781085803680,781134108608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨185892025408,186084460544⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-224125219264,-223845823808⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e848_ok : ecellOkT e848 = true := by decide +kernel
theorem e848_pos {a z : ℝ} (ha1 : ((150897/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((377667/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e848 e848_ok ha1 ha2 hz1 hz2 hz

-- box ['377667/2048000', '756183/4096000', '999/1000', '3997/4000']  interval_lower 196613161/1099511627776
noncomputable def e849 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1302270054498,0,true,186084460480,186084460544⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨896753201054,0,false,-224125219264,-224125219200⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1302497956201,0,true,186276861952,186276862016⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨896525299351,0,false,-224404685696,-224404685632⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1302067296071,0,true,185913257472,185913257536⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨896955959481,0,false,-223876644672,-223876644608⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1302345716455,0,true,186148340352,186148340416⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨896677539097,0,false,-224217992512,-224217992448⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589583258,0,true,77952704,77952768⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433672294,0,false,-77958272,-77958208⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099615692465,0,true,104059712,104059776⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099407563087,0,false,-104069632,-104069568⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511617926,0,false,-9856,-9792⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622249,0,false,-5568,-5504⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1302168671324,0,true,185998858944,185998859008⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨896854584228,0,false,-224000920128,-224000920064⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1302421845544,0,true,186212610816,186212610880⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨896601410008,0,false,-224311346432,-224311346368⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1062065405803,0,false,-38098735616,-38098735552⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1062158791970,0,false,-38002061120,-38002061056⟩
    { al := (377667/2048000), au := (756183/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨202758426722,202986328425⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186084460480,186084460544⟩ : DyadicInterval 40),(⟨-224125219264,-224125219200⟩ : DyadicInterval 40),(⟨743320848119,743320867449⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186276861952,186276862016⟩ : DyadicInterval 40),(⟨-224404685696,-224404685632⟩ : DyadicInterval 40),(⟨743278310469,743278329798⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185913257472,185913257536⟩ : DyadicInterval 40),(⟨-223876644672,-223876644608⟩ : DyadicInterval 40),(⟨743358651651,743358670980⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186148340352,186148340416⟩ : DyadicInterval 40),(⟨-224217992512,-224217992448⟩ : DyadicInterval 40),(⟨743306731280,743306750610⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨77955482,104064689⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77952704,77952768⟩ : DyadicInterval 40),(⟨-77958272,-77958208⟩ : DyadicInterval 40),(⟨762123380808,762123400138⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨104059712,104059776⟩ : DyadicInterval 40),(⟨-104069632,-104069568⟩ : DyadicInterval 40),(⟨762123378662,762123397992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9856,-5504⟩ : DyadicInterval 40),(⟨762123386368,762123407808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨202657043548,202910217768⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185998858944,185998859008⟩ : DyadicInterval 40),(⟨-224000920128,-224000920064⟩ : DyadicInterval 40),(⟨743339755490,743339774819⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186212610816,186212610880⟩ : DyadicInterval 40),(⟨-224311346432,-224311346368⟩ : DyadicInterval 40),(⟨743292521874,743292541203⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38098735616,-38002061056⟩ : DyadicInterval 40),(⟨781124414144,781172770688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨186084460480,186276862016⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-224404685696,-224125219200⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e849_ok : ecellOkT e849 = true := by decide +kernel
theorem e849_pos {a z : ℝ} (ha1 : ((377667/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((756183/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e849 e849_ok ha1 ha2 hz1 hz2 hz

-- box ['756183/4096000', '94629/512000', '999/1000', '3997/4000']  interval_lower 200066987/1099511627776
noncomputable def e850 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1302497956200,0,true,186276861952,186276862016⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨896525299352,0,false,-224404685696,-224404685632⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1302725857903,0,true,186469229760,186469229824⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨896297397649,0,false,-224684223168,-224684223104⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1302294969871,0,true,186105496448,186105496512⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨896728285681,0,false,-224155768512,-224155768448⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1302573447231,0,true,186340586304,186340586368⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨896449808321,0,false,-224497272896,-224497272832⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589675343,0,true,78044736,78044800⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433580209,0,false,-78050368,-78050304⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099615815267,0,true,104182528,104182592⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099407440285,0,false,-104192448,-104192384⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511617903,0,false,-9920,-9856⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622236,0,false,-5568,-5504⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1302396459073,0,true,186191179200,186191179264⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨896626796479,0,false,-224280215168,-224280215104⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1302649661784,0,true,186404917696,186404917760⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨896373593768,0,false,-224590755392,-224590755328⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1061981273554,0,false,-38185837632,-38185837568⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1062074775150,0,false,-38089035968,-38089035904⟩
    { al := (756183/4096000), au := (94629/512000), zl := (999/1000), zu := (3997/4000),
      A := ⟨202986328424,203214230127⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186276861952,186276862016⟩ : DyadicInterval 40),(⟨-224404685696,-224404685632⟩ : DyadicInterval 40),(⟨743278310469,743278329798⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186469229760,186469229824⟩ : DyadicInterval 40),(⟨-224684223168,-224684223104⟩ : DyadicInterval 40),(⟨743235723910,743235743240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186105496448,186105496512⟩ : DyadicInterval 40),(⟨-224155768512,-224155768448⟩ : DyadicInterval 40),(⟨743316200061,743316219391⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186340586304,186340586368⟩ : DyadicInterval 40),(⟨-224497272896,-224497272832⟩ : DyadicInterval 40),(⟨743264209370,743264228700⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨78047567,104187491⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78044736,78044800⟩ : DyadicInterval 40),(⟨-78050368,-78050304⟩ : DyadicInterval 40),(⟨762123380827,762123400157⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨104182528,104182592⟩ : DyadicInterval 40),(⟨-104192448,-104192384⟩ : DyadicInterval 40),(⟨762123378638,762123397968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9920,-5504⟩ : DyadicInterval 40),(⟨762123386368,762123407840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨202884831297,203138034008⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186191179200,186191179264⟩ : DyadicInterval 40),(⟨-224280215168,-224280215104⟩ : DyadicInterval 40),(⟨743297260837,743297280166⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186404917696,186404917760⟩ : DyadicInterval 40),(⟨-224590755392,-224590755328⟩ : DyadicInterval 40),(⟨743249967661,743249986991⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38185837632,-38089035904⟩ : DyadicInterval 40),(⟨781167901568,781216321696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨186276861952,186469229824⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-224684223168,-224404685632⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e850_ok : ecellOkT e850 = true := by decide +kernel
theorem e850_pos {a z : ℝ} (ha1 : ((756183/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((94629/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e850 e850_ok ha1 ha2 hz1 hz2 hz

-- box ['377667/2048000', '756183/4096000', '3997/4000', '1999/2000']  interval_lower 97980421/549755813888
noncomputable def e851 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1302270054498,0,true,186084460480,186084460544⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨896753201054,0,false,-224125219264,-224125219200⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1302497956201,0,true,186276861952,186276862016⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨896525299351,0,false,-224404685696,-224404685632⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1302117985677,0,true,185956060736,185956060800⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨896905269875,0,false,-223938783040,-223938782976⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1302396463037,0,true,186191182528,186191182592⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨896626792515,0,false,-224280220032,-224280219968⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099563598342,0,true,51969280,51969344⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459657210,0,false,-51971840,-51971776⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589676855,0,true,78046272,78046336⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433578697,0,false,-78051904,-78051840⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622235,0,false,-5568,-5504⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625320,0,false,-2496,-2432⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1302194015578,0,true,186020258688,186020258752⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨896829239974,0,false,-224031991680,-224031991616⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1302447218440,0,true,186234030528,186234030592⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨896576037112,0,false,-224342461952,-224342461888⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1062056040297,0,false,-38108431360,-38108431296⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1062149448708,0,false,-38011732992,-38011732928⟩
    { al := (377667/2048000), au := (756183/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨202758426722,202986328425⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186084460480,186084460544⟩ : DyadicInterval 40),(⟨-224125219264,-224125219200⟩ : DyadicInterval 40),(⟨743320848119,743320867449⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186276861952,186276862016⟩ : DyadicInterval 40),(⟨-224404685696,-224404685632⟩ : DyadicInterval 40),(⟨743278310469,743278329798⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185956060736,185956060800⟩ : DyadicInterval 40),(⟨-223938783040,-223938782976⟩ : DyadicInterval 40),(⟨743349204384,743349223714⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186191182528,186191182592⟩ : DyadicInterval 40),(⟨-224280220032,-224280219968⟩ : DyadicInterval 40),(⟨743297260109,743297279439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨51970566,78049079⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨51969280,51969344⟩ : DyadicInterval 40),(⟨-51971840,-51971776⟩ : DyadicInterval 40),(⟨762123382375,762123401704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78046272,78046336⟩ : DyadicInterval 40),(⟨-78051904,-78051840⟩ : DyadicInterval 40),(⟨762123380827,762123400156⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5568,-2432⟩ : DyadicInterval 40),(⟨762123384832,762123405664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨202682387802,202935590664⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186020258688,186020258752⟩ : DyadicInterval 40),(⟨-224031991680,-224031991616⟩ : DyadicInterval 40),(⟨743335029810,743335049139⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186234030528,186234030592⟩ : DyadicInterval 40),(⟨-224342461952,-224342461888⟩ : DyadicInterval 40),(⟨743287784863,743287804192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38108431360,-38011732928⟩ : DyadicInterval 40),(⟨781129250080,781177618560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨186084460480,186276862016⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-224404685696,-224125219200⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e851_ok : ecellOkT e851 = true := by decide +kernel
theorem e851_pos {a z : ℝ} (ha1 : ((377667/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((756183/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e851 e851_ok ha1 ha2 hz1 hz2 hz

-- box ['756183/4096000', '94629/512000', '3997/4000', '1999/2000']  interval_lower 199412073/1099511627776
noncomputable def e852 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1302497956200,0,true,186276861952,186276862016⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨896525299352,0,false,-224404685696,-224404685632⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1302725857903,0,true,186469229760,186469229824⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨896297397649,0,false,-224684223168,-224684223104⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1302345716453,0,true,186148340352,186148340416⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨896677539099,0,false,-224217992512,-224217992448⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1302624250789,0,true,186383469120,186383469184⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨896399004763,0,false,-224559586112,-224559586048⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099563659733,0,true,52030720,52030784⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459595819,0,false,-52033216,-52033152⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589768958,0,true,78138368,78138432⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433486594,0,false,-78144000,-78143936⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622222,0,false,-5568,-5504⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625314,0,false,-2496,-2432⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1302421831815,0,true,186212599232,186212599296⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨896601423737,0,false,-224311329600,-224311329536⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1302675063170,0,true,186426357696,186426357760⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨896348192382,0,false,-224621913728,-224621913664⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1061971887005,0,false,-38195555968,-38195555904⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1062065410872,0,false,-38098730368,-38098730304⟩
    { al := (756183/4096000), au := (94629/512000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨202986328424,203214230127⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186276861952,186276862016⟩ : DyadicInterval 40),(⟨-224404685696,-224404685632⟩ : DyadicInterval 40),(⟨743278310469,743278329798⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186469229760,186469229824⟩ : DyadicInterval 40),(⟨-224684223168,-224684223104⟩ : DyadicInterval 40),(⟨743235723910,743235743240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186148340352,186148340416⟩ : DyadicInterval 40),(⟨-224217992512,-224217992448⟩ : DyadicInterval 40),(⟨743306731280,743306750610⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186383469120,186383469184⟩ : DyadicInterval 40),(⟨-224559586112,-224559586048⟩ : DyadicInterval 40),(⟨743254716648,743254735978⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨52031957,78141182⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52030720,52030784⟩ : DyadicInterval 40),(⟨-52033216,-52033152⟩ : DyadicInterval 40),(⟨762123382337,762123401666⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78138368,78138432⟩ : DyadicInterval 40),(⟨-78144000,-78143936⟩ : DyadicInterval 40),(⟨762123380814,762123400143⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5568,-2432⟩ : DyadicInterval 40),(⟨762123384832,762123405664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨202910204039,203163435394⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186212599232,186212599296⟩ : DyadicInterval 40),(⟨-224311329600,-224311329536⟩ : DyadicInterval 40),(⟨743292524435,743292543764⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186426357696,186426357760⟩ : DyadicInterval 40),(⟨-224621913728,-224621913664⟩ : DyadicInterval 40),(⟨743245219874,743245239203⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38195555968,-38098730304⟩ : DyadicInterval 40),(⟨781172748768,781221180864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨186276861952,186469229824⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-224684223168,-224404685632⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e852_ok : ecellOkT e852 = true := by decide +kernel
theorem e852_pos {a z : ℝ} (ha1 : ((756183/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((94629/512000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e852 e852_ok ha1 ha2 hz1 hz2 hz

-- box ['188409/1024000', '150897/819200', '1999/2000', '3999/4000']  interval_lower 94228529/549755813888
noncomputable def e853 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1301814251094,0,true,185699556544,185699556608⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨897209004458,0,false,-223566499392,-223566499328⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1302042152797,0,true,185892025408,185892025472⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨896981102755,0,false,-223845823872,-223845823808⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1301713099782,0,true,185614120896,185614120960⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨897310155770,0,false,-223442547520,-223442547456⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1301991520166,0,true,185849267712,185849267776⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨897031735386,0,false,-223783760576,-223783760512⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537551719,0,true,25923584,25923648⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485703833,0,false,-25924288,-25924224⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099563538137,0,true,51909120,51909184⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459717415,0,false,-51911616,-51911552⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625325,0,false,-2496,-2432⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627165,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1301763670540,0,true,185656835456,185656835520⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨897259585012,0,false,-223504515712,-223504515648⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1302016845063,0,true,185870654016,185870654080⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨897006410489,0,false,-223814802304,-223814802240⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1062214738873,0,false,-37944148224,-37944148160⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1062307938640,0,false,-37847680256,-37847680192⟩
    { al := (188409/1024000), au := (150897/819200), zl := (1999/2000), zu := (3999/4000),
      A := ⟨202302623318,202530525021⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185699556544,185699556608⟩ : DyadicInterval 40),(⟨-223566499392,-223566499328⟩ : DyadicInterval 40),(⟨743405776688,743405796017⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185892025408,185892025472⟩ : DyadicInterval 40),(⟨-223845823872,-223845823808⟩ : DyadicInterval 40),(⟨743363336834,743363356163⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185614120896,185614120960⟩ : DyadicInterval 40),(⟨-223442547520,-223442547456⟩ : DyadicInterval 40),(⟨743424597420,743424616749⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185849267712,185849267776⟩ : DyadicInterval 40),(⟨-223783760576,-223783760512⟩ : DyadicInterval 40),(⟨743372769893,743372789223⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨25923943,51910361⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25923584,25923648⟩ : DyadicInterval 40),(⟨-25924288,-25924224⟩ : DyadicInterval 40),(⟨762123383292,762123402621⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨51909120,51909184⟩ : DyadicInterval 40),(⟨-51911616,-51911552⟩ : DyadicInterval 40),(⟨762123382349,762123401678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2496,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨202252042764,202505217287⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185656835456,185656835520⟩ : DyadicInterval 40),(⟨-223504515712,-223504515648⟩ : DyadicInterval 40),(⟨743415189146,743415208475⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185870654016,185870654080⟩ : DyadicInterval 40),(⟨-223814802304,-223814802240⟩ : DyadicInterval 40),(⟨743368052066,743368071395⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37944148224,-37847680192⟩ : DyadicInterval 40),(⟨781047223712,781095476992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨185699556544,185892025472⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-223845823872,-223566499328⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e853_ok : ecellOkT e853 = true := by decide +kernel
theorem e853_pos {a z : ℝ} (ha1 : ((188409/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((150897/819200 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e853 e853_ok ha1 ha2 hz1 hz2 hz

-- box ['150897/819200', '377667/2048000', '1999/2000', '3999/4000']  interval_lower 95937265/549755813888
noncomputable def e854 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1302042152796,0,true,185892025408,185892025472⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨896981102756,0,false,-223845823872,-223845823808⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1302270054499,0,true,186084460480,186084460544⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨896753201053,0,false,-224125219264,-224125219200⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1301940887533,0,true,185806508416,185806508480⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨897082368019,0,false,-223721700800,-223721700736⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1302219364893,0,true,186041662272,186041662336⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨896803890659,0,false,-224063070336,-224063070272⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537582405,0,true,25954304,25954368⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485673147,0,false,-25954944,-25954880⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099563599519,0,true,51970496,51970560⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459656033,0,false,-51972992,-51972928⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625319,0,false,-2496,-2432⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627164,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1301991515263,0,true,185849263616,185849263680⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨897031740289,0,false,-223783754560,-223783754496⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1302244718282,0,true,186063068800,186063068864⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨896778537270,0,false,-224094154880,-224094154816⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1062130753442,0,false,-38031086016,-38031085952⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1062224068645,0,false,-37934490944,-37934490880⟩
    { al := (150897/819200), au := (377667/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨202530525020,202758426723⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185892025408,185892025472⟩ : DyadicInterval 40),(⟨-223845823872,-223845823808⟩ : DyadicInterval 40),(⟨743363336834,743363356164⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186084460480,186084460544⟩ : DyadicInterval 40),(⟨-224125219264,-224125219200⟩ : DyadicInterval 40),(⟨743320848119,743320867448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185806508416,185806508480⟩ : DyadicInterval 40),(⟨-223721700800,-223721700736⟩ : DyadicInterval 40),(⟨743382200510,743382219839⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186041662272,186041662336⟩ : DyadicInterval 40),(⟨-224063070336,-224063070272⟩ : DyadicInterval 40),(⟨743330302599,743330321928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨25954629,51971743⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25954304,25954368⟩ : DyadicInterval 40),(⟨-25954944,-25954880⟩ : DyadicInterval 40),(⟨762123383259,762123402588⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨51970496,51970560⟩ : DyadicInterval 40),(⟨-51972992,-51972928⟩ : DyadicInterval 40),(⟨762123382343,762123401672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2496,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨202479887487,202733090506⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185849263616,185849263680⟩ : DyadicInterval 40),(⟨-223783754560,-223783754496⟩ : DyadicInterval 40),(⟨743372770778,743372790107⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186063068800,186063068864⟩ : DyadicInterval 40),(⟨-224094154880,-224094154816⟩ : DyadicInterval 40),(⟨743325574077,743325593406⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38031086016,-37934490880⟩ : DyadicInterval 40),(⟨781090629056,781138945888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨185892025408,186084460544⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-224125219264,-223845823808⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e854_ok : ecellOkT e854 = true := by decide +kernel
theorem e854_pos {a z : ℝ} (ha1 : ((150897/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((377667/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e854 e854_ok ha1 ha2 hz1 hz2 hz

-- box ['188409/1024000', '150897/819200', '3999/4000', '1']  interval_lower 183407/1073741824
noncomputable def e855 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1301814251094,0,true,185699556544,185699556608⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨897209004458,0,false,-223566499392,-223566499328⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1302042152797,0,true,185892025408,185892025472⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨896981102755,0,false,-223845823872,-223845823808⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1301763675438,0,true,185656839552,185656839616⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨897259580114,0,false,-223504521728,-223504521664⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537583250,0,true,25955136,25955200⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485672302,0,false,-25955840,-25955776⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627163,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1301788958133,0,true,185678193920,185678193984⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨897234297419,0,false,-223535503808,-223535503744⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1302042161304,0,true,185892032576,185892032640⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨896981094248,0,false,-223845834304,-223845834240⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1062205412930,0,false,-37953801664,-37953801600⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1062298634896,0,false,-37857309888,-37857309824⟩
    { al := (188409/1024000), au := (150897/819200), zl := (3999/4000), zu := 1,
      A := ⟨202302623318,202530525021⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185699556544,185699556608⟩ : DyadicInterval 40),(⟨-223566499392,-223566499328⟩ : DyadicInterval 40),(⟨743405776688,743405796017⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185892025408,185892025472⟩ : DyadicInterval 40),(⟨-223845823872,-223845823808⟩ : DyadicInterval 40),(⟨743363336834,743363356163⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185656839552,185656839616⟩ : DyadicInterval 40),(⟨-223504521728,-223504521664⟩ : DyadicInterval 40),(⟨743415188264,743415207594⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185892025408,185892025472⟩ : DyadicInterval 40),(⟨-223845823872,-223845823808⟩ : DyadicInterval 40),(⟨743363336834,743363356163⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,25955474⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25955136,25955200⟩ : DyadicInterval 40),(⟨-25955840,-25955776⟩ : DyadicInterval 40),(⟨762123383291,762123402620⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨202277330357,202530533528⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185678193920,185678193984⟩ : DyadicInterval 40),(⟨-223535503808,-223535503744⟩ : DyadicInterval 40),(⟨743410483722,743410503051⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185892032576,185892032640⟩ : DyadicInterval 40),(⟨-223845834304,-223845834240⟩ : DyadicInterval 40),(⟨743363335260,743363354590⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37953801664,-37857309824⟩ : DyadicInterval 40),(⟨781052038528,781100303712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨185699556544,185892025472⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-223845823872,-223566499328⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e855_ok : ecellOkT e855 = true := by decide +kernel
theorem e855_pos {a z : ℝ} (ha1 : ((188409/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((150897/819200 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e855 e855_ok ha1 ha2 hz1 hz2 hz

-- box ['150897/819200', '377667/2048000', '3999/4000', '1']  interval_lower 95611799/549755813888
noncomputable def e856 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1302042152796,0,true,185892025408,185892025472⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨896981102756,0,false,-223845823872,-223845823808⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1302270054499,0,true,186084460480,186084460544⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨896753201053,0,false,-224125219264,-224125219200⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1301991520164,0,true,185849267712,185849267776⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨897031735388,0,false,-223783760576,-223783760512⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537613941,0,true,25985856,25985920⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485641611,0,false,-25986496,-25986432⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627161,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1302016831344,0,true,185870642432,185870642496⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨897006424208,0,false,-223814785472,-223814785408⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1302270063001,0,true,186084467712,186084467776⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨896753192551,0,false,-224125229696,-224125229632⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1062121406502,0,false,-38040761984,-38040761920⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1062214743927,0,false,-37944143040,-37944142976⟩
    { al := (150897/819200), au := (377667/2048000), zl := (3999/4000), zu := 1,
      A := ⟨202530525020,202758426723⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185892025408,185892025472⟩ : DyadicInterval 40),(⟨-223845823872,-223845823808⟩ : DyadicInterval 40),(⟨743363336834,743363356164⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186084460480,186084460544⟩ : DyadicInterval 40),(⟨-224125219264,-224125219200⟩ : DyadicInterval 40),(⟨743320848119,743320867448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185849267712,185849267776⟩ : DyadicInterval 40),(⟨-223783760576,-223783760512⟩ : DyadicInterval 40),(⟨743372769894,743372789223⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186084460480,186084460544⟩ : DyadicInterval 40),(⟨-224125219264,-224125219200⟩ : DyadicInterval 40),(⟨743320848119,743320867448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,25986165⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25985856,25985920⟩ : DyadicInterval 40),(⟨-25986496,-25986432⟩ : DyadicInterval 40),(⟨762123383257,762123402586⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨202505203568,202758435225⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185870642432,185870642496⟩ : DyadicInterval 40),(⟨-223814785472,-223814785408⟩ : DyadicInterval 40),(⟨743368054614,743368073944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186084467712,186084467776⟩ : DyadicInterval 40),(⟨-224125229696,-224125229632⟩ : DyadicInterval 40),(⟨743320846504,743320865834⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38040761984,-37944142976⟩ : DyadicInterval 40),(⟨781095455104,781143783872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨185892025408,186084460544⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-224125219264,-223845823808⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e856_ok : ecellOkT e856 = true := by decide +kernel
theorem e856_pos {a z : ℝ} (ha1 : ((150897/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((377667/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e856 e856_ok ha1 ha2 hz1 hz2 hz

-- box ['377667/2048000', '756183/4096000', '1999/2000', '3999/4000']  interval_lower 195307559/1099511627776
noncomputable def e857 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1302270054498,0,true,186084460480,186084460544⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨896753201054,0,false,-224125219264,-224125219200⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1302497956201,0,true,186276861952,186276862016⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨896525299351,0,false,-224404685696,-224404685632⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1302168675284,0,true,185998862336,185998862400⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨896854580268,0,false,-224000924928,-224000924864⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1302447209620,0,true,186234023104,186234023168⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨896576045932,0,false,-224342451136,-224342451072⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537613096,0,true,25984960,25985024⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485642456,0,false,-25985664,-25985600⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099563660912,0,true,52031872,52031936⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459594640,0,false,-52034368,-52034304⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625313,0,false,-2496,-2432⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627162,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1302219359989,0,true,186041658112,186041658176⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨896803895563,0,false,-224063064320,-224063064256⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1302472591496,0,true,186255449984,186255450048⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨896550664056,0,false,-224373578496,-224373578432⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1062046673560,0,false,-38118128512,-38118128448⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1062140104219,0,false,-38021406208,-38021406144⟩
    { al := (377667/2048000), au := (756183/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨202758426722,202986328425⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186084460480,186084460544⟩ : DyadicInterval 40),(⟨-224125219264,-224125219200⟩ : DyadicInterval 40),(⟨743320848119,743320867449⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186276861952,186276862016⟩ : DyadicInterval 40),(⟨-224404685696,-224404685632⟩ : DyadicInterval 40),(⟨743278310469,743278329798⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185998862336,185998862400⟩ : DyadicInterval 40),(⟨-224000924928,-224000924864⟩ : DyadicInterval 40),(⟨743339754701,743339774030⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186234023104,186234023168⟩ : DyadicInterval 40),(⟨-224342451136,-224342451072⟩ : DyadicInterval 40),(⟨743287786497,743287805827⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨25985320,52033136⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25984960,25985024⟩ : DyadicInterval 40),(⟨-25985664,-25985600⟩ : DyadicInterval 40),(⟨762123383289,762123402618⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52031872,52031936⟩ : DyadicInterval 40),(⟨-52034368,-52034304⟩ : DyadicInterval 40),(⟨762123382337,762123401666⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2496,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨202707732213,202960963720⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186041658112,186041658176⟩ : DyadicInterval 40),(⟨-224063064320,-224063064256⟩ : DyadicInterval 40),(⟨743330303524,743330322853⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186255449984,186255450048⟩ : DyadicInterval 40),(⟨-224373578496,-224373578432⟩ : DyadicInterval 40),(⟨743283047180,743283066509⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38118128512,-38021406144⟩ : DyadicInterval 40),(⟨781134086688,781182467136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨186084460480,186276862016⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-224404685696,-224125219200⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e857_ok : ecellOkT e857 = true := by decide +kernel
theorem e857_pos {a z : ℝ} (ha1 : ((377667/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((756183/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e857 e857_ok ha1 ha2 hz1 hz2 hz

-- box ['756183/4096000', '94629/512000', '1999/2000', '3999/4000']  interval_lower 198756229/1099511627776
noncomputable def e858 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1302497956200,0,true,186276861952,186276862016⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨896525299352,0,false,-224404685696,-224404685632⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1302725857903,0,true,186469229760,186469229824⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨896297397649,0,false,-224684223168,-224684223104⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1302396463035,0,true,186191182528,186191182592⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨896626792517,0,false,-224280220032,-224280219968⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1302675054346,0,true,186426350272,186426350336⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨896348201206,0,false,-224621902912,-224621902848⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537643791,0,true,26015680,26015744⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485611761,0,false,-26016384,-26016320⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099563722316,0,true,52093248,52093312⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459533236,0,false,-52095808,-52095744⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625307,0,false,-2496,-2432⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627161,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1302447204710,0,true,186234018944,186234019008⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨896576050842,0,false,-224342445120,-224342445056⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1302700464711,0,true,186447797440,186447797504⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨896322790841,0,false,-224653073152,-224653073088⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1061962499224,0,false,-38205275648,-38205275584⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1062056045366,0,false,-38108426112,-38108426048⟩
    { al := (756183/4096000), au := (94629/512000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨202986328424,203214230127⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186276861952,186276862016⟩ : DyadicInterval 40),(⟨-224404685696,-224404685632⟩ : DyadicInterval 40),(⟨743278310469,743278329798⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186469229760,186469229824⟩ : DyadicInterval 40),(⟨-224684223168,-224684223104⟩ : DyadicInterval 40),(⟨743235723910,743235743240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186191182528,186191182592⟩ : DyadicInterval 40),(⟨-224280220032,-224280219968⟩ : DyadicInterval 40),(⟨743297260109,743297279439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186426350272,186426350336⟩ : DyadicInterval 40),(⟨-224621902912,-224621902848⟩ : DyadicInterval 40),(⟨743245221512,743245240842⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨26016015,52094540⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26015680,26015744⟩ : DyadicInterval 40),(⟨-26016384,-26016320⟩ : DyadicInterval 40),(⟨762123383288,762123402617⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52093248,52093312⟩ : DyadicInterval 40),(⟨-52095808,-52095744⟩ : DyadicInterval 40),(⟨762123382363,762123401692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2496,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨202935576934,203188836935⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186234018944,186234019008⟩ : DyadicInterval 40),(⟨-224342445120,-224342445056⟩ : DyadicInterval 40),(⟨743287787425,743287806755⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186447797440,186447797504⟩ : DyadicInterval 40),(⟨-224653073152,-224653073088⟩ : DyadicInterval 40),(⟨743240471437,743240490767⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38205275648,-38108426048⟩ : DyadicInterval 40),(⟨781177596640,781226040704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨186276861952,186469229824⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-224684223168,-224404685632⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e858_ok : ecellOkT e858 = true := by decide +kernel
theorem e858_pos {a z : ℝ} (ha1 : ((756183/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((94629/512000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e858 e858_ok ha1 ha2 hz1 hz2 hz

-- box ['377667/2048000', '756183/4096000', '3999/4000', '1']  interval_lower 194654027/1099511627776
noncomputable def e859 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1302270054498,0,true,186084460480,186084460544⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨896753201054,0,false,-224125219264,-224125219200⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1302497956201,0,true,186276861952,186276862016⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨896525299351,0,false,-224404685696,-224404685632⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1302219364891,0,true,186041662208,186041662272⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨896803890661,0,false,-224063070336,-224063070272⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537644639,0,true,26016512,26016576⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485610913,0,false,-26017216,-26017152⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627160,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1302244704552,0,true,186063057216,186063057280⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨896778551000,0,false,-224094138048,-224094137984⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1302497964706,0,true,186276869120,186276869184⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨896525290846,0,false,-224404696128,-224404696064⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1062037305595,0,false,-38127826944,-38127826880⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1062130758506,0,false,-38031080768,-38031080704⟩
    { al := (377667/2048000), au := (756183/4096000), zl := (3999/4000), zu := 1,
      A := ⟨202758426722,202986328425⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186084460480,186084460544⟩ : DyadicInterval 40),(⟨-224125219264,-224125219200⟩ : DyadicInterval 40),(⟨743320848119,743320867449⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186276861952,186276862016⟩ : DyadicInterval 40),(⟨-224404685696,-224404685632⟩ : DyadicInterval 40),(⟨743278310469,743278329798⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186041662208,186041662272⟩ : DyadicInterval 40),(⟨-224063070336,-224063070272⟩ : DyadicInterval 40),(⟨743330302638,743330321967⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186276861952,186276862016⟩ : DyadicInterval 40),(⟨-224404685696,-224404685632⟩ : DyadicInterval 40),(⟨743278310469,743278329798⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,26016863⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26016512,26016576⟩ : DyadicInterval 40),(⟨-26017216,-26017152⟩ : DyadicInterval 40),(⟨762123383288,762123402617⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨202733076776,202986336930⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186063057216,186063057280⟩ : DyadicInterval 40),(⟨-224094138048,-224094137984⟩ : DyadicInterval 40),(⟨743325576633,743325595963⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186276869120,186276869184⟩ : DyadicInterval 40),(⟨-224404696128,-224404696064⟩ : DyadicInterval 40),(⟨743278308888,743278328217⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38127826944,-38031080704⟩ : DyadicInterval 40),(⟨781138923968,781187316352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨186084460480,186276862016⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-224404685696,-224125219200⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e859_ok : ecellOkT e859 = true := by decide +kernel
theorem e859_pos {a z : ℝ} (ha1 : ((377667/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((756183/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e859 e859_ok ha1 ha2 hz1 hz2 hz

-- box ['756183/4096000', '94629/512000', '3999/4000', '1']  interval_lower 99050119/549755813888
noncomputable def e860 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1302497956200,0,true,186276861952,186276862016⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨896525299352,0,false,-224404685696,-224404685632⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1302725857903,0,true,186469229760,186469229824⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨896297397649,0,false,-224684223168,-224684223104⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1302447209617,0,true,186234023104,186234023168⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨896576045935,0,false,-224342451136,-224342451072⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537675341,0,true,26047232,26047296⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485580211,0,false,-26047936,-26047872⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627158,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1302472577765,0,true,186255438400,186255438464⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨896550677787,0,false,-224373561664,-224373561600⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1302725866413,0,true,186469236928,186469236992⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨896297389139,0,false,-224684233600,-224684233536⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1061953110210,0,false,-38214996672,-38214996608⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1062046678630,0,false,-38118123264,-38118123200⟩
    { al := (756183/4096000), au := (94629/512000), zl := (3999/4000), zu := 1,
      A := ⟨202986328424,203214230127⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186276861952,186276862016⟩ : DyadicInterval 40),(⟨-224404685696,-224404685632⟩ : DyadicInterval 40),(⟨743278310469,743278329798⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186469229760,186469229824⟩ : DyadicInterval 40),(⟨-224684223168,-224684223104⟩ : DyadicInterval 40),(⟨743235723910,743235743240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186234023104,186234023168⟩ : DyadicInterval 40),(⟨-224342451136,-224342451072⟩ : DyadicInterval 40),(⟨743287786498,743287805827⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186469229760,186469229824⟩ : DyadicInterval 40),(⟨-224684223168,-224684223104⟩ : DyadicInterval 40),(⟨743235723910,743235743240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,26047565⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26047232,26047296⟩ : DyadicInterval 40),(⟨-26047936,-26047872⟩ : DyadicInterval 40),(⟨762123383286,762123402615⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨202960949989,203214238637⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186255438400,186255438464⟩ : DyadicInterval 40),(⟨-224373561664,-224373561600⟩ : DyadicInterval 40),(⟨743283049742,743283069072⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186469236928,186469236992⟩ : DyadicInterval 40),(⟨-224684233600,-224684233536⟩ : DyadicInterval 40),(⟨743235722325,743235741654⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38214996672,-38118123200⟩ : DyadicInterval 40),(⟨781182445216,781230901216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨186276861952,186469229824⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-224684223168,-224404685632⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e860_ok : ecellOkT e860 = true := by decide +kernel
theorem e860_pos {a z : ℝ} (ha1 : ((756183/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((94629/512000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e860 e860_ok ha1 ha2 hz1 hz2 hz

-- box ['94629/512000', '757881/4096000', '999/1000', '3997/4000']  interval_lower 203536449/1099511627776
noncomputable def e861 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1302725857902,0,true,186469229760,186469229824⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨896297397650,0,false,-224684223168,-224684223104⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1302953759605,0,true,186661563904,186661563968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨896069495947,0,false,-224963831744,-224963831680⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1302522643671,0,true,186297701824,186297701888⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨896500611881,0,false,-224434963200,-224434963136⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1302801178007,0,true,186532798720,186532798784⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨896222077545,0,false,-224776624192,-224776624128⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589767443,0,true,78136832,78136896⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433488109,0,false,-78142464,-78142400⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099615938090,0,true,104305344,104305408⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099407317462,0,false,-104315264,-104315200⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511617880,0,false,-9920,-9856⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622223,0,false,-5568,-5504⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1302624246825,0,true,186383465792,186383465856⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨896399008727,0,false,-224559581248,-224559581184⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1302877478030,0,true,186597190976,186597191040⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨896145777522,0,false,-224870235328,-224870235264⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1061897046897,0,false,-38273044352,-38273044288⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1061990663946,0,false,-38176115456,-38176115392⟩
    { al := (94629/512000), au := (757881/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨203214230126,203442131829⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186469229760,186469229824⟩ : DyadicInterval 40),(⟨-224684223168,-224684223104⟩ : DyadicInterval 40),(⟨743235723910,743235743240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186661563904,186661563968⟩ : DyadicInterval 40),(⟨-224963831744,-224963831680⟩ : DyadicInterval 40),(⟨743193088458,743193107787⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186297701824,186297701888⟩ : DyadicInterval 40),(⟨-224434963200,-224434963136⟩ : DyadicInterval 40),(⟨743273699652,743273718982⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186532798720,186532798784⟩ : DyadicInterval 40),(⟨-224776624192,-224776624128⟩ : DyadicInterval 40),(⟨743221638567,743221657896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨78139667,104310314⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78136832,78136896⟩ : DyadicInterval 40),(⟨-78142464,-78142400⟩ : DyadicInterval 40),(⟨762123380814,762123400144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨104305344,104305408⟩ : DyadicInterval 40),(⟨-104315264,-104315200⟩ : DyadicInterval 40),(⟨762123378615,762123397945⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9920,-5504⟩ : DyadicInterval 40),(⟨762123386368,762123407840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨203112619049,203365850254⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186383465792,186383465856⟩ : DyadicInterval 40),(⟨-224559581248,-224559581184⟩ : DyadicInterval 40),(⟨743254717378,743254736707⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186597190976,186597191040⟩ : DyadicInterval 40),(⟨-224870235328,-224870235264⟩ : DyadicInterval 40),(⟨743207364541,743207383870⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38273044352,-38176115392⟩ : DyadicInterval 40),(⟨781211441312,781259925056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨186469229760,186661563968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-224963831744,-224684223104⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e861_ok : ecellOkT e861 = true := by decide +kernel
theorem e861_pos {a z : ℝ} (ha1 : ((94629/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((757881/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e861 e861_ok ha1 ha2 hz1 hz2 hz

-- box ['757881/4096000', '75873/409600', '999/1000', '3997/4000']  interval_lower 103510885/549755813888
noncomputable def e862 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1302953759604,0,true,186661563904,186661563968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨896069495948,0,false,-224963831744,-224963831680⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1303181661307,0,true,186853864384,186853864448⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨895841594245,0,false,-225243511424,-225243511360⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1302750317472,0,true,186489873600,186489873664⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨896272938080,0,false,-224714228800,-224714228736⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1303028908783,0,true,186724977472,186724977536⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨895994346769,0,false,-225056046528,-225056046464⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589859559,0,true,78228992,78229056⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433395993,0,false,-78234624,-78234560⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099616060935,0,true,104428160,104428224⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099407194617,0,false,-104438144,-104438080⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511617856,0,false,-9984,-9920⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622210,0,false,-5568,-5504⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1302852034575,0,true,186575718784,186575718848⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨896171220977,0,false,-224839018304,-224839018240⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1303105294267,0,true,186789430592,186789430656⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨895917961285,0,false,-225149786304,-225149786240⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1061812725837,0,false,-38360355648,-38360355584⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1061906458361,0,false,-38263299520,-38263299456⟩
    { al := (757881/4096000), au := (75873/409600), zl := (999/1000), zu := (3997/4000),
      A := ⟨203442131828,203670033531⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186661563904,186661563968⟩ : DyadicInterval 40),(⟨-224963831744,-224963831680⟩ : DyadicInterval 40),(⟨743193088458,743193107787⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186853864384,186853864448⟩ : DyadicInterval 40),(⟨-225243511424,-225243511360⟩ : DyadicInterval 40),(⟨743150404099,743150423429⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186489873600,186489873664⟩ : DyadicInterval 40),(⟨-224714228800,-224714228736⟩ : DyadicInterval 40),(⟨743231150439,743231169769⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186724977472,186724977536⟩ : DyadicInterval 40),(⟨-225056046528,-225056046464⟩ : DyadicInterval 40),(⟨743179018985,743179038315⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨78231783,104433159⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78228992,78229056⟩ : DyadicInterval 40),(⟨-78234624,-78234560⟩ : DyadicInterval 40),(⟨762123380801,762123400130⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨104428160,104428224⟩ : DyadicInterval 40),(⟨-104438144,-104438080⟩ : DyadicInterval 40),(⟨762123378624,762123397954⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9984,-5504⟩ : DyadicInterval 40),(⟨762123386368,762123407872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨203340406799,203593666491⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186575718784,186575718848⟩ : DyadicInterval 40),(⟨-224839018304,-224839018240⟩ : DyadicInterval 40),(⟨743212125038,743212144367⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186789430592,186789430656⟩ : DyadicInterval 40),(⟨-225149786304,-225149786240⟩ : DyadicInterval 40),(⟨743164712567,743164731897⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38360355648,-38263299456⟩ : DyadicInterval 40),(⟨781255033344,781303580704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨186661563904,186853864448⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-225243511424,-224963831680⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e862_ok : ecellOkT e862 = true := by decide +kernel
theorem e862_pos {a z : ℝ} (ha1 : ((757881/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((75873/409600 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e862 e862_ok ha1 ha2 hz1 hz2 hz

-- box ['94629/512000', '757881/4096000', '3997/4000', '1999/2000']  interval_lower 202878967/1099511627776
noncomputable def e863 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1302725857902,0,true,186469229760,186469229824⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨896297397650,0,false,-224684223168,-224684223104⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1302953759605,0,true,186661563904,186661563968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨896069495947,0,false,-224963831744,-224963831680⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1302573447229,0,true,186340586304,186340586368⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨896449808323,0,false,-224497272896,-224497272832⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1302852038540,0,true,186575722112,186575722176⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨896171217012,0,false,-224839023168,-224839023104⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099563721134,0,true,52092096,52092160⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459534418,0,false,-52094656,-52094592⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589861077,0,true,78230464,78230528⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433394475,0,false,-78236096,-78236032⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622209,0,false,-5568,-5504⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625308,0,false,-2496,-2432⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1302649648050,0,true,186404906112,186404906176⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨896373607502,0,false,-224590738496,-224590738432⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1302902907900,0,true,186618651264,186618651328⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨896120347652,0,false,-224901436544,-224901436480⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1061887639283,0,false,-38282785216,-38282785152⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1061981278630,0,false,-38185832384,-38185832320⟩
    { al := (94629/512000), au := (757881/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨203214230126,203442131829⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186469229760,186469229824⟩ : DyadicInterval 40),(⟨-224684223168,-224684223104⟩ : DyadicInterval 40),(⟨743235723910,743235743240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186661563904,186661563968⟩ : DyadicInterval 40),(⟨-224963831744,-224963831680⟩ : DyadicInterval 40),(⟨743193088458,743193107787⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186340586304,186340586368⟩ : DyadicInterval 40),(⟨-224497272896,-224497272832⟩ : DyadicInterval 40),(⟨743264209370,743264228700⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186575722112,186575722176⟩ : DyadicInterval 40),(⟨-224839023168,-224839023104⟩ : DyadicInterval 40),(⟨743212124307,743212143636⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨52093358,78233301⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52092096,52092160⟩ : DyadicInterval 40),(⟨-52094656,-52094592⟩ : DyadicInterval 40),(⟨762123382363,762123401692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78230464,78230528⟩ : DyadicInterval 40),(⟨-78236096,-78236032⟩ : DyadicInterval 40),(⟨762123380801,762123400130⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5568,-2432⟩ : DyadicInterval 40),(⟨762123384832,762123405664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨203138020274,203391280124⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186404906112,186404906176⟩ : DyadicInterval 40),(⟨-224590738496,-224590738432⟩ : DyadicInterval 40),(⟨743249970203,743249989532⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186618651264,186618651328⟩ : DyadicInterval 40),(⟨-224901436544,-224901436480⟩ : DyadicInterval 40),(⟨743202605978,743202625308⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38282785216,-38185832320⟩ : DyadicInterval 40),(⟨781216299776,781264795488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨186469229760,186661563968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-224963831744,-224684223104⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e863_ok : ecellOkT e863 = true := by decide +kernel
theorem e863_pos {a z : ℝ} (ha1 : ((94629/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((757881/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e863 e863_ok ha1 ha2 hz1 hz2 hz

-- box ['757881/4096000', '75873/409600', '3997/4000', '1999/2000']  interval_lower 206361385/1099511627776
noncomputable def e864 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1302953759604,0,true,186661563904,186661563968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨896069495948,0,false,-224963831744,-224963831680⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1303181661307,0,true,186853864384,186853864448⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨895841594245,0,false,-225243511424,-225243511360⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1302801178005,0,true,186532798720,186532798784⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨896222077547,0,false,-224776624192,-224776624128⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1303079826291,0,true,186767941504,186767941568⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨895943429261,0,false,-225118531264,-225118531200⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099563782546,0,true,52153472,52153536⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459473006,0,false,-52156032,-52155968⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589953212,0,true,78322624,78322688⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433302340,0,false,-78328256,-78328192⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622196,0,false,-5632,-5568⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625303,0,false,-2496,-2432⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1302877464291,0,true,186597179392,186597179456⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨896145791261,0,false,-224870218496,-224870218432⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1303130752629,0,true,186810911232,186810911296⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨895892502923,0,false,-225181030464,-225181030400⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1061803297133,0,false,-38370119168,-38370119104⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1061897051981,0,false,-38273039040,-38273038976⟩
    { al := (757881/4096000), au := (75873/409600), zl := (3997/4000), zu := (1999/2000),
      A := ⟨203442131828,203670033531⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186661563904,186661563968⟩ : DyadicInterval 40),(⟨-224963831744,-224963831680⟩ : DyadicInterval 40),(⟨743193088458,743193107787⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186853864384,186853864448⟩ : DyadicInterval 40),(⟨-225243511424,-225243511360⟩ : DyadicInterval 40),(⟨743150404099,743150423429⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186532798720,186532798784⟩ : DyadicInterval 40),(⟨-224776624192,-224776624128⟩ : DyadicInterval 40),(⟨743221638567,743221657896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186767941504,186767941568⟩ : DyadicInterval 40),(⟨-225118531264,-225118531200⟩ : DyadicInterval 40),(⟨743169483098,743169502427⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨52154770,78325436⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52153472,52153536⟩ : DyadicInterval 40),(⟨-52156032,-52155968⟩ : DyadicInterval 40),(⟨762123382358,762123401687⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78322624,78322688⟩ : DyadicInterval 40),(⟨-78328256,-78328192⟩ : DyadicInterval 40),(⟨762123380788,762123400117⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5632,-2432⟩ : DyadicInterval 40),(⟨762123384832,762123405696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨203365836515,203619124853⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186597179392,186597179456⟩ : DyadicInterval 40),(⟨-224870218496,-224870218432⟩ : DyadicInterval 40),(⟨743207367115,743207386445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186810911232,186810911296⟩ : DyadicInterval 40),(⟨-225181030464,-225181030400⟩ : DyadicInterval 40),(⟨743159943190,743159962519⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38370119168,-38273038976⟩ : DyadicInterval 40),(⟨781259903104,781308462464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨186661563904,186853864448⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-225243511424,-224963831680⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e864_ok : ecellOkT e864 = true := by decide +kernel
theorem e864_pos {a z : ℝ} (ha1 : ((757881/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((75873/409600 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e864 e864_ok ha1 ha2 hz1 hz2 hz

-- box ['75873/409600', '759579/4096000', '999/1000', '3997/4000']  interval_lower 105261351/549755813888
noncomputable def e865 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1303181661306,0,true,186853864384,186853864448⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨895841594246,0,false,-225243511424,-225243511360⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1303409563010,0,true,187046131264,187046131328⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨895613692542,0,false,-225523262336,-225523262272⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1302977991272,0,true,186682011840,186682011904⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨896045264280,0,false,-224993565312,-224993565248⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1303256639559,0,true,186917122688,186917122752⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨895766615993,0,false,-225335539904,-225335539840⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589951691,0,true,78321088,78321152⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433303861,0,false,-78326720,-78326656⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099616183801,0,true,104551040,104551104⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099407071751,0,false,-104561024,-104560960⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511617833,0,false,-9984,-9920⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622197,0,false,-5632,-5568⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1303079822328,0,true,186767938112,186767938176⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨895943433224,0,false,-225118526464,-225118526400⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1303333110507,0,true,186981636672,186981636736⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨895690145045,0,false,-225429408384,-225429408320⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1061728310371,0,false,-38447771712,-38447771648⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1061822158392,0,false,-38350588288,-38350588224⟩
    { al := (75873/409600), au := (759579/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨203670033530,203897935234⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186853864384,186853864448⟩ : DyadicInterval 40),(⟨-225243511424,-225243511360⟩ : DyadicInterval 40),(⟨743150404099,743150423429⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187046131264,187046131328⟩ : DyadicInterval 40),(⟨-225523262336,-225523262272⟩ : DyadicInterval 40),(⟨743107670837,743107690167⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186682011840,186682011904⟩ : DyadicInterval 40),(⟨-224993565312,-224993565248⟩ : DyadicInterval 40),(⟨743188552372,743188571702⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186917122688,186917122752⟩ : DyadicInterval 40),(⟨-225335539904,-225335539840⟩ : DyadicInterval 40),(⟨743136350539,743136369869⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨78323915,104556025⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78321088,78321152⟩ : DyadicInterval 40),(⟨-78326720,-78326656⟩ : DyadicInterval 40),(⟨762123380788,762123400117⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨104551040,104551104⟩ : DyadicInterval 40),(⟨-104561024,-104560960⟩ : DyadicInterval 40),(⟨762123378600,762123397930⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9984,-5568⟩ : DyadicInterval 40),(⟨762123386400,762123407872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨203568194552,203821482731⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186767938112,186767938176⟩ : DyadicInterval 40),(⟨-225118526464,-225118526400⟩ : DyadicInterval 40),(⟨743169483894,743169503224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186981636672,186981636736⟩ : DyadicInterval 40),(⟨-225429408384,-225429408320⟩ : DyadicInterval 40),(⟨743122011677,743122031007⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38447771712,-38350588224⟩ : DyadicInterval 40),(⟨781298677728,781347288736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨186853864384,187046131328⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-225523262336,-225243511360⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e865_ok : ecellOkT e865 = true := by decide +kernel
theorem e865_pos {a z : ℝ} (ha1 : ((75873/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((759579/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e865 e865_ok ha1 ha2 hz1 hz2 hz

-- box ['759579/4096000', '190107/1024000', '999/1000', '3997/4000']  interval_lower 53509899/274877906944
noncomputable def e866 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1303409563009,0,true,187046131264,187046131328⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨895613692543,0,false,-225523262272,-225523262208⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1303637464712,0,true,187238364544,187238364608⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨895385790840,0,false,-225803084352,-225803084288⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1303205665073,0,true,186874116480,186874116544⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨895817590479,0,false,-225272972864,-225272972800⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1303484370335,0,true,187109234368,187109234432⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨895538885217,0,false,-225615104320,-225615104256⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590043838,0,true,78413248,78413312⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433211714,0,false,-78418880,-78418816⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099616306686,0,true,104673920,104673984⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099406948866,0,false,-104683904,-104683840⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511617810,0,false,-9984,-9920⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622184,0,false,-5632,-5568⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1303307610079,0,true,186960123904,186960123968⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨895715645473,0,false,-225398105600,-225398105536⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1303560926756,0,true,187173809088,187173809152⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨895462328796,0,false,-225709101632,-225709101568⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1061643800494,0,false,-38535292480,-38535292416⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1061737764041,0,false,-38437981696,-38437981632⟩
    { al := (759579/4096000), au := (190107/1024000), zl := (999/1000), zu := (3997/4000),
      A := ⟨203897935233,204125836936⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187046131264,187046131328⟩ : DyadicInterval 40),(⟨-225523262272,-225523262208⟩ : DyadicInterval 40),(⟨743107670811,743107690141⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187238364544,187238364608⟩ : DyadicInterval 40),(⟨-225803084352,-225803084288⟩ : DyadicInterval 40),(⟨743064888609,743064907938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186874116480,186874116544⟩ : DyadicInterval 40),(⟨-225272972864,-225272972800⟩ : DyadicInterval 40),(⟨743145905530,743145924859⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187109234368,187109234432⟩ : DyadicInterval 40),(⟨-225615104320,-225615104256⟩ : DyadicInterval 40),(⟨743093633216,743093652546⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨78416062,104678910⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78413248,78413312⟩ : DyadicInterval 40),(⟨-78418880,-78418816⟩ : DyadicInterval 40),(⟨762123380775,762123400104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨104673920,104673984⟩ : DyadicInterval 40),(⟨-104683904,-104683840⟩ : DyadicInterval 40),(⟨762123378577,762123397907⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9984,-5568⟩ : DyadicInterval 40),(⟨762123386400,762123407872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨203795982303,204049298980⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186960123904,186960123968⟩ : DyadicInterval 40),(⟨-225398105600,-225398105536⟩ : DyadicInterval 40),(⟨743126793809,743126813139⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187173809088,187173809152⟩ : DyadicInterval 40),(⟨-225709101632,-225709101568⟩ : DyadicInterval 40),(⟨743079261959,743079281289⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38535292480,-38437981632⟩ : DyadicInterval 40),(⟨781342374432,781391049120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨187046131264,187238364608⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-225803084352,-225523262208⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e866_ok : ecellOkT e866 = true := by decide +kernel
theorem e866_pos {a z : ℝ} (ha1 : ((759579/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((190107/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e866 e866_ok ha1 ha2 hz1 hz2 hz

-- box ['75873/409600', '759579/4096000', '3997/4000', '1999/2000']  interval_lower 104929869/549755813888
noncomputable def e867 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1303181661306,0,true,186853864384,186853864448⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨895841594246,0,false,-225243511424,-225243511360⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1303409563010,0,true,187046131264,187046131328⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨895613692542,0,false,-225523262336,-225523262272⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1303028908780,0,true,186724977472,186724977536⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨895994346772,0,false,-225056046528,-225056046464⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1303307614043,0,true,186960127232,186960127296⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨895715641509,0,false,-225398110464,-225398110400⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099563843968,0,true,52214912,52214976⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459411584,0,false,-52217472,-52217408⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590045363,0,true,78414784,78414848⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433210189,0,false,-78420416,-78420352⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622183,0,false,-5632,-5568⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625297,0,false,-2496,-2432⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1303105280523,0,true,186789419008,186789419072⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨895917975029,0,false,-225149769472,-225149769408⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1303358597352,0,true,187003137536,187003137600⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨895664658200,0,false,-225460695424,-225460695360⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1061718860555,0,false,-38457557888,-38457557824⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1061812730928,0,false,-38360350400,-38360350336⟩
    { al := (75873/409600), au := (759579/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨203670033530,203897935234⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186853864384,186853864448⟩ : DyadicInterval 40),(⟨-225243511424,-225243511360⟩ : DyadicInterval 40),(⟨743150404099,743150423429⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187046131264,187046131328⟩ : DyadicInterval 40),(⟨-225523262336,-225523262272⟩ : DyadicInterval 40),(⟨743107670837,743107690167⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186724977472,186724977536⟩ : DyadicInterval 40),(⟨-225056046528,-225056046464⟩ : DyadicInterval 40),(⟨743179018986,743179038315⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186960127232,186960127296⟩ : DyadicInterval 40),(⟨-225398110464,-225398110400⟩ : DyadicInterval 40),(⟨743126793074,743126812404⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨52216192,78417587⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52214912,52214976⟩ : DyadicInterval 40),(⟨-52217472,-52217408⟩ : DyadicInterval 40),(⟨762123382352,762123401681⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78414784,78414848⟩ : DyadicInterval 40),(⟨-78420416,-78420352⟩ : DyadicInterval 40),(⟨762123380775,762123400104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5632,-2432⟩ : DyadicInterval 40),(⟨762123384832,762123405696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨203593652747,203846969576⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186789419008,186789419072⟩ : DyadicInterval 40),(⟨-225149769472,-225149769408⟩ : DyadicInterval 40),(⟨743164715149,743164734478⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187003137536,187003137600⟩ : DyadicInterval 40),(⟨-225460695424,-225460695360⟩ : DyadicInterval 40),(⟨743117231511,743117250840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38457557888,-38360350336⟩ : DyadicInterval 40),(⟨781303558784,781352181824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨186853864384,187046131328⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-225523262336,-225243511360⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e867_ok : ecellOkT e867 = true := by decide +kernel
theorem e867_pos {a z : ℝ} (ha1 : ((75873/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((759579/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e867 e867_ok ha1 ha2 hz1 hz2 hz

-- box ['759579/4096000', '190107/1024000', '3997/4000', '1999/2000']  interval_lower 106686953/549755813888
noncomputable def e868 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1303409563009,0,true,187046131264,187046131328⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨895613692543,0,false,-225523262272,-225523262208⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1303637464712,0,true,187238364544,187238364608⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨895385790840,0,false,-225803084352,-225803084288⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1303256639557,0,true,186917122688,186917122752⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨895766615995,0,false,-225335539904,-225335539840⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1303535401794,0,true,187152279424,187152279488⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨895487853758,0,false,-225677760768,-225677760704⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099563905401,0,true,52276352,52276416⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459350151,0,false,-52278912,-52278848⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590137529,0,true,78506944,78507008⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433118023,0,false,-78512576,-78512512⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622170,0,false,-5632,-5568⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625291,0,false,-2496,-2432⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1303333096760,0,true,186981625024,186981625088⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨895690158792,0,false,-225429391552,-225429391488⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1303586442083,0,true,187195330240,187195330304⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨895436813469,0,false,-225740431616,-225740431552⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1061634329544,0,false,-38545101312,-38545101248⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1061728315468,0,false,-38447766464,-38447766400⟩
    { al := (759579/4096000), au := (190107/1024000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨203897935233,204125836936⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187046131264,187046131328⟩ : DyadicInterval 40),(⟨-225523262272,-225523262208⟩ : DyadicInterval 40),(⟨743107670811,743107690141⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187238364544,187238364608⟩ : DyadicInterval 40),(⟨-225803084352,-225803084288⟩ : DyadicInterval 40),(⟨743064888609,743064907938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186917122688,186917122752⟩ : DyadicInterval 40),(⟨-225335539904,-225335539840⟩ : DyadicInterval 40),(⟨743136350540,743136369869⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187152279424,187152279488⟩ : DyadicInterval 40),(⟨-225677760768,-225677760704⟩ : DyadicInterval 40),(⟨743084054149,743084073479⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨52277625,78509753⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52276352,52276416⟩ : DyadicInterval 40),(⟨-52278912,-52278848⟩ : DyadicInterval 40),(⟨762123382346,762123401675⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78506944,78507008⟩ : DyadicInterval 40),(⟨-78512576,-78512512⟩ : DyadicInterval 40),(⟨762123380761,762123400091⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5632,-2432⟩ : DyadicInterval 40),(⟨762123384832,762123405696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨203821468984,204074814307⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186981625024,186981625088⟩ : DyadicInterval 40),(⟨-225429391552,-225429391488⟩ : DyadicInterval 40),(⟨743122014303,743122033633⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187195330240,187195330304⟩ : DyadicInterval 40),(⟨-225740431616,-225740431552⟩ : DyadicInterval 40),(⟨743074470967,743074490297⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38545101312,-38447766400⟩ : DyadicInterval 40),(⟨781347266816,781395953536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨187046131264,187238364608⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-225803084352,-225523262208⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e868_ok : ecellOkT e868 = true := by decide +kernel
theorem e868_pos {a z : ℝ} (ha1 : ((759579/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((190107/1024000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e868 e868_ok ha1 ha2 hz1 hz2 hz

-- box ['94629/512000', '757881/4096000', '1999/2000', '3999/4000']  interval_lower 50555141/274877906944
noncomputable def e869 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1302725857902,0,true,186469229760,186469229824⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨896297397650,0,false,-224684223168,-224684223104⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1302953759605,0,true,186661563904,186661563968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨896069495947,0,false,-224963831744,-224963831680⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1302624250786,0,true,186383469120,186383469184⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨896399004766,0,false,-224559586112,-224559586048⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1302902899073,0,true,186618643840,186618643904⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨896120356479,0,false,-224901425728,-224901425664⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537674493,0,true,26046400,26046464⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485581059,0,false,-26047040,-26046976⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099563783730,0,true,52154688,52154752⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459471822,0,false,-52157248,-52157184⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625301,0,false,-2496,-2432⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627159,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1302675049435,0,true,186426346112,186426346176⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨896348206117,0,false,-224621896896,-224621896832⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1302928337926,0,true,186640111296,186640111360⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨896094917626,0,false,-224932638848,-224932638784⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1061878230435,0,false,-38292527488,-38292527424⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1061971892082,0,false,-38195550720,-38195550656⟩
    { al := (94629/512000), au := (757881/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨203214230126,203442131829⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186469229760,186469229824⟩ : DyadicInterval 40),(⟨-224684223168,-224684223104⟩ : DyadicInterval 40),(⟨743235723910,743235743240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186661563904,186661563968⟩ : DyadicInterval 40),(⟨-224963831744,-224963831680⟩ : DyadicInterval 40),(⟨743193088458,743193107787⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186383469120,186383469184⟩ : DyadicInterval 40),(⟨-224559586112,-224559586048⟩ : DyadicInterval 40),(⟨743254716649,743254735978⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186618643840,186618643904⟩ : DyadicInterval 40),(⟨-224901425728,-224901425664⟩ : DyadicInterval 40),(⟨743202607621,743202626950⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨26046717,52155954⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26046400,26046464⟩ : DyadicInterval 40),(⟨-26047040,-26046976⟩ : DyadicInterval 40),(⟨762123383254,762123402583⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52154688,52154752⟩ : DyadicInterval 40),(⟨-52157248,-52157184⟩ : DyadicInterval 40),(⟨762123382357,762123401687⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2496,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨203163421659,203416710150⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186426346112,186426346176⟩ : DyadicInterval 40),(⟨-224621896896,-224621896832⟩ : DyadicInterval 40),(⟨743245222442,743245241772⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186640111296,186640111360⟩ : DyadicInterval 40),(⟨-224932638848,-224932638784⟩ : DyadicInterval 40),(⟨743197846763,743197866092⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38292527488,-38195550656⟩ : DyadicInterval 40),(⟨781221158944,781269666624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨186469229760,186661563968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-224963831744,-224684223104⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e869_ok : ecellOkT e869 = true := by decide +kernel
theorem e869_pos {a z : ℝ} (ha1 : ((94629/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((757881/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e869 e869_ok ha1 ha2 hz1 hz2 hz

-- box ['757881/4096000', '75873/409600', '1999/2000', '3999/4000']  interval_lower 102850323/549755813888
noncomputable def e870 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1302953759604,0,true,186661563904,186661563968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨896069495948,0,false,-224963831744,-224963831680⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1303181661307,0,true,186853864384,186853864448⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨895841594245,0,false,-225243511424,-225243511360⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1302852038538,0,true,186575722112,186575722176⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨896171217014,0,false,-224839023168,-224839023104⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1303130743799,0,true,186810903744,186810903808⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨895892511753,0,false,-225181019584,-225181019520⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537705199,0,true,26077056,26077120⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485550353,0,false,-26077760,-26077696⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099563845154,0,true,52216128,52216192⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459410398,0,false,-52218624,-52218560⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625296,0,false,-2496,-2432⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627158,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1302902894160,0,true,186618639680,186618639744⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨896120361392,0,false,-224901419648,-224901419584⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1303156211140,0,true,186832391552,186832391616⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨895867044412,0,false,-225212275648,-225212275584⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1061793867194,0,false,-38379884032,-38379883968⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1061887644368,0,false,-38282779968,-38282779904⟩
    { al := (757881/4096000), au := (75873/409600), zl := (1999/2000), zu := (3999/4000),
      A := ⟨203442131828,203670033531⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186661563904,186661563968⟩ : DyadicInterval 40),(⟨-224963831744,-224963831680⟩ : DyadicInterval 40),(⟨743193088458,743193107787⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186853864384,186853864448⟩ : DyadicInterval 40),(⟨-225243511424,-225243511360⟩ : DyadicInterval 40),(⟨743150404099,743150423429⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186575722112,186575722176⟩ : DyadicInterval 40),(⟨-224839023168,-224839023104⟩ : DyadicInterval 40),(⟨743212124307,743212143636⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186810903744,186810903808⟩ : DyadicInterval 40),(⟨-225181019584,-225181019520⟩ : DyadicInterval 40),(⟨743159944849,743159964178⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨26077423,52217378⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26077056,26077120⟩ : DyadicInterval 40),(⟨-26077760,-26077696⟩ : DyadicInterval 40),(⟨762123383285,762123402614⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52216128,52216192⟩ : DyadicInterval 40),(⟨-52218624,-52218560⟩ : DyadicInterval 40),(⟨762123382320,762123401649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2496,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨203391266384,203644583364⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186618639680,186618639744⟩ : DyadicInterval 40),(⟨-224901419648,-224901419584⟩ : DyadicInterval 40),(⟨743202608527,743202627857⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186832391552,186832391616⟩ : DyadicInterval 40),(⟨-225212275648,-225212275584⟩ : DyadicInterval 40),(⟨743155173170,743155192500⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38379884032,-38282779904⟩ : DyadicInterval 40),(⟨781264773568,781313344896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨186661563904,186853864448⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-225243511424,-224963831680⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e870_ok : ecellOkT e870 = true := by decide +kernel
theorem e870_pos {a z : ℝ} (ha1 : ((757881/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((75873/409600 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e870 e870_ok ha1 ha2 hz1 hz2 hz

-- box ['94629/512000', '757881/4096000', '3999/4000', '1']  interval_lower 201561801/1099511627776
noncomputable def e871 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1302725857902,0,true,186469229760,186469229824⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨896297397650,0,false,-224684223168,-224684223104⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1302953759605,0,true,186661563904,186661563968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨896069495947,0,false,-224963831744,-224963831680⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1302675054344,0,true,186426350272,186426350336⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨896348201208,0,false,-224621902912,-224621902848⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537706049,0,true,26077952,26078016⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485549503,0,false,-26078592,-26078528⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627157,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1302700450975,0,true,186447785856,186447785920⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨896322804577,0,false,-224653056256,-224653056192⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1302953768116,0,true,186661571072,186661571136⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨896069487436,0,false,-224963842176,-224963842112⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1061868820350,0,false,-38302271104,-38302271040⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1061962504302,0,false,-38205270400,-38205270336⟩
    { al := (94629/512000), au := (757881/4096000), zl := (3999/4000), zu := 1,
      A := ⟨203214230126,203442131829⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186469229760,186469229824⟩ : DyadicInterval 40),(⟨-224684223168,-224684223104⟩ : DyadicInterval 40),(⟨743235723910,743235743240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186661563904,186661563968⟩ : DyadicInterval 40),(⟨-224963831744,-224963831680⟩ : DyadicInterval 40),(⟨743193088458,743193107787⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186426350272,186426350336⟩ : DyadicInterval 40),(⟨-224621902912,-224621902848⟩ : DyadicInterval 40),(⟨743245221513,743245240842⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186661563904,186661563968⟩ : DyadicInterval 40),(⟨-224963831744,-224963831680⟩ : DyadicInterval 40),(⟨743193088458,743193107787⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,26078273⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26077952,26078016⟩ : DyadicInterval 40),(⟨-26078592,-26078528⟩ : DyadicInterval 40),(⟨762123383253,762123402582⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨203188823199,203442140340⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186447785856,186447785920⟩ : DyadicInterval 40),(⟨-224653056256,-224653056192⟩ : DyadicInterval 40),(⟨743240473981,743240493311⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186661571072,186661571136⟩ : DyadicInterval 40),(⟨-224963842176,-224963842112⟩ : DyadicInterval 40),(⟨743193086868,743193106198⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38302271104,-38205270336⟩ : DyadicInterval 40),(⟨781226018784,781274538432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨186469229760,186661563968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-224963831744,-224684223104⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e871_ok : ecellOkT e871 = true := by decide +kernel
theorem e871_pos {a z : ℝ} (ha1 : ((94629/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((757881/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e871 e871_ok ha1 ha2 hz1 hz2 hz

-- box ['757881/4096000', '75873/409600', '3999/4000', '1']  interval_lower 205039265/1099511627776
noncomputable def e872 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1302953759604,0,true,186661563904,186661563968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨896069495948,0,false,-224963831744,-224963831680⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1303181661307,0,true,186853864384,186853864448⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨895841594245,0,false,-225243511424,-225243511360⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1302902899071,0,true,186618643840,186618643904⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨896120356481,0,false,-224901425728,-224901425664⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537736762,0,true,26108672,26108736⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485518790,0,false,-26109312,-26109248⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627156,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1302928324185,0,true,186640099712,186640099776⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨896094931367,0,false,-224932621952,-224932621888⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1303181669817,0,true,186853871552,186853871616⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨895841585735,0,false,-225243521920,-225243521856⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1061784436014,0,false,-38389650304,-38389650240⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1061878235521,0,false,-38292522240,-38292522176⟩
    { al := (757881/4096000), au := (75873/409600), zl := (3999/4000), zu := 1,
      A := ⟨203442131828,203670033531⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186661563904,186661563968⟩ : DyadicInterval 40),(⟨-224963831744,-224963831680⟩ : DyadicInterval 40),(⟨743193088458,743193107787⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186853864384,186853864448⟩ : DyadicInterval 40),(⟨-225243511424,-225243511360⟩ : DyadicInterval 40),(⟨743150404099,743150423429⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186618643840,186618643904⟩ : DyadicInterval 40),(⟨-224901425728,-224901425664⟩ : DyadicInterval 40),(⟨743202607621,743202626950⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186853864384,186853864448⟩ : DyadicInterval 40),(⟨-225243511424,-225243511360⟩ : DyadicInterval 40),(⟨743150404099,743150423429⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,26108986⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26108672,26108736⟩ : DyadicInterval 40),(⟨-26109312,-26109248⟩ : DyadicInterval 40),(⟨762123383252,762123402581⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨203416696409,203670042041⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186640099712,186640099776⟩ : DyadicInterval 40),(⟨-224932621952,-224932621888⟩ : DyadicInterval 40),(⟨743197849313,743197868643⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186853871552,186853871616⟩ : DyadicInterval 40),(⟨-225243521920,-225243521856⟩ : DyadicInterval 40),(⟨743150402532,743150421862⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38389650304,-38292522176⟩ : DyadicInterval 40),(⟨781269644704,781318228032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨186661563904,186853864448⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-225243511424,-224963831680⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e872_ok : ecellOkT e872 = true := by decide +kernel
theorem e872_pos {a z : ℝ} (ha1 : ((757881/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((75873/409600 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e872 e872_ok ha1 ha2 hz1 hz2 hz

-- box ['75873/409600', '759579/4096000', '1999/2000', '3999/4000']  interval_lower 209196209/1099511627776
noncomputable def e873 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1303181661306,0,true,186853864384,186853864448⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨895841594246,0,false,-225243511424,-225243511360⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1303409563010,0,true,187046131264,187046131328⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨895613692542,0,false,-225523262336,-225523262272⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1303079826289,0,true,186767941440,186767941504⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨895943429263,0,false,-225118531264,-225118531200⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1303358588527,0,true,187003130112,187003130176⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨895664667025,0,false,-225460684608,-225460684544⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537735911,0,true,26107776,26107840⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485519641,0,false,-26108480,-26108416⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099563906589,0,true,52277568,52277632⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459348963,0,false,-52280064,-52280000⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625290,0,false,-2496,-2432⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627157,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1303130738879,0,true,186810899584,186810899648⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨895892516673,0,false,-225181013568,-225181013504⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1303384084357,0,true,187024638144,187024638208⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨895639171195,0,false,-225491983552,-225491983488⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1061709409498,0,false,-38467345408,-38467345344⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1061803302226,0,false,-38370113920,-38370113856⟩
    { al := (75873/409600), au := (759579/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨203670033530,203897935234⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186853864384,186853864448⟩ : DyadicInterval 40),(⟨-225243511424,-225243511360⟩ : DyadicInterval 40),(⟨743150404099,743150423429⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187046131264,187046131328⟩ : DyadicInterval 40),(⟨-225523262336,-225523262272⟩ : DyadicInterval 40),(⟨743107670837,743107690167⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186767941440,186767941504⟩ : DyadicInterval 40),(⟨-225118531264,-225118531200⟩ : DyadicInterval 40),(⟨743169483136,743169502465⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187003130112,187003130176⟩ : DyadicInterval 40),(⟨-225460684608,-225460684544⟩ : DyadicInterval 40),(⟨743117233161,743117252491⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨26108135,52278813⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26107776,26107840⟩ : DyadicInterval 40),(⟨-26108480,-26108416⟩ : DyadicInterval 40),(⟨762123383284,762123402613⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52277568,52277632⟩ : DyadicInterval 40),(⟨-52280064,-52280000⟩ : DyadicInterval 40),(⟨762123382314,762123401643⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2496,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨203619111103,203872456581⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186810899584,186810899648⟩ : DyadicInterval 40),(⟨-225181013568,-225181013504⟩ : DyadicInterval 40),(⟨743159945785,743159965114⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187024638144,187024638208⟩ : DyadicInterval 40),(⟨-225491983552,-225491983488⟩ : DyadicInterval 40),(⟨743112450686,743112470016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38467345408,-38370113856⟩ : DyadicInterval 40),(⟨781308440544,781357075584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨186853864384,187046131328⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-225523262336,-225243511360⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e873_ok : ecellOkT e873 = true := by decide +kernel
theorem e873_pos {a z : ℝ} (ha1 : ((75873/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((759579/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e873 e873_ok ha1 ha2 hz1 hz2 hz

-- box ['759579/4096000', '190107/1024000', '1999/2000', '3999/4000']  interval_lower 212707983/1099511627776
noncomputable def e874 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1303409563009,0,true,187046131264,187046131328⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨895613692543,0,false,-225523262272,-225523262208⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1303637464712,0,true,187238364544,187238364608⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨895385790840,0,false,-225803084352,-225803084288⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1303307614041,0,true,186960127232,186960127296⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨895715641511,0,false,-225398110464,-225398110400⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1303586433253,0,true,187195322816,187195322880⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨895436822299,0,false,-225740420800,-225740420736⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537766628,0,true,26138496,26138560⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485488924,0,false,-26139200,-26139136⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099563968036,0,true,52339008,52339072⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459287516,0,false,-52341568,-52341504⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625284,0,false,-2496,-2432⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627155,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1303358583605,0,true,187003125952,187003126016⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨895664671947,0,false,-225460678592,-225460678528⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1303611957571,0,true,187216851136,187216851200⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨895411297981,0,false,-225771762688,-225771762624⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1061624857349,0,false,-38554911488,-38554911424⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1061718865653,0,false,-38457552576,-38457552512⟩
    { al := (759579/4096000), au := (190107/1024000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨203897935233,204125836936⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187046131264,187046131328⟩ : DyadicInterval 40),(⟨-225523262272,-225523262208⟩ : DyadicInterval 40),(⟨743107670811,743107690141⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187238364544,187238364608⟩ : DyadicInterval 40),(⟨-225803084352,-225803084288⟩ : DyadicInterval 40),(⟨743064888609,743064907938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186960127232,186960127296⟩ : DyadicInterval 40),(⟨-225398110464,-225398110400⟩ : DyadicInterval 40),(⟨743126793075,743126812404⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187195322816,187195322880⟩ : DyadicInterval 40),(⟨-225740420800,-225740420736⟩ : DyadicInterval 40),(⟨743074472622,743074491952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨26138852,52340260⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26138496,26138560⟩ : DyadicInterval 40),(⟨-26139200,-26139136⟩ : DyadicInterval 40),(⟨762123383282,762123402611⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52339008,52339072⟩ : DyadicInterval 40),(⟨-52341568,-52341504⟩ : DyadicInterval 40),(⟨762123382340,762123401669⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2496,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨203846955829,204100329795⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187003125952,187003126016⟩ : DyadicInterval 40),(⟨-225460678592,-225460678528⟩ : DyadicInterval 40),(⟨743117234100,743117253429⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187216851136,187216851200⟩ : DyadicInterval 40),(⟨-225771762688,-225771762624⟩ : DyadicInterval 40),(⟨743069679313,743069698643⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38554911488,-38457552512⟩ : DyadicInterval 40),(⟨781352159872,781400858624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨187046131264,187238364608⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-225803084352,-225523262208⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e874_ok : ecellOkT e874 = true := by decide +kernel
theorem e874_pos {a z : ℝ} (ha1 : ((759579/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((190107/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e874 e874_ok ha1 ha2 hz1 hz2 hz

-- box ['75873/409600', '759579/4096000', '3999/4000', '1']  interval_lower 104266151/549755813888
noncomputable def e875 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1303181661306,0,true,186853864384,186853864448⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨895841594246,0,false,-225243511424,-225243511360⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1303409563010,0,true,187046131264,187046131328⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨895613692542,0,false,-225523262336,-225523262272⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1303130743797,0,true,186810903744,186810903808⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨895892511755,0,false,-225181019584,-225181019520⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537767479,0,true,26139392,26139456⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485488073,0,false,-26140032,-26139968⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627154,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1303156197393,0,true,186832379904,186832379968⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨895867058159,0,false,-225212258752,-225212258688⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1303409571515,0,true,187046138432,187046138496⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨895613684037,0,false,-225523272768,-225523272704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1061699957202,0,false,-38477134272,-38477134208⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1061793872287,0,false,-38379878784,-38379878720⟩
    { al := (75873/409600), au := (759579/4096000), zl := (3999/4000), zu := 1,
      A := ⟨203670033530,203897935234⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186853864384,186853864448⟩ : DyadicInterval 40),(⟨-225243511424,-225243511360⟩ : DyadicInterval 40),(⟨743150404099,743150423429⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187046131264,187046131328⟩ : DyadicInterval 40),(⟨-225523262336,-225523262272⟩ : DyadicInterval 40),(⟨743107670837,743107690167⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186810903744,186810903808⟩ : DyadicInterval 40),(⟨-225181019584,-225181019520⟩ : DyadicInterval 40),(⟨743159944850,743159964179⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187046131264,187046131328⟩ : DyadicInterval 40),(⟨-225523262336,-225523262272⟩ : DyadicInterval 40),(⟨743107670837,743107690167⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,26139703⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26139392,26139456⟩ : DyadicInterval 40),(⟨-26140032,-26139968⟩ : DyadicInterval 40),(⟨762123383250,762123402579⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨203644569617,203897943739⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨186832379904,186832379968⟩ : DyadicInterval 40),(⟨-225212258752,-225212258688⟩ : DyadicInterval 40),(⟨743155175766,743155195096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187046138432,187046138496⟩ : DyadicInterval 40),(⟨-225523272768,-225523272704⟩ : DyadicInterval 40),(⟨743107669242,743107688571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38477134272,-38379878720⟩ : DyadicInterval 40),(⟨781313322976,781361970016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨186853864384,187046131328⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-225523262336,-225243511360⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e875_ok : ecellOkT e875 = true := by decide +kernel
theorem e875_pos {a z : ℝ} (ha1 : ((75873/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((759579/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e875 e875_ok ha1 ha2 hz1 hz2 hz

-- box ['759579/4096000', '190107/1024000', '3999/4000', '1']  interval_lower 212041383/1099511627776
noncomputable def e876 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1303409563009,0,true,187046131264,187046131328⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨895613692543,0,false,-225523262272,-225523262208⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1303637464712,0,true,187238364544,187238364608⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨895385790840,0,false,-225803084352,-225803084288⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1303358588525,0,true,187003130112,187003130176⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨895664667027,0,false,-225460684608,-225460684544⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537798203,0,true,26170112,26170176⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485457349,0,false,-26170752,-26170688⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627153,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1303384070609,0,true,187024626560,187024626624⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨895639184943,0,false,-225491966656,-225491966592⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1303637473224,0,true,187238371712,187238371776⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨895385782328,0,false,-225803094784,-225803094720⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1061615383909,0,false,-38564723072,-38564723008⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1061709414597,0,false,-38467340096,-38467340032⟩
    { al := (759579/4096000), au := (190107/1024000), zl := (3999/4000), zu := 1,
      A := ⟨203897935233,204125836936⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187046131264,187046131328⟩ : DyadicInterval 40),(⟨-225523262272,-225523262208⟩ : DyadicInterval 40),(⟨743107670811,743107690141⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187238364544,187238364608⟩ : DyadicInterval 40),(⟨-225803084352,-225803084288⟩ : DyadicInterval 40),(⟨743064888609,743064907938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187003130112,187003130176⟩ : DyadicInterval 40),(⟨-225460684608,-225460684544⟩ : DyadicInterval 40),(⟨743117233161,743117252491⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187238364544,187238364608⟩ : DyadicInterval 40),(⟨-225803084352,-225803084288⟩ : DyadicInterval 40),(⟨743064888609,743064907938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,26170427⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26170112,26170176⟩ : DyadicInterval 40),(⟨-26170752,-26170688⟩ : DyadicInterval 40),(⟨762123383249,762123402578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨203872442833,204125845448⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187024626560,187024626624⟩ : DyadicInterval 40),(⟨-225491966656,-225491966592⟩ : DyadicInterval 40),(⟨743112453249,743112472579⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187238371712,187238371776⟩ : DyadicInterval 40),(⟨-225803094784,-225803094720⟩ : DyadicInterval 40),(⟨743064887008,743064906338⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38564723072,-38467340032⟩ : DyadicInterval 40),(⟨781357053632,781405764416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨187046131264,187238364608⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-225803084352,-225523262208⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e876_ok : ecellOkT e876 = true := by decide +kernel
theorem e876_pos {a z : ℝ} (ha1 : ((759579/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((190107/1024000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e876 e876_ok ha1 ha2 hz1 hz2 hz

-- box ['190107/1024000', '761277/4096000', '999/1000', '3997/4000']  interval_lower 54393085/274877906944
noncomputable def e877 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1303637464711,0,true,187238364544,187238364608⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨895385790841,0,false,-225803084352,-225803084288⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1303865366414,0,true,187430564160,187430564224⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨895157889138,0,false,-226082977664,-226082977600⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1303433338874,0,true,187066187584,187066187648⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨895589916678,0,false,-225552451456,-225552451392⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1303712101111,0,true,187301312384,187301312448⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨895311154441,0,false,-225894739840,-225894739776⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590136001,0,true,78505408,78505472⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433119551,0,false,-78511040,-78510976⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099616429595,0,true,104796800,104796864⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099406825957,0,false,-104806848,-104806784⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511617786,0,false,-10048,-9984⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622171,0,false,-5632,-5568⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1303535397829,0,true,187152276096,187152276160⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨895487857723,0,false,-225677755904,-225677755840⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1303788742988,0,true,187365947968,187365948032⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨895234512564,0,false,-225988866048,-225988865984⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1061559196218,0,false,-38622918016,-38622917952⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1061653275309,0,false,-38525479808,-38525479744⟩
    { al := (190107/1024000), au := (761277/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨204125836935,204353738638⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187238364544,187238364608⟩ : DyadicInterval 40),(⟨-225803084352,-225803084288⟩ : DyadicInterval 40),(⟨743064888609,743064907938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187430564160,187430564224⟩ : DyadicInterval 40),(⟨-226082977664,-226082977600⟩ : DyadicInterval 40),(⟨743022057518,743022076847⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187066187584,187066187648⟩ : DyadicInterval 40),(⟨-225552451456,-225552451392⟩ : DyadicInterval 40),(⟨743103209862,743103229191⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187301312384,187301312448⟩ : DyadicInterval 40),(⟨-225894739840,-225894739776⟩ : DyadicInterval 40),(⟨743050867108,743050886437⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨78508225,104801819⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78505408,78505472⟩ : DyadicInterval 40),(⟨-78511040,-78510976⟩ : DyadicInterval 40),(⟨762123380762,762123400091⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨104796800,104796864⟩ : DyadicInterval 40),(⟨-104806848,-104806784⟩ : DyadicInterval 40),(⟨762123378586,762123397916⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-10048,-5568⟩ : DyadicInterval 40),(⟨762123386400,762123407904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨204023770053,204277115212⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187152276096,187152276160⟩ : DyadicInterval 40),(⟨-225677755904,-225677755840⟩ : DyadicInterval 40),(⟨743084054886,743084074216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187365947968,187365948032⟩ : DyadicInterval 40),(⟨-225988866048,-225988865984⟩ : DyadicInterval 40),(⟨743036463332,743036482662⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38622918016,-38525479744⟩ : DyadicInterval 40),(⟨781386123488,781434861888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨187238364544,187430564224⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-226082977664,-225803084288⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e877_ok : ecellOkT e877 = true := by decide +kernel
theorem e877_pos {a z : ℝ} (ha1 : ((190107/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((761277/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e877 e877_ok ha1 ha2 hz1 hz2 hz

-- box ['761277/4096000', '381063/2048000', '999/1000', '3997/4000']  interval_lower 221120933/1099511627776
noncomputable def e878 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1303865366413,0,true,187430564160,187430564224⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨895157889139,0,false,-226082977664,-226082977600⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1304093268116,0,true,187622730240,187622730304⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨894929987436,0,false,-226362942208,-226362942144⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1303661012674,0,true,187258225088,187258225152⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨895362242878,0,false,-225832001024,-225832000960⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1303939831886,0,true,187493356928,187493356992⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨895083423666,0,false,-226174446464,-226174446400⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590228179,0,true,78597568,78597632⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433027373,0,false,-78603264,-78603200⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099616552523,0,true,104919680,104919744⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099406703029,0,false,-104929792,-104929728⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511617763,0,false,-10048,-9984⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622158,0,false,-5632,-5568⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1303763185575,0,true,187344394688,187344394752⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨895260069977,0,false,-225957477312,-225957477248⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1304016559234,0,true,187558053248,187558053312⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨895006696318,0,false,-226268701632,-226268701568⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1061474497531,0,false,-38710648320,-38710648256⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1061568692195,0,false,-38613082624,-38613082560⟩
    { al := (761277/4096000), au := (381063/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨204353738637,204581640340⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187430564160,187430564224⟩ : DyadicInterval 40),(⟨-226082977664,-226082977600⟩ : DyadicInterval 40),(⟨743022057518,743022076847⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187622730240,187622730304⟩ : DyadicInterval 40),(⟨-226362942208,-226362942144⟩ : DyadicInterval 40),(⟨742979177450,742979196779⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187258225088,187258225152⟩ : DyadicInterval 40),(⟨-225832001024,-225832000960⟩ : DyadicInterval 40),(⟨743060465370,743060484700⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187493356928,187493356992⟩ : DyadicInterval 40),(⟨-226174446464,-226174446400⟩ : DyadicInterval 40),(⟨743008052088,743008071417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨78600403,104924747⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78597568,78597632⟩ : DyadicInterval 40),(⟨-78603264,-78603200⟩ : DyadicInterval 40),(⟨762123380780,762123400110⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨104919680,104919744⟩ : DyadicInterval 40),(⟨-104929792,-104929728⟩ : DyadicInterval 40),(⟨762123378594,762123397924⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-10048,-5568⟩ : DyadicInterval 40),(⟨762123386400,762123407904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨204251557799,204504931458⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187344394688,187344394752⟩ : DyadicInterval 40),(⟨-225957477312,-225957477248⟩ : DyadicInterval 40),(⟨743041267088,743041286418⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187558053248,187558053312⟩ : DyadicInterval 40),(⟨-226268701632,-226268701568⟩ : DyadicInterval 40),(⟨742993615815,742993635145⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38710648320,-38613082560⟩ : DyadicInterval 40),(⟨781429924896,781478727040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨187430564160,187622730304⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-226362942208,-226082977600⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e878_ok : ecellOkT e878 = true := by decide +kernel
theorem e878_pos {a z : ℝ} (ha1 : ((761277/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((381063/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e878 e878_ok ha1 ha2 hz1 hz2 hz

-- box ['190107/1024000', '761277/4096000', '3997/4000', '1999/2000']  interval_lower 108452131/549755813888
noncomputable def e879 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1303637464711,0,true,187238364544,187238364608⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨895385790841,0,false,-225803084352,-225803084288⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1303865366414,0,true,187430564160,187430564224⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨895157889138,0,false,-226082977664,-226082977600⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1303484370333,0,true,187109234368,187109234432⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨895538885219,0,false,-225615104320,-225615104256⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1303763189545,0,true,187344398016,187344398080⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨895260066007,0,false,-225957482176,-225957482112⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099563966845,0,true,52337792,52337856⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459288707,0,false,-52340352,-52340288⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590229712,0,true,78599104,78599168⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433025840,0,false,-78604800,-78604736⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622156,0,false,-5632,-5568⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625285,0,false,-2496,-2432⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1303560913001,0,true,187173797504,187173797568⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨895462342551,0,false,-225709084736,-225709084672⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1303814286806,0,true,187387489408,187387489472⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨895208968746,0,false,-226020238976,-226020238912⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1061549704107,0,false,-38632749568,-38632749504⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1061643805601,0,false,-38535287232,-38535287168⟩
    { al := (190107/1024000), au := (761277/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨204125836935,204353738638⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187238364544,187238364608⟩ : DyadicInterval 40),(⟨-225803084352,-225803084288⟩ : DyadicInterval 40),(⟨743064888609,743064907938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187430564160,187430564224⟩ : DyadicInterval 40),(⟨-226082977664,-226082977600⟩ : DyadicInterval 40),(⟨743022057518,743022076847⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187109234368,187109234432⟩ : DyadicInterval 40),(⟨-225615104320,-225615104256⟩ : DyadicInterval 40),(⟨743093633217,743093652547⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187344398016,187344398080⟩ : DyadicInterval 40),(⟨-225957482176,-225957482112⟩ : DyadicInterval 40),(⟨743041266349,743041285678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨52339069,78601936⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52337792,52337856⟩ : DyadicInterval 40),(⟨-52340352,-52340288⟩ : DyadicInterval 40),(⟨762123382340,762123401669⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78599104,78599168⟩ : DyadicInterval 40),(⟨-78604800,-78604736⟩ : DyadicInterval 40),(⟨762123380780,762123400110⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5632,-2432⟩ : DyadicInterval 40),(⟨762123384832,762123405696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨204049285225,204302659030⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187173797504,187173797568⟩ : DyadicInterval 40),(⟨-225709084736,-225709084672⟩ : DyadicInterval 40),(⟨743079264529,743079283859⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187387489408,187387489472⟩ : DyadicInterval 40),(⟨-226020238976,-226020238912⟩ : DyadicInterval 40),(⟨743031661486,743031680816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38632749568,-38535287168⟩ : DyadicInterval 40),(⟨781391027200,781439777664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨187238364544,187430564224⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-226082977664,-225803084288⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e879_ok : ecellOkT e879 = true := by decide +kernel
theorem e879_pos {a z : ℝ} (ha1 : ((190107/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((761277/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e879 e879_ok ha1 ha2 hz1 hz2 hz

-- box ['761277/4096000', '381063/2048000', '3997/4000', '1999/2000']  interval_lower 55112469/274877906944
noncomputable def e880 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1303865366413,0,true,187430564160,187430564224⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨895157889139,0,false,-226082977664,-226082977600⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1304093268116,0,true,187622730240,187622730304⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨894929987436,0,false,-226362942208,-226362942144⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1303712101108,0,true,187301312384,187301312448⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨895311154444,0,false,-225894739840,-225894739776⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1303990977296,0,true,187536483072,187536483136⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨895032278256,0,false,-226237274816,-226237274752⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564028298,0,true,52399232,52399296⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459227254,0,false,-52401792,-52401728⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590321911,0,true,78691264,78691328⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432933641,0,false,-78696960,-78696896⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622143,0,false,-5696,-5632⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625279,0,false,-2560,-2496⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1303788729226,0,true,187365936384,187365936448⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨895234526326,0,false,-225988849152,-225988849088⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1304042131535,0,true,187579614912,187579614976⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨894981124017,0,false,-226300117568,-226300117504⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1061464984237,0,false,-38720502592,-38720502528⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1061559201333,0,false,-38622912704,-38622912640⟩
    { al := (761277/4096000), au := (381063/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨204353738637,204581640340⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187430564160,187430564224⟩ : DyadicInterval 40),(⟨-226082977664,-226082977600⟩ : DyadicInterval 40),(⟨743022057518,743022076847⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187622730240,187622730304⟩ : DyadicInterval 40),(⟨-226362942208,-226362942144⟩ : DyadicInterval 40),(⟨742979177450,742979196779⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187301312384,187301312448⟩ : DyadicInterval 40),(⟨-225894739840,-225894739776⟩ : DyadicInterval 40),(⟨743050867109,743050886438⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187536483072,187536483136⟩ : DyadicInterval 40),(⟨-226237274816,-226237274752⟩ : DyadicInterval 40),(⟨742998429675,742998449005⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨52400522,78694135⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52399232,52399296⟩ : DyadicInterval 40),(⟨-52401792,-52401728⟩ : DyadicInterval 40),(⟨762123382334,762123401663⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78691264,78691328⟩ : DyadicInterval 40),(⟨-78696960,-78696896⟩ : DyadicInterval 40),(⟨762123380767,762123400096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5696,-2496⟩ : DyadicInterval 40),(⟨762123384864,762123405728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨204277101450,204530503759⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187365936384,187365936448⟩ : DyadicInterval 40),(⟨-225988849152,-225988849088⟩ : DyadicInterval 40),(⟨743036465909,743036485238⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187579614912,187579614976⟩ : DyadicInterval 40),(⟨-226300117568,-226300117504⟩ : DyadicInterval 40),(⟨742988803155,742988822485⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38720502592,-38622912640⟩ : DyadicInterval 40),(⟨781434839936,781483654176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨187430564160,187622730304⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-226362942208,-226082977600⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e880_ok : ecellOkT e880 = true := by decide +kernel
theorem e880_pos {a z : ℝ} (ha1 : ((761277/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((381063/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e880 e880_ok ha1 ha2 hz1 hz2 hz

-- box ['381063/2048000', '30519/163840', '999/1000', '3997/4000']  interval_lower 224685273/1099511627776
noncomputable def e881 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1304093268115,0,true,187622730240,187622730304⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨894929987437,0,false,-226362942208,-226362942144⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1304321169818,0,true,187814862720,187814862784⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨894702085734,0,false,-226642978048,-226642977984⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1303888686474,0,true,187450229120,187450229184⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨895134569078,0,false,-226111621760,-226111621696⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1304167562662,0,true,187685367936,187685368000⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨894855692890,0,false,-226454224320,-226454224256⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590320374,0,true,78689728,78689792⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432935178,0,false,-78695424,-78695360⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099616675473,0,true,105042624,105042688⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099406580079,0,false,-105052736,-105052672⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511617739,0,false,-10048,-9984⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622144,0,false,-5696,-5632⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1303990973327,0,true,187536479680,187536479744⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨895032282225,0,false,-226237269888,-226237269824⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1304244375476,0,true,187750124992,187750125056⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨894778880076,0,false,-226548608448,-226548608384⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1061389704440,0,false,-38798483456,-38798483392⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1061484014697,0,false,-38700790144,-38700790080⟩
    { al := (381063/2048000), au := (30519/163840), zl := (999/1000), zu := (3997/4000),
      A := ⟨204581640339,204809542042⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187622730240,187622730304⟩ : DyadicInterval 40),(⟨-226362942208,-226362942144⟩ : DyadicInterval 40),(⟨742979177450,742979196780⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187814862720,187814862784⟩ : DyadicInterval 40),(⟨-226642978048,-226642977984⟩ : DyadicInterval 40),(⟨742936248459,742936267788⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187450229120,187450229184⟩ : DyadicInterval 40),(⟨-226111621760,-226111621696⟩ : DyadicInterval 40),(⟨743017672044,743017691373⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187685367936,187685368000⟩ : DyadicInterval 40),(⟨-226454224320,-226454224256⟩ : DyadicInterval 40),(⟨742965188234,742965207564⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨78692598,105047697⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78689728,78689792⟩ : DyadicInterval 40),(⟨-78695424,-78695360⟩ : DyadicInterval 40),(⟨762123380767,762123400097⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨105042624,105042688⟩ : DyadicInterval 40),(⟨-105052736,-105052672⟩ : DyadicInterval 40),(⟨762123378571,762123397901⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-10048,-5632⟩ : DyadicInterval 40),(⟨762123386432,762123407904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨204479345551,204732747700⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187536479680,187536479744⟩ : DyadicInterval 40),(⟨-226237269888,-226237269824⟩ : DyadicInterval 40),(⟨742998430428,742998449757⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187750124992,187750125056⟩ : DyadicInterval 40),(⟨-226548608448,-226548608384⟩ : DyadicInterval 40),(⟨742950719388,742950738717⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38798483456,-38700790080⟩ : DyadicInterval 40),(⟨781473778656,781522644608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨187622730240,187814862784⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-226642978048,-226362942144⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e881_ok : ecellOkT e881 = true := by decide +kernel
theorem e881_pos {a z : ℝ} (ha1 : ((381063/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((30519/163840 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e881 e881_ok ha1 ha2 hz1 hz2 hz

-- box ['30519/163840', '47739/256000', '999/1000', '3997/4000']  interval_lower 228265653/1099511627776
noncomputable def e882 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1304321169817,0,true,187814862720,187814862784⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨894702085735,0,false,-226642978048,-226642977984⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1304549071520,0,true,188006961600,188006961664⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨894474184032,0,false,-226923085248,-226923085184⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1304116360274,0,true,187642199616,187642199680⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨894906895278,0,false,-226391313600,-226391313536⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1304395293438,0,true,187877345408,187877345472⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨894627962114,0,false,-226734073344,-226734073280⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590412585,0,true,78781952,78782016⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432842967,0,false,-78787648,-78787584⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099616798443,0,true,105165632,105165696⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099406457109,0,false,-105175744,-105175680⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511617716,0,false,-10112,-10048⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622131,0,false,-5696,-5632⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1304218761079,0,true,187728531200,187728531264⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨894804494473,0,false,-226517133760,-226517133696⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1304472191716,0,true,187942163200,187942163264⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨894551063836,0,false,-226828586560,-226828586496⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1061304816943,0,false,-38886423360,-38886423296⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1061399242817,0,false,-38788602496,-38788602432⟩
    { al := (30519/163840), au := (47739/256000), zl := (999/1000), zu := (3997/4000),
      A := ⟨204809542041,205037443744⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187814862720,187814862784⟩ : DyadicInterval 40),(⟨-226642978048,-226642977984⟩ : DyadicInterval 40),(⟨742936248459,742936267788⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188006961600,188006961664⟩ : DyadicInterval 40),(⟨-226923085248,-226923085184⟩ : DyadicInterval 40),(⟨742893270558,742893289887⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187642199616,187642199680⟩ : DyadicInterval 40),(⟨-226391313600,-226391313536⟩ : DyadicInterval 40),(⟨742974829884,742974849213⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187877345408,187877345472⟩ : DyadicInterval 40),(⟨-226734073344,-226734073280⟩ : DyadicInterval 40),(⟨742922275510,742922294839⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨78784809,105170667⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78781952,78782016⟩ : DyadicInterval 40),(⟨-78787648,-78787584⟩ : DyadicInterval 40),(⟨762123380754,762123400083⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨105165632,105165696⟩ : DyadicInterval 40),(⟨-105175744,-105175680⟩ : DyadicInterval 40),(⟨762123378547,762123397877⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-10112,-5632⟩ : DyadicInterval 40),(⟨762123386432,762123407936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨204707133303,204960563940⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187728531200,187728531264⟩ : DyadicInterval 40),(⟨-226517133760,-226517133696⟩ : DyadicInterval 40),(⟨742955544871,742955564200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187942163200,187942163264⟩ : DyadicInterval 40),(⟨-226828586560,-226828586496⟩ : DyadicInterval 40),(⟨742907774065,742907793395⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38886423360,-38788602432⟩ : DyadicInterval 40),(⟨781517684832,781566614560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨187814862720,188006961664⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-226923085248,-226642977984⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e882_ok : ecellOkT e882 = true := by decide +kernel
theorem e882_pos {a z : ℝ} (ha1 : ((30519/163840 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((47739/256000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e882 e882_ok ha1 ha2 hz1 hz2 hz

-- box ['381063/2048000', '30519/163840', '3997/4000', '1999/2000']  interval_lower 224011745/1099511627776
noncomputable def e883 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1304093268115,0,true,187622730240,187622730304⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨894929987437,0,false,-226362942208,-226362942144⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1304321169818,0,true,187814862720,187814862784⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨894702085734,0,false,-226642978048,-226642977984⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1303939831884,0,true,187493356928,187493356992⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨895083423668,0,false,-226174446464,-226174446400⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1304218765048,0,true,187728534528,187728534592⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨894804490504,0,false,-226517138624,-226517138560⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564089763,0,true,52460672,52460736⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459165789,0,false,-52463296,-52463232⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590414124,0,true,78783488,78783552⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432841428,0,false,-78789184,-78789120⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622130,0,false,-5696,-5632⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625273,0,false,-2560,-2496⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1304016545467,0,true,187558041664,187558041728⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨895006710085,0,false,-226268684736,-226268684672⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1304269976263,0,true,187771706944,187771707008⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨894753279289,0,false,-226580067392,-226580067328⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1061380169939,0,false,-38808360448,-38808360384⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1061474502654,0,false,-38710643008,-38710642944⟩
    { al := (381063/2048000), au := (30519/163840), zl := (3997/4000), zu := (1999/2000),
      A := ⟨204581640339,204809542042⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187622730240,187622730304⟩ : DyadicInterval 40),(⟨-226362942208,-226362942144⟩ : DyadicInterval 40),(⟨742979177450,742979196780⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187814862720,187814862784⟩ : DyadicInterval 40),(⟨-226642978048,-226642977984⟩ : DyadicInterval 40),(⟨742936248459,742936267788⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187493356928,187493356992⟩ : DyadicInterval 40),(⟨-226174446464,-226174446400⟩ : DyadicInterval 40),(⟨743008052088,743008071418⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187728534528,187728534592⟩ : DyadicInterval 40),(⟨-226517138624,-226517138560⟩ : DyadicInterval 40),(⟨742955544128,742955563458⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨52461987,78786348⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52460672,52460736⟩ : DyadicInterval 40),(⟨-52463296,-52463232⟩ : DyadicInterval 40),(⟨762123382360,762123401689⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78783488,78783552⟩ : DyadicInterval 40),(⟨-78789184,-78789120⟩ : DyadicInterval 40),(⟨762123380754,762123400083⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5696,-2496⟩ : DyadicInterval 40),(⟨762123384864,762123405728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨204504917691,204758348487⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187558041664,187558041728⟩ : DyadicInterval 40),(⟨-226268684736,-226268684672⟩ : DyadicInterval 40),(⟨742993618398,742993637728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187771706944,187771707008⟩ : DyadicInterval 40),(⟨-226580067392,-226580067328⟩ : DyadicInterval 40),(⟨742945895850,742945915179⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38808360448,-38710642944⟩ : DyadicInterval 40),(⟨781478705088,781527583104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨187622730240,187814862784⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-226642978048,-226362942144⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e883_ok : ecellOkT e883 = true := by decide +kernel
theorem e883_pos {a z : ℝ} (ha1 : ((381063/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((30519/163840 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e883 e883_ok ha1 ha2 hz1 hz2 hz

-- box ['30519/163840', '47739/256000', '3997/4000', '1999/2000']  interval_lower 113794853/549755813888
noncomputable def e884 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1304321169817,0,true,187814862720,187814862784⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨894702085735,0,false,-226642978048,-226642977984⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1304549071520,0,true,188006961600,188006961664⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨894474184032,0,false,-226923085248,-226923085184⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1304167562660,0,true,187685367936,187685368000⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨894855692892,0,false,-226454224320,-226454224256⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1304446552799,0,true,187920552512,187920552576⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨894576702753,0,false,-226797073664,-226797073600⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564151237,0,true,52522176,52522240⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459104315,0,false,-52524736,-52524672⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590506354,0,true,78875712,78875776⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432749198,0,false,-78881408,-78881344⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622117,0,false,-5696,-5632⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625267,0,false,-2560,-2496⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1304244361705,0,true,187750113408,187750113472⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨894778893847,0,false,-226548591552,-226548591488⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1304497820992,0,true,187963765376,187963765440⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨894525434560,0,false,-226860088512,-226860088448⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1061295261211,0,false,-38896323136,-38896323072⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1061389709569,0,false,-38798478144,-38798478080⟩
    { al := (30519/163840), au := (47739/256000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨204809542041,205037443744⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187814862720,187814862784⟩ : DyadicInterval 40),(⟨-226642978048,-226642977984⟩ : DyadicInterval 40),(⟨742936248459,742936267788⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188006961600,188006961664⟩ : DyadicInterval 40),(⟨-226923085248,-226923085184⟩ : DyadicInterval 40),(⟨742893270558,742893289887⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187685367936,187685368000⟩ : DyadicInterval 40),(⟨-226454224320,-226454224256⟩ : DyadicInterval 40),(⟨742965188234,742965207564⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187920552512,187920552576⟩ : DyadicInterval 40),(⟨-226797073664,-226797073600⟩ : DyadicInterval 40),(⟨742912609648,742912628977⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨52523461,78878578⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52522176,52522240⟩ : DyadicInterval 40),(⟨-52524736,-52524672⟩ : DyadicInterval 40),(⟨762123382322,762123401652⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78875712,78875776⟩ : DyadicInterval 40),(⟨-78881408,-78881344⟩ : DyadicInterval 40),(⟨762123380741,762123400070⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5696,-2496⟩ : DyadicInterval 40),(⟨762123384864,762123405728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨204732733929,204986193216⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187750113408,187750113472⟩ : DyadicInterval 40),(⟨-226548591552,-226548591488⟩ : DyadicInterval 40),(⟨742950721978,742950741308⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187963765376,187963765440⟩ : DyadicInterval 40),(⟨-226860088512,-226860088448⟩ : DyadicInterval 40),(⟨742902939660,742902958990⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38896323136,-38798478080⟩ : DyadicInterval 40),(⟨781522622656,781571564448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨187814862720,188006961664⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-226923085248,-226642977984⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e884_ok : ecellOkT e884 = true := by decide +kernel
theorem e884_pos {a z : ℝ} (ha1 : ((30519/163840 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((47739/256000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e884 e884_ok ha1 ha2 hz1 hz2 hz

-- box ['190107/1024000', '761277/4096000', '1999/2000', '3999/4000']  interval_lower 216235367/1099511627776
noncomputable def e885 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1303637464711,0,true,187238364544,187238364608⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨895385790841,0,false,-225803084352,-225803084288⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1303865366414,0,true,187430564160,187430564224⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨895157889138,0,false,-226082977664,-226082977600⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1303535401792,0,true,187152279424,187152279488⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨895487853760,0,false,-225677760768,-225677760704⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1303814277980,0,true,187387481920,187387481984⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨895208977572,0,false,-226020228096,-226020228032⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537797350,0,true,26169216,26169280⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485458202,0,false,-26169920,-26169856⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564029491,0,true,52400448,52400512⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459226061,0,false,-52403008,-52402944⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625278,0,false,-2560,-2496⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627154,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1303586428327,0,true,187195318656,187195318720⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨895436827225,0,false,-225740414720,-225740414656⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1303839830782,0,true,187409030528,187409030592⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨895183424770,0,false,-226051612992,-226051612928⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1061540210749,0,false,-38642582464,-38642582400⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1061634334651,0,false,-38545096064,-38545096000⟩
    { al := (190107/1024000), au := (761277/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨204125836935,204353738638⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187238364544,187238364608⟩ : DyadicInterval 40),(⟨-225803084352,-225803084288⟩ : DyadicInterval 40),(⟨743064888609,743064907938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187430564160,187430564224⟩ : DyadicInterval 40),(⟨-226082977664,-226082977600⟩ : DyadicInterval 40),(⟨743022057518,743022076847⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187152279424,187152279488⟩ : DyadicInterval 40),(⟨-225677760768,-225677760704⟩ : DyadicInterval 40),(⟨743084054150,743084073480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187387481920,187387481984⟩ : DyadicInterval 40),(⟨-226020228096,-226020228032⟩ : DyadicInterval 40),(⟨743031663156,743031682485⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨26169574,52401715⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26169216,26169280⟩ : DyadicInterval 40),(⟨-26169920,-26169856⟩ : DyadicInterval 40),(⟨762123383281,762123402610⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52400448,52400512⟩ : DyadicInterval 40),(⟨-52403008,-52402944⟩ : DyadicInterval 40),(⟨762123382334,762123401663⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2560,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨204074800551,204328203006⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187195318656,187195318720⟩ : DyadicInterval 40),(⟨-225740414720,-225740414656⟩ : DyadicInterval 40),(⟨743074473537,743074492867⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187409030528,187409030592⟩ : DyadicInterval 40),(⟨-226051612992,-226051612928⟩ : DyadicInterval 40),(⟨743026859014,743026878344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38642582464,-38545096000⟩ : DyadicInterval 40),(⟨781395931616,781444694112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨187238364544,187430564224⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-226082977664,-225803084288⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e885_ok : ecellOkT e885 = true := by decide +kernel
theorem e885_pos {a z : ℝ} (ha1 : ((190107/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((761277/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e885 e885_ok ha1 ha2 hz1 hz2 hz

-- box ['761277/4096000', '381063/2048000', '1999/2000', '3999/4000']  interval_lower 219778445/1099511627776
noncomputable def e886 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1303865366413,0,true,187430564160,187430564224⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨895157889139,0,false,-226082977664,-226082977600⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1304093268116,0,true,187622730240,187622730304⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨894929987436,0,false,-226362942208,-226362942144⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1303763189543,0,true,187344398016,187344398080⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨895260066009,0,false,-225957482176,-225957482112⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1304042122707,0,true,187579607488,187579607552⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨894981132845,0,false,-226300106688,-226300106624⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537828077,0,true,26199936,26200000⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485427475,0,false,-26200640,-26200576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564090958,0,true,52461888,52461952⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459164594,0,false,-52464448,-52464384⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625272,0,false,-2560,-2496⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627152,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1303814273045,0,true,187387477760,187387477824⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨895208982507,0,false,-226020222080,-226020222016⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1304067704000,0,true,187601176320,187601176384⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨894955551552,0,false,-226331534528,-226331534464⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1061455469693,0,false,-38730358208,-38730358144⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1061549709221,0,false,-38632744256,-38632744192⟩
    { al := (761277/4096000), au := (381063/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨204353738637,204581640340⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187430564160,187430564224⟩ : DyadicInterval 40),(⟨-226082977664,-226082977600⟩ : DyadicInterval 40),(⟨743022057518,743022076847⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187622730240,187622730304⟩ : DyadicInterval 40),(⟨-226362942208,-226362942144⟩ : DyadicInterval 40),(⟨742979177450,742979196779⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187344398016,187344398080⟩ : DyadicInterval 40),(⟨-225957482176,-225957482112⟩ : DyadicInterval 40),(⟨743041266349,743041285679⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187579607488,187579607552⟩ : DyadicInterval 40),(⟨-226300106688,-226300106624⟩ : DyadicInterval 40),(⟨742988804791,742988824121⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨26200301,52463182⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26199936,26200000⟩ : DyadicInterval 40),(⟨-26200640,-26200576⟩ : DyadicInterval 40),(⟨762123383279,762123402608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52461888,52461952⟩ : DyadicInterval 40),(⟨-52464448,-52464384⟩ : DyadicInterval 40),(⟨762123382328,762123401657⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2560,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨204302645269,204556076224⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187387477760,187387477824⟩ : DyadicInterval 40),(⟨-226020222080,-226020222016⟩ : DyadicInterval 40),(⟨743031664101,743031683431⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187601176320,187601176384⟩ : DyadicInterval 40),(⟨-226331534528,-226331534464⟩ : DyadicInterval 40),(⟨742983989801,742984009130⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38730358208,-38632744192⟩ : DyadicInterval 40),(⟨781439755712,781488581984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨187430564160,187622730304⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-226362942208,-226082977600⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e886_ok : ecellOkT e886 = true := by decide +kernel
theorem e886_pos {a z : ℝ} (ha1 : ((761277/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((381063/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e886 e886_ok ha1 ha2 hz1 hz2 hz

-- box ['190107/1024000', '761277/4096000', '3999/4000', '1']  interval_lower 215566069/1099511627776
noncomputable def e887 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1303637464711,0,true,187238364544,187238364608⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨895385790841,0,false,-225803084352,-225803084288⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1303865366414,0,true,187430564160,187430564224⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨895157889138,0,false,-226082977664,-226082977600⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1303586433251,0,true,187195322816,187195322880⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨895436822301,0,false,-225740420736,-225740420672⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537828932,0,true,26200832,26200896⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485426620,0,false,-26201472,-26201408⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627151,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1303611943818,0,true,187216839488,187216839552⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨895411311734,0,false,-225771745792,-225771745728⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1303865374917,0,true,187430571328,187430571392⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨895157880635,0,false,-226082988096,-226082988032⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1061530716146,0,false,-38652416704,-38652416640⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1061624862456,0,false,-38554906240,-38554906176⟩
    { al := (190107/1024000), au := (761277/4096000), zl := (3999/4000), zu := 1,
      A := ⟨204125836935,204353738638⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187238364544,187238364608⟩ : DyadicInterval 40),(⟨-225803084352,-225803084288⟩ : DyadicInterval 40),(⟨743064888609,743064907938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187430564160,187430564224⟩ : DyadicInterval 40),(⟨-226082977664,-226082977600⟩ : DyadicInterval 40),(⟨743022057518,743022076847⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187195322816,187195322880⟩ : DyadicInterval 40),(⟨-225740420736,-225740420672⟩ : DyadicInterval 40),(⟨743074472597,743074491926⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187430564160,187430564224⟩ : DyadicInterval 40),(⟨-226082977664,-226082977600⟩ : DyadicInterval 40),(⟨743022057518,743022076847⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,26201156⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26200832,26200896⟩ : DyadicInterval 40),(⟨-26201472,-26201408⟩ : DyadicInterval 40),(⟨762123383247,762123402576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨204100316042,204353747141⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187216839488,187216839552⟩ : DyadicInterval 40),(⟨-225771745792,-225771745728⟩ : DyadicInterval 40),(⟨743069681921,743069701251⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187430571328,187430571392⟩ : DyadicInterval 40),(⟨-226082988096,-226082988032⟩ : DyadicInterval 40),(⟨743022055915,743022075244⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38652416704,-38554906176⟩ : DyadicInterval 40),(⟨781400836704,781449611232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨187238364544,187430564224⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-226082977664,-225803084288⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e887_ok : ecellOkT e887 = true := by decide +kernel
theorem e887_pos {a z : ℝ} (ha1 : ((190107/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((761277/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e887 e887_ok ha1 ha2 hz1 hz2 hz

-- box ['761277/4096000', '381063/2048000', '3999/4000', '1']  interval_lower 219106729/1099511627776
noncomputable def e888 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1303865366413,0,true,187430564160,187430564224⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨895157889139,0,false,-226082977664,-226082977600⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1304093268116,0,true,187622730240,187622730304⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨894929987436,0,false,-226362942208,-226362942144⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1303814277978,0,true,187387481920,187387481984⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨895208977574,0,false,-226020228096,-226020228032⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537859666,0,true,26231552,26231616⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485395886,0,false,-26232256,-26232192⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627150,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1303839817020,0,true,187409018880,187409018944⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨895183438532,0,false,-226051596096,-226051596032⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1304093276623,0,true,187622737408,187622737472⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨894929978929,0,false,-226362952640,-226362952576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1061445953900,0,false,-38740215232,-38740215168⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1061540215865,0,false,-38642577152,-38642577088⟩
    { al := (761277/4096000), au := (381063/2048000), zl := (3999/4000), zu := 1,
      A := ⟨204353738637,204581640340⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187430564160,187430564224⟩ : DyadicInterval 40),(⟨-226082977664,-226082977600⟩ : DyadicInterval 40),(⟨743022057518,743022076847⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187622730240,187622730304⟩ : DyadicInterval 40),(⟨-226362942208,-226362942144⟩ : DyadicInterval 40),(⟨742979177450,742979196779⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187387481920,187387481984⟩ : DyadicInterval 40),(⟨-226020228096,-226020228032⟩ : DyadicInterval 40),(⟨743031663157,743031682486⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187622730240,187622730304⟩ : DyadicInterval 40),(⟨-226362942208,-226362942144⟩ : DyadicInterval 40),(⟨742979177450,742979196779⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,26231890⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26231552,26231616⟩ : DyadicInterval 40),(⟨-26232256,-26232192⟩ : DyadicInterval 40),(⟨762123383278,762123402607⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨204328189244,204581648847⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187409018880,187409018944⟩ : DyadicInterval 40),(⟨-226051596096,-226051596032⟩ : DyadicInterval 40),(⟨743026861630,743026880959⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187622737408,187622737472⟩ : DyadicInterval 40),(⟨-226362952640,-226362952576⟩ : DyadicInterval 40),(⟨742979175843,742979195173⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38740215232,-38642577088⟩ : DyadicInterval 40),(⟨781444672160,781493510496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨187430564160,187622730304⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-226362942208,-226082977600⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e888_ok : ecellOkT e888 = true := by decide +kernel
theorem e888_pos {a z : ℝ} (ha1 : ((761277/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((381063/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e888 e888_ok ha1 ha2 hz1 hz2 hz

-- box ['381063/2048000', '30519/163840', '1999/2000', '3999/4000']  interval_lower 111668903/549755813888
noncomputable def e889 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1304093268115,0,true,187622730240,187622730304⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨894929987437,0,false,-226362942208,-226362942144⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1304321169818,0,true,187814862720,187814862784⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨894702085734,0,false,-226642978048,-226642977984⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1303990977294,0,true,187536483072,187536483136⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨895032278258,0,false,-226237274816,-226237274752⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1304269967433,0,true,187771699456,187771699520⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨894753288119,0,false,-226580056512,-226580056448⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537858809,0,true,26230720,26230784⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485396743,0,false,-26231360,-26231296⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564152435,0,true,52523392,52523456⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459103117,0,false,-52525952,-52525888⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625266,0,false,-2560,-2496⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627151,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1304042117768,0,true,187579603328,187579603392⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨894981137784,0,false,-226300100608,-226300100544⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1304295577214,0,true,187793288576,187793288640⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨894727678338,0,false,-226611527360,-226611527296⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1061370634185,0,false,-38818238784,-38818238720⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1061464989360,0,false,-38720497280,-38720497216⟩
    { al := (381063/2048000), au := (30519/163840), zl := (1999/2000), zu := (3999/4000),
      A := ⟨204581640339,204809542042⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187622730240,187622730304⟩ : DyadicInterval 40),(⟨-226362942208,-226362942144⟩ : DyadicInterval 40),(⟨742979177450,742979196780⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187814862720,187814862784⟩ : DyadicInterval 40),(⟨-226642978048,-226642977984⟩ : DyadicInterval 40),(⟨742936248459,742936267788⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187536483072,187536483136⟩ : DyadicInterval 40),(⟨-226237274816,-226237274752⟩ : DyadicInterval 40),(⟨742998429675,742998449005⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187771699456,187771699520⟩ : DyadicInterval 40),(⟨-226580056512,-226580056448⟩ : DyadicInterval 40),(⟨742945897528,742945916858⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨26231033,52524659⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26230720,26230784⟩ : DyadicInterval 40),(⟨-26231360,-26231296⟩ : DyadicInterval 40),(⟨762123383246,762123402575⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52523392,52523456⟩ : DyadicInterval 40),(⟨-52525952,-52525888⟩ : DyadicInterval 40),(⟨762123382322,762123401651⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2560,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨204530489992,204783949438⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187579603328,187579603392⟩ : DyadicInterval 40),(⟨-226300100608,-226300100544⟩ : DyadicInterval 40),(⟨742988805713,742988825043⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187793288576,187793288640⟩ : DyadicInterval 40),(⟨-226611527360,-226611527296⟩ : DyadicInterval 40),(⟨742941071652,742941090982⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38818238784,-38720497216⟩ : DyadicInterval 40),(⟨781483632224,781532522272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨187622730240,187814862784⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-226642978048,-226362942144⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e889_ok : ecellOkT e889 = true := by decide +kernel
theorem e889_pos {a z : ℝ} (ha1 : ((381063/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((30519/163840 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e889 e889_ok ha1 ha2 hz1 hz2 hz

-- box ['30519/163840', '47739/256000', '1999/2000', '3999/4000']  interval_lower 226913063/1099511627776
noncomputable def e890 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1304321169817,0,true,187814862720,187814862784⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨894702085735,0,false,-226642978048,-226642977984⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1304549071520,0,true,188006961600,188006961664⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨894474184032,0,false,-226923085248,-226923085184⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1304218765045,0,true,187728534528,187728534592⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨894804490507,0,false,-226517138624,-226517138560⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1304497812160,0,true,187963757888,187963757952⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨894525443392,0,false,-226860077632,-226860077568⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537889548,0,true,26261440,26261504⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485366004,0,false,-26262144,-26262080⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564213922,0,true,52584832,52584896⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459041630,0,false,-52587456,-52587392⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625260,0,false,-2560,-2496⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627149,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1304269962490,0,true,187771695296,187771695360⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨894753293062,0,false,-226580050432,-226580050368⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1304523450426,0,true,187985367232,187985367296⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨894499805126,0,false,-226891591552,-226891591488⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1061285704225,0,false,-38906224320,-38906224256⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1061380175070,0,false,-38808355136,-38808355072⟩
    { al := (30519/163840), au := (47739/256000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨204809542041,205037443744⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187814862720,187814862784⟩ : DyadicInterval 40),(⟨-226642978048,-226642977984⟩ : DyadicInterval 40),(⟨742936248459,742936267788⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188006961600,188006961664⟩ : DyadicInterval 40),(⟨-226923085248,-226923085184⟩ : DyadicInterval 40),(⟨742893270558,742893289887⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187728534528,187728534592⟩ : DyadicInterval 40),(⟨-226517138624,-226517138560⟩ : DyadicInterval 40),(⟨742955544129,742955563458⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187963757888,187963757952⟩ : DyadicInterval 40),(⟨-226860077632,-226860077568⟩ : DyadicInterval 40),(⟨742902941343,742902960672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨26261772,52586146⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26261440,26261504⟩ : DyadicInterval 40),(⟨-26262144,-26262080⟩ : DyadicInterval 40),(⟨762123383276,762123402605⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52584832,52584896⟩ : DyadicInterval 40),(⟨-52587456,-52587392⟩ : DyadicInterval 40),(⟨762123382348,762123401678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2560,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨204758334714,205011822650⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187771695296,187771695360⟩ : DyadicInterval 40),(⟨-226580050432,-226580050368⟩ : DyadicInterval 40),(⟨742945898453,742945917783⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187985367232,187985367296⟩ : DyadicInterval 40),(⟨-226891591552,-226891591488⟩ : DyadicInterval 40),(⟨742898104621,742898123950⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38906224320,-38808355072⟩ : DyadicInterval 40),(⟨781527561152,781576515040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨187814862720,188006961664⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-226923085248,-226642977984⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e890_ok : ecellOkT e890 = true := by decide +kernel
theorem e890_pos {a z : ℝ} (ha1 : ((30519/163840 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((47739/256000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e890 e890_ok ha1 ha2 hz1 hz2 hz

-- box ['381063/2048000', '30519/163840', '3999/4000', '1']  interval_lower 55665859/274877906944
noncomputable def e891 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1304093268115,0,true,187622730240,187622730304⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨894929987437,0,false,-226362942208,-226362942144⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1304321169818,0,true,187814862720,187814862784⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨894702085734,0,false,-226642978048,-226642977984⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1304042122704,0,true,187579607488,187579607552⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨894981132848,0,false,-226300106688,-226300106624⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537890405,0,true,26262272,26262336⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485365147,0,false,-26262976,-26262912⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627148,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1304067690231,0,true,187601164736,187601164800⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨894955565321,0,false,-226331517632,-226331517568⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1304321178326,0,true,187814869888,187814869952⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨894702077226,0,false,-226642988480,-226642988416⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1061361097179,0,false,-38828118592,-38828118528⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1061455474817,0,false,-38730352896,-38730352832⟩
    { al := (381063/2048000), au := (30519/163840), zl := (3999/4000), zu := 1,
      A := ⟨204581640339,204809542042⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187622730240,187622730304⟩ : DyadicInterval 40),(⟨-226362942208,-226362942144⟩ : DyadicInterval 40),(⟨742979177450,742979196780⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187814862720,187814862784⟩ : DyadicInterval 40),(⟨-226642978048,-226642977984⟩ : DyadicInterval 40),(⟨742936248459,742936267788⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187579607488,187579607552⟩ : DyadicInterval 40),(⟨-226300106688,-226300106624⟩ : DyadicInterval 40),(⟨742988804792,742988824121⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187814862720,187814862784⟩ : DyadicInterval 40),(⟨-226642978048,-226642977984⟩ : DyadicInterval 40),(⟨742936248459,742936267788⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,26262629⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26262272,26262336⟩ : DyadicInterval 40),(⟨-26262976,-26262912⟩ : DyadicInterval 40),(⟨762123383276,762123402605⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨204556062455,204809550550⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187601164736,187601164800⟩ : DyadicInterval 40),(⟨-226331517632,-226331517568⟩ : DyadicInterval 40),(⟨742983992386,742984011715⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187814869888,187814869952⟩ : DyadicInterval 40),(⟨-226642988480,-226642988416⟩ : DyadicInterval 40),(⟨742936246848,742936266178⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38828118592,-38730352832⟩ : DyadicInterval 40),(⟨781488560032,781537462176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨187622730240,187814862784⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-226642978048,-226362942144⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e891_ok : ecellOkT e891 = true := by decide +kernel
theorem e891_pos {a z : ℝ} (ha1 : ((381063/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((30519/163840 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e891 e891_ok ha1 ha2 hz1 hz2 hz

-- box ['30519/163840', '47739/256000', '3999/4000', '1']  interval_lower 56558921/274877906944
noncomputable def e892 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1304321169817,0,true,187814862720,187814862784⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨894702085735,0,false,-226642978048,-226642977984⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1304549071520,0,true,188006961600,188006961664⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨894474184032,0,false,-226923085248,-226923085184⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1304269967431,0,true,187771699456,187771699520⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨894753288121,0,false,-226580056512,-226580056448⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537921149,0,true,26293056,26293120⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485334403,0,false,-26293696,-26293632⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627147,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1304295563442,0,true,187793276928,187793276992⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨894727692110,0,false,-226611510464,-226611510400⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1304549080022,0,true,188006968768,188006968832⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨894474175530,0,false,-226923095680,-226923095616⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1061276145984,0,false,-38916126848,-38916126784⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1061370639316,0,false,-38818233472,-38818233408⟩
    { al := (30519/163840), au := (47739/256000), zl := (3999/4000), zu := 1,
      A := ⟨204809542041,205037443744⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187814862720,187814862784⟩ : DyadicInterval 40),(⟨-226642978048,-226642977984⟩ : DyadicInterval 40),(⟨742936248459,742936267788⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188006961600,188006961664⟩ : DyadicInterval 40),(⟨-226923085248,-226923085184⟩ : DyadicInterval 40),(⟨742893270558,742893289887⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187771699456,187771699520⟩ : DyadicInterval 40),(⟨-226580056512,-226580056448⟩ : DyadicInterval 40),(⟨742945897528,742945916858⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188006961600,188006961664⟩ : DyadicInterval 40),(⟨-226923085248,-226923085184⟩ : DyadicInterval 40),(⟨742893270558,742893289887⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,26293373⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26293056,26293120⟩ : DyadicInterval 40),(⟨-26293696,-26293632⟩ : DyadicInterval 40),(⟨762123383243,762123402572⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨204783935666,205037452246⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187793276928,187793276992⟩ : DyadicInterval 40),(⟨-226611510464,-226611510400⟩ : DyadicInterval 40),(⟨742941074282,742941093612⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188006968768,188006968832⟩ : DyadicInterval 40),(⟨-226923095680,-226923095616⟩ : DyadicInterval 40),(⟨742893268945,742893288274⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38916126848,-38818233408⟩ : DyadicInterval 40),(⟨781532500320,781581466304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨187814862720,188006961664⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-226923085248,-226642977984⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e892_ok : ecellOkT e892 = true := by decide +kernel
theorem e892_pos {a z : ℝ} (ha1 : ((30519/163840 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((47739/256000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e892 e892_ok ha1 ha2 hz1 hz2 hz

-- box ['47739/256000', '764673/4096000', '999/1000', '3997/4000']  interval_lower 231862183/1099511627776
noncomputable def e893 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1304549071519,0,true,188006961600,188006961664⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨894474184033,0,false,-226923085248,-226923085184⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1304776973222,0,true,188199027008,188199027072⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨894246282330,0,false,-227203263808,-227203263744⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1304344034075,0,true,187834136576,187834136640⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨894679221477,0,false,-226671076608,-226671076544⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1304623024214,0,true,188069289344,188069289408⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨894400231338,0,false,-227013993600,-227013993536⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590504811,0,true,78874176,78874240⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432750741,0,false,-78879872,-78879808⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099616921435,0,true,105288576,105288640⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099406334117,0,false,-105298752,-105298688⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511617692,0,false,-10112,-10048⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622118,0,false,-5696,-5632⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1304446548826,0,true,187920549120,187920549184⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨894576706726,0,false,-226797068800,-226797068736⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1304700007963,0,true,188134167872,188134167936⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨894323247589,0,false,-227108636032,-227108635968⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1061219835038,0,false,-38974468096,-38974468032⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1061314376556,0,false,-38876519616,-38876519552⟩
    { al := (47739/256000), au := (764673/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨205037443743,205265345446⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188006961600,188006961664⟩ : DyadicInterval 40),(⟨-226923085248,-226923085184⟩ : DyadicInterval 40),(⟨742893270558,742893289887⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188199027008,188199027072⟩ : DyadicInterval 40),(⟨-227203263808,-227203263744⟩ : DyadicInterval 40),(⟨742850243660,742850262989⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187834136576,187834136640⟩ : DyadicInterval 40),(⟨-226671076608,-226671076544⟩ : DyadicInterval 40),(⟨742931938904,742931958233⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188069289344,188069289408⟩ : DyadicInterval 40),(⟨-227013993600,-227013993536⟩ : DyadicInterval 40),(⟨742879313928,742879333257⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨78877035,105293659⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78874176,78874240⟩ : DyadicInterval 40),(⟨-78879872,-78879808⟩ : DyadicInterval 40),(⟨762123380741,762123400070⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨105288576,105288640⟩ : DyadicInterval 40),(⟨-105298752,-105298688⟩ : DyadicInterval 40),(⟨762123378556,762123397886⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-10112,-5632⟩ : DyadicInterval 40),(⟨762123386432,762123407936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨204934921050,205188380187⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187920549120,187920549184⟩ : DyadicInterval 40),(⟨-226797068800,-226797068736⟩ : DyadicInterval 40),(⟨742912610430,742912629760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188134167872,188134167936⟩ : DyadicInterval 40),(⟨-227108636032,-227108635968⟩ : DyadicInterval 40),(⟨742864779859,742864799188⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38974468096,-38876519552⟩ : DyadicInterval 40),(⟨781561643392,781610636928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨188006961600,188199027072⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-227203263808,-226923085184⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e893_ok : ecellOkT e893 = true := by decide +kernel
theorem e893_pos {a z : ℝ} (ha1 : ((47739/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((764673/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e893 e893_ok ha1 ha2 hz1 hz2 hz

-- box ['764673/4096000', '382761/2048000', '999/1000', '3997/4000']  interval_lower 58868711/274877906944
noncomputable def e894 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1304776973221,0,true,188199027008,188199027072⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨894246282331,0,false,-227203263808,-227203263744⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1305004874925,0,true,188391058816,188391058880⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨894018380627,0,false,-227483513792,-227483513728⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1304571707875,0,true,188026040064,188026040128⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨894451547677,0,false,-226950910784,-226950910720⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1304850754990,0,true,188261199744,188261199808⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨894172500562,0,false,-227293985216,-227293985152⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590597053,0,true,78966400,78966464⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432658499,0,false,-78972160,-78972096⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099617044448,0,true,105411584,105411648⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099406211104,0,false,-105421760,-105421696⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511617669,0,false,-10112,-10048⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622105,0,false,-5696,-5632⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1304674336584,0,true,188112533568,188112533632⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨894348918968,0,false,-227077075200,-227077075136⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1304927824199,0,true,188326139008,188326139072⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨894095431353,0,false,-227388756800,-227388756736⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1061134758730,0,false,-39062617728,-39062617664⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1061229415909,0,false,-38964541568,-38964541504⟩
    { al := (764673/4096000), au := (382761/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨205265345445,205493247149⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188199027008,188199027072⟩ : DyadicInterval 40),(⟨-227203263808,-227203263744⟩ : DyadicInterval 40),(⟨742850243660,742850262989⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188391058816,188391058880⟩ : DyadicInterval 40),(⟨-227483513792,-227483513728⟩ : DyadicInterval 40),(⟨742807167854,742807187183⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188026040064,188026040128⟩ : DyadicInterval 40),(⟨-226950910784,-226950910720⟩ : DyadicInterval 40),(⟨742888999055,742889018384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188261199744,188261199808⟩ : DyadicInterval 40),(⟨-227293985216,-227293985152⟩ : DyadicInterval 40),(⟨742836303530,742836322860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨78969277,105416672⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78966400,78966464⟩ : DyadicInterval 40),(⟨-78972160,-78972096⟩ : DyadicInterval 40),(⟨762123380760,762123400089⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨105411584,105411648⟩ : DyadicInterval 40),(⟨-105421760,-105421696⟩ : DyadicInterval 40),(⟨762123378532,762123397862⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-10112,-5632⟩ : DyadicInterval 40),(⟨762123386432,762123407936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨205162708808,205416196423⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188112533568,188112533632⟩ : DyadicInterval 40),(⟨-227077075200,-227077075136⟩ : DyadicInterval 40),(⟨742869627093,742869646423⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188326139008,188326139072⟩ : DyadicInterval 40),(⟨-227388756800,-227388756736⟩ : DyadicInterval 40),(⟨742821736735,742821756065⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39062617728,-38964541504⟩ : DyadicInterval 40),(⟨781605654368,781654711744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨188199027008,188391058880⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-227483513792,-227203263744⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e894_ok : ecellOkT e894 = true := by decide +kernel
theorem e894_pos {a z : ℝ} (ha1 : ((764673/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((382761/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e894 e894_ok ha1 ha2 hz1 hz2 hz

-- box ['47739/256000', '764673/4096000', '3997/4000', '1999/2000']  interval_lower 14448977/68719476736
noncomputable def e895 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1304549071519,0,true,188006961600,188006961664⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨894474184033,0,false,-226923085248,-226923085184⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1304776973222,0,true,188199027008,188199027072⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨894246282330,0,false,-227203263808,-227203263744⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1304395293436,0,true,187877345408,187877345472⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨894627962116,0,false,-226734073344,-226734073280⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1304674340550,0,true,188112536896,188112536960⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨894348915002,0,false,-227077080064,-227077080000⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564212722,0,true,52583680,52583744⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459042830,0,false,-52586240,-52586176⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590598600,0,true,78967936,78968000⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432656952,0,false,-78973696,-78973632⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622104,0,false,-5696,-5632⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625262,0,false,-2560,-2496⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1304472177940,0,true,187942151616,187942151680⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨894551077612,0,false,-226828569664,-226828569600⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1304725665720,0,true,188155790272,188155790336⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨894297589832,0,false,-227140180992,-227140180928⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1061210258053,0,false,-38984390720,-38984390656⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1061304822080,0,false,-38886418048,-38886417984⟩
    { al := (47739/256000), au := (764673/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨205037443743,205265345446⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188006961600,188006961664⟩ : DyadicInterval 40),(⟨-226923085248,-226923085184⟩ : DyadicInterval 40),(⟨742893270558,742893289887⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188199027008,188199027072⟩ : DyadicInterval 40),(⟨-227203263808,-227203263744⟩ : DyadicInterval 40),(⟨742850243660,742850262989⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187877345408,187877345472⟩ : DyadicInterval 40),(⟨-226734073344,-226734073280⟩ : DyadicInterval 40),(⟨742922275510,742922294839⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188112536896,188112536960⟩ : DyadicInterval 40),(⟨-227077080064,-227077080000⟩ : DyadicInterval 40),(⟨742869626348,742869645677⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨52584946,78970824⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52583680,52583744⟩ : DyadicInterval 40),(⟨-52586240,-52586176⟩ : DyadicInterval 40),(⟨762123382317,762123401646⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨78967936,78968000⟩ : DyadicInterval 40),(⟨-78973696,-78973632⟩ : DyadicInterval 40),(⟨762123380759,762123400089⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5696,-2496⟩ : DyadicInterval 40),(⟨762123384864,762123405728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨204960550164,205214037944⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187942151616,187942151680⟩ : DyadicInterval 40),(⟨-226828569664,-226828569600⟩ : DyadicInterval 40),(⟨742907776662,742907795992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188155790272,188155790336⟩ : DyadicInterval 40),(⟨-227140180992,-227140180928⟩ : DyadicInterval 40),(⟨742859934563,742859953893⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38984390720,-38886417984⟩ : DyadicInterval 40),(⟨781566592608,781615598240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨188006961600,188199027072⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-227203263808,-226923085184⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e895_ok : ecellOkT e895 = true := by decide +kernel
theorem e895_pos {a z : ℝ} (ha1 : ((47739/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((764673/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e895 e895_ok ha1 ha2 hz1 hz2 hz

-- box ['764673/4096000', '382761/2048000', '3997/4000', '1999/2000']  interval_lower 234793367/1099511627776
noncomputable def e896 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1304776973221,0,true,188199027008,188199027072⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨894246282331,0,false,-227203263808,-227203263744⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1305004874925,0,true,188391058816,188391058880⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨894018380627,0,false,-227483513792,-227483513728⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1304623024211,0,true,188069289344,188069289408⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨894400231341,0,false,-227013993600,-227013993536⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1304902128302,0,true,188304487808,188304487872⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨894121127250,0,false,-227357157760,-227357157696⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564274219,0,true,52645120,52645184⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458981333,0,false,-52647744,-52647680⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590690861,0,true,79060224,79060288⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432564691,0,false,-79065984,-79065920⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622090,0,false,-5696,-5632⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625256,0,false,-2560,-2496⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1304699994181,0,true,188134156224,188134156288⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨894323261371,0,false,-227108619072,-227108619008⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1304953510449,0,true,188347781632,188347781696⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨894069745103,0,false,-227420344832,-227420344768⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1061125160466,0,false,-39072563200,-39072563136⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1061219840182,0,false,-38974462784,-38974462720⟩
    { al := (764673/4096000), au := (382761/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨205265345445,205493247149⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188199027008,188199027072⟩ : DyadicInterval 40),(⟨-227203263808,-227203263744⟩ : DyadicInterval 40),(⟨742850243660,742850262989⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188391058816,188391058880⟩ : DyadicInterval 40),(⟨-227483513792,-227483513728⟩ : DyadicInterval 40),(⟨742807167854,742807187183⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188069289344,188069289408⟩ : DyadicInterval 40),(⟨-227013993600,-227013993536⟩ : DyadicInterval 40),(⟨742879313929,742879333258⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188304487808,188304487872⟩ : DyadicInterval 40),(⟨-227357157760,-227357157696⟩ : DyadicInterval 40),(⟨742826594116,742826613446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨52646443,79063085⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52645120,52645184⟩ : DyadicInterval 40),(⟨-52647744,-52647680⟩ : DyadicInterval 40),(⟨762123382343,762123401672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79060224,79060288⟩ : DyadicInterval 40),(⟨-79065984,-79065920⟩ : DyadicInterval 40),(⟨762123380746,762123400075⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5696,-2496⟩ : DyadicInterval 40),(⟨762123384864,762123405728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨205188366405,205441882673⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188134156224,188134156288⟩ : DyadicInterval 40),(⟨-227108619072,-227108619008⟩ : DyadicInterval 40),(⟨742864782474,742864801804⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188347781632,188347781696⟩ : DyadicInterval 40),(⟨-227420344832,-227420344768⟩ : DyadicInterval 40),(⟨742816880547,742816899876⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39072563200,-38974462720⟩ : DyadicInterval 40),(⟨781610614976,781659684480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨188199027008,188391058880⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-227483513792,-227203263744⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e896_ok : ecellOkT e896 = true := by decide +kernel
theorem e896_pos {a z : ℝ} (ha1 : ((764673/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((382761/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e896 e896_ok ha1 ha2 hz1 hz2 hz

-- box ['382761/2048000', '766371/4096000', '999/1000', '3997/4000']  interval_lower 119551713/549755813888
noncomputable def e897 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1305004874924,0,true,188391058816,188391058880⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨894018380628,0,false,-227483513792,-227483513728⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1305232776627,0,true,188583057088,188583057152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨893790478925,0,false,-227763835200,-227763835136⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1304799381676,0,true,188217910016,188217910080⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨894223873876,0,false,-227230816256,-227230816192⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1305078485766,0,true,188453076736,188453076800⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨893944769786,0,false,-227574048064,-227574048000⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590689311,0,true,79058688,79058752⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432566241,0,false,-79064384,-79064320⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099617167482,0,true,105534592,105534656⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099406088070,0,false,-105544832,-105544768⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511617645,0,false,-10176,-10112⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622091,0,false,-5696,-5632⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1304902124331,0,true,188304484480,188304484544⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨894121131221,0,false,-227357152896,-227357152832⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1305155640446,0,true,188518076608,188518076672⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨893867615106,0,false,-227668948928,-227668948864⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1061049588013,0,false,-39150872256,-39150872192⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1061144360883,0,false,-39052668352,-39052668288⟩
    { al := (382761/2048000), au := (766371/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨205493247148,205721148851⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188391058816,188391058880⟩ : DyadicInterval 40),(⟨-227483513792,-227483513728⟩ : DyadicInterval 40),(⟨742807167854,742807187184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188583057088,188583057152⟩ : DyadicInterval 40),(⟨-227763835200,-227763835136⟩ : DyadicInterval 40),(⟨742764043092,742764062421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188217910016,188217910080⟩ : DyadicInterval 40),(⟨-227230816256,-227230816192⟩ : DyadicInterval 40),(⟨742846010415,742846029744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188453076736,188453076800⟩ : DyadicInterval 40),(⟨-227574048064,-227574048000⟩ : DyadicInterval 40),(⟨742793244176,742793263506⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨79061535,105539706⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79058688,79058752⟩ : DyadicInterval 40),(⟨-79064384,-79064320⟩ : DyadicInterval 40),(⟨762123380714,762123400044⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨105534592,105534656⟩ : DyadicInterval 40),(⟨-105544832,-105544768⟩ : DyadicInterval 40),(⟨762123378540,762123397870⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-10176,-5632⟩ : DyadicInterval 40),(⟨762123386432,762123407968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨205390496555,205644012670⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188304484480,188304484544⟩ : DyadicInterval 40),(⟨-227357152896,-227357152832⟩ : DyadicInterval 40),(⟨742826594864,742826614194⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188518076608,188518076672⟩ : DyadicInterval 40),(⟨-227668948928,-227668948864⟩ : DyadicInterval 40),(⟨742778644704,742778664033⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39150872256,-39052668288⟩ : DyadicInterval 40),(⟨781649717760,781698839008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨188391058816,188583057152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-227763835200,-227483513728⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e897_ok : ecellOkT e897 = true := by decide +kernel
theorem e897_pos {a z : ℝ} (ha1 : ((382761/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((766371/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e897 e897_ok ha1 ha2 hz1 hz2 hz

-- box ['766371/4096000', '38361/204800', '999/1000', '3997/4000']  interval_lower 121374051/549755813888
noncomputable def e898 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1305232776626,0,true,188583057088,188583057152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨893790478926,0,false,-227763835200,-227763835136⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1305460678329,0,true,188775021824,188775021888⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨893562577223,0,false,-228044228160,-228044228096⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1305027055477,0,true,188409746496,188409746560⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨893996200075,0,false,-227510792960,-227510792896⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1305306216542,0,true,188644920192,188644920256⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨893717039010,0,false,-227854182272,-227854182208⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590781585,0,true,79150912,79150976⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432473967,0,false,-79156672,-79156608⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099617290538,0,true,105657664,105657728⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099405965014,0,false,-105667840,-105667776⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511617621,0,false,-10176,-10112⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622078,0,false,-5760,-5696⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1305129912080,0,true,188496401856,188496401920⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨893893343472,0,false,-227637301952,-227637301888⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1305383456684,0,true,188709980736,188709980800⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨893639798868,0,false,-227949212480,-227949212416⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1060964322893,0,false,-39239231744,-39239231680⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1061059211475,0,false,-39140900032,-39140899968⟩
    { al := (766371/4096000), au := (38361/204800), zl := (999/1000), zu := (3997/4000),
      A := ⟨205721148850,205949050553⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188583057088,188583057152⟩ : DyadicInterval 40),(⟨-227763835200,-227763835136⟩ : DyadicInterval 40),(⟨742764043092,742764062421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188775021824,188775021888⟩ : DyadicInterval 40),(⟨-228044228160,-228044228096⟩ : DyadicInterval 40),(⟨742720869413,742720888742⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188409746496,188409746560⟩ : DyadicInterval 40),(⟨-227510792960,-227510792896⟩ : DyadicInterval 40),(⟨742802972908,742802992238⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188644920192,188644920256⟩ : DyadicInterval 40),(⟨-227854182272,-227854182208⟩ : DyadicInterval 40),(⟨742750135983,742750155312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨79153809,105662762⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79150912,79150976⟩ : DyadicInterval 40),(⟨-79156672,-79156608⟩ : DyadicInterval 40),(⟨762123380733,762123400062⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨105657664,105657728⟩ : DyadicInterval 40),(⟨-105667840,-105667776⟩ : DyadicInterval 40),(⟨762123378485,762123397815⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-10176,-5696⟩ : DyadicInterval 40),(⟨762123386464,762123407968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨205618284304,205871828908⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188496401856,188496401920⟩ : DyadicInterval 40),(⟨-227637301952,-227637301888⟩ : DyadicInterval 40),(⟨742783513755,742783533085⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188709980736,188709980800⟩ : DyadicInterval 40),(⟨-227949212480,-227949212416⟩ : DyadicInterval 40),(⟨742735503744,742735523074⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39239231744,-39140899968⟩ : DyadicInterval 40),(⟨781693833600,781743018752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨188583057088,188775021888⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-228044228160,-227763835136⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e898_ok : ecellOkT e898 = true := by decide +kernel
theorem e898_pos {a z : ℝ} (ha1 : ((766371/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((38361/204800 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e898 e898_ok ha1 ha2 hz1 hz2 hz

-- box ['382761/2048000', '766371/4096000', '3997/4000', '1999/2000']  interval_lower 119209581/549755813888
noncomputable def e899 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1305004874924,0,true,188391058816,188391058880⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨894018380628,0,false,-227483513792,-227483513728⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1305232776627,0,true,188583057088,188583057152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨893790478925,0,false,-227763835200,-227763835136⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1304850754988,0,true,188261199744,188261199808⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨894172500564,0,false,-227293985152,-227293985088⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1305129916053,0,true,188496405248,188496405312⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨893893339499,0,false,-227637306816,-227637306752⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564335724,0,true,52706624,52706688⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458919828,0,false,-52709248,-52709184⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590783138,0,true,79152512,79152576⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432472414,0,false,-79158272,-79158208⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622077,0,false,-5760,-5696⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625250,0,false,-2560,-2496⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1304927810415,0,true,188326127360,188326127424⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨894095445137,0,false,-227388739840,-227388739776⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1305181355181,0,true,188539739456,188539739520⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨893841900371,0,false,-227700580096,-227700580032⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1061039968448,0,false,-39160840576,-39160840512⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1061134763882,0,false,-39062612416,-39062612352⟩
    { al := (382761/2048000), au := (766371/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨205493247148,205721148851⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188391058816,188391058880⟩ : DyadicInterval 40),(⟨-227483513792,-227483513728⟩ : DyadicInterval 40),(⟨742807167854,742807187184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188583057088,188583057152⟩ : DyadicInterval 40),(⟨-227763835200,-227763835136⟩ : DyadicInterval 40),(⟨742764043092,742764062421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188261199744,188261199808⟩ : DyadicInterval 40),(⟨-227293985152,-227293985088⟩ : DyadicInterval 40),(⟨742836303505,742836322834⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188496405248,188496405312⟩ : DyadicInterval 40),(⟨-227637306816,-227637306752⟩ : DyadicInterval 40),(⟨742783512967,742783532297⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨52707948,79155362⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52706624,52706688⟩ : DyadicInterval 40),(⟨-52709248,-52709184⟩ : DyadicInterval 40),(⟨762123382337,762123401666⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79152512,79152576⟩ : DyadicInterval 40),(⟨-79158272,-79158208⟩ : DyadicInterval 40),(⟨762123380733,762123400062⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5760,-2496⟩ : DyadicInterval 40),(⟨762123384864,762123405760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨205416182639,205669727405⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188326127360,188326127424⟩ : DyadicInterval 40),(⟨-227388739840,-227388739776⟩ : DyadicInterval 40),(⟨742821739357,742821758687⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188539739456,188539739520⟩ : DyadicInterval 40),(⟨-227700580096,-227700580032⟩ : DyadicInterval 40),(⟨742773777624,742773796954⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39160840576,-39062612352⟩ : DyadicInterval 40),(⟨781654689792,781703823168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨188391058816,188583057152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-227763835200,-227483513728⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e899_ok : ecellOkT e899 = true := by decide +kernel
theorem e899_pos {a z : ℝ} (ha1 : ((382761/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((766371/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e899 e899_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B014

end


