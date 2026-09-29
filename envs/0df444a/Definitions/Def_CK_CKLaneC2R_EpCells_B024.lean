-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B024
-- name    : CK_CKLaneC2R_EpCells_B024
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:19:47.174681+00:00
-- url     : https://prove2.me/theorems/3854cbe2-262f-4103-a336-e086b82ed653
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B024` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B024` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B024` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B024 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B024.lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheckT

-- ===== source module CKLaneC2R.EpCells.B024 =====
section

namespace CKLaneC2R.EpCells.B024

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['69081/409600', '691659/4096000', '1599/1600', '1999/2000']  interval_lower 1050555/137438953472
noncomputable def e1440 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284949525135,0,true,171362549696,171362549760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914073730417,0,false,-203090957056,-203090956992⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1285177426838,0,true,171557544384,171557544448⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨913845828714,0,false,-203365127296,-203365127232⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1284833626449,0,true,171263372480,171263372544⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨914189629103,0,false,-202951554880,-202951554816⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1285084593939,0,true,171478119936,171478120000⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨913938661613,0,false,-203253439232,-203253439168⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558962267,0,true,47333440,47333504⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464293285,0,false,-47335552,-47335488⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570872425,0,true,59243008,59243072⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452383127,0,false,-59246272,-59246208⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624583,0,false,-3200,-3136⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625739,0,false,-2048,-1984⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1284891571334,0,true,171312958400,171312958464⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨914131684218,0,false,-203021248384,-203021248320⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1285131019110,0,true,171517840320,171517840384⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨913892236442,0,false,-203309292352,-203309292288⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068175389423,0,false,-31791451968,-31791451904⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068256184355,0,false,-31708289984,-31708289920⟩
    { al := (69081/409600), au := (691659/4096000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨185437897359,185665799062⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171362549696,171362549760⟩ : DyadicInterval 40),(⟨-203090957056,-203090956992⟩ : DyadicInterval 40),(⟨746410899365,746410918695⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171557544384,171557544448⟩ : DyadicInterval 40),(⟨-203365127296,-203365127232⟩ : DyadicInterval 40),(⟨746372067565,746372086894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171263372480,171263372544⟩ : DyadicInterval 40),(⟨-202951554880,-202951554816⟩ : DyadicInterval 40),(⟨746430628519,746430647848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171478119936,171478120000⟩ : DyadicInterval 40),(⟨-203253439232,-203253439168⟩ : DyadicInterval 40),(⟨746387891068,746387910398⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨47334491,59244649⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨47333440,47333504⟩ : DyadicInterval 40),(⟨-47335552,-47335488⟩ : DyadicInterval 40),(⟨762123382570,762123401899⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59243008,59243072⟩ : DyadicInterval 40),(⟨-59246272,-59246208⟩ : DyadicInterval 40),(⟨762123381991,762123401320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3200,-1984⟩ : DyadicInterval 40),(⟨762123384608,762123404480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨185379943558,185619391334⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171312958400,171312958464⟩ : DyadicInterval 40),(⟨-203021248384,-203021248320⟩ : DyadicInterval 40),(⟨746420766262,746420785592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171517840320,171517840384⟩ : DyadicInterval 40),(⟨-203309292352,-203309292288⟩ : DyadicInterval 40),(⟨746379978855,746379998184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31791451968,-31708289920⟩ : DyadicInterval 40),(⟨777977528576,778019128864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨171362549696,171557544448⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-203365127296,-203090956992⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1440_ok : ecellOkT e1440 = true := by decide +kernel
theorem e1440_pos {a z : ℝ} (ha1 : ((69081/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((691659/4096000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1440 e1440_ok ha1 ha2 hz1 hz2 hz

-- box ['691659/4096000', '173127/1024000', '3997/4000', '1599/1600']  interval_lower 1388171/137438953472
noncomputable def e1441 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1285177426837,0,true,171557544384,171557544448⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨913845828715,0,false,-203365127296,-203365127232⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1285405328540,0,true,171752504512,171752504576⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨913617927012,0,false,-203639365952,-203639365888⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1285038177487,0,true,171438405504,171438405568⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨913985078065,0,false,-203197599488,-203197599424⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1285289144978,0,true,171653118784,171653118848⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨913734110574,0,false,-203499551424,-203499551360⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570871594,0,true,59242176,59242240⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452383958,0,false,-59245440,-59245376⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582812085,0,true,71181952,71182016⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099440443467,0,false,-71186624,-71186560⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623167,0,false,-4672,-4608⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624584,0,false,-3200,-3136⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1285107797863,0,true,171497972928,171497972992⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨913915457689,0,false,-203281355008,-203281354944⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1285347245613,0,true,171702820352,171702820416⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨913676009939,0,false,-203569467072,-203569467008⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068102340248,0,false,-31866646720,-31866646656⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068183229349,0,false,-31783382080,-31783382016⟩
    { al := (691659/4096000), au := (173127/1024000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨185665799061,185893700764⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171557544384,171557544448⟩ : DyadicInterval 40),(⟨-203365127296,-203365127232⟩ : DyadicInterval 40),(⟨746372067565,746372086894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171752504512,171752504576⟩ : DyadicInterval 40),(⟨-203639365952,-203639365888⟩ : DyadicInterval 40),(⟨746333187143,746333206473⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171438405504,171438405568⟩ : DyadicInterval 40),(⟨-203197599488,-203197599424⟩ : DyadicInterval 40),(⟨746395799842,746395819172⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171653118784,171653118848⟩ : DyadicInterval 40),(⟨-203499551424,-203499551360⟩ : DyadicInterval 40),(⟨746353014336,746353033666⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨59243818,71184309⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59242176,59242240⟩ : DyadicInterval 40),(⟨-59245440,-59245376⟩ : DyadicInterval 40),(⟨762123381991,762123401320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨71181952,71182016⟩ : DyadicInterval 40),(⟨-71186624,-71186560⟩ : DyadicInterval 40),(⟨762123381279,762123400608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4672,-3136⟩ : DyadicInterval 40),(⟨762123385184,762123405216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨185596170087,185835617837⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171497972928,171497972992⟩ : DyadicInterval 40),(⟨-203281355008,-203281354944⟩ : DyadicInterval 40),(⟨746383936668,746383955998⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171702820352,171702820416⟩ : DyadicInterval 40),(⟨-203569467072,-203569467008⟩ : DyadicInterval 40),(⟨746343100784,746343120114⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31866646720,-31783382016⟩ : DyadicInterval 40),(⟨778015074624,778056726240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨171557544384,171752504576⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-203639365952,-203365127232⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1441_ok : ecellOkT e1441 = true := by decide +kernel
theorem e1441_pos {a z : ℝ} (ha1 : ((691659/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((173127/1024000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1441 e1441_ok ha1 ha2 hz1 hz2 hz

-- box ['691659/4096000', '173127/1024000', '1599/1600', '1999/2000']  interval_lower 10864449/1099511627776
noncomputable def e1442 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1285177426837,0,true,171557544384,171557544448⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨913845828715,0,false,-203365127296,-203365127232⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1285405328540,0,true,171752504512,171752504576⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨913617927012,0,false,-203639365952,-203639365888⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1285061385712,0,true,171458262912,171458262976⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨913961869840,0,false,-203225518976,-203225518912⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1285312381690,0,true,171672996672,171672996736⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨913710873862,0,false,-203527512896,-203527512832⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099559022905,0,true,47394048,47394112⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464232647,0,false,-47396160,-47396096⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570948234,0,true,59318848,59318912⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452307318,0,false,-59322112,-59322048⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624575,0,false,-3264,-3200⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625734,0,false,-2048,-1984⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1285119401814,0,true,171507900928,171507900992⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨913903853738,0,false,-203295315584,-203295315520⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1285358863835,0,true,171712758784,171712758848⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨913664391717,0,false,-203583448448,-203583448384⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068098412782,0,false,-31870689664,-31870689600⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068179311762,0,false,-31787414592,-31787414528⟩
    { al := (691659/4096000), au := (173127/1024000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨185665799061,185893700764⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171557544384,171557544448⟩ : DyadicInterval 40),(⟨-203365127296,-203365127232⟩ : DyadicInterval 40),(⟨746372067565,746372086894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171752504512,171752504576⟩ : DyadicInterval 40),(⟨-203639365952,-203639365888⟩ : DyadicInterval 40),(⟨746333187143,746333206473⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171458262912,171458262976⟩ : DyadicInterval 40),(⟨-203225518976,-203225518912⟩ : DyadicInterval 40),(⟨746391845688,746391865018⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171672996672,171672996736⟩ : DyadicInterval 40),(⟨-203527512896,-203527512832⟩ : DyadicInterval 40),(⟨746349049891,746349069220⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨47395129,59320458⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨47394048,47394112⟩ : DyadicInterval 40),(⟨-47396160,-47396096⟩ : DyadicInterval 40),(⟨762123382564,762123401894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59318848,59318912⟩ : DyadicInterval 40),(⟨-59322112,-59322048⟩ : DyadicInterval 40),(⟨762123381983,762123401312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3264,-1984⟩ : DyadicInterval 40),(⟨762123384608,762123404512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨185607774038,185847236059⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171507900928,171507900992⟩ : DyadicInterval 40),(⟨-203295315584,-203295315520⟩ : DyadicInterval 40),(⟨746381958989,746381978319⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171712758784,171712758848⟩ : DyadicInterval 40),(⟨-203583448448,-203583448384⟩ : DyadicInterval 40),(⟨746341118012,746341137341⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31870689664,-31787414528⟩ : DyadicInterval 40),(⟨778017090880,778058747712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨171557544384,171752504576⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-203639365952,-203365127232⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1442_ok : ecellOkT e1442 = true := by decide +kernel
theorem e1442_pos {a z : ℝ} (ha1 : ((691659/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((173127/1024000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1442 e1442_ok ha1 ha2 hz1 hz2 hz

-- box ['86139/512000', '689961/4096000', '1999/2000', '7997/8000']  interval_lower 3284107/1099511627776
noncomputable def e1443 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284493721731,0,true,170972456512,170972456576⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914529533821,0,false,-202542821568,-202542821504⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284721623434,0,true,171167520384,171167520448⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914301632118,0,false,-202816855168,-202816855104⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1284401230684,0,true,170893282432,170893282496⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨914622024868,0,false,-202431627968,-202431627904⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1284652169686,0,true,171108077760,171108077824⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨914371085866,0,false,-202733335360,-202733335296⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099547037736,0,true,35409344,35409408⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476217816,0,false,-35410560,-35410496⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558902402,0,true,47273600,47273664⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464353150,0,false,-47275648,-47275584⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625743,0,false,-2048,-1984⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626636,0,false,-1152,-1088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1284447471628,0,true,170932866240,170932866304⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨914575783924,0,false,-202487217856,-202487217792⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1284686905174,0,true,171137806848,171137806912⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨914336350378,0,false,-202775104832,-202775104768⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068325160536,0,false,-31637297984,-31637297920⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068405757245,0,false,-31554351616,-31554351552⟩
    { al := (86139/512000), au := (689961/4096000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨184982093955,185209995658⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170972456512,170972456576⟩ : DyadicInterval 40),(⟨-202542821568,-202542821504⟩ : DyadicInterval 40),(⟨746488417116,746488436445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171167520384,171167520448⟩ : DyadicInterval 40),(⟨-202816855168,-202816855104⟩ : DyadicInterval 40),(⟨746449682567,746449701896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170893282432,170893282496⟩ : DyadicInterval 40),(⟨-202431627968,-202431627904⟩ : DyadicInterval 40),(⟨746504123175,746504142505⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171108077760,171108077824⟩ : DyadicInterval 40),(⟨-202733335360,-202733335296⟩ : DyadicInterval 40),(⟨746461492180,746461511509⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨35409960,47274626⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35409344,35409408⟩ : DyadicInterval 40),(⟨-35410560,-35410496⟩ : DyadicInterval 40),(⟨762123383019,762123402348⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨47273600,47273664⟩ : DyadicInterval 40),(⟨-47275648,-47275584⟩ : DyadicInterval 40),(⟨762123382543,762123401872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2048,-1088⟩ : DyadicInterval 40),(⟨762123384160,762123403904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184935843852,185175277398⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170932866240,170932866304⟩ : DyadicInterval 40),(⟨-202487217856,-202487217792⟩ : DyadicInterval 40),(⟨746496271938,746496291267⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171137806848,171137806912⟩ : DyadicInterval 40),(⟨-202775104832,-202775104768⟩ : DyadicInterval 40),(⟨746455586473,746455605803⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31637297984,-31554351552⟩ : DyadicInterval 40),(⟨777900559392,777942051872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170972456512,171167520448⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-202816855168,-202542821504⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1443_ok : ecellOkT e1443 = true := by decide +kernel
theorem e1443_pos {a z : ℝ} (ha1 : ((86139/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((689961/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1443 e1443_ok ha1 ha2 hz1 hz2 hz

-- box ['86139/512000', '689961/4096000', '7997/8000', '3999/4000']  interval_lower 47593/17179869184
noncomputable def e1444 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284493721731,0,true,170972456512,170972456576⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914529533821,0,false,-202542821568,-202542821504⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284721623434,0,true,171167520384,171167520448⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914301632118,0,false,-202816855168,-202816855104⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1284424353445,0,true,170913076480,170913076544⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨914598902107,0,false,-202459425344,-202459425280⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1284675320936,0,true,171127892288,171127892352⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨914347934616,0,false,-202761174592,-202761174528⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535234392,0,true,23606336,23606400⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488021160,0,false,-23606912,-23606848⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099547083904,0,true,35455552,35455616⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476171648,0,false,-35456704,-35456640⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626632,0,false,-1152,-1088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627270,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1284459032902,0,true,170942762880,170942762944⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨914564222650,0,false,-202501117056,-202501116992⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1284698480721,0,true,171147713856,171147713920⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨914324774831,0,false,-202789024768,-202789024704⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068321261401,0,false,-31641310912,-31641310848⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068401867953,0,false,-31558354112,-31558354048⟩
    { al := (86139/512000), au := (689961/4096000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨184982093955,185209995658⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170972456512,170972456576⟩ : DyadicInterval 40),(⟨-202542821568,-202542821504⟩ : DyadicInterval 40),(⟨746488417116,746488436445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171167520384,171167520448⟩ : DyadicInterval 40),(⟨-202816855168,-202816855104⟩ : DyadicInterval 40),(⟨746449682567,746449701896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170913076480,170913076544⟩ : DyadicInterval 40),(⟨-202459425344,-202459425280⟩ : DyadicInterval 40),(⟨746500197427,746500216757⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171127892288,171127892352⟩ : DyadicInterval 40),(⟨-202761174592,-202761174528⟩ : DyadicInterval 40),(⟨746457556166,746457575496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23606616,35456128⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23606336,23606400⟩ : DyadicInterval 40),(⟨-23606912,-23606848⟩ : DyadicInterval 40),(⟨762123383333,762123402662⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35455552,35455616⟩ : DyadicInterval 40),(⟨-35456704,-35456640⟩ : DyadicInterval 40),(⟨762123382984,762123402313⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1152,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184947405126,185186852945⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170942762880,170942762944⟩ : DyadicInterval 40),(⟨-202501117056,-202501116992⟩ : DyadicInterval 40),(⟨746494308644,746494327973⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171147713856,171147713920⟩ : DyadicInterval 40),(⟨-202789024768,-202789024704⟩ : DyadicInterval 40),(⟨746453618134,746453637464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31641310912,-31558354048⟩ : DyadicInterval 40),(⟨777902560640,777944058336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170972456512,171167520448⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-202816855168,-202542821504⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1444_ok : ecellOkT e1444 = true := by decide +kernel
theorem e1444_pos {a z : ℝ} (ha1 : ((86139/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((689961/4096000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1444 e1444_ok ha1 ha2 hz1 hz2 hz

-- box ['689961/4096000', '69081/409600', '1999/2000', '7997/8000']  interval_lower 2858939/549755813888
noncomputable def e1445 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284721623433,0,true,171167520384,171167520448⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914301632119,0,false,-202816855168,-202816855104⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284949525136,0,true,171362549696,171362549760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914073730416,0,false,-203090957056,-203090956992⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1284629018435,0,true,171088262784,171088262848⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨914394237117,0,false,-202705496832,-202705496768⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1284879985925,0,true,171303044416,171303044480⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨914143269627,0,false,-203007313664,-203007313600⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099547083202,0,true,35454848,35454912⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476172350,0,false,-35456000,-35455936⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558963033,0,true,47334208,47334272⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464292519,0,false,-47336320,-47336256⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625738,0,false,-2048,-1984⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626633,0,false,-1152,-1088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1284675316343,0,true,171127888384,171127888448⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨914347939209,0,false,-202761169088,-202761169024⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1284914764143,0,true,171332804864,171332804928⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨914108491409,0,false,-203049144896,-203049144832⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068248363153,0,false,-31716340032,-31716339968⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068329063902,0,false,-31633280640,-31633280576⟩
    { al := (689961/4096000), au := (69081/409600), zl := (1999/2000), zu := (7997/8000),
      A := ⟨185209995657,185437897360⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171167520384,171167520448⟩ : DyadicInterval 40),(⟨-202816855168,-202816855104⟩ : DyadicInterval 40),(⟨746449682567,746449701896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171362549696,171362549760⟩ : DyadicInterval 40),(⟨-203090957056,-203090956992⟩ : DyadicInterval 40),(⟨746410899365,746410918695⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171088262784,171088262848⟩ : DyadicInterval 40),(⟨-202705496832,-202705496768⟩ : DyadicInterval 40),(⟨746465427746,746465447075⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171303044416,171303044480⟩ : DyadicInterval 40),(⟨-203007313664,-203007313600⟩ : DyadicInterval 40),(⟨746422738394,746422757724⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨35455426,47335257⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35454848,35454912⟩ : DyadicInterval 40),(⟨-35456000,-35455936⟩ : DyadicInterval 40),(⟨762123382984,762123402313⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨47334208,47334272⟩ : DyadicInterval 40),(⟨-47336320,-47336256⟩ : DyadicInterval 40),(⟨762123382570,762123401899⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2048,-1088⟩ : DyadicInterval 40),(⟨762123384160,762123403904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨185163688567,185403136367⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171127888384,171127888448⟩ : DyadicInterval 40),(⟨-202761169088,-202761169024⟩ : DyadicInterval 40),(⟨746457556939,746457576269⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171332804864,171332804928⟩ : DyadicInterval 40),(⟨-203049144896,-203049144832⟩ : DyadicInterval 40),(⟨746416817947,746416837276⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31716340032,-31633280576⟩ : DyadicInterval 40),(⟨777940023904,777981572896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨171167520384,171362549760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-203090957056,-202816855104⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1445_ok : ecellOkT e1445 = true := by decide +kernel
theorem e1445_pos {a z : ℝ} (ha1 : ((689961/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((69081/409600 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1445 e1445_ok ha1 ha2 hz1 hz2 hz

-- box ['689961/4096000', '69081/409600', '7997/8000', '3999/4000']  interval_lower 5478815/1099511627776
noncomputable def e1446 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284721623433,0,true,171167520384,171167520448⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914301632119,0,false,-202816855168,-202816855104⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284949525136,0,true,171362549696,171362549760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914073730416,0,false,-203090957056,-203090956992⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1284652169684,0,true,171108077760,171108077824⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨914371085868,0,false,-202733335360,-202733335296⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1284903165662,0,true,171322879872,171322879936⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨914120089890,0,false,-203035194048,-203035193984⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535264703,0,true,23636672,23636736⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487990849,0,false,-23637184,-23637120⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099547129377,0,true,35500992,35501056⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476126175,0,false,-35502208,-35502144⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626629,0,false,-1152,-1088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627268,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1284686891865,0,true,171137795456,171137795520⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨914336363687,0,false,-202775088832,-202775088768⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1284926353939,0,true,171342722304,171342722368⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨914096901613,0,false,-203063085504,-203063085440⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068244454415,0,false,-31720363200,-31720363136⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068325165020,0,false,-31637293312,-31637293248⟩
    { al := (689961/4096000), au := (69081/409600), zl := (7997/8000), zu := (3999/4000),
      A := ⟨185209995657,185437897360⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171167520384,171167520448⟩ : DyadicInterval 40),(⟨-202816855168,-202816855104⟩ : DyadicInterval 40),(⟨746449682567,746449701896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171362549696,171362549760⟩ : DyadicInterval 40),(⟨-203090957056,-203090956992⟩ : DyadicInterval 40),(⟨746410899365,746410918695⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171108077760,171108077824⟩ : DyadicInterval 40),(⟨-202733335360,-202733335296⟩ : DyadicInterval 40),(⟨746461492181,746461511510⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171322879872,171322879936⟩ : DyadicInterval 40),(⟨-203035194048,-203035193984⟩ : DyadicInterval 40),(⟨746418792535,746418811864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23636927,35501601⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23636672,23636736⟩ : DyadicInterval 40),(⟨-23637184,-23637120⟩ : DyadicInterval 40),(⟨762123383299,762123402628⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35500992,35501056⟩ : DyadicInterval 40),(⟨-35502208,-35502144⟩ : DyadicInterval 40),(⟨762123383013,762123402342⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1152,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨185175264089,185414726163⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171137795456,171137795520⟩ : DyadicInterval 40),(⟨-202775088832,-202775088768⟩ : DyadicInterval 40),(⟨746455588738,746455608068⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171342722304,171342722368⟩ : DyadicInterval 40),(⟨-203063085504,-203063085440⟩ : DyadicInterval 40),(⟨746414844742,746414864071⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31720363200,-31637293248⟩ : DyadicInterval 40),(⟨777942030240,777983584480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨171167520384,171362549760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-203090957056,-202816855104⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1446_ok : ecellOkT e1446 = true := by decide +kernel
theorem e1446_pos {a z : ℝ} (ha1 : ((689961/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((69081/409600 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1446 e1446_ok ha1 ha2 hz1 hz2 hz

-- box ['86139/512000', '689961/4096000', '3999/4000', '7999/8000']  interval_lower 2807871/1099511627776
noncomputable def e1447 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284493721731,0,true,170972456512,170972456576⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914529533821,0,false,-202542821568,-202542821504⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284721623434,0,true,171167520384,171167520448⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914301632118,0,false,-202816855168,-202816855104⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1284447476207,0,true,170932870144,170932870208⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨914575779345,0,false,-202487223360,-202487223296⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1284698472185,0,true,171147706560,171147706624⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨914324783367,0,false,-202789014528,-202789014464⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523430986,0,true,11803136,11803200⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499824566,0,false,-11803328,-11803264⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535265343,0,true,23637312,23637376⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487990209,0,false,-23637824,-23637760⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627267,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627650,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1284470594207,0,true,170952659456,170952659520⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨914552661345,0,false,-202515016384,-202515016320⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1284710056305,0,true,171157620800,171157620864⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨914313199247,0,false,-202802944960,-202802944896⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068317362010,0,false,-31645324160,-31645324096⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068397978408,0,false,-31562356928,-31562356864⟩
    { al := (86139/512000), au := (689961/4096000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨184982093955,185209995658⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170972456512,170972456576⟩ : DyadicInterval 40),(⟨-202542821568,-202542821504⟩ : DyadicInterval 40),(⟨746488417116,746488436445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171167520384,171167520448⟩ : DyadicInterval 40),(⟨-202816855168,-202816855104⟩ : DyadicInterval 40),(⟨746449682567,746449701896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170932870144,170932870208⟩ : DyadicInterval 40),(⟨-202487223360,-202487223296⟩ : DyadicInterval 40),(⟨746496271169,746496290499⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171147706560,171147706624⟩ : DyadicInterval 40),(⟨-202789014528,-202789014464⟩ : DyadicInterval 40),(⟨746453619591,746453638920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11803210,23637567⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11803136,11803200⟩ : DyadicInterval 40),(⟨-11803328,-11803264⟩ : DyadicInterval 40),(⟨762123383521,762123402850⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23637312,23637376⟩ : DyadicInterval 40),(⟨-23637824,-23637760⟩ : DyadicInterval 40),(⟨762123383299,762123402628⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184958966431,185198428529⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170952659456,170952659520⟩ : DyadicInterval 40),(⟨-202515016384,-202515016320⟩ : DyadicInterval 40),(⟨746492345185,746492364514⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171157620800,171157620864⟩ : DyadicInterval 40),(⟨-202802944960,-202802944896⟩ : DyadicInterval 40),(⟨746451649683,746451669012⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31645324160,-31562356864⟩ : DyadicInterval 40),(⟨777904562048,777946064960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170972456512,171167520448⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-202816855168,-202542821504⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1447_ok : ecellOkT e1447 = true := by decide +kernel
theorem e1447_pos {a z : ℝ} (ha1 : ((86139/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((689961/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1447 e1447_ok ha1 ha2 hz1 hz2 hz

-- box ['86139/512000', '689961/4096000', '7999/8000', '1']  interval_lower 1284899/549755813888
noncomputable def e1448 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284493721731,0,true,170972456512,170972456576⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914529533821,0,false,-202542821568,-202542821504⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284721623434,0,true,171167520384,171167520448⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914301632118,0,false,-202816855168,-202816855104⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1284470598969,0,true,170952663488,170952663552⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨914552656583,0,false,-202515022144,-202515022080⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523446719,0,true,11818816,11818880⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499808833,0,false,-11819008,-11818944⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627648,0,false,-192,-128⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1284482155541,0,true,170962555968,170962556032⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨914541100011,0,false,-202528915968,-202528915904⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1284721631912,0,true,171167527680,171167527744⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨914301623640,0,false,-202816865344,-202816865280⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1068313462367,0,false,-31649337664,-31649337600⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1068394088610,0,false,-31566360000,-31566359936⟩
    { al := (86139/512000), au := (689961/4096000), zl := (7999/8000), zu := 1,
      A := ⟨184982093955,185209995658⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170972456512,170972456576⟩ : DyadicInterval 40),(⟨-202542821568,-202542821504⟩ : DyadicInterval 40),(⟨746488417116,746488436445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171167520384,171167520448⟩ : DyadicInterval 40),(⟨-202816855168,-202816855104⟩ : DyadicInterval 40),(⟨746449682567,746449701896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170952663488,170952663552⟩ : DyadicInterval 40),(⟨-202515022144,-202515022080⟩ : DyadicInterval 40),(⟨746492344416,746492363746⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171167520384,171167520448⟩ : DyadicInterval 40),(⟨-202816855168,-202816855104⟩ : DyadicInterval 40),(⟨746449682567,746449701896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11818943⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11818816,11818880⟩ : DyadicInterval 40),(⟨-11819008,-11818944⟩ : DyadicInterval 40),(⟨762123383520,762123402849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-192,0⟩ : DyadicInterval 40),(⟨762123383616,762123402976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨184970527765,185210004136⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170962555968,170962556032⟩ : DyadicInterval 40),(⟨-202528915968,-202528915904⟩ : DyadicInterval 40),(⟨746490381614,746490400944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171167527680,171167527744⟩ : DyadicInterval 40),(⟨-202816865344,-202816865280⟩ : DyadicInterval 40),(⟨746449681093,746449700423⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31649337664,-31566359936⟩ : DyadicInterval 40),(⟨777906563584,777948071712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨170972456512,171167520448⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-202816855168,-202542821504⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1448_ok : ecellOkT e1448 = true := by decide +kernel
theorem e1448_pos {a z : ℝ} (ha1 : ((86139/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((689961/4096000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1448 e1448_ok ha1 ha2 hz1 hz2 hz

-- box ['689961/4096000', '69081/409600', '3999/4000', '7999/8000']  interval_lower 1309943/274877906944
noncomputable def e1449 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284721623433,0,true,171167520384,171167520448⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914301632119,0,false,-202816855168,-202816855104⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284949525136,0,true,171362549696,171362549760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914073730416,0,false,-203090957056,-203090956992⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1284675320934,0,true,171127892288,171127892352⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨914347934618,0,false,-202761174592,-202761174528⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1284926345399,0,true,171342714944,171342715008⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨914096910153,0,false,-203063075200,-203063075136⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523446142,0,true,11818240,11818304⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499809410,0,false,-11818432,-11818368⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535295659,0,true,23667584,23667648⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487959893,0,false,-23668160,-23668096⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627266,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627649,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1284698467412,0,true,171147702464,171147702528⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨914324788140,0,false,-202789008768,-202789008704⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1284937943762,0,true,171352639616,171352639680⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨914085311790,0,false,-203077026240,-203077026176⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068240545423,0,false,-31724386624,-31724386560⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068321265885,0,false,-31641306304,-31641306240⟩
    { al := (689961/4096000), au := (69081/409600), zl := (3999/4000), zu := (7999/8000),
      A := ⟨185209995657,185437897360⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171167520384,171167520448⟩ : DyadicInterval 40),(⟨-202816855168,-202816855104⟩ : DyadicInterval 40),(⟨746449682567,746449701896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171362549696,171362549760⟩ : DyadicInterval 40),(⟨-203090957056,-203090956992⟩ : DyadicInterval 40),(⟨746410899365,746410918695⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171127892288,171127892352⟩ : DyadicInterval 40),(⟨-202761174592,-202761174528⟩ : DyadicInterval 40),(⟨746457556166,746457575496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171342714944,171342715008⟩ : DyadicInterval 40),(⟨-203063075200,-203063075136⟩ : DyadicInterval 40),(⟨746414846213,746414865543⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11818366,23667883⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11818240,11818304⟩ : DyadicInterval 40),(⟨-11818432,-11818368⟩ : DyadicInterval 40),(⟨762123383520,762123402849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23667584,23667648⟩ : DyadicInterval 40),(⟨-23668160,-23668096⟩ : DyadicInterval 40),(⟨762123383330,762123402659⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨185186839636,185426315986⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171147702464,171147702528⟩ : DyadicInterval 40),(⟨-202789008768,-202789008704⟩ : DyadicInterval 40),(⟨746453620400,746453639730⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171352639616,171352639680⟩ : DyadicInterval 40),(⟨-203077026240,-203077026176⟩ : DyadicInterval 40),(⟨746412871409,746412890738⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31724386624,-31641306240⟩ : DyadicInterval 40),(⟨777944036736,777985596192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨171167520384,171362549760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-203090957056,-202816855104⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1449_ok : ecellOkT e1449 = true := by decide +kernel
theorem e1449_pos {a z : ℝ} (ha1 : ((689961/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((69081/409600 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1449 e1449_ok ha1 ha2 hz1 hz2 hz

-- box ['689961/4096000', '69081/409600', '7999/8000', '1']  interval_lower 5000585/1099511627776
noncomputable def e1450 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284721623433,0,true,171167520384,171167520448⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914301632119,0,false,-202816855168,-202816855104⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284949525136,0,true,171362549696,171362549760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914073730416,0,false,-203090957056,-203090956992⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1284698472183,0,true,171147706560,171147706624⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨914324783369,0,false,-202789014528,-202789014464⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523461877,0,true,11833984,11834048⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499793675,0,false,-11834176,-11834112⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627648,0,false,-192,-128⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1284710042995,0,true,171157609408,171157609472⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨914313212557,0,false,-202802928960,-202802928896⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1284949533617,0,true,171362556928,171362556992⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨914073721935,0,false,-203090967296,-203090967232⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1068236636176,0,false,-31728410304,-31728410240⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1068317366494,0,false,-31645319552,-31645319488⟩
    { al := (689961/4096000), au := (69081/409600), zl := (7999/8000), zu := 1,
      A := ⟨185209995657,185437897360⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171167520384,171167520448⟩ : DyadicInterval 40),(⟨-202816855168,-202816855104⟩ : DyadicInterval 40),(⟨746449682567,746449701896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171362549696,171362549760⟩ : DyadicInterval 40),(⟨-203090957056,-203090956992⟩ : DyadicInterval 40),(⟨746410899365,746410918695⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171147706560,171147706624⟩ : DyadicInterval 40),(⟨-202789014528,-202789014464⟩ : DyadicInterval 40),(⟨746453619591,746453638921⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171362549696,171362549760⟩ : DyadicInterval 40),(⟨-203090957056,-203090956992⟩ : DyadicInterval 40),(⟨746410899365,746410918695⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11834101⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11833984,11834048⟩ : DyadicInterval 40),(⟨-11834176,-11834112⟩ : DyadicInterval 40),(⟨762123383520,762123402849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-192,0⟩ : DyadicInterval 40),(⟨762123383616,762123402976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨185198415219,185437905841⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171157609408,171157609472⟩ : DyadicInterval 40),(⟨-202802928960,-202802928896⟩ : DyadicInterval 40),(⟨746451651949,746451671279⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171362556928,171362556992⟩ : DyadicInterval 40),(⟨-203090967296,-203090967232⟩ : DyadicInterval 40),(⟨746410897951,746410917281⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31728410304,-31645319488⟩ : DyadicInterval 40),(⟨777946043360,777987608032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨171167520384,171362549760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-203090957056,-202816855104⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1450_ok : ecellOkT e1450 = true := by decide +kernel
theorem e1450_pos {a z : ℝ} (ha1 : ((689961/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((69081/409600 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1450 e1450_ok ha1 ha2 hz1 hz2 hz

-- box ['69081/409600', '691659/4096000', '1999/2000', '7997/8000']  interval_lower 1020563/137438953472
noncomputable def e1451 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284949525135,0,true,171362549696,171362549760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914073730417,0,false,-203090957056,-203090956992⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1285177426838,0,true,171557544384,171557544448⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨913845828714,0,false,-203365127296,-203365127232⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1284856806186,0,true,171283208640,171283208704⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨914166449366,0,false,-202979433920,-202979433856⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1285107802164,0,true,171497976576,171497976640⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨913915453388,0,false,-203281360192,-203281360128⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099547128673,0,true,35500288,35500352⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476126879,0,false,-35501504,-35501440⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099559023671,0,true,47394816,47394880⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464231881,0,false,-47396928,-47396864⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625732,0,false,-2048,-1984⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626630,0,false,-1152,-1088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1284903161067,0,true,171322875968,171322876032⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨914120094485,0,false,-203035188544,-203035188480⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1285142623116,0,true,171527768256,171527768320⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨913880632436,0,false,-203323253312,-203323253248⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068171471327,0,false,-31795485056,-31795484992⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068252276126,0,false,-31712312576,-31712312512⟩
    { al := (69081/409600), au := (691659/4096000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨185437897359,185665799062⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171362549696,171362549760⟩ : DyadicInterval 40),(⟨-203090957056,-203090956992⟩ : DyadicInterval 40),(⟨746410899365,746410918695⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171557544384,171557544448⟩ : DyadicInterval 40),(⟨-203365127296,-203365127232⟩ : DyadicInterval 40),(⟨746372067565,746372086894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171283208640,171283208704⟩ : DyadicInterval 40),(⟨-202979433920,-202979433856⟩ : DyadicInterval 40),(⟨746426683701,746426703031⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171497976576,171497976640⟩ : DyadicInterval 40),(⟨-203281360192,-203281360128⟩ : DyadicInterval 40),(⟨746383935957,746383955287⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨35500897,47395895⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35500288,35500352⟩ : DyadicInterval 40),(⟨-35501504,-35501440⟩ : DyadicInterval 40),(⟨762123383013,762123402342⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨47394816,47394880⟩ : DyadicInterval 40),(⟨-47396928,-47396864⟩ : DyadicInterval 40),(⟨762123382564,762123401893⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2048,-1088⟩ : DyadicInterval 40),(⟨762123384160,762123403904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨185391533291,185630995340⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171322875968,171322876032⟩ : DyadicInterval 40),(⟨-203035188544,-203035188480⟩ : DyadicInterval 40),(⟨746418793311,746418812640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171527768256,171527768320⟩ : DyadicInterval 40),(⟨-203323253312,-203323253248⟩ : DyadicInterval 40),(⟨746378000859,746378020189⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31795485056,-31712312512⟩ : DyadicInterval 40),(⟨777979539872,778021145408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨171362549696,171557544448⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-203365127296,-203090956992⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1451_ok : ecellOkT e1451 = true := by decide +kernel
theorem e1451_pos {a z : ℝ} (ha1 : ((69081/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((691659/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1451 e1451_ok ha1 ha2 hz1 hz2 hz

-- box ['69081/409600', '691659/4096000', '7997/8000', '3999/4000']  interval_lower 247641/34359738368
noncomputable def e1452 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284949525135,0,true,171362549696,171362549760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914073730417,0,false,-203090957056,-203090956992⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1285177426838,0,true,171557544384,171557544448⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨913845828714,0,false,-203365127296,-203365127232⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1284879985923,0,true,171303044416,171303044480⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨914143269629,0,false,-203007313600,-203007313536⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1285131010389,0,true,171517832896,171517832960⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨913892245163,0,false,-203309281856,-203309281792⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535295018,0,true,23666944,23667008⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487960534,0,false,-23667520,-23667456⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099547174857,0,true,35546496,35546560⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476080695,0,false,-35547712,-35547648⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626626,0,false,-1152,-1088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627267,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1284914750832,0,true,171332793472,171332793536⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨914108504720,0,false,-203049128896,-203049128832⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1285154227155,0,true,171537696128,171537696192⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨913869028397,0,false,-203337214528,-203337214464⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068167552976,0,false,-31799518336,-31799518272⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068248367643,0,false,-31716335424,-31716335360⟩
    { al := (69081/409600), au := (691659/4096000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨185437897359,185665799062⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171362549696,171362549760⟩ : DyadicInterval 40),(⟨-203090957056,-203090956992⟩ : DyadicInterval 40),(⟨746410899365,746410918695⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171557544384,171557544448⟩ : DyadicInterval 40),(⟨-203365127296,-203365127232⟩ : DyadicInterval 40),(⟨746372067565,746372086894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171303044416,171303044480⟩ : DyadicInterval 40),(⟨-203007313600,-203007313536⟩ : DyadicInterval 40),(⟨746422738368,746422757697⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171517832896,171517832960⟩ : DyadicInterval 40),(⟨-203309281856,-203309281792⟩ : DyadicInterval 40),(⟨746379980318,746379999648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23667242,35547081⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23666944,23667008⟩ : DyadicInterval 40),(⟨-23667520,-23667456⟩ : DyadicInterval 40),(⟨762123383330,762123402659⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35546496,35546560⟩ : DyadicInterval 40),(⟨-35547712,-35547648⟩ : DyadicInterval 40),(⟨762123383010,762123402339⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1152,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨185403123056,185642599379⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171332793472,171332793536⟩ : DyadicInterval 40),(⟨-203049128896,-203049128832⟩ : DyadicInterval 40),(⟨746416820218,746416839548⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171537696128,171537696192⟩ : DyadicInterval 40),(⟨-203337214528,-203337214464⟩ : DyadicInterval 40),(⟨746376022749,746376042078⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31799518336,-31716335360⟩ : DyadicInterval 40),(⟨777981551296,778023162048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨171362549696,171557544448⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-203365127296,-203090956992⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1452_ok : ecellOkT e1452 = true := by decide +kernel
theorem e1452_pos {a z : ℝ} (ha1 : ((69081/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((691659/4096000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1452 e1452_ok ha1 ha2 hz1 hz2 hz

-- box ['691659/4096000', '173127/1024000', '1999/2000', '7997/8000']  interval_lower 10623537/1099511627776
noncomputable def e1453 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1285177426837,0,true,171557544384,171557544448⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨913845828715,0,false,-203365127296,-203365127232⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1285405328540,0,true,171752504512,171752504576⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨913617927012,0,false,-203639365952,-203639365888⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1285084593937,0,true,171478119936,171478120000⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨913938661615,0,false,-203253439232,-203253439168⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1285335618403,0,true,171692874176,171692874240⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨913687637149,0,false,-203555475072,-203555475008⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099547174152,0,true,35545792,35545856⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476081400,0,false,-35547008,-35546944⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099559084320,0,true,47455488,47455552⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464171232,0,false,-47457600,-47457536⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625727,0,false,-2112,-2048⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626627,0,false,-1152,-1088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1285131005791,0,true,171517828928,171517828992⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨913892249761,0,false,-203309276352,-203309276288⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1285370482087,0,true,171722697088,171722697152⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨913652773465,0,false,-203597430080,-203597430016⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068094485061,0,false,-31874732928,-31874732864⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068175393921,0,false,-31791447360,-31791447296⟩
    { al := (691659/4096000), au := (173127/1024000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨185665799061,185893700764⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171557544384,171557544448⟩ : DyadicInterval 40),(⟨-203365127296,-203365127232⟩ : DyadicInterval 40),(⟨746372067565,746372086894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171752504512,171752504576⟩ : DyadicInterval 40),(⟨-203639365952,-203639365888⟩ : DyadicInterval 40),(⟨746333187143,746333206473⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171478119936,171478120000⟩ : DyadicInterval 40),(⟨-203253439232,-203253439168⟩ : DyadicInterval 40),(⟨746387891069,746387910398⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171692874176,171692874240⟩ : DyadicInterval 40),(⟨-203555475072,-203555475008⟩ : DyadicInterval 40),(⟨746345084950,746345104279⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨35546376,47456544⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35545792,35545856⟩ : DyadicInterval 40),(⟨-35547008,-35546944⟩ : DyadicInterval 40),(⟨762123383010,762123402339⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨47455488,47455552⟩ : DyadicInterval 40),(⟨-47457600,-47457536⟩ : DyadicInterval 40),(⟨762123382559,762123401888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2112,-1088⟩ : DyadicInterval 40),(⟨762123384160,762123403936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨185619378015,185858854311⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171517828928,171517828992⟩ : DyadicInterval 40),(⟨-203309276352,-203309276288⟩ : DyadicInterval 40),(⟨746379981133,746380000463⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171722697088,171722697152⟩ : DyadicInterval 40),(⟨-203597430080,-203597430016⟩ : DyadicInterval 40),(⟨746339135162,746339154492⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31874732928,-31791447296⟩ : DyadicInterval 40),(⟨778019107264,778060769344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨171557544384,171752504576⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-203639365952,-203365127232⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1453_ok : ecellOkT e1453 = true := by decide +kernel
theorem e1453_pos {a z : ℝ} (ha1 : ((691659/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((173127/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1453 e1453_ok ha1 ha2 hz1 hz2 hz

-- box ['691659/4096000', '173127/1024000', '7997/8000', '3999/4000']  interval_lower 10382545/1099511627776
noncomputable def e1454 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1285177426837,0,true,171557544384,171557544448⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨913845828715,0,false,-203365127296,-203365127232⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1285405328540,0,true,171752504512,171752504576⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨913617927012,0,false,-203639365952,-203639365888⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1285107802162,0,true,171497976576,171497976640⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨913915453390,0,false,-203281360192,-203281360128⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1285358855115,0,true,171712751296,171712751360⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨913664400437,0,false,-203583438016,-203583437952⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535325336,0,true,23697280,23697344⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487930216,0,false,-23697856,-23697792⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099547220342,0,true,35591936,35592000⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476035210,0,false,-35593152,-35593088⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626623,0,false,-1216,-1152⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627266,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1285142609796,0,true,171527756864,171527756928⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨913880645756,0,false,-203323237312,-203323237248⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1285382100365,0,true,171732635392,171732635456⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨913641155187,0,false,-203611411904,-203611411840⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068090557086,0,false,-31878776448,-31878776384⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068171475826,0,false,-31795480384,-31795480320⟩
    { al := (691659/4096000), au := (173127/1024000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨185665799061,185893700764⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171557544384,171557544448⟩ : DyadicInterval 40),(⟨-203365127296,-203365127232⟩ : DyadicInterval 40),(⟨746372067565,746372086894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171752504512,171752504576⟩ : DyadicInterval 40),(⟨-203639365952,-203639365888⟩ : DyadicInterval 40),(⟨746333187143,746333206473⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171497976576,171497976640⟩ : DyadicInterval 40),(⟨-203281360192,-203281360128⟩ : DyadicInterval 40),(⟨746383935958,746383955288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171712751296,171712751360⟩ : DyadicInterval 40),(⟨-203583438016,-203583437952⟩ : DyadicInterval 40),(⟨746341119542,746341138872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23697560,35592566⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23697280,23697344⟩ : DyadicInterval 40),(⟨-23697856,-23697792⟩ : DyadicInterval 40),(⟨762123383329,762123402658⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35591936,35592000⟩ : DyadicInterval 40),(⟨-35593152,-35593088⟩ : DyadicInterval 40),(⟨762123383007,762123402336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1216,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨185630982020,185870472589⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171527756864,171527756928⟩ : DyadicInterval 40),(⟨-203323237312,-203323237248⟩ : DyadicInterval 40),(⟨746378003138,746378022467⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171732635392,171732635456⟩ : DyadicInterval 40),(⟨-203611411904,-203611411840⟩ : DyadicInterval 40),(⟨746337152136,746337171465⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31878776448,-31795480320⟩ : DyadicInterval 40),(⟨778021123776,778062791104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨171557544384,171752504576⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-203639365952,-203365127232⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1454_ok : ecellOkT e1454 = true := by decide +kernel
theorem e1454_pos {a z : ℝ} (ha1 : ((691659/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((173127/1024000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1454 e1454_ok ha1 ha2 hz1 hz2 hz

-- box ['69081/409600', '691659/4096000', '3999/4000', '7999/8000']  interval_lower 7684265/1099511627776
noncomputable def e1455 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284949525135,0,true,171362549696,171362549760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914073730417,0,false,-203090957056,-203090956992⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1285177426838,0,true,171557544384,171557544448⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨913845828714,0,false,-203365127296,-203365127232⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1284903165660,0,true,171322879872,171322879936⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨914120089892,0,false,-203035194048,-203035193984⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1285154218614,0,true,171537688832,171537688896⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨913869036938,0,false,-203337204224,-203337204160⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523461299,0,true,11833408,11833472⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499794253,0,false,-11833600,-11833536⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535325978,0,true,23697920,23697984⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487929574,0,false,-23698496,-23698432⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627265,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627649,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1284926340625,0,true,171342710912,171342710976⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨914096914927,0,false,-203063069504,-203063069440⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1285165831222,0,true,171547623936,171547624000⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨913857424330,0,false,-203351175872,-203351175808⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068163634370,0,false,-31803551936,-31803551872⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068244458906,0,false,-31720358528,-31720358464⟩
    { al := (69081/409600), au := (691659/4096000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨185437897359,185665799062⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171362549696,171362549760⟩ : DyadicInterval 40),(⟨-203090957056,-203090956992⟩ : DyadicInterval 40),(⟨746410899365,746410918695⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171557544384,171557544448⟩ : DyadicInterval 40),(⟨-203365127296,-203365127232⟩ : DyadicInterval 40),(⟨746372067565,746372086894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171322879872,171322879936⟩ : DyadicInterval 40),(⟨-203035194048,-203035193984⟩ : DyadicInterval 40),(⟨746418792535,746418811865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171537688832,171537688896⟩ : DyadicInterval 40),(⟨-203337204224,-203337204160⟩ : DyadicInterval 40),(⟨746376024187,746376043517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11833523,23698202⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11833408,11833472⟩ : DyadicInterval 40),(⟨-11833600,-11833536⟩ : DyadicInterval 40),(⟨762123383520,762123402849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23697920,23697984⟩ : DyadicInterval 40),(⟨-23698496,-23698432⟩ : DyadicInterval 40),(⟨762123383329,762123402658⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨185414712849,185654203446⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171342710912,171342710976⟩ : DyadicInterval 40),(⟨-203063069504,-203063069440⟩ : DyadicInterval 40),(⟨746414847014,746414866343⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171547623936,171547624000⟩ : DyadicInterval 40),(⟨-203351175872,-203351175808⟩ : DyadicInterval 40),(⟨746374044473,746374063802⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31803551936,-31720358464⟩ : DyadicInterval 40),(⟨777983562848,778025178848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨171362549696,171557544448⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-203365127296,-203090956992⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1455_ok : ecellOkT e1455 = true := by decide +kernel
theorem e1455_pos {a z : ℝ} (ha1 : ((69081/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((691659/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1455 e1455_ok ha1 ha2 hz1 hz2 hz

-- box ['69081/409600', '691659/4096000', '7999/8000', '1']  interval_lower 3722003/549755813888
noncomputable def e1456 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284949525135,0,true,171362549696,171362549760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914073730417,0,false,-203090957056,-203090956992⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1285177426838,0,true,171557544384,171557544448⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨913845828714,0,false,-203365127296,-203365127232⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1284926345397,0,true,171342714944,171342715008⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨914096910155,0,false,-203063075200,-203063075136⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523477037,0,true,11849152,11849216⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499778515,0,false,-11849344,-11849280⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627648,0,false,-192,-128⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1284937930447,0,true,171352628224,171352628288⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨914085325105,0,false,-203077010240,-203077010176⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1285177435317,0,true,171557551680,171557551744⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨913845820235,0,false,-203365137536,-203365137472⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1068159715509,0,false,-31807585856,-31807585792⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1068240549915,0,false,-31724381952,-31724381888⟩
    { al := (69081/409600), au := (691659/4096000), zl := (7999/8000), zu := 1,
      A := ⟨185437897359,185665799062⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171362549696,171362549760⟩ : DyadicInterval 40),(⟨-203090957056,-203090956992⟩ : DyadicInterval 40),(⟨746410899365,746410918695⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171557544384,171557544448⟩ : DyadicInterval 40),(⟨-203365127296,-203365127232⟩ : DyadicInterval 40),(⟨746372067565,746372086894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171342714944,171342715008⟩ : DyadicInterval 40),(⟨-203063075200,-203063075136⟩ : DyadicInterval 40),(⟨746414846213,746414865543⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171557544384,171557544448⟩ : DyadicInterval 40),(⟨-203365127296,-203365127232⟩ : DyadicInterval 40),(⟨746372067565,746372086894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11849261⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11849152,11849216⟩ : DyadicInterval 40),(⟨-11849344,-11849280⟩ : DyadicInterval 40),(⟨762123383520,762123402849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-192,0⟩ : DyadicInterval 40),(⟨762123383616,762123402976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨185426302671,185665807541⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171352628224,171352628288⟩ : DyadicInterval 40),(⟨-203077010240,-203077010176⟩ : DyadicInterval 40),(⟨746412873682,746412893011⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171557551680,171557551744⟩ : DyadicInterval 40),(⟨-203365137536,-203365137472⟩ : DyadicInterval 40),(⟨746372066110,746372085439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31807585856,-31724381888⟩ : DyadicInterval 40),(⟨777985574560,778027195808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨171362549696,171557544448⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-203365127296,-203090956992⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1456_ok : ecellOkT e1456 = true := by decide +kernel
theorem e1456_pos {a z : ℝ} (ha1 : ((69081/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((691659/4096000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1456 e1456_ok ha1 ha2 hz1 hz2 hz

-- box ['691659/4096000', '173127/1024000', '3999/4000', '7999/8000']  interval_lower 10141575/1099511627776
noncomputable def e1457 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1285177426837,0,true,171557544384,171557544448⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨913845828715,0,false,-203365127296,-203365127232⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1285405328540,0,true,171752504512,171752504576⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨913617927012,0,false,-203639365952,-203639365888⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1285131010387,0,true,171517832896,171517832960⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨913892245165,0,false,-203309281856,-203309281792⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1285382091828,0,true,171732628096,171732628160⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨913641163724,0,false,-203611401600,-203611401536⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523476460,0,true,11848576,11848640⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499779092,0,false,-11848768,-11848704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535356303,0,true,23728256,23728320⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487899249,0,false,-23728832,-23728768⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627263,0,false,-576,-512⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627649,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1285154213835,0,true,171537684736,171537684800⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨913869041717,0,false,-203337198464,-203337198400⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1285393718677,0,true,171742573632,171742573696⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨913629536875,0,false,-203625393920,-203625393856⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068086628853,0,false,-31882820224,-31882820160⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068167557475,0,false,-31799513728,-31799513664⟩
    { al := (691659/4096000), au := (173127/1024000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨185665799061,185893700764⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171557544384,171557544448⟩ : DyadicInterval 40),(⟨-203365127296,-203365127232⟩ : DyadicInterval 40),(⟨746372067565,746372086894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171752504512,171752504576⟩ : DyadicInterval 40),(⟨-203639365952,-203639365888⟩ : DyadicInterval 40),(⟨746333187143,746333206473⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171517832896,171517832960⟩ : DyadicInterval 40),(⟨-203309281856,-203309281792⟩ : DyadicInterval 40),(⟨746379980318,746379999648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171732628096,171732628160⟩ : DyadicInterval 40),(⟨-203611401600,-203611401536⟩ : DyadicInterval 40),(⟨746337153577,746337172906⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11848684,23728527⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11848576,11848640⟩ : DyadicInterval 40),(⟨-11848768,-11848704⟩ : DyadicInterval 40),(⟨762123383520,762123402849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23728256,23728320⟩ : DyadicInterval 40),(⟨-23728832,-23728768⟩ : DyadicInterval 40),(⟨762123383327,762123402656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨185642586059,185882090901⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171537684736,171537684800⟩ : DyadicInterval 40),(⟨-203337198464,-203337198400⟩ : DyadicInterval 40),(⟨746376025002,746376044331⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171742573632,171742573696⟩ : DyadicInterval 40),(⟨-203625393920,-203625393856⟩ : DyadicInterval 40),(⟨746335168968,746335188297⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31882820224,-31799513664⟩ : DyadicInterval 40),(⟨778023140448,778064812992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨171557544384,171752504576⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-203639365952,-203365127232⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1457_ok : ecellOkT e1457 = true := by decide +kernel
theorem e1457_pos {a z : ℝ} (ha1 : ((691659/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((173127/1024000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1457 e1457_ok ha1 ha2 hz1 hz2 hz

-- box ['691659/4096000', '173127/1024000', '7999/8000', '1']  interval_lower 9900541/1099511627776
noncomputable def e1458 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1285177426837,0,true,171557544384,171557544448⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨913845828715,0,false,-203365127296,-203365127232⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1285405328540,0,true,171752504512,171752504576⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨913617927012,0,false,-203639365952,-203639365888⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1285154218612,0,true,171537688832,171537688896⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨913869036940,0,false,-203337204224,-203337204160⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523492200,0,true,11864320,11864384⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499763352,0,false,-11864512,-11864448⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627647,0,false,-192,-128⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1285165817901,0,true,171547612544,171547612608⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨913857437651,0,false,-203351159872,-203351159808⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1285405337016,0,true,171752511744,171752511808⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨913617918536,0,false,-203639376128,-203639376064⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1068082700366,0,false,-31886864320,-31886864256⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1068163638869,0,false,-31803547328,-31803547264⟩
    { al := (691659/4096000), au := (173127/1024000), zl := (7999/8000), zu := 1,
      A := ⟨185665799061,185893700764⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171557544384,171557544448⟩ : DyadicInterval 40),(⟨-203365127296,-203365127232⟩ : DyadicInterval 40),(⟨746372067565,746372086894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171752504512,171752504576⟩ : DyadicInterval 40),(⟨-203639365952,-203639365888⟩ : DyadicInterval 40),(⟨746333187143,746333206473⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171537688832,171537688896⟩ : DyadicInterval 40),(⟨-203337204224,-203337204160⟩ : DyadicInterval 40),(⟨746376024187,746376043517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171752504512,171752504576⟩ : DyadicInterval 40),(⟨-203639365952,-203639365888⟩ : DyadicInterval 40),(⟨746333187143,746333206473⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11864424⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11864320,11864384⟩ : DyadicInterval 40),(⟨-11864512,-11864448⟩ : DyadicInterval 40),(⟨762123383519,762123402848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-192,0⟩ : DyadicInterval 40),(⟨762123383616,762123402976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨185654190125,185893709240⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171547612544,171547612608⟩ : DyadicInterval 40),(⟨-203351159872,-203351159808⟩ : DyadicInterval 40),(⟨746374046752,746374066082⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171752511744,171752511808⟩ : DyadicInterval 40),(⟨-203639376128,-203639376064⟩ : DyadicInterval 40),(⟨746333185697,746333205026⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31886864320,-31803547264⟩ : DyadicInterval 40),(⟨778025157248,778066835040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨171557544384,171752504576⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-203639365952,-203365127232⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1458_ok : ecellOkT e1458 = true := by decide +kernel
theorem e1458_pos {a z : ℝ} (ha1 : ((691659/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((173127/1024000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1458 e1458_ok ha1 ha2 hz1 hz2 hz

-- box ['173127/1024000', '693357/4096000', '999/1000', '7993/8000']  interval_lower 14062573/1099511627776
noncomputable def e1459 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1285405328539,0,true,171752504512,171752504576⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨913617927013,0,false,-203639365952,-203639365888⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1285633230242,0,true,171947430080,171947430144⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨913390025310,0,false,-203913672960,-203913672896⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1285219434838,0,true,171593483008,171593483072⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨913803820714,0,false,-203415671232,-203415671168⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1285470373840,0,true,171808141632,171808141696⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨913552881712,0,false,-203717648768,-203717648704⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594674916,0,true,83043968,83044032⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099428580636,0,false,-83050304,-83050240⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099606660911,0,true,95028992,95029056⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099416594641,0,false,-95037248,-95037184⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619562,0,false,-8256,-8192⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621504,0,false,-6336,-6272⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1285312377807,0,true,171672993344,171672993408⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨913710877745,0,false,-203527508224,-203527508160⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1285551811263,0,true,171877795968,171877796032⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨913471444289,0,false,-203815667584,-203815667520⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068033152244,0,false,-31937871616,-31937871552⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068114125613,0,false,-31854514816,-31854514752⟩
    { al := (173127/1024000), au := (693357/4096000), zl := (999/1000), zu := (7993/8000),
      A := ⟨185893700763,186121602466⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171752504512,171752504576⟩ : DyadicInterval 40),(⟨-203639365952,-203639365888⟩ : DyadicInterval 40),(⟨746333187143,746333206473⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171947430080,171947430144⟩ : DyadicInterval 40),(⟨-203913672960,-203913672896⟩ : DyadicInterval 40),(⟨746294258065,746294277394⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171593483008,171593483072⟩ : DyadicInterval 40),(⟨-203415671232,-203415671168⟩ : DyadicInterval 40),(⟨746364904599,746364923928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171808141632,171808141696⟩ : DyadicInterval 40),(⟨-203717648768,-203717648704⟩ : DyadicInterval 40),(⟨746322081370,746322100699⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨83047140,95033135⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨83043968,83044032⟩ : DyadicInterval 40),(⟨-83050304,-83050240⟩ : DyadicInterval 40),(⟨762123380447,762123399776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨95028992,95029056⟩ : DyadicInterval 40),(⟨-95037248,-95037184⟩ : DyadicInterval 40),(⟨762123379465,762123398795⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8256,-6272⟩ : DyadicInterval 40),(⟨762123386752,762123407008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨185800750031,186040183487⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171672993344,171672993408⟩ : DyadicInterval 40),(⟨-203527508224,-203527508160⟩ : DyadicInterval 40),(⟨746349050557,746349069886⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171877795968,171877796032⟩ : DyadicInterval 40),(⟨-203815667584,-203815667520⟩ : DyadicInterval 40),(⟨746308171230,746308190560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31937871616,-31854514752⟩ : DyadicInterval 40),(⟨778050640992,778092338688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨171752504512,171947430144⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-203913672960,-203639365888⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1459_ok : ecellOkT e1459 = true := by decide +kernel
theorem e1459_pos {a z : ℝ} (ha1 : ((173127/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((693357/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1459 e1459_ok ha1 ha2 hz1 hz2 hz

-- box ['173127/1024000', '693357/4096000', '7993/8000', '3997/4000']  interval_lower 107979/8589934592
noncomputable def e1460 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1285405328539,0,true,171752504512,171752504576⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨913617927013,0,false,-203639365952,-203639365888⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1285633230242,0,true,171947430080,171947430144⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨913390025310,0,false,-203913672960,-203913672896⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1285242671550,0,true,171613361984,171613362048⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨913780584002,0,false,-203443630592,-203443630528⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1285493639041,0,true,171828041088,171828041152⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨913529616511,0,false,-203745650112,-203745650048⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582811190,0,true,71181056,71181120⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099440444362,0,false,-71185728,-71185664⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594782023,0,true,83151040,83151104⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099428473529,0,false,-83157440,-83157376⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621487,0,false,-6336,-6272⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623168,0,false,-4672,-4608⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1285323995939,0,true,171682931968,171682932032⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨913699259613,0,false,-203541488960,-203541488896⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1285563443667,0,true,171887744896,171887744960⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨913459811885,0,false,-203829669184,-203829669120⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068029215656,0,false,-31941924224,-31941924160⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068110198915,0,false,-31858556992,-31858556928⟩
    { al := (173127/1024000), au := (693357/4096000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨185893700763,186121602466⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171752504512,171752504576⟩ : DyadicInterval 40),(⟨-203639365952,-203639365888⟩ : DyadicInterval 40),(⟨746333187143,746333206473⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171947430080,171947430144⟩ : DyadicInterval 40),(⟨-203913672960,-203913672896⟩ : DyadicInterval 40),(⟨746294258065,746294277394⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171613361984,171613362048⟩ : DyadicInterval 40),(⟨-203443630592,-203443630528⟩ : DyadicInterval 40),(⟨746360941672,746360961002⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171828041088,171828041152⟩ : DyadicInterval 40),(⟨-203745650112,-203745650048⟩ : DyadicInterval 40),(⟨746318108128,746318127458⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨71183414,83154247⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨71181056,71181120⟩ : DyadicInterval 40),(⟨-71185728,-71185664⟩ : DyadicInterval 40),(⟨762123381279,762123400608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨83151040,83151104⟩ : DyadicInterval 40),(⟨-83157440,-83157376⟩ : DyadicInterval 40),(⟨762123380462,762123399792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6336,-4608⟩ : DyadicInterval 40),(⟨762123385920,762123406048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨185812368163,186051815891⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171682931968,171682932032⟩ : DyadicInterval 40),(⟨-203541488960,-203541488896⟩ : DyadicInterval 40),(⟨746347068180,746347087510⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171887744896,171887744960⟩ : DyadicInterval 40),(⟨-203829669184,-203829669120⟩ : DyadicInterval 40),(⟨746306183849,746306203178⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31941924224,-31858556928⟩ : DyadicInterval 40),(⟨778052662080,778094364992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨171752504512,171947430144⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-203913672960,-203639365888⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1460_ok : ecellOkT e1460 = true := by decide +kernel
theorem e1460_pos {a z : ℝ} (ha1 : ((173127/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((693357/4096000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1460 e1460_ok ha1 ha2 hz1 hz2 hz

-- box ['693357/4096000', '347103/2048000', '999/1000', '7993/8000']  interval_lower 8275839/549755813888
noncomputable def e1461 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1285633230241,0,true,171947430080,171947430144⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨913390025311,0,false,-203913672960,-203913672896⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1285861131944,0,true,172142321088,172142321152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨913162123608,0,false,-204188048448,-204188048384⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1285447108638,0,true,171788241856,171788241920⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨913576146914,0,false,-203689648192,-203689648128⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1285698076128,0,true,172002886784,172002886848⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨913325179424,0,false,-203991735296,-203991735232⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594781063,0,true,83150080,83150144⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099428474489,0,false,-83156480,-83156416⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099606782241,0,true,95150336,95150400⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099416473311,0,false,-95158592,-95158528⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619541,0,false,-8256,-8192⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621488,0,false,-6336,-6272⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1285540165560,0,true,171867835520,171867835584⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨913483089992,0,false,-203801650176,-203801650112⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1285779613259,0,true,172072614080,172072614144⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨913243642293,0,false,-204089898624,-204089898560⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067956015684,0,false,-32017284480,-32017284416⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068037093087,0,false,-31933814656,-31933814592⟩
    { al := (693357/4096000), au := (347103/2048000), zl := (999/1000), zu := (7993/8000),
      A := ⟨186121602465,186349504168⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171947430080,171947430144⟩ : DyadicInterval 40),(⟨-203913672960,-203913672896⟩ : DyadicInterval 40),(⟨746294258065,746294277395⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172142321088,172142321152⟩ : DyadicInterval 40),(⟨-204188048448,-204188048384⟩ : DyadicInterval 40),(⟨746255280372,746255299701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171788241856,171788241920⟩ : DyadicInterval 40),(⟨-203689648192,-203689648128⟩ : DyadicInterval 40),(⟨746326054104,746326073434⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172002886784,172002886848⟩ : DyadicInterval 40),(⟨-203991735296,-203991735232⟩ : DyadicInterval 40),(⟨746283172540,746283191870⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨83153287,95154465⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨83150080,83150144⟩ : DyadicInterval 40),(⟨-83156480,-83156416⟩ : DyadicInterval 40),(⟨762123380463,762123399792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨95150336,95150400⟩ : DyadicInterval 40),(⟨-95158592,-95158528⟩ : DyadicInterval 40),(⟨762123379444,762123398774⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8256,-6272⟩ : DyadicInterval 40),(⟨762123386752,762123407008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨186028537784,186267985483⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171867835520,171867835584⟩ : DyadicInterval 40),(⟨-203801650176,-203801650112⟩ : DyadicInterval 40),(⟨746310160798,746310180127⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172072614080,172072614144⟩ : DyadicInterval 40),(⟨-204089898624,-204089898560⟩ : DyadicInterval 40),(⟨746269227975,746269247304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32017284480,-31933814592⟩ : DyadicInterval 40),(⟨778090290912,778132045120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨171947430080,172142321152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-204188048448,-203913672896⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1461_ok : ecellOkT e1461 = true := by decide +kernel
theorem e1461_pos {a z : ℝ} (ha1 : ((693357/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((347103/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1461 e1461_ok ha1 ha2 hz1 hz2 hz

-- box ['693357/4096000', '347103/2048000', '7993/8000', '3997/4000']  interval_lower 8154555/549755813888
noncomputable def e1462 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1285633230241,0,true,171947430080,171947430144⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨913390025311,0,false,-203913672960,-203913672896⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1285861131944,0,true,172142321088,172142321152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨913162123608,0,false,-204188048448,-204188048384⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1285470373838,0,true,171808141632,171808141696⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨913552881714,0,false,-203717648768,-203717648704⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1285721369817,0,true,172022807104,172022807168⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨913301885735,0,false,-204019777856,-204019777792⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582902174,0,true,71272064,71272128⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099440353378,0,false,-71276736,-71276672⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594888188,0,true,83257216,83257280⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099428367364,0,false,-83263616,-83263552⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621471,0,false,-6336,-6272⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623156,0,false,-4672,-4608⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1285551797933,0,true,171877784576,171877784640⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨913471457619,0,false,-203815651584,-203815651520⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1285791259912,0,true,172082573440,172082573504⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨913231995640,0,false,-204103920832,-204103920768⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067952069448,0,false,-32021347328,-32021347264⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068033156756,0,false,-31937866944,-31937866880⟩
    { al := (693357/4096000), au := (347103/2048000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨186121602465,186349504168⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171947430080,171947430144⟩ : DyadicInterval 40),(⟨-203913672960,-203913672896⟩ : DyadicInterval 40),(⟨746294258065,746294277395⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172142321088,172142321152⟩ : DyadicInterval 40),(⟨-204188048448,-204188048384⟩ : DyadicInterval 40),(⟨746255280372,746255299701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171808141632,171808141696⟩ : DyadicInterval 40),(⟨-203717648768,-203717648704⟩ : DyadicInterval 40),(⟨746322081370,746322100700⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172022807104,172022807168⟩ : DyadicInterval 40),(⟨-204019777856,-204019777792⟩ : DyadicInterval 40),(⟨746279189426,746279208756⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨71274398,83260412⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨71272064,71272128⟩ : DyadicInterval 40),(⟨-71276736,-71276672⟩ : DyadicInterval 40),(⟨762123381267,762123400596⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨83257216,83257280⟩ : DyadicInterval 40),(⟨-83263616,-83263552⟩ : DyadicInterval 40),(⟨762123380446,762123399776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6336,-4608⟩ : DyadicInterval 40),(⟨762123385920,762123406048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨186040170157,186279632136⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171877784576,171877784640⟩ : DyadicInterval 40),(⟨-203815651584,-203815651520⟩ : DyadicInterval 40),(⟨746308173521,746308192850⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172082573440,172082573504⟩ : DyadicInterval 40),(⟨-204103920832,-204103920768⟩ : DyadicInterval 40),(⟨746267235653,746267254982⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32021347328,-31937866880⟩ : DyadicInterval 40),(⟨778092317056,778134076544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨171947430080,172142321152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-204188048448,-203913672896⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1462_ok : ecellOkT e1462 = true := by decide +kernel
theorem e1462_pos {a z : ℝ} (ha1 : ((693357/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((347103/2048000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1462 e1462_ok ha1 ha2 hz1 hz2 hz

-- box ['173127/1024000', '693357/4096000', '3997/4000', '1599/1600']  interval_lower 6789645/549755813888
noncomputable def e1463 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1285405328539,0,true,171752504512,171752504576⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨913617927013,0,false,-203639365952,-203639365888⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1285633230242,0,true,171947430080,171947430144⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨913390025310,0,false,-203913672960,-203913672896⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1285265908263,0,true,171633240576,171633240640⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨913757347289,0,false,-203471590656,-203471590592⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1285516904241,0,true,171847940160,171847940224⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨913506351311,0,false,-203773652096,-203773652032⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570947403,0,true,59318016,59318080⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452308149,0,false,-59321280,-59321216⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582903070,0,true,71272960,71273024⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099440352482,0,false,-71277632,-71277568⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623155,0,false,-4672,-4608⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624576,0,false,-3264,-3200⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1285335614100,0,true,171692870464,171692870528⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨913687641452,0,false,-203555469888,-203555469824⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1285575076104,0,true,171897693824,171897693888⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨913448179448,0,false,-203843670976,-203843670912⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068025278810,0,false,-31945977152,-31945977088⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068106271961,0,false,-31862599360,-31862599296⟩
    { al := (173127/1024000), au := (693357/4096000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨185893700763,186121602466⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171752504512,171752504576⟩ : DyadicInterval 40),(⟨-203639365952,-203639365888⟩ : DyadicInterval 40),(⟨746333187143,746333206473⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171947430080,171947430144⟩ : DyadicInterval 40),(⟨-203913672960,-203913672896⟩ : DyadicInterval 40),(⟨746294258065,746294277394⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171633240576,171633240640⟩ : DyadicInterval 40),(⟨-203471590656,-203471590592⟩ : DyadicInterval 40),(⟨746356978251,746356997581⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171847940160,171847940224⟩ : DyadicInterval 40),(⟨-203773652096,-203773652032⟩ : DyadicInterval 40),(⟨746314134364,746314153693⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨59319627,71275294⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59318016,59318080⟩ : DyadicInterval 40),(⟨-59321280,-59321216⟩ : DyadicInterval 40),(⟨762123381983,762123401312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨71272960,71273024⟩ : DyadicInterval 40),(⟨-71277632,-71277568⟩ : DyadicInterval 40),(⟨762123381267,762123400596⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4672,-3200⟩ : DyadicInterval 40),(⟨762123385216,762123405216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨185823986324,186063448328⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171692870464,171692870528⟩ : DyadicInterval 40),(⟨-203555469888,-203555469824⟩ : DyadicInterval 40),(⟨746345085700,746345105030⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171897693824,171897693888⟩ : DyadicInterval 40),(⟨-203843670976,-203843670912⟩ : DyadicInterval 40),(⟨746304196288,746304215618⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31945977152,-31862599296⟩ : DyadicInterval 40),(⟨778054683264,778096391456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨171752504512,171947430144⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-203913672960,-203639365888⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1463_ok : ecellOkT e1463 = true := by decide +kernel
theorem e1463_pos {a z : ℝ} (ha1 : ((173127/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((693357/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1463 e1463_ok ha1 ha2 hz1 hz2 hz

-- box ['173127/1024000', '693357/4096000', '1599/1600', '1999/2000']  interval_lower 6668763/549755813888
noncomputable def e1464 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1285405328539,0,true,171752504512,171752504576⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨913617927013,0,false,-203639365952,-203639365888⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1285633230242,0,true,171947430080,171947430144⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨913390025310,0,false,-203913672960,-203913672896⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1285289144975,0,true,171653118784,171653118848⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨913734110577,0,false,-203499551424,-203499551360⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1285540169441,0,true,171867838848,171867838912⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨913483086111,0,false,-203801654848,-203801654784⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099559083552,0,true,47454720,47454784⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464172000,0,false,-47456832,-47456768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571024055,0,true,59394624,59394688⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452231497,0,false,-59397888,-59397824⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624567,0,false,-3264,-3200⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625728,0,false,-2112,-2048⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1285347232289,0,true,171702808960,171702809024⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨913676023263,0,false,-203569451072,-203569451008⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1285586708565,0,true,171907642624,171907642688⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨913436546987,0,false,-203857672960,-203857672896⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068021341710,0,false,-31950030336,-31950030272⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068102344753,0,false,-31866642048,-31866641984⟩
    { al := (173127/1024000), au := (693357/4096000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨185893700763,186121602466⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171752504512,171752504576⟩ : DyadicInterval 40),(⟨-203639365952,-203639365888⟩ : DyadicInterval 40),(⟨746333187143,746333206473⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171947430080,171947430144⟩ : DyadicInterval 40),(⟨-203913672960,-203913672896⟩ : DyadicInterval 40),(⟨746294258065,746294277394⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171653118784,171653118848⟩ : DyadicInterval 40),(⟨-203499551424,-203499551360⟩ : DyadicInterval 40),(⟨746353014337,746353033667⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171867838848,171867838912⟩ : DyadicInterval 40),(⟨-203801654848,-203801654784⟩ : DyadicInterval 40),(⟨746310160130,746310179459⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨47455776,59396279⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨47454720,47454784⟩ : DyadicInterval 40),(⟨-47456832,-47456768⟩ : DyadicInterval 40),(⟨762123382559,762123401888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59394624,59394688⟩ : DyadicInterval 40),(⟨-59397888,-59397824⟩ : DyadicInterval 40),(⟨762123381975,762123401304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3264,-2048⟩ : DyadicInterval 40),(⟨762123384640,762123404512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨185835604513,186075080789⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171702808960,171702809024⟩ : DyadicInterval 40),(⟨-203569451072,-203569451008⟩ : DyadicInterval 40),(⟨746343103069,746343122399⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171907642624,171907642688⟩ : DyadicInterval 40),(⟨-203857672960,-203857672896⟩ : DyadicInterval 40),(⟨746302208625,746302227955⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31950030336,-31866641984⟩ : DyadicInterval 40),(⟨778056704608,778098418048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨171752504512,171947430144⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-203913672960,-203639365888⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1464_ok : ecellOkT e1464 = true := by decide +kernel
theorem e1464_pos {a z : ℝ} (ha1 : ((173127/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((693357/4096000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1464 e1464_ok ha1 ha2 hz1 hz2 hz

-- box ['693357/4096000', '347103/2048000', '3997/4000', '1599/1600']  interval_lower 4016603/274877906944
noncomputable def e1465 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1285633230241,0,true,171947430080,171947430144⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨913390025311,0,false,-203913672960,-203913672896⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1285861131944,0,true,172142321088,172142321152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨913162123608,0,false,-204188048448,-204188048384⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1285493639039,0,true,171828041088,171828041152⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨913529616513,0,false,-203745650112,-203745650048⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1285744663504,0,true,172042726976,172042727040⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨913278592048,0,false,-204047821184,-204047821120⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571023223,0,true,59393792,59393856⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452232329,0,false,-59397056,-59396992⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582994071,0,true,71363968,71364032⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099440261481,0,false,-71368640,-71368576⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623143,0,false,-4672,-4608⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624568,0,false,-3264,-3200⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1285563430338,0,true,171887733504,171887733568⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨913459825214,0,false,-203829653120,-203829653056⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1285802906584,0,true,172092532736,172092532800⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨913220348968,0,false,-204117943232,-204117943168⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067948122958,0,false,-32025410496,-32025410432⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068029220167,0,false,-31941919616,-31941919552⟩
    { al := (693357/4096000), au := (347103/2048000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨186121602465,186349504168⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171947430080,171947430144⟩ : DyadicInterval 40),(⟨-203913672960,-203913672896⟩ : DyadicInterval 40),(⟨746294258065,746294277395⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172142321088,172142321152⟩ : DyadicInterval 40),(⟨-204188048448,-204188048384⟩ : DyadicInterval 40),(⟨746255280372,746255299701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171828041088,171828041152⟩ : DyadicInterval 40),(⟨-203745650112,-203745650048⟩ : DyadicInterval 40),(⟨746318108129,746318127459⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172042726976,172042727040⟩ : DyadicInterval 40),(⟨-204047821184,-204047821120⟩ : DyadicInterval 40),(⟨746275205878,746275225207⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨59395447,71366295⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59393792,59393856⟩ : DyadicInterval 40),(⟨-59397056,-59396992⟩ : DyadicInterval 40),(⟨762123381975,762123401304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨71363968,71364032⟩ : DyadicInterval 40),(⟨-71368640,-71368576⟩ : DyadicInterval 40),(⟨762123381255,762123400584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4672,-3200⟩ : DyadicInterval 40),(⟨762123385216,762123405216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨186051802562,186291278808⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171887733504,171887733568⟩ : DyadicInterval 40),(⟨-203829653120,-203829653056⟩ : DyadicInterval 40),(⟨746306186113,746306205443⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172092532736,172092532800⟩ : DyadicInterval 40),(⟨-204117943232,-204117943168⟩ : DyadicInterval 40),(⟨746265243190,746265262519⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32025410496,-31941919552⟩ : DyadicInterval 40),(⟨778094343392,778136108128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨171947430080,172142321152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-204188048448,-203913672896⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1465_ok : ecellOkT e1465 = true := by decide +kernel
theorem e1465_pos {a z : ℝ} (ha1 : ((693357/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((347103/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1465 e1465_ok ha1 ha2 hz1 hz2 hz

-- box ['693357/4096000', '347103/2048000', '1599/1600', '1999/2000']  interval_lower 15823705/1099511627776
noncomputable def e1466 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1285633230241,0,true,171947430080,171947430144⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨913390025311,0,false,-203913672960,-203913672896⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1285861131944,0,true,172142321088,172142321152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨913162123608,0,false,-204188048448,-204188048384⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1285516904239,0,true,171847940160,171847940224⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨913506351313,0,false,-203773652096,-203773652032⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1285767957193,0,true,172062646528,172062646592⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨913255298359,0,false,-204075865216,-204075865152⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099559144209,0,true,47515392,47515456⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464111343,0,false,-47517504,-47517440⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571099890,0,true,59470464,59470528⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452155662,0,false,-59473728,-59473664⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624559,0,false,-3264,-3200⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625723,0,false,-2112,-2048⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1285575062773,0,true,171897682432,171897682496⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨913448192779,0,false,-203843654912,-203843654848⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1285814553292,0,true,172102491968,172102492032⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨913208702260,0,false,-204131965888,-204131965824⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067944176210,0,false,-32029473856,-32029473792⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068025283323,0,false,-31945972480,-31945972416⟩
    { al := (693357/4096000), au := (347103/2048000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨186121602465,186349504168⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171947430080,171947430144⟩ : DyadicInterval 40),(⟨-203913672960,-203913672896⟩ : DyadicInterval 40),(⟨746294258065,746294277395⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172142321088,172142321152⟩ : DyadicInterval 40),(⟨-204188048448,-204188048384⟩ : DyadicInterval 40),(⟨746255280372,746255299701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171847940160,171847940224⟩ : DyadicInterval 40),(⟨-203773652096,-203773652032⟩ : DyadicInterval 40),(⟨746314134365,746314153694⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172062646528,172062646592⟩ : DyadicInterval 40),(⟨-204075865216,-204075865152⟩ : DyadicInterval 40),(⟨746271221792,746271241121⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨47516433,59472114⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨47515392,47515456⟩ : DyadicInterval 40),(⟨-47517504,-47517440⟩ : DyadicInterval 40),(⟨762123382554,762123401883⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59470464,59470528⟩ : DyadicInterval 40),(⟨-59473728,-59473664⟩ : DyadicInterval 40),(⟨762123381967,762123401296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3264,-2048⟩ : DyadicInterval 40),(⟨762123384640,762123404512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨186063434997,186302925516⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171897682432,171897682496⟩ : DyadicInterval 40),(⟨-203843654912,-203843654848⟩ : DyadicInterval 40),(⟨746304198553,746304217883⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172102491968,172102492032⟩ : DyadicInterval 40),(⟨-204131965888,-204131965824⟩ : DyadicInterval 40),(⟨746263250611,746263269940⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32029473856,-31945972416⟩ : DyadicInterval 40),(⟨778096369824,778138139808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨171947430080,172142321152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-204188048448,-203913672896⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1466_ok : ecellOkT e1466 = true := by decide +kernel
theorem e1466_pos {a z : ℝ} (ha1 : ((693357/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((347103/2048000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1466 e1466_ok ha1 ha2 hz1 hz2 hz

-- box ['347103/2048000', '139011/819200', '999/1000', '7993/8000']  interval_lower 9526659/549755813888
noncomputable def e1467 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1285861131943,0,true,172142321088,172142321152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨913162123609,0,false,-204188048448,-204188048384⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1286089033647,0,true,172337177600,172337177664⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨912934221905,0,false,-204462492416,-204462492352⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1285674782438,0,true,171982966208,171982966272⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨913348473114,0,false,-203963693376,-203963693312⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1285925778417,0,true,172197597504,172197597568⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨913097477135,0,false,-204265890112,-204265890048⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594887227,0,true,83256256,83256320⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099428368325,0,false,-83262656,-83262592⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099606903591,0,true,95271680,95271744⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099416351961,0,false,-95280000,-95279936⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619520,0,false,-8320,-8256⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621472,0,false,-6336,-6272⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1285767953314,0,true,172062643200,172062643264⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨913255302238,0,false,-204075860544,-204075860480⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1286007415265,0,true,172267397632,172267397696⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨913015840287,0,false,-204364198016,-204364197952⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067878784727,0,false,-32096800320,-32096800256⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067959966178,0,false,-32013217280,-32013217216⟩
    { al := (347103/2048000), au := (139011/819200), zl := (999/1000), zu := (7993/8000),
      A := ⟨186349504167,186577405871⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172142321088,172142321152⟩ : DyadicInterval 40),(⟨-204188048448,-204188048384⟩ : DyadicInterval 40),(⟨746255280372,746255299701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172337177600,172337177664⟩ : DyadicInterval 40),(⟨-204462492416,-204462492352⟩ : DyadicInterval 40),(⟨746216254015,746216273345⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171982966208,171982966272⟩ : DyadicInterval 40),(⟨-203963693376,-203963693312⟩ : DyadicInterval 40),(⟨746287155053,746287174383⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172197597504,172197597568⟩ : DyadicInterval 40),(⟨-204265890112,-204265890048⟩ : DyadicInterval 40),(⟨746244215108,746244234438⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨83259451,95275815⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨83256256,83256320⟩ : DyadicInterval 40),(⟨-83262656,-83262592⟩ : DyadicInterval 40),(⟨762123380447,762123399776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨95271680,95271744⟩ : DyadicInterval 40),(⟨-95280000,-95279936⟩ : DyadicInterval 40),(⟨762123379455,762123398785⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8320,-6272⟩ : DyadicInterval 40),(⟨762123386752,762123407040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨186256325538,186495787489⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172062643200,172062643264⟩ : DyadicInterval 40),(⟨-204075860544,-204075860480⟩ : DyadicInterval 40),(⟨746271222461,746271241790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172267397632,172267397696⟩ : DyadicInterval 40),(⟨-204364198016,-204364197952⟩ : DyadicInterval 40),(⟨746230236128,746230255458⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32096800320,-32013217216⟩ : DyadicInterval 40),(⟨778129992224,778171803040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨172142321088,172337177664⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-204462492416,-204188048384⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1467_ok : ecellOkT e1467 = true := by decide +kernel
theorem e1467_pos {a z : ℝ} (ha1 : ((347103/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((139011/819200 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1467 e1467_ok ha1 ha2 hz1 hz2 hz

-- box ['347103/2048000', '139011/819200', '7993/8000', '3997/4000']  interval_lower 587809/34359738368
noncomputable def e1468 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1285861131943,0,true,172142321088,172142321152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨913162123609,0,false,-204188048448,-204188048384⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1286089033647,0,true,172337177600,172337177664⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨912934221905,0,false,-204462492416,-204462492352⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1285698076126,0,true,172002886784,172002886848⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨913325179426,0,false,-203991735296,-203991735232⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1285949100593,0,true,172217538560,172217538624⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨913074154959,0,false,-204293974016,-204293973952⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582993173,0,true,71363072,71363136⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099440262379,0,false,-71367744,-71367680⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594994370,0,true,83363392,83363456⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099428261182,0,false,-83369792,-83369728⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621455,0,false,-6336,-6272⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623144,0,false,-4672,-4608⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1285779599923,0,true,172072602624,172072602688⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨913243655629,0,false,-204089882560,-204089882496⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1286019076151,0,true,172277367424,172277367488⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨913004179401,0,false,-204378240896,-204378240832⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067874828836,0,false,-32100873408,-32100873344⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067956020204,0,false,-32017279872,-32017279808⟩
    { al := (347103/2048000), au := (139011/819200), zl := (7993/8000), zu := (3997/4000),
      A := ⟨186349504167,186577405871⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172142321088,172142321152⟩ : DyadicInterval 40),(⟨-204188048448,-204188048384⟩ : DyadicInterval 40),(⟨746255280372,746255299701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172337177600,172337177664⟩ : DyadicInterval 40),(⟨-204462492416,-204462492352⟩ : DyadicInterval 40),(⟨746216254015,746216273345⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172002886784,172002886848⟩ : DyadicInterval 40),(⟨-203991735296,-203991735232⟩ : DyadicInterval 40),(⟨746283172540,746283191870⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172217538560,172217538624⟩ : DyadicInterval 40),(⟨-204293974016,-204293973952⟩ : DyadicInterval 40),(⟨746240222224,746240241554⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨71365397,83366594⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨71363072,71363136⟩ : DyadicInterval 40),(⟨-71367744,-71367680⟩ : DyadicInterval 40),(⟨762123381255,762123400585⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨83363392,83363456⟩ : DyadicInterval 40),(⟨-83369792,-83369728⟩ : DyadicInterval 40),(⟨762123380430,762123399760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6336,-4608⟩ : DyadicInterval 40),(⟨762123385920,762123406048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨186267972147,186507448375⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172072602624,172072602688⟩ : DyadicInterval 40),(⟨-204089882560,-204089882496⟩ : DyadicInterval 40),(⟨746269230283,746269249613⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172277367424,172277367488⟩ : DyadicInterval 40),(⟨-204378240896,-204378240832⟩ : DyadicInterval 40),(⟨746228238881,746228258211⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32100873408,-32017279808⟩ : DyadicInterval 40),(⟨778132023520,778173839584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨172142321088,172337177664⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-204462492416,-204188048384⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1468_ok : ecellOkT e1468 = true := by decide +kernel
theorem e1468_pos {a z : ℝ} (ha1 : ((347103/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((139011/819200 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1468 e1468_ok ha1 ha2 hz1 hz2 hz

-- box ['139011/819200', '21747/128000', '999/1000', '7993/8000']  interval_lower 21568179/1099511627776
noncomputable def e1469 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1286089033646,0,true,172337177600,172337177664⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨912934221906,0,false,-204462492416,-204462492352⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1286316935349,0,true,172531999552,172531999616⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨912706320203,0,false,-204737004928,-204737004864⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1285902456240,0,true,172177656064,172177656128⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨913120799312,0,false,-204237806976,-204237806912⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1286153480705,0,true,172392273728,172392273792⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨912869774847,0,false,-204540113344,-204540113280⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594993407,0,true,83362432,83362496⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099428262145,0,false,-83368832,-83368768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099607024959,0,true,95393024,95393088⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099416230593,0,false,-95401344,-95401280⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619499,0,false,-8320,-8256⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621456,0,false,-6336,-6272⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1285995741066,0,true,172257416384,172257416448⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨913027514486,0,false,-204350139264,-204350139200⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1286235217264,0,true,172462146752,172462146816⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨912788038288,0,false,-204638565888,-204638565824⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067801459378,0,false,-32176419136,-32176419072⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067882744888,0,false,-32092722880,-32092722816⟩
    { al := (139011/819200), au := (21747/128000), zl := (999/1000), zu := (7993/8000),
      A := ⟨186577405870,186805307573⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172337177600,172337177664⟩ : DyadicInterval 40),(⟨-204462492416,-204462492352⟩ : DyadicInterval 40),(⟨746216254016,746216273345⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172531999552,172531999616⟩ : DyadicInterval 40),(⟨-204737004928,-204737004864⟩ : DyadicInterval 40),(⟨746177179050,746177198380⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172177656064,172177656128⟩ : DyadicInterval 40),(⟨-204237806976,-204237806912⟩ : DyadicInterval 40),(⟨746248207516,746248226846⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172392273728,172392273792⟩ : DyadicInterval 40),(⟨-204540113344,-204540113280⟩ : DyadicInterval 40),(⟨746205209154,746205228483⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨83365631,95397183⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨83362432,83362496⟩ : DyadicInterval 40),(⟨-83368832,-83368768⟩ : DyadicInterval 40),(⟨762123380430,762123399760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨95393024,95393088⟩ : DyadicInterval 40),(⟨-95401344,-95401280⟩ : DyadicInterval 40),(⟨762123379434,762123398764⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8320,-6272⟩ : DyadicInterval 40),(⟨762123386752,762123407040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨186484113290,186723589488⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172257416384,172257416448⟩ : DyadicInterval 40),(⟨-204350139264,-204350139200⟩ : DyadicInterval 40),(⟨746232235510,746232254839⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172462146752,172462146816⟩ : DyadicInterval 40),(⟨-204638565888,-204638565824⟩ : DyadicInterval 40),(⟨746191195661,746191214991⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32176419136,-32092722816⟩ : DyadicInterval 40),(⟨778169745024,778211612448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨172337177600,172531999616⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-204737004928,-204462492352⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1469_ok : ecellOkT e1469 = true := by decide +kernel
theorem e1469_pos {a z : ℝ} (ha1 : ((139011/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((21747/128000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1469 e1469_ok ha1 ha2 hz1 hz2 hz

-- box ['139011/819200', '21747/128000', '7993/8000', '3997/4000']  interval_lower 10661763/549755813888
noncomputable def e1470 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1286089033646,0,true,172337177600,172337177664⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨912934221906,0,false,-204462492416,-204462492352⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1286316935349,0,true,172531999552,172531999616⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨912706320203,0,false,-204737004928,-204737004864⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1285925778415,0,true,172197597504,172197597568⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨913097477137,0,false,-204265890112,-204265890048⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1286176831369,0,true,172412235648,172412235712⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨912846424183,0,false,-204568238592,-204568238528⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099583084186,0,true,71454080,71454144⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099440171366,0,false,-71458752,-71458688⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099595100568,0,true,83469568,83469632⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099428154984,0,false,-83475968,-83475904⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621438,0,false,-6400,-6336⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623133,0,false,-4672,-4608⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1286007401925,0,true,172267386240,172267386304⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨913015853627,0,false,-204364181952,-204364181888⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1286246892395,0,true,172472126912,172472126976⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨912776363157,0,false,-204652629376,-204652629312⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067797493817,0,false,-32180502464,-32180502400⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067878789254,0,false,-32096795648,-32096795584⟩
    { al := (139011/819200), au := (21747/128000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨186577405870,186805307573⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172337177600,172337177664⟩ : DyadicInterval 40),(⟨-204462492416,-204462492352⟩ : DyadicInterval 40),(⟨746216254016,746216273345⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172531999552,172531999616⟩ : DyadicInterval 40),(⟨-204737004928,-204737004864⟩ : DyadicInterval 40),(⟨746177179050,746177198380⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172197597504,172197597568⟩ : DyadicInterval 40),(⟨-204265890112,-204265890048⟩ : DyadicInterval 40),(⟨746244215108,746244234438⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172412235648,172412235712⟩ : DyadicInterval 40),(⟨-204568238592,-204568238528⟩ : DyadicInterval 40),(⟨746201206400,746201225729⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨71456410,83472792⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨71454080,71454144⟩ : DyadicInterval 40),(⟨-71458752,-71458688⟩ : DyadicInterval 40),(⟨762123381243,762123400573⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨83469568,83469632⟩ : DyadicInterval 40),(⟨-83475968,-83475904⟩ : DyadicInterval 40),(⟨762123380414,762123399744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6400,-4608⟩ : DyadicInterval 40),(⟨762123385920,762123406080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨186495774149,186735264619⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172267386240,172267386304⟩ : DyadicInterval 40),(⟨-204364181952,-204364181888⟩ : DyadicInterval 40),(⟨746230238406,746230257735⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172472126912,172472126976⟩ : DyadicInterval 40),(⟨-204652629376,-204652629312⟩ : DyadicInterval 40),(⟨746189193486,746189212815⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32180502464,-32096795584⟩ : DyadicInterval 40),(⟨778171781408,778213654112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨172337177600,172531999616⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-204737004928,-204462492352⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1470_ok : ecellOkT e1470 = true := by decide +kernel
theorem e1470_pos {a z : ℝ} (ha1 : ((139011/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((21747/128000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1470 e1470_ok ha1 ha2 hz1 hz2 hz

-- box ['347103/2048000', '139011/819200', '3997/4000', '1599/1600']  interval_lower 1160393/68719476736
noncomputable def e1471 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1285861131943,0,true,172142321088,172142321152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨913162123609,0,false,-204188048448,-204188048384⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1286089033647,0,true,172337177600,172337177664⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨912934221905,0,false,-204462492416,-204462492352⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1285721369814,0,true,172022807104,172022807168⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨913301885738,0,false,-204019777856,-204019777792⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1285972422769,0,true,172237479296,172237479360⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨913050832783,0,false,-204322058624,-204322058560⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571099056,0,true,59469632,59469696⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452156496,0,false,-59472896,-59472832⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099583085085,0,true,71454976,71455040⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099440170467,0,false,-71459648,-71459584⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623131,0,false,-4672,-4608⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624560,0,false,-3264,-3200⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1285791246575,0,true,172082562048,172082562112⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨913232008977,0,false,-204103904768,-204103904704⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1286030737072,0,true,172287337152,172287337216⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨912992518480,0,false,-204392283968,-204392283904⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067870872686,0,false,-32104946752,-32104946688⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067952073968,0,false,-32021342720,-32021342656⟩
    { al := (347103/2048000), au := (139011/819200), zl := (3997/4000), zu := (1599/1600),
      A := ⟨186349504167,186577405871⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172142321088,172142321152⟩ : DyadicInterval 40),(⟨-204188048448,-204188048384⟩ : DyadicInterval 40),(⟨746255280372,746255299701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172337177600,172337177664⟩ : DyadicInterval 40),(⟨-204462492416,-204462492352⟩ : DyadicInterval 40),(⟨746216254015,746216273345⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172022807104,172022807168⟩ : DyadicInterval 40),(⟨-204019777856,-204019777792⟩ : DyadicInterval 40),(⟨746279189427,746279208756⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172237479296,172237479360⟩ : DyadicInterval 40),(⟨-204322058624,-204322058560⟩ : DyadicInterval 40),(⟨746236228801,746236248131⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨59471280,71457309⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59469632,59469696⟩ : DyadicInterval 40),(⟨-59472896,-59472832⟩ : DyadicInterval 40),(⟨762123381967,762123401296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨71454976,71455040⟩ : DyadicInterval 40),(⟨-71459648,-71459584⟩ : DyadicInterval 40),(⟨762123381243,762123400573⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4672,-3200⟩ : DyadicInterval 40),(⟨762123385216,762123405216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨186279618799,186519109296⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172082562048,172082562112⟩ : DyadicInterval 40),(⟨-204103904768,-204103904704⟩ : DyadicInterval 40),(⟨746267237924,746267257253⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172287337152,172287337216⟩ : DyadicInterval 40),(⟨-204392283968,-204392283904⟩ : DyadicInterval 40),(⟨746226241490,746226260820⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32104946752,-32021342656⟩ : DyadicInterval 40),(⟨778134054944,778175876256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨172142321088,172337177664⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-204462492416,-204188048384⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1471_ok : ecellOkT e1471 = true := by decide +kernel
theorem e1471_pos {a z : ℝ} (ha1 : ((347103/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((139011/819200 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1471 e1471_ok ha1 ha2 hz1 hz2 hz

-- box ['347103/2048000', '139011/819200', '1599/1600', '1999/2000']  interval_lower 18322577/1099511627776
noncomputable def e1472 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1285861131943,0,true,172142321088,172142321152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨913162123609,0,false,-204188048448,-204188048384⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1286089033647,0,true,172337177600,172337177664⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨912934221905,0,false,-204462492416,-204462492352⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1285744663502,0,true,172042726976,172042727040⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨913278592050,0,false,-204047821184,-204047821120⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1285995744945,0,true,172257419712,172257419776⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨913027510607,0,false,-204350143936,-204350143872⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099559204875,0,true,47576064,47576128⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464050677,0,false,-47578176,-47578112⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571175736,0,true,59546304,59546368⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452079816,0,false,-59549632,-59549568⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624550,0,false,-3264,-3200⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625718,0,false,-2112,-2048⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1285802893248,0,true,172092521344,172092521408⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨913220362304,0,false,-204117927168,-204117927104⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1286042398026,0,true,172297306816,172297306880⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨912980857526,0,false,-204406327296,-204406327232⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067866916277,0,false,-32109020416,-32109020352⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067948127478,0,false,-32025405824,-32025405760⟩
    { al := (347103/2048000), au := (139011/819200), zl := (1599/1600), zu := (1999/2000),
      A := ⟨186349504167,186577405871⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172142321088,172142321152⟩ : DyadicInterval 40),(⟨-204188048448,-204188048384⟩ : DyadicInterval 40),(⟨746255280372,746255299701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172337177600,172337177664⟩ : DyadicInterval 40),(⟨-204462492416,-204462492352⟩ : DyadicInterval 40),(⟨746216254015,746216273345⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172042726976,172042727040⟩ : DyadicInterval 40),(⟨-204047821184,-204047821120⟩ : DyadicInterval 40),(⟨746275205878,746275225207⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172257419712,172257419776⟩ : DyadicInterval 40),(⟨-204350143936,-204350143872⟩ : DyadicInterval 40),(⟨746232234839,746232254169⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨47577099,59547960⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨47576064,47576128⟩ : DyadicInterval 40),(⟨-47578176,-47578112⟩ : DyadicInterval 40),(⟨762123382549,762123401878⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59546304,59546368⟩ : DyadicInterval 40),(⟨-59549632,-59549568⟩ : DyadicInterval 40),(⟨762123381990,762123401320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3264,-2048⟩ : DyadicInterval 40),(⟨762123384640,762123404512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨186291265472,186530770250⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172092521344,172092521408⟩ : DyadicInterval 40),(⟨-204117927168,-204117927104⟩ : DyadicInterval 40),(⟨746265245461,746265264791⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172297306816,172297306880⟩ : DyadicInterval 40),(⟨-204406327296,-204406327232⟩ : DyadicInterval 40),(⟨746224243984,746224263313⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32109020416,-32025405760⟩ : DyadicInterval 40),(⟨778136086496,778177913088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨172142321088,172337177664⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-204462492416,-204188048384⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1472_ok : ecellOkT e1472 = true := by decide +kernel
theorem e1472_pos {a z : ℝ} (ha1 : ((347103/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((139011/819200 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1472 e1472_ok ha1 ha2 hz1 hz2 hz

-- box ['139011/819200', '21747/128000', '3997/4000', '1599/1600']  interval_lower 10539501/549755813888
noncomputable def e1473 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1286089033646,0,true,172337177600,172337177664⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨912934221906,0,false,-204462492416,-204462492352⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1286316935349,0,true,172531999552,172531999616⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨912706320203,0,false,-204737004928,-204737004864⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1285949100591,0,true,172217538560,172217538624⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨913074154961,0,false,-204293974016,-204293973952⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1286200182032,0,true,172432197184,172432197248⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨912823073520,0,false,-204596364480,-204596364416⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571174900,0,true,59545472,59545536⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452080652,0,false,-59548800,-59548736⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099583176112,0,true,71545984,71546048⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099440079440,0,false,-71550720,-71550656⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623120,0,false,-4672,-4608⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624552,0,false,-3264,-3200⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1286019062810,0,true,172277356032,172277356096⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨913004192742,0,false,-204378224832,-204378224768⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1286258567559,0,true,172482107072,172482107136⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨912764687993,0,false,-204666693184,-204666693120⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067793527996,0,false,-32184586048,-32184585984⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067874833363,0,false,-32100868736,-32100868672⟩
    { al := (139011/819200), au := (21747/128000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨186577405870,186805307573⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172337177600,172337177664⟩ : DyadicInterval 40),(⟨-204462492416,-204462492352⟩ : DyadicInterval 40),(⟨746216254016,746216273345⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172531999552,172531999616⟩ : DyadicInterval 40),(⟨-204737004928,-204737004864⟩ : DyadicInterval 40),(⟨746177179050,746177198380⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172217538560,172217538624⟩ : DyadicInterval 40),(⟨-204293974016,-204293973952⟩ : DyadicInterval 40),(⟨746240222225,746240241554⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172432197184,172432197248⟩ : DyadicInterval 40),(⟨-204596364480,-204596364416⟩ : DyadicInterval 40),(⟨746197203115,746197222445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨59547124,71548336⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59545472,59545536⟩ : DyadicInterval 40),(⟨-59548800,-59548736⟩ : DyadicInterval 40),(⟨762123381990,762123401320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨71545984,71546048⟩ : DyadicInterval 40),(⟨-71550720,-71550656⟩ : DyadicInterval 40),(⟨762123381263,762123400593⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4672,-3200⟩ : DyadicInterval 40),(⟨762123385216,762123405216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨186507435034,186746939783⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172277356032,172277356096⟩ : DyadicInterval 40),(⟨-204378224832,-204378224768⟩ : DyadicInterval 40),(⟨746228241159,746228260489⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172482107072,172482107136⟩ : DyadicInterval 40),(⟨-204666693184,-204666693120⟩ : DyadicInterval 40),(⟨746187191182,746187210512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32184586048,-32100868672⟩ : DyadicInterval 40),(⟨778173817952,778215695904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨172337177600,172531999616⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-204737004928,-204462492352⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1473_ok : ecellOkT e1473 = true := by decide +kernel
theorem e1473_pos {a z : ℝ} (ha1 : ((139011/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((21747/128000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1473 e1473_ok ha1 ha2 hz1 hz2 hz

-- box ['139011/819200', '21747/128000', '1599/1600', '1999/2000']  interval_lower 5208591/274877906944
noncomputable def e1474 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1286089033646,0,true,172337177600,172337177664⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨912934221906,0,false,-204462492416,-204462492352⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1286316935349,0,true,172531999552,172531999616⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨912706320203,0,false,-204737004928,-204737004864⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1285972422767,0,true,172237479296,172237479360⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨913050832785,0,false,-204322058624,-204322058560⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1286223532696,0,true,172452158400,172452158464⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨912799722856,0,false,-204624491136,-204624491072⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099559265551,0,true,47636736,47636800⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099463990001,0,false,-47638848,-47638784⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571251592,0,true,59622144,59622208⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452003960,0,false,-59625472,-59625408⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624542,0,false,-3264,-3200⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625713,0,false,-2112,-2048⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1286030723731,0,true,172287325760,172287325824⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨912992531821,0,false,-204392267904,-204392267840⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1286270242754,0,true,172492087168,172492087232⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨912753012798,0,false,-204680757120,-204680757056⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067789561917,0,false,-32188669952,-32188669888⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067870877213,0,false,-32104942144,-32104942080⟩
    { al := (139011/819200), au := (21747/128000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨186577405870,186805307573⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172337177600,172337177664⟩ : DyadicInterval 40),(⟨-204462492416,-204462492352⟩ : DyadicInterval 40),(⟨746216254016,746216273345⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172531999552,172531999616⟩ : DyadicInterval 40),(⟨-204737004928,-204737004864⟩ : DyadicInterval 40),(⟨746177179050,746177198380⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172237479296,172237479360⟩ : DyadicInterval 40),(⟨-204322058624,-204322058560⟩ : DyadicInterval 40),(⟨746236228802,746236248131⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172452158400,172452158464⟩ : DyadicInterval 40),(⟨-204624491136,-204624491072⟩ : DyadicInterval 40),(⟨746193199315,746193218645⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨47637775,59623816⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨47636736,47636800⟩ : DyadicInterval 40),(⟨-47638848,-47638784⟩ : DyadicInterval 40),(⟨762123382543,762123401873⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59622144,59622208⟩ : DyadicInterval 40),(⟨-59625472,-59625408⟩ : DyadicInterval 40),(⟨762123381982,762123401311⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3264,-2048⟩ : DyadicInterval 40),(⟨762123384640,762123404512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨186519095955,186758614978⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172287325760,172287325824⟩ : DyadicInterval 40),(⟨-204392267904,-204392267840⟩ : DyadicInterval 40),(⟨746226243769,746226263098⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172492087168,172492087232⟩ : DyadicInterval 40),(⟨-204680757120,-204680757056⟩ : DyadicInterval 40),(⟨746185188708,746185208038⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32188669952,-32104942080⟩ : DyadicInterval 40),(⟨778175854656,778217737856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨172337177600,172531999616⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-204737004928,-204462492352⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1474_ok : ecellOkT e1474 = true := by decide +kernel
theorem e1474_pos {a z : ℝ} (ha1 : ((139011/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((21747/128000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1474 e1474_ok ha1 ha2 hz1 hz2 hz

-- box ['173127/1024000', '693357/4096000', '1999/2000', '7997/8000']  interval_lower 13095803/1099511627776
noncomputable def e1475 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1285405328539,0,true,171752504512,171752504576⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨913617927013,0,false,-203639365952,-203639365888⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1285633230242,0,true,171947430080,171947430144⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨913390025310,0,false,-203913672960,-203913672896⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1285312381688,0,true,171672996672,171672996736⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨913710873864,0,false,-203527512896,-203527512832⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1285563434642,0,true,171887737216,171887737280⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨913459820910,0,false,-203829658304,-203829658240⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099547219638,0,true,35591232,35591296⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476035914,0,false,-35592448,-35592384⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099559144978,0,true,47516160,47516224⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464110574,0,false,-47518272,-47518208⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625722,0,false,-2112,-2048⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626624,0,false,-1216,-1152⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1285358850510,0,true,171712747392,171712747456⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨913664405042,0,false,-203583432448,-203583432384⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1285598341060,0,true,171917591424,171917591488⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨913424914492,0,false,-203871675200,-203871675136⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068017404353,0,false,-31954083776,-31954083712⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068098417288,0,false,-31870685056,-31870684992⟩
    { al := (173127/1024000), au := (693357/4096000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨185893700763,186121602466⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171752504512,171752504576⟩ : DyadicInterval 40),(⟨-203639365952,-203639365888⟩ : DyadicInterval 40),(⟨746333187143,746333206473⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171947430080,171947430144⟩ : DyadicInterval 40),(⟨-203913672960,-203913672896⟩ : DyadicInterval 40),(⟨746294258065,746294277394⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171672996672,171672996736⟩ : DyadicInterval 40),(⟨-203527512896,-203527512832⟩ : DyadicInterval 40),(⟨746349049891,746349069220⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171887737216,171887737280⟩ : DyadicInterval 40),(⟨-203829658304,-203829658240⟩ : DyadicInterval 40),(⟨746306185361,746306204691⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨35591862,47517202⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35591232,35591296⟩ : DyadicInterval 40),(⟨-35592448,-35592384⟩ : DyadicInterval 40),(⟨762123383007,762123402336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨47516160,47516224⟩ : DyadicInterval 40),(⟨-47518272,-47518208⟩ : DyadicInterval 40),(⟨762123382554,762123401883⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2112,-1152⟩ : DyadicInterval 40),(⟨762123384192,762123403936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨185847222734,186086713284⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171712747392,171712747456⟩ : DyadicInterval 40),(⟨-203583432448,-203583432384⟩ : DyadicInterval 40),(⟨746341120297,746341139626⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171917591424,171917591488⟩ : DyadicInterval 40),(⟨-203871675200,-203871675136⟩ : DyadicInterval 40),(⟨746300220809,746300240138⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31954083776,-31870684992⟩ : DyadicInterval 40),(⟨778058726112,778100444768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨171752504512,171947430144⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-203913672960,-203639365888⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1475_ok : ecellOkT e1475 = true := by decide +kernel
theorem e1475_pos {a z : ℝ} (ha1 : ((173127/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((693357/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1475 e1475_ok ha1 ha2 hz1 hz2 hz

-- box ['173127/1024000', '693357/4096000', '7997/8000', '3999/4000']  interval_lower 6426833/549755813888
noncomputable def e1476 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1285405328539,0,true,171752504512,171752504576⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨913617927013,0,false,-203639365952,-203639365888⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1285633230242,0,true,171947430080,171947430144⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨913390025310,0,false,-203913672960,-203913672896⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1285335618401,0,true,171692874176,171692874240⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨913687637151,0,false,-203555475072,-203555475008⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1285586699842,0,true,171907635200,171907635264⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨913436555710,0,false,-203857662464,-203857662400⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535355662,0,true,23727616,23727680⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487899890,0,false,-23728192,-23728128⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099547265837,0,true,35637440,35637504⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099475989715,0,false,-35638656,-35638592⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626620,0,false,-1216,-1152⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627264,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1285370468762,0,true,171722685696,171722685760⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨913652786790,0,false,-203597414016,-203597413952⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1285609973585,0,true,171927540096,171927540160⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨913413281967,0,false,-203885677632,-203885677568⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068013466739,0,false,-31958137472,-31958137408⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068094489567,0,false,-31874728256,-31874728192⟩
    { al := (173127/1024000), au := (693357/4096000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨185893700763,186121602466⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171752504512,171752504576⟩ : DyadicInterval 40),(⟨-203639365952,-203639365888⟩ : DyadicInterval 40),(⟨746333187143,746333206473⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171947430080,171947430144⟩ : DyadicInterval 40),(⟨-203913672960,-203913672896⟩ : DyadicInterval 40),(⟨746294258065,746294277394⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171692874176,171692874240⟩ : DyadicInterval 40),(⟨-203555475072,-203555475008⟩ : DyadicInterval 40),(⟨746345084950,746345104280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171907635200,171907635264⟩ : DyadicInterval 40),(⟨-203857662464,-203857662400⟩ : DyadicInterval 40),(⟨746302210096,746302229426⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23727886,35638061⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23727616,23727680⟩ : DyadicInterval 40),(⟨-23728192,-23728128⟩ : DyadicInterval 40),(⟨762123383327,762123402656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35637440,35637504⟩ : DyadicInterval 40),(⟨-35638656,-35638592⟩ : DyadicInterval 40),(⟨762123383004,762123402333⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1216,-512⟩ : DyadicInterval 40),(⟨762123383872,762123403488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨185858840986,186098345809⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171722685696,171722685760⟩ : DyadicInterval 40),(⟨-203597414016,-203597413952⟩ : DyadicInterval 40),(⟨746339137421,746339156751⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171927540096,171927540160⟩ : DyadicInterval 40),(⟨-203885677632,-203885677568⟩ : DyadicInterval 40),(⟨746298232889,746298252218⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31958137472,-31874728192⟩ : DyadicInterval 40),(⟨778060747712,778102471616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨171752504512,171947430144⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-203913672960,-203639365888⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1476_ok : ecellOkT e1476 = true := by decide +kernel
theorem e1476_pos {a z : ℝ} (ha1 : ((173127/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((693357/4096000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1476 e1476_ok ha1 ha2 hz1 hz2 hz

-- box ['693357/4096000', '347103/2048000', '1999/2000', '7997/8000']  interval_lower 15580671/1099511627776
noncomputable def e1477 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1285633230241,0,true,171947430080,171947430144⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨913390025311,0,false,-203913672960,-203913672896⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1285861131944,0,true,172142321088,172142321152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨913162123608,0,false,-204188048448,-204188048384⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1285540169439,0,true,171867838848,171867838912⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨913483086113,0,false,-203801654848,-203801654784⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1285791250881,0,true,172082565696,172082565760⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨913232004671,0,false,-204103909952,-204103909888⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099547265131,0,true,35636736,35636800⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099475990421,0,false,-35637952,-35637888⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099559205646,0,true,47576832,47576896⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464049906,0,false,-47578944,-47578880⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625717,0,false,-2112,-2048⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626621,0,false,-1216,-1152⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1285586695234,0,true,171907631232,171907631296⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨913436560318,0,false,-203857656960,-203857656896⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1285826200029,0,true,172112451200,172112451264⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨913197055523,0,false,-204145988800,-204145988736⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067940229205,0,false,-32033537536,-32033537472⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068021346223,0,false,-31950025664,-31950025600⟩
    { al := (693357/4096000), au := (347103/2048000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨186121602465,186349504168⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171947430080,171947430144⟩ : DyadicInterval 40),(⟨-203913672960,-203913672896⟩ : DyadicInterval 40),(⟨746294258065,746294277395⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172142321088,172142321152⟩ : DyadicInterval 40),(⟨-204188048448,-204188048384⟩ : DyadicInterval 40),(⟨746255280372,746255299701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171867838848,171867838912⟩ : DyadicInterval 40),(⟨-203801654848,-203801654784⟩ : DyadicInterval 40),(⟨746310160130,746310179460⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172082565696,172082565760⟩ : DyadicInterval 40),(⟨-204103909952,-204103909888⟩ : DyadicInterval 40),(⟨746267237207,746267256537⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨35637355,47577870⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35636736,35636800⟩ : DyadicInterval 40),(⟨-35637952,-35637888⟩ : DyadicInterval 40),(⟨762123383004,762123402333⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨47576832,47576896⟩ : DyadicInterval 40),(⟨-47578944,-47578880⟩ : DyadicInterval 40),(⟨762123382549,762123401878⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2112,-1152⟩ : DyadicInterval 40),(⟨762123384192,762123403936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨186075067458,186314572253⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171907631232,171907631296⟩ : DyadicInterval 40),(⟨-203857656960,-203857656896⟩ : DyadicInterval 40),(⟨746302210917,746302230247⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172112451200,172112451264⟩ : DyadicInterval 40),(⟨-204145988800,-204145988736⟩ : DyadicInterval 40),(⟨746261257879,746261277209⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32033537536,-31950025600⟩ : DyadicInterval 40),(⟨778098396416,778140171648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨171947430080,172142321152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-204188048448,-203913672896⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1477_ok : ecellOkT e1477 = true := by decide +kernel
theorem e1477_pos {a z : ℝ} (ha1 : ((693357/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((347103/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1477 e1477_ok ha1 ha2 hz1 hz2 hz

-- box ['693357/4096000', '347103/2048000', '7997/8000', '3999/4000']  interval_lower 7668829/549755813888
noncomputable def e1478 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1285633230241,0,true,171947430080,171947430144⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨913390025311,0,false,-203913672960,-203913672896⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1285861131944,0,true,172142321088,172142321152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨913162123608,0,false,-204188048448,-204188048384⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1285563434639,0,true,171887737216,171887737280⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨913459820913,0,false,-203829658304,-203829658240⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1285814544569,0,true,172102484544,172102484608⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨913208710983,0,false,-204131955392,-204131955328⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535385990,0,true,23757952,23758016⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487869562,0,false,-23758528,-23758464⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099547311338,0,true,35682944,35683008⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099475944214,0,false,-35684160,-35684096⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626617,0,false,-1216,-1152⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627263,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1285598327730,0,true,171917580032,171917580096⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨913424927822,0,false,-203871659200,-203871659136⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1285837846799,0,true,172122410304,172122410368⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨913185408753,0,false,-204160011840,-204160011776⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067936281942,0,false,-32037601536,-32037601472⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068017408866,0,false,-31954079104,-31954079040⟩
    { al := (693357/4096000), au := (347103/2048000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨186121602465,186349504168⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171947430080,171947430144⟩ : DyadicInterval 40),(⟨-203913672960,-203913672896⟩ : DyadicInterval 40),(⟨746294258065,746294277395⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172142321088,172142321152⟩ : DyadicInterval 40),(⟨-204188048448,-204188048384⟩ : DyadicInterval 40),(⟨746255280372,746255299701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171887737216,171887737280⟩ : DyadicInterval 40),(⟨-203829658304,-203829658240⟩ : DyadicInterval 40),(⟨746306185361,746306204691⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172102484544,172102484608⟩ : DyadicInterval 40),(⟨-204131955392,-204131955328⟩ : DyadicInterval 40),(⟨746263252086,746263271415⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23758214,35683562⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23757952,23758016⟩ : DyadicInterval 40),(⟨-23758528,-23758464⟩ : DyadicInterval 40),(⟨762123383326,762123402655⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35682944,35683008⟩ : DyadicInterval 40),(⟨-35684160,-35684096⟩ : DyadicInterval 40),(⟨762123383001,762123402330⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1216,-512⟩ : DyadicInterval 40),(⟨762123383872,762123403488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨186086699954,186326219023⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171917580032,171917580096⟩ : DyadicInterval 40),(⟨-203871659200,-203871659136⟩ : DyadicInterval 40),(⟨746300223101,746300242430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172122410304,172122410368⟩ : DyadicInterval 40),(⟨-204160011840,-204160011776⟩ : DyadicInterval 40),(⟨746259265016,746259284345⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32037601536,-31954079040⟩ : DyadicInterval 40),(⟨778100423136,778142203648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨171947430080,172142321152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-204188048448,-203913672896⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1478_ok : ecellOkT e1478 = true := by decide +kernel
theorem e1478_pos {a z : ℝ} (ha1 : ((693357/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((347103/2048000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1478 e1478_ok ha1 ha2 hz1 hz2 hz

-- box ['173127/1024000', '693357/4096000', '3999/4000', '7999/8000']  interval_lower 3152901/274877906944
noncomputable def e1479 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1285405328539,0,true,171752504512,171752504576⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨913617927013,0,false,-203639365952,-203639365888⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1285633230242,0,true,171947430080,171947430144⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨913390025310,0,false,-203913672960,-203913672896⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1285358855113,0,true,171712751296,171712751360⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨913664400439,0,false,-203583437952,-203583437888⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1285609965042,0,true,171927532800,171927532864⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨913413290510,0,false,-203885667392,-203885667328⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523491622,0,true,11863744,11863808⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499763930,0,false,-11863936,-11863872⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535386632,0,true,23758592,23758656⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487868920,0,false,-23759168,-23759104⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627262,0,false,-576,-512⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627648,0,false,-192,-128⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1285382087042,0,true,171732624000,171732624064⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨913641168510,0,false,-203611395840,-203611395776⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1285621606135,0,true,171937488768,171937488832⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨913401649417,0,false,-203899680320,-203899680256⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068009528871,0,false,-31962191488,-31962191424⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068090561591,0,false,-31878771776,-31878771712⟩
    { al := (173127/1024000), au := (693357/4096000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨185893700763,186121602466⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171752504512,171752504576⟩ : DyadicInterval 40),(⟨-203639365952,-203639365888⟩ : DyadicInterval 40),(⟨746333187143,746333206473⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171947430080,171947430144⟩ : DyadicInterval 40),(⟨-203913672960,-203913672896⟩ : DyadicInterval 40),(⟨746294258065,746294277394⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171712751296,171712751360⟩ : DyadicInterval 40),(⟨-203583437952,-203583437888⟩ : DyadicInterval 40),(⟨746341119516,746341138846⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171927532800,171927532864⟩ : DyadicInterval 40),(⟨-203885667392,-203885667328⟩ : DyadicInterval 40),(⟨746298234361,746298253690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11863846,23758856⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11863744,11863808⟩ : DyadicInterval 40),(⟨-11863936,-11863872⟩ : DyadicInterval 40),(⟨762123383519,762123402848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23758592,23758656⟩ : DyadicInterval 40),(⟨-23759168,-23759104⟩ : DyadicInterval 40),(⟨762123383326,762123402655⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,-128⟩ : DyadicInterval 40),(⟨762123383680,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨185870459266,186109978359⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171732624000,171732624064⟩ : DyadicInterval 40),(⟨-203611395840,-203611395776⟩ : DyadicInterval 40),(⟨746337154395,746337173724⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171937488768,171937488832⟩ : DyadicInterval 40),(⟨-203899680320,-203899680256⟩ : DyadicInterval 40),(⟨746296244817,746296264147⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31962191488,-31878771712⟩ : DyadicInterval 40),(⟨778062769472,778104498624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨171752504512,171947430144⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-203913672960,-203639365888⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1479_ok : ecellOkT e1479 = true := by decide +kernel
theorem e1479_pos {a z : ℝ} (ha1 : ((173127/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((693357/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1479 e1479_ok ha1 ha2 hz1 hz2 hz

-- box ['173127/1024000', '693357/4096000', '7999/8000', '1']  interval_lower 3092403/274877906944
noncomputable def e1480 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1285405328539,0,true,171752504512,171752504576⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨913617927013,0,false,-203639365952,-203639365888⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1285633230242,0,true,171947430080,171947430144⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨913390025310,0,false,-203913672960,-203913672896⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1285382091826,0,true,171732628096,171732628160⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨913641163726,0,false,-203611401600,-203611401536⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523507365,0,true,11879488,11879552⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499748187,0,false,-11879680,-11879616⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627647,0,false,-192,-128⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1285393705352,0,true,171742562240,171742562304⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨913629550200,0,false,-203625377856,-203625377792⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1285633238722,0,true,171947437312,171947437376⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨913390016830,0,false,-203913683200,-203913683136⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1068005590744,0,false,-31966245824,-31966245760⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1068086633360,0,false,-31882815616,-31882815552⟩
    { al := (173127/1024000), au := (693357/4096000), zl := (7999/8000), zu := 1,
      A := ⟨185893700763,186121602466⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171752504512,171752504576⟩ : DyadicInterval 40),(⟨-203639365952,-203639365888⟩ : DyadicInterval 40),(⟨746333187143,746333206473⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171947430080,171947430144⟩ : DyadicInterval 40),(⟨-203913672960,-203913672896⟩ : DyadicInterval 40),(⟨746294258065,746294277394⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171732628096,171732628160⟩ : DyadicInterval 40),(⟨-203611401600,-203611401536⟩ : DyadicInterval 40),(⟨746337153577,746337172906⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171947430080,171947430144⟩ : DyadicInterval 40),(⟨-203913672960,-203913672896⟩ : DyadicInterval 40),(⟨746294258065,746294277394⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11879589⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11879488,11879552⟩ : DyadicInterval 40),(⟨-11879680,-11879616⟩ : DyadicInterval 40),(⟨762123383519,762123402848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-192,0⟩ : DyadicInterval 40),(⟨762123383616,762123402976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨185882077576,186121610946⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171742562240,171742562304⟩ : DyadicInterval 40),(⟨-203625377856,-203625377792⟩ : DyadicInterval 40),(⟨746335171227,746335190557⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171947437312,171947437376⟩ : DyadicInterval 40),(⟨-203913683200,-203913683136⟩ : DyadicInterval 40),(⟨746294256641,746294275970⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31966245824,-31882815552⟩ : DyadicInterval 40),(⟨778064791392,778106525792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨171752504512,171947430144⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-203913672960,-203639365888⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1480_ok : ecellOkT e1480 = true := by decide +kernel
theorem e1480_pos {a z : ℝ} (ha1 : ((173127/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((693357/4096000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1480 e1480_ok ha1 ha2 hz1 hz2 hz

-- box ['693357/4096000', '347103/2048000', '3999/4000', '7999/8000']  interval_lower 15094549/1099511627776
noncomputable def e1481 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1285633230241,0,true,171947430080,171947430144⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨913390025311,0,false,-203913672960,-203913672896⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1285861131944,0,true,172142321088,172142321152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨913162123608,0,false,-204188048448,-204188048384⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1285586699840,0,true,171907635200,171907635264⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨913436555712,0,false,-203857662464,-203857662400⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1285837838257,0,true,172122403008,172122403072⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨913185417295,0,false,-204160001600,-204160001536⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523506787,0,true,11878912,11878976⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499748765,0,false,-11879104,-11879040⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535416967,0,true,23788928,23788992⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487838585,0,false,-23789504,-23789440⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627261,0,false,-576,-512⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627648,0,false,-192,-128⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1285609960254,0,true,171927528704,171927528768⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨913413295298,0,false,-203885661632,-203885661568⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1285849493596,0,true,172132369344,172132369408⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨913173761956,0,false,-204174035136,-204174035072⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067932334423,0,false,-32041665792,-32041665728⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068013471253,0,false,-31958132864,-31958132800⟩
    { al := (693357/4096000), au := (347103/2048000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨186121602465,186349504168⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171947430080,171947430144⟩ : DyadicInterval 40),(⟨-203913672960,-203913672896⟩ : DyadicInterval 40),(⟨746294258065,746294277395⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172142321088,172142321152⟩ : DyadicInterval 40),(⟨-204188048448,-204188048384⟩ : DyadicInterval 40),(⟨746255280372,746255299701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171907635200,171907635264⟩ : DyadicInterval 40),(⟨-203857662464,-203857662400⟩ : DyadicInterval 40),(⟨746302210096,746302229426⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172122403008,172122403072⟩ : DyadicInterval 40),(⟨-204160001600,-204160001536⟩ : DyadicInterval 40),(⟨746259266491,746259285821⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11879011,23789191⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11878912,11878976⟩ : DyadicInterval 40),(⟨-11879104,-11879040⟩ : DyadicInterval 40),(⟨762123383519,762123402848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23788928,23788992⟩ : DyadicInterval 40),(⟨-23789504,-23789440⟩ : DyadicInterval 40),(⟨762123383325,762123402654⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,-128⟩ : DyadicInterval 40),(⟨762123383680,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨186098332478,186337865820⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171927528704,171927528768⟩ : DyadicInterval 40),(⟨-203885661632,-203885661568⟩ : DyadicInterval 40),(⟨746298235181,746298254511⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172132369344,172132369408⟩ : DyadicInterval 40),(⟨-204174035136,-204174035072⟩ : DyadicInterval 40),(⟨746257272038,746257291367⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32041665792,-31958132800⟩ : DyadicInterval 40),(⟨778102450016,778144235776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨171947430080,172142321152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-204188048448,-203913672896⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1481_ok : ecellOkT e1481 = true := by decide +kernel
theorem e1481_pos {a z : ℝ} (ha1 : ((693357/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((347103/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1481 e1481_ok ha1 ha2 hz1 hz2 hz

-- box ['693357/4096000', '347103/2048000', '7999/8000', '1']  interval_lower 14851593/1099511627776
noncomputable def e1482 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1285633230241,0,true,171947430080,171947430144⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨913390025311,0,false,-203913672960,-203913672896⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1285861131944,0,true,172142321088,172142321152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨913162123608,0,false,-204188048448,-204188048384⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1285609965040,0,true,171927532800,171927532864⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨913413290512,0,false,-203885667392,-203885667328⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523522532,0,true,11894656,11894720⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499733020,0,false,-11894848,-11894784⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627647,0,false,-192,-128⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1285621592804,0,true,171937477376,171937477440⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨913401662748,0,false,-203899664256,-203899664192⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1285861140424,0,true,172142328384,172142328448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨913162115128,0,false,-204188058688,-204188058624⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1067928386647,0,false,-32045730304,-32045730240⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1068009533385,0,false,-31962186880,-31962186816⟩
    { al := (693357/4096000), au := (347103/2048000), zl := (7999/8000), zu := 1,
      A := ⟨186121602465,186349504168⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171947430080,171947430144⟩ : DyadicInterval 40),(⟨-203913672960,-203913672896⟩ : DyadicInterval 40),(⟨746294258065,746294277395⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172142321088,172142321152⟩ : DyadicInterval 40),(⟨-204188048448,-204188048384⟩ : DyadicInterval 40),(⟨746255280372,746255299701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171927532800,171927532864⟩ : DyadicInterval 40),(⟨-203885667392,-203885667328⟩ : DyadicInterval 40),(⟨746298234361,746298253691⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172142321088,172142321152⟩ : DyadicInterval 40),(⟨-204188048448,-204188048384⟩ : DyadicInterval 40),(⟨746255280372,746255299701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11894756⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11894656,11894720⟩ : DyadicInterval 40),(⟨-11894848,-11894784⟩ : DyadicInterval 40),(⟨762123383519,762123402848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-192,0⟩ : DyadicInterval 40),(⟨762123383616,762123402976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨186109965028,186349512648⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171937477376,171937477440⟩ : DyadicInterval 40),(⟨-203899664256,-203899664192⟩ : DyadicInterval 40),(⟨746296247084,746296266413⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172142328384,172142328448⟩ : DyadicInterval 40),(⟨-204188058688,-204188058624⟩ : DyadicInterval 40),(⟨746255278907,746255298236⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32045730304,-31962186816⟩ : DyadicInterval 40),(⟨778104477024,778146268032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨171947430080,172142321152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-204188048448,-203913672896⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1482_ok : ecellOkT e1482 = true := by decide +kernel
theorem e1482_pos {a z : ℝ} (ha1 : ((693357/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((347103/2048000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1482 e1482_ok ha1 ha2 hz1 hz2 hz

-- box ['347103/2048000', '139011/819200', '1999/2000', '7997/8000']  interval_lower 9039279/549755813888
noncomputable def e1483 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1285861131943,0,true,172142321088,172142321152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨913162123609,0,false,-204188048448,-204188048384⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1286089033647,0,true,172337177600,172337177664⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨912934221905,0,false,-204462492416,-204462492352⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1285767957190,0,true,172062646528,172062646592⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨913255298362,0,false,-204075865216,-204075865152⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1286019067120,0,true,172277359744,172277359808⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨913004188432,0,false,-204378230016,-204378229952⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099547310631,0,true,35682240,35682304⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099475944921,0,false,-35683456,-35683392⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099559266322,0,true,47637504,47637568⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099463989230,0,false,-47639616,-47639552⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625711,0,false,-2112,-2048⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626618,0,false,-1216,-1152⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1285814539956,0,true,172102480576,172102480640⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨913208715596,0,false,-204131949824,-204131949760⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1286054059007,0,true,172307276416,172307276480⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨912969196545,0,false,-204420370816,-204420370752⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067862959612,0,false,-32113094336,-32113094272⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067944180730,0,false,-32029469248,-32029469184⟩
    { al := (347103/2048000), au := (139011/819200), zl := (1999/2000), zu := (7997/8000),
      A := ⟨186349504167,186577405871⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172142321088,172142321152⟩ : DyadicInterval 40),(⟨-204188048448,-204188048384⟩ : DyadicInterval 40),(⟨746255280372,746255299701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172337177600,172337177664⟩ : DyadicInterval 40),(⟨-204462492416,-204462492352⟩ : DyadicInterval 40),(⟨746216254015,746216273345⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172062646528,172062646592⟩ : DyadicInterval 40),(⟨-204075865216,-204075865152⟩ : DyadicInterval 40),(⟨746271221792,746271241122⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172277359744,172277359808⟩ : DyadicInterval 40),(⟨-204378230016,-204378229952⟩ : DyadicInterval 40),(⟨746228240402,746228259732⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨35682855,47638546⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35682240,35682304⟩ : DyadicInterval 40),(⟨-35683456,-35683392⟩ : DyadicInterval 40),(⟨762123383001,762123402330⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨47637504,47637568⟩ : DyadicInterval 40),(⟨-47639616,-47639552⟩ : DyadicInterval 40),(⟨762123382543,762123401873⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2112,-1152⟩ : DyadicInterval 40),(⟨762123384192,762123403936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨186302912180,186542431231⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172102480576,172102480640⟩ : DyadicInterval 40),(⟨-204131949824,-204131949760⟩ : DyadicInterval 40),(⟨746263252883,746263272212⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172307276416,172307276480⟩ : DyadicInterval 40),(⟨-204420370816,-204420370752⟩ : DyadicInterval 40),(⟨746222246334,746222265664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32113094336,-32029469184⟩ : DyadicInterval 40),(⟨778138118208,778179950048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨172142321088,172337177664⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-204462492416,-204188048384⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1483_ok : ecellOkT e1483 = true := by decide +kernel
theorem e1483_pos {a z : ℝ} (ha1 : ((347103/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((139011/819200 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1483 e1483_ok ha1 ha2 hz1 hz2 hz

-- box ['347103/2048000', '139011/819200', '7997/8000', '3999/4000']  interval_lower 8917277/549755813888
noncomputable def e1484 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1285861131943,0,true,172142321088,172142321152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨913162123609,0,false,-204188048448,-204188048384⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1286089033647,0,true,172337177600,172337177664⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨912934221905,0,false,-204462492416,-204462492352⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1285791250878,0,true,172082565696,172082565760⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨913232004674,0,false,-204103909952,-204103909888⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1286042389296,0,true,172297299392,172297299456⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨912980866256,0,false,-204406316736,-204406316672⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535416324,0,true,23788288,23788352⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487839228,0,false,-23788864,-23788800⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099547356845,0,true,35728448,35728512⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099475898707,0,false,-35729664,-35729600⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626614,0,false,-1216,-1152⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627262,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1285826186692,0,true,172112439808,172112439872⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨913197068860,0,false,-204145972736,-204145972672⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1286065720020,0,true,172317245952,172317246016⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨912957535532,0,false,-204434414528,-204434414464⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067859002688,0,false,-32117168576,-32117168512⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067940233726,0,false,-32033532928,-32033532864⟩
    { al := (347103/2048000), au := (139011/819200), zl := (7997/8000), zu := (3999/4000),
      A := ⟨186349504167,186577405871⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172142321088,172142321152⟩ : DyadicInterval 40),(⟨-204188048448,-204188048384⟩ : DyadicInterval 40),(⟨746255280372,746255299701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172337177600,172337177664⟩ : DyadicInterval 40),(⟨-204462492416,-204462492352⟩ : DyadicInterval 40),(⟨746216254015,746216273345⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172082565696,172082565760⟩ : DyadicInterval 40),(⟨-204103909952,-204103909888⟩ : DyadicInterval 40),(⟨746267237208,746267256537⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172297299392,172297299456⟩ : DyadicInterval 40),(⟨-204406316736,-204406316672⟩ : DyadicInterval 40),(⟨746224245437,746224264766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23788548,35729069⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23788288,23788352⟩ : DyadicInterval 40),(⟨-23788864,-23788800⟩ : DyadicInterval 40),(⟨762123383325,762123402654⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35728448,35728512⟩ : DyadicInterval 40),(⟨-35729664,-35729600⟩ : DyadicInterval 40),(⟨762123382998,762123402327⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1216,-512⟩ : DyadicInterval 40),(⟨762123383872,762123403488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨186314558916,186554092244⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172112439808,172112439872⟩ : DyadicInterval 40),(⟨-204145972736,-204145972672⟩ : DyadicInterval 40),(⟨746261260152,746261279481⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172317245952,172317246016⟩ : DyadicInterval 40),(⟨-204434414528,-204434414464⟩ : DyadicInterval 40),(⟨746220248542,746220267872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32117168576,-32033532864⟩ : DyadicInterval 40),(⟨778140150048,778181987168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨172142321088,172337177664⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-204462492416,-204188048384⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1484_ok : ecellOkT e1484 = true := by decide +kernel
theorem e1484_pos {a z : ℝ} (ha1 : ((347103/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((139011/819200 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1484 e1484_ok ha1 ha2 hz1 hz2 hz

-- box ['139011/819200', '21747/128000', '1999/2000', '7997/8000']  interval_lower 20589253/1099511627776
noncomputable def e1485 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1286089033646,0,true,172337177600,172337177664⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨912934221906,0,false,-204462492416,-204462492352⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1286316935349,0,true,172531999552,172531999616⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨912706320203,0,false,-204737004928,-204737004864⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1285995744943,0,true,172257419712,172257419776⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨913027510609,0,false,-204350143936,-204350143872⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1286246883359,0,true,172472119232,172472119296⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨912776372193,0,false,-204652618496,-204652618432⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099547356139,0,true,35727744,35727808⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099475899413,0,false,-35728960,-35728896⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099559327008,0,true,47698176,47698240⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099463928544,0,false,-47700288,-47700224⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625706,0,false,-2112,-2048⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626616,0,false,-1216,-1152⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1286042384685,0,true,172297295424,172297295488⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨912980870867,0,false,-204406311232,-204406311168⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1286281917979,0,true,172502067136,172502067200⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨912741337573,0,false,-204694821312,-204694821248⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067785595580,0,false,-32192754112,-32192754048⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067866920805,0,false,-32109015744,-32109015680⟩
    { al := (139011/819200), au := (21747/128000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨186577405870,186805307573⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172337177600,172337177664⟩ : DyadicInterval 40),(⟨-204462492416,-204462492352⟩ : DyadicInterval 40),(⟨746216254016,746216273345⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172531999552,172531999616⟩ : DyadicInterval 40),(⟨-204737004928,-204737004864⟩ : DyadicInterval 40),(⟨746177179050,746177198380⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172257419712,172257419776⟩ : DyadicInterval 40),(⟨-204350143936,-204350143872⟩ : DyadicInterval 40),(⟨746232234840,746232254169⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172472119232,172472119296⟩ : DyadicInterval 40),(⟨-204652618496,-204652618432⟩ : DyadicInterval 40),(⟨746189195011,746189214341⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨35728363,47699232⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35727744,35727808⟩ : DyadicInterval 40),(⟨-35728960,-35728896⟩ : DyadicInterval 40),(⟨762123382998,762123402328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨47698176,47698240⟩ : DyadicInterval 40),(⟨-47700288,-47700224⟩ : DyadicInterval 40),(⟨762123382538,762123401867⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2112,-1152⟩ : DyadicInterval 40),(⟨762123384192,762123403936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨186530756909,186770290203⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172297295424,172297295488⟩ : DyadicInterval 40),(⟨-204406311232,-204406311168⟩ : DyadicInterval 40),(⟨746224246262,746224265591⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172502067136,172502067200⟩ : DyadicInterval 40),(⟨-204694821312,-204694821248⟩ : DyadicInterval 40),(⟨746183186155,746183205485⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32192754112,-32109015680⟩ : DyadicInterval 40),(⟨778177891456,778219779936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨172337177600,172531999616⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-204737004928,-204462492352⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1485_ok : ecellOkT e1485 = true := by decide +kernel
theorem e1485_pos {a z : ℝ} (ha1 : ((139011/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((21747/128000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1485 e1485_ok ha1 ha2 hz1 hz2 hz

-- box ['139011/819200', '21747/128000', '7997/8000', '3999/4000']  interval_lower 1271515/68719476736
noncomputable def e1486 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1286089033646,0,true,172337177600,172337177664⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨912934221906,0,false,-204462492416,-204462492352⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1286316935349,0,true,172531999552,172531999616⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨912706320203,0,false,-204737004928,-204737004864⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1286019067118,0,true,172277359680,172277359744⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨913004188434,0,false,-204378230016,-204378229952⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1286270234023,0,true,172492079680,172492079744⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨912753021529,0,false,-204680746624,-204680746560⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535446662,0,true,23818624,23818688⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487808890,0,false,-23819200,-23819136⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099547402361,0,true,35773952,35774016⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099475853191,0,false,-35775168,-35775104⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626612,0,false,-1216,-1152⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627261,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1286054045661,0,true,172307265024,172307265088⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨912969209891,0,false,-204420354752,-204420354688⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1286293593230,0,true,172512047104,172512047168⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨912729662322,0,false,-204708885696,-204708885632⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067781628986,0,false,-32196838592,-32196838528⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067862964141,0,false,-32113089664,-32113089600⟩
    { al := (139011/819200), au := (21747/128000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨186577405870,186805307573⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172337177600,172337177664⟩ : DyadicInterval 40),(⟨-204462492416,-204462492352⟩ : DyadicInterval 40),(⟨746216254016,746216273345⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172531999552,172531999616⟩ : DyadicInterval 40),(⟨-204737004928,-204737004864⟩ : DyadicInterval 40),(⟨746177179050,746177198380⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172277359680,172277359744⟩ : DyadicInterval 40),(⟨-204378230016,-204378229952⟩ : DyadicInterval 40),(⟨746228240440,746228259770⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172492079680,172492079744⟩ : DyadicInterval 40),(⟨-204680746624,-204680746560⟩ : DyadicInterval 40),(⟨746185190229,746185209558⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23818886,35774585⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23818624,23818688⟩ : DyadicInterval 40),(⟨-23819200,-23819136⟩ : DyadicInterval 40),(⟨762123383324,762123402653⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35773952,35774016⟩ : DyadicInterval 40),(⟨-35775168,-35775104⟩ : DyadicInterval 40),(⟨762123382995,762123402325⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1216,-512⟩ : DyadicInterval 40),(⟨762123383872,762123403488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨186542417885,186781965454⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172307265024,172307265088⟩ : DyadicInterval 40),(⟨-204420354752,-204420354688⟩ : DyadicInterval 40),(⟨746222248614,746222267943⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172512047104,172512047168⟩ : DyadicInterval 40),(⟨-204708885696,-204708885632⟩ : DyadicInterval 40),(⟨746181183422,746181202751⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32196838592,-32113089600⟩ : DyadicInterval 40),(⟨778179928416,778221822176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨172337177600,172531999616⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-204737004928,-204462492352⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1486_ok : ecellOkT e1486 = true := by decide +kernel
theorem e1486_pos {a z : ℝ} (ha1 : ((139011/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((21747/128000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1486 e1486_ok ha1 ha2 hz1 hz2 hz

-- box ['347103/2048000', '139011/819200', '3999/4000', '7999/8000']  interval_lower 8795251/549755813888
noncomputable def e1487 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1285861131943,0,true,172142321088,172142321152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨913162123609,0,false,-204188048448,-204188048384⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1286089033647,0,true,172337177600,172337177664⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨912934221905,0,false,-204462492416,-204462492352⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1285814544566,0,true,172102484544,172102484608⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨913208710986,0,false,-204131955392,-204131955328⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1286065711472,0,true,172317238656,172317238720⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨912957544080,0,false,-204434404224,-204434404160⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523521953,0,true,11894080,11894144⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499733599,0,false,-11894272,-11894208⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535447305,0,true,23819264,23819328⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487808247,0,false,-23819840,-23819776⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627259,0,false,-576,-512⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627648,0,false,-192,-128⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1285837833462,0,true,172122398912,172122398976⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨913185422090,0,false,-204159995776,-204159995712⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1286077381061,0,true,172327215424,172327215488⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨912945874491,0,false,-204448458496,-204448458432⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067855045508,0,false,-32121243008,-32121242944⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067936286463,0,false,-32037596864,-32037596800⟩
    { al := (347103/2048000), au := (139011/819200), zl := (3999/4000), zu := (7999/8000),
      A := ⟨186349504167,186577405871⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172142321088,172142321152⟩ : DyadicInterval 40),(⟨-204188048448,-204188048384⟩ : DyadicInterval 40),(⟨746255280372,746255299701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172337177600,172337177664⟩ : DyadicInterval 40),(⟨-204462492416,-204462492352⟩ : DyadicInterval 40),(⟨746216254015,746216273345⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172102484544,172102484608⟩ : DyadicInterval 40),(⟨-204131955392,-204131955328⟩ : DyadicInterval 40),(⟨746263252086,746263271416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172317238656,172317238720⟩ : DyadicInterval 40),(⟨-204434404224,-204434404160⟩ : DyadicInterval 40),(⟨746220249995,746220269325⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11894177,23819529⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11894080,11894144⟩ : DyadicInterval 40),(⟨-11894272,-11894208⟩ : DyadicInterval 40),(⟨762123383519,762123402848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23819264,23819328⟩ : DyadicInterval 40),(⟨-23819840,-23819776⟩ : DyadicInterval 40),(⟨762123383323,762123402652⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,-128⟩ : DyadicInterval 40),(⟨762123383680,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨186326205686,186565753285⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172122398912,172122398976⟩ : DyadicInterval 40),(⟨-204159995776,-204159995712⟩ : DyadicInterval 40),(⟨746259267289,746259286618⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172327215424,172327215488⟩ : DyadicInterval 40),(⟨-204448458496,-204448458432⟩ : DyadicInterval 40),(⟨746218250634,746218269963⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32121243008,-32037596800⟩ : DyadicInterval 40),(⟨778142182016,778184024384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨172142321088,172337177664⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-204462492416,-204188048384⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1487_ok : ecellOkT e1487 = true := by decide +kernel
theorem e1487_pos {a z : ℝ} (ha1 : ((347103/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((139011/819200 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1487 e1487_ok ha1 ha2 hz1 hz2 hz

-- box ['347103/2048000', '139011/819200', '7999/8000', '1']  interval_lower 17346367/1099511627776
noncomputable def e1488 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1285861131943,0,true,172142321088,172142321152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨913162123609,0,false,-204188048448,-204188048384⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1286089033647,0,true,172337177600,172337177664⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨912934221905,0,false,-204462492416,-204462492352⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1285837838254,0,true,172122403008,172122403072⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨913185417298,0,false,-204160001600,-204160001536⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523537701,0,true,11909824,11909888⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499717851,0,false,-11910016,-11909952⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627646,0,false,-192,-128⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1285849480258,0,true,172132357952,172132358016⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨913173775294,0,false,-204174019072,-204174019008⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1286089042133,0,true,172337184832,172337184896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨912934213419,0,false,-204462502656,-204462502592⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1067851088070,0,false,-32125317824,-32125317760⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1067932338945,0,false,-32041661120,-32041661056⟩
    { al := (347103/2048000), au := (139011/819200), zl := (7999/8000), zu := 1,
      A := ⟨186349504167,186577405871⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172142321088,172142321152⟩ : DyadicInterval 40),(⟨-204188048448,-204188048384⟩ : DyadicInterval 40),(⟨746255280372,746255299701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172337177600,172337177664⟩ : DyadicInterval 40),(⟨-204462492416,-204462492352⟩ : DyadicInterval 40),(⟨746216254015,746216273345⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172122403008,172122403072⟩ : DyadicInterval 40),(⟨-204160001600,-204160001536⟩ : DyadicInterval 40),(⟨746259266492,746259285821⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172337177600,172337177664⟩ : DyadicInterval 40),(⟨-204462492416,-204462492352⟩ : DyadicInterval 40),(⟨746216254015,746216273345⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11909925⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11909824,11909888⟩ : DyadicInterval 40),(⟨-11910016,-11909952⟩ : DyadicInterval 40),(⟨762123383518,762123402847⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-192,0⟩ : DyadicInterval 40),(⟨762123383616,762123402976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨186337852482,186577414357⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172132357952,172132358016⟩ : DyadicInterval 40),(⟨-204174019072,-204174019008⟩ : DyadicInterval 40),(⟨746257274311,746257293640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172337184832,172337184896⟩ : DyadicInterval 40),(⟨-204462502656,-204462502592⟩ : DyadicInterval 40),(⟨746216252583,746216271912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32125317824,-32041661056⟩ : DyadicInterval 40),(⟨778144214144,778186061792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨172142321088,172337177664⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-204462492416,-204188048384⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1488_ok : ecellOkT e1488 = true := by decide +kernel
theorem e1488_pos {a z : ℝ} (ha1 : ((347103/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((139011/819200 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1488 e1488_ok ha1 ha2 hz1 hz2 hz

-- box ['139011/819200', '21747/128000', '3999/4000', '7999/8000']  interval_lower 20099297/1099511627776
noncomputable def e1489 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1286089033646,0,true,172337177600,172337177664⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨912934221906,0,false,-204462492416,-204462492352⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1286316935349,0,true,172531999552,172531999616⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨912706320203,0,false,-204737004928,-204737004864⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1286042389294,0,true,172297299392,172297299456⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨912980866258,0,false,-204406316736,-204406316672⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1286293584686,0,true,172512039808,172512039872⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨912729670866,0,false,-204708875392,-204708875328⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523537122,0,true,11909248,11909312⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499718430,0,false,-11909440,-11909376⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535477649,0,true,23849600,23849664⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487777903,0,false,-23850176,-23850112⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627258,0,false,-576,-512⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627648,0,false,-192,-128⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1286065706679,0,true,172317234560,172317234624⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨912957548873,0,false,-204434398464,-204434398400⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1286305268520,0,true,172522026944,172522027008⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨912717987032,0,false,-204722950336,-204722950272⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067777662130,0,false,-32200923328,-32200923264⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067859007216,0,false,-32117163904,-32117163840⟩
    { al := (139011/819200), au := (21747/128000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨186577405870,186805307573⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172337177600,172337177664⟩ : DyadicInterval 40),(⟨-204462492416,-204462492352⟩ : DyadicInterval 40),(⟨746216254016,746216273345⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172531999552,172531999616⟩ : DyadicInterval 40),(⟨-204737004928,-204737004864⟩ : DyadicInterval 40),(⟨746177179050,746177198380⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172297299392,172297299456⟩ : DyadicInterval 40),(⟨-204406316736,-204406316672⟩ : DyadicInterval 40),(⟨746224245437,746224264767⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172512039808,172512039872⟩ : DyadicInterval 40),(⟨-204708875392,-204708875328⟩ : DyadicInterval 40),(⟨746181184878,746181204208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11909346,23849873⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11909248,11909312⟩ : DyadicInterval 40),(⟨-11909440,-11909376⟩ : DyadicInterval 40),(⟨762123383519,762123402848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23849600,23849664⟩ : DyadicInterval 40),(⟨-23850176,-23850112⟩ : DyadicInterval 40),(⟨762123383322,762123402651⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,-128⟩ : DyadicInterval 40),(⟨762123383680,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨186554078903,186793640744⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172317234560,172317234624⟩ : DyadicInterval 40),(⟨-204434398464,-204434398400⟩ : DyadicInterval 40),(⟨746220250821,746220270150⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172522026944,172522027008⟩ : DyadicInterval 40),(⟨-204722950336,-204722950272⟩ : DyadicInterval 40),(⟨746179180608,746179199938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32200923328,-32117163840⟩ : DyadicInterval 40),(⟨778181965536,778223864544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨172337177600,172531999616⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-204737004928,-204462492352⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1489_ok : ecellOkT e1489 = true := by decide +kernel
theorem e1489_pos {a z : ℝ} (ha1 : ((139011/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((21747/128000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1489 e1489_ok ha1 ha2 hz1 hz2 hz

-- box ['139011/819200', '21747/128000', '7999/8000', '1']  interval_lower 9927119/549755813888
noncomputable def e1490 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1286089033646,0,true,172337177600,172337177664⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨912934221906,0,false,-204462492416,-204462492352⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1286316935349,0,true,172531999552,172531999616⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨912706320203,0,false,-204737004928,-204737004864⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1286065711470,0,true,172317238656,172317238720⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨912957544082,0,false,-204434404224,-204434404160⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523552873,0,true,11924992,11925056⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499702679,0,false,-11925184,-11925120⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627646,0,false,-192,-128⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1286077367718,0,true,172327204032,172327204096⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨912945887834,0,false,-204448442432,-204448442368⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1286316943835,0,true,172532006784,172532006848⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨912706311717,0,false,-204737015168,-204737015104⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1067773695018,0,false,-32205008320,-32205008256⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1067855050037,0,false,-32121238400,-32121238336⟩
    { al := (139011/819200), au := (21747/128000), zl := (7999/8000), zu := 1,
      A := ⟨186577405870,186805307573⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172337177600,172337177664⟩ : DyadicInterval 40),(⟨-204462492416,-204462492352⟩ : DyadicInterval 40),(⟨746216254016,746216273345⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172531999552,172531999616⟩ : DyadicInterval 40),(⟨-204737004928,-204737004864⟩ : DyadicInterval 40),(⟨746177179050,746177198380⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172317238656,172317238720⟩ : DyadicInterval 40),(⟨-204434404224,-204434404160⟩ : DyadicInterval 40),(⟨746220249996,746220269326⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172531999552,172531999616⟩ : DyadicInterval 40),(⟨-204737004928,-204737004864⟩ : DyadicInterval 40),(⟨746177179050,746177198380⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11925097⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11924992,11925056⟩ : DyadicInterval 40),(⟨-11925184,-11925120⟩ : DyadicInterval 40),(⟨762123383518,762123402847⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-192,0⟩ : DyadicInterval 40),(⟨762123383616,762123402976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨186565739942,186805316059⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172327204032,172327204096⟩ : DyadicInterval 40),(⟨-204448442432,-204448442368⟩ : DyadicInterval 40),(⟨746218252913,746218272243⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172532006784,172532006848⟩ : DyadicInterval 40),(⟨-204737015168,-204737015104⟩ : DyadicInterval 40),(⟨746177177614,746177196943⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32205008320,-32121238336⟩ : DyadicInterval 40),(⟨778184002784,778225907040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨172337177600,172531999616⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-204737004928,-204462492352⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1490_ok : ecellOkT e1490 = true := by decide +kernel
theorem e1490_pos {a z : ℝ} (ha1 : ((139011/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((21747/128000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1490 e1490_ok ha1 ha2 hz1 hz2 hz

-- box ['21747/128000', '696753/4096000', '999/1000', '7993/8000']  interval_lower 3012021/137438953472
noncomputable def e1491 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1286316935348,0,true,172531999552,172531999616⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨912706320204,0,false,-204737004928,-204737004864⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1286544837051,0,true,172726786944,172726787008⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨912478418501,0,false,-205011585984,-205011585920⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1286130130040,0,true,172372311424,172372311488⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨912893125512,0,false,-204511988864,-204511988800⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1286381182993,0,true,172586915456,172586915520⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨912642072559,0,false,-204814404992,-204814404928⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099595099603,0,true,83468608,83468672⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099428155949,0,false,-83475008,-83474944⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099607146347,0,true,95514368,95514432⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099416109205,0,false,-95522752,-95522688⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619477,0,false,-8320,-8256⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621440,0,false,-6400,-6336⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1286223528815,0,true,172452155072,172452155136⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨912799726737,0,false,-204624486464,-204624486400⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1286463019257,0,true,172656861312,172656861376⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨912560236295,0,false,-204913002176,-204913002112⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067724039638,0,false,-32256140864,-32256140800⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067805429216,0,false,-32172331392,-32172331328⟩
    { al := (21747/128000), au := (696753/4096000), zl := (999/1000), zu := (7993/8000),
      A := ⟨186805307572,187033209275⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172531999552,172531999616⟩ : DyadicInterval 40),(⟨-204737004928,-204737004864⟩ : DyadicInterval 40),(⟨746177179050,746177198380⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172726786944,172726787008⟩ : DyadicInterval 40),(⟨-205011585984,-205011585920⟩ : DyadicInterval 40),(⟨746138055465,746138074794⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172372311424,172372311488⟩ : DyadicInterval 40),(⟨-204511988864,-204511988800⟩ : DyadicInterval 40),(⟨746209211430,746209230759⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172586915456,172586915520⟩ : DyadicInterval 40),(⟨-204814404992,-204814404928⟩ : DyadicInterval 40),(⟨746166154667,746166173996⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨83471827,95518571⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨83468608,83468672⟩ : DyadicInterval 40),(⟨-83475008,-83474944⟩ : DyadicInterval 40),(⟨762123380414,762123399744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨95514368,95514432⟩ : DyadicInterval 40),(⟨-95522752,-95522688⟩ : DyadicInterval 40),(⟨762123379445,762123398775⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8320,-6336⟩ : DyadicInterval 40),(⟨762123386784,762123407040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨186711901039,186951391481⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172452155072,172452155136⟩ : DyadicInterval 40),(⟨-204624486464,-204624486400⟩ : DyadicInterval 40),(⟨746193199988,746193219318⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172656861312,172656861376⟩ : DyadicInterval 40),(⟨-204913002176,-204913002112⟩ : DyadicInterval 40),(⟨746152106611,746152125940⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32256140864,-32172331328⟩ : DyadicInterval 40),(⟨778209549280,778251473312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨172531999552,172726787008⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-205011585984,-204737004864⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1491_ok : ecellOkT e1491 = true := by decide +kernel
theorem e1491_pos {a z : ℝ} (ha1 : ((21747/128000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((696753/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1491 e1491_ok ha1 ha2 hz1 hz2 hz

-- box ['21747/128000', '696753/4096000', '7993/8000', '3997/4000']  interval_lower 23850319/1099511627776
noncomputable def e1492 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1286316935348,0,true,172531999552,172531999616⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨912706320204,0,false,-204737004928,-204737004864⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1286544837051,0,true,172726786944,172726787008⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨912478418501,0,false,-205011585984,-205011585920⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1286153480703,0,true,172392273728,172392273792⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨912869774849,0,false,-204540113344,-204540113280⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1286404562145,0,true,172606898176,172606898240⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨912618693407,0,false,-204842571520,-204842571456⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099583175212,0,true,71545088,71545152⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099440080340,0,false,-71549824,-71549760⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099595206783,0,true,83575808,83575872⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099428048769,0,false,-83582208,-83582144⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621422,0,false,-6400,-6336⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623121,0,false,-4672,-4608⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1286235203918,0,true,172462135296,172462135360⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨912788051634,0,false,-204638549824,-204638549760⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1286474708634,0,true,172666851904,172666851968⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨912548546918,0,false,-204927086400,-204927086336⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067720064393,0,false,-32260234432,-32260234368⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067801463912,0,false,-32176414464,-32176414400⟩
    { al := (21747/128000), au := (696753/4096000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨186805307572,187033209275⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172531999552,172531999616⟩ : DyadicInterval 40),(⟨-204737004928,-204737004864⟩ : DyadicInterval 40),(⟨746177179050,746177198380⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172726786944,172726787008⟩ : DyadicInterval 40),(⟨-205011585984,-205011585920⟩ : DyadicInterval 40),(⟨746138055465,746138074794⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172392273728,172392273792⟩ : DyadicInterval 40),(⟨-204540113344,-204540113280⟩ : DyadicInterval 40),(⟨746205209154,746205228483⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172606898176,172606898240⟩ : DyadicInterval 40),(⟨-204842571520,-204842571456⟩ : DyadicInterval 40),(⟨746162142028,746162161358⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨71547436,83579007⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨71545088,71545152⟩ : DyadicInterval 40),(⟨-71549824,-71549760⟩ : DyadicInterval 40),(⟨762123381264,762123400593⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨83575808,83575872⟩ : DyadicInterval 40),(⟨-83582208,-83582144⟩ : DyadicInterval 40),(⟨762123380398,762123399728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6400,-4608⟩ : DyadicInterval 40),(⟨762123385920,762123406080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨186723576142,186963080858⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172462135296,172462135360⟩ : DyadicInterval 40),(⟨-204638549824,-204638549760⟩ : DyadicInterval 40),(⟨746191197983,746191217312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172666851904,172666851968⟩ : DyadicInterval 40),(⟨-204927086400,-204927086336⟩ : DyadicInterval 40),(⟨746150099509,746150118839⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32260234432,-32176414400⟩ : DyadicInterval 40),(⟨778211590816,778253520096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨172531999552,172726787008⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-205011585984,-204737004864⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1492_ok : ecellOkT e1492 = true := by decide +kernel
theorem e1492_pos {a z : ℝ} (ha1 : ((21747/128000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((696753/4096000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1492 e1492_ok ha1 ha2 hz1 hz2 hz

-- box ['696753/4096000', '348801/2048000', '999/1000', '7993/8000']  interval_lower 13318373/549755813888
noncomputable def e1493 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1286544837050,0,true,172726786944,172726787008⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨912478418502,0,false,-205011585984,-205011585920⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1286772738753,0,true,172921539904,172921539968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨912250516799,0,false,-205286235648,-205286235584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1286357803840,0,true,172566932352,172566932416⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨912665451712,0,false,-204786239168,-204786239104⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1286608885281,0,true,172781522752,172781522816⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨912414370271,0,false,-205088765056,-205088764992⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099595205817,0,true,83574848,83574912⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099428049735,0,false,-83581248,-83581184⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099607267754,0,true,95635776,95635840⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099415987798,0,false,-95644160,-95644096⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619456,0,false,-8384,-8320⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621423,0,false,-6400,-6336⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1286451316561,0,true,172646859264,172646859328⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨912571938991,0,false,-204898902144,-204898902080⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1286690821257,0,true,172851541440,172851541504⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨912332434295,0,false,-205187507072,-205187507008⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067646525500,0,false,-32335965568,-32335965504⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067728019163,0,false,-32252042880,-32252042816⟩
    { al := (696753/4096000), au := (348801/2048000), zl := (999/1000), zu := (7993/8000),
      A := ⟨187033209274,187261110977⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172726786944,172726787008⟩ : DyadicInterval 40),(⟨-205011585984,-205011585920⟩ : DyadicInterval 40),(⟨746138055465,746138074794⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172921539904,172921539968⟩ : DyadicInterval 40),(⟨-205286235648,-205286235584⟩ : DyadicInterval 40),(⟨746098883200,746098902530⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172566932352,172566932416⟩ : DyadicInterval 40),(⟨-204786239168,-204786239104⟩ : DyadicInterval 40),(⟨746170166798,746170186128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172781522752,172781522816⟩ : DyadicInterval 40),(⟨-205088765056,-205088764992⟩ : DyadicInterval 40),(⟨746127051599,746127070928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨83578041,95639978⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨83574848,83574912⟩ : DyadicInterval 40),(⟨-83581248,-83581184⟩ : DyadicInterval 40),(⟨762123380398,762123399728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨95635776,95635840⟩ : DyadicInterval 40),(⟨-95644160,-95644096⟩ : DyadicInterval 40),(⟨762123379424,762123398754⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8384,-6336⟩ : DyadicInterval 40),(⟨762123386784,762123407072⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨186939688785,187179193481⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172646859264,172646859328⟩ : DyadicInterval 40),(⟨-204898902144,-204898902080⟩ : DyadicInterval 40),(⟨746154115885,746154135214⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172851541440,172851541504⟩ : DyadicInterval 40),(⟨-205187507072,-205187507008⟩ : DyadicInterval 40),(⟨746112968969,746112988299⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32335965568,-32252042816⟩ : DyadicInterval 40),(⟨778249405024,778291385664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨172726786944,172921539968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-205286235648,-205011585920⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1493_ok : ecellOkT e1493 = true := by decide +kernel
theorem e1493_pos {a z : ℝ} (ha1 : ((696753/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((348801/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1493 e1493_ok ha1 ha2 hz1 hz2 hz

-- box ['696753/4096000', '348801/2048000', '7993/8000', '3997/4000']  interval_lower 13195085/549755813888
noncomputable def e1494 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1286544837050,0,true,172726786944,172726787008⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨912478418502,0,false,-205011585984,-205011585920⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1286772738753,0,true,172921539904,172921539968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨912250516799,0,false,-205286235648,-205286235584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1286381182991,0,true,172586915456,172586915520⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨912642072561,0,false,-204814404992,-204814404928⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1286632292920,0,true,172801526272,172801526336⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨912390962632,0,false,-205116972992,-205116972928⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099583266252,0,true,71636096,71636160⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099439989300,0,false,-71640832,-71640768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099595313014,0,true,83682048,83682112⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099427942538,0,false,-83688448,-83688384⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621406,0,false,-6400,-6336⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623109,0,false,-4672,-4608⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1286463005906,0,true,172656849920,172656849984⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨912560249646,0,false,-204912986112,-204912986048⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1286702524874,0,true,172861542464,172861542528⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨912320730678,0,false,-205201611968,-205201611904⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067642540563,0,false,-32340069440,-32340069376⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067724044179,0,false,-32256136192,-32256136128⟩
    { al := (696753/4096000), au := (348801/2048000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨187033209274,187261110977⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172726786944,172726787008⟩ : DyadicInterval 40),(⟨-205011585984,-205011585920⟩ : DyadicInterval 40),(⟨746138055465,746138074794⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172921539904,172921539968⟩ : DyadicInterval 40),(⟨-205286235648,-205286235584⟩ : DyadicInterval 40),(⟨746098883200,746098902530⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172586915456,172586915520⟩ : DyadicInterval 40),(⟨-204814404992,-204814404928⟩ : DyadicInterval 40),(⟨746166154667,746166173996⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172801526272,172801526336⟩ : DyadicInterval 40),(⟨-205116972992,-205116972928⟩ : DyadicInterval 40),(⟨746123029104,746123048433⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨71638476,83685238⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨71636096,71636160⟩ : DyadicInterval 40),(⟨-71640832,-71640768⟩ : DyadicInterval 40),(⟨762123381252,762123400581⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨83682048,83682112⟩ : DyadicInterval 40),(⟨-83688448,-83688384⟩ : DyadicInterval 40),(⟨762123380382,762123399711⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6400,-4608⟩ : DyadicInterval 40),(⟨762123385920,762123406080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨186951378130,187190897098⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172656849920,172656849984⟩ : DyadicInterval 40),(⟨-204912986112,-204912986048⟩ : DyadicInterval 40),(⟨746152108901,746152128231⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172861542464,172861542528⟩ : DyadicInterval 40),(⟨-205201611968,-205201611904⟩ : DyadicInterval 40),(⟨746110956904,746110976234⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32340069440,-32256136128⟩ : DyadicInterval 40),(⟨778251451680,778293437600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨172726786944,172921539968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-205286235648,-205011585920⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1494_ok : ecellOkT e1494 = true := by decide +kernel
theorem e1494_pos {a z : ℝ} (ha1 : ((696753/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((348801/2048000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1494 e1494_ok ha1 ha2 hz1 hz2 hz

-- box ['21747/128000', '696753/4096000', '3997/4000', '1599/1600']  interval_lower 23604929/1099511627776
noncomputable def e1495 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1286316935348,0,true,172531999552,172531999616⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨912706320204,0,false,-204737004928,-204737004864⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1286544837051,0,true,172726786944,172726787008⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨912478418501,0,false,-205011585984,-205011585920⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1286176831367,0,true,172412235648,172412235712⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨912846424185,0,false,-204568238592,-204568238528⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1286427941296,0,true,172626880576,172626880640⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨912595314256,0,false,-204870738816,-204870738752⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571250756,0,true,59621312,59621376⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452004796,0,false,-59624640,-59624576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099583267154,0,true,71636992,71637056⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099439988398,0,false,-71641728,-71641664⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623108,0,false,-4672,-4608⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624543,0,false,-3264,-3200⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1286246879049,0,true,172472115520,172472115584⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨912776376503,0,false,-204652613312,-204652613248⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1286486398041,0,true,172676842496,172676842560⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨912536857511,0,false,-204941170816,-204941170752⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067716088890,0,false,-32264328320,-32264328256⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067797498351,0,false,-32180497792,-32180497728⟩
    { al := (21747/128000), au := (696753/4096000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨186805307572,187033209275⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172531999552,172531999616⟩ : DyadicInterval 40),(⟨-204737004928,-204737004864⟩ : DyadicInterval 40),(⟨746177179050,746177198380⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172726786944,172726787008⟩ : DyadicInterval 40),(⟨-205011585984,-205011585920⟩ : DyadicInterval 40),(⟨746138055465,746138074794⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172412235648,172412235712⟩ : DyadicInterval 40),(⟨-204568238592,-204568238528⟩ : DyadicInterval 40),(⟨746201206400,746201225730⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172626880576,172626880640⟩ : DyadicInterval 40),(⟨-204870738816,-204870738752⟩ : DyadicInterval 40),(⟨746158128872,746158148201⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨59622980,71639378⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59621312,59621376⟩ : DyadicInterval 40),(⟨-59624640,-59624576⟩ : DyadicInterval 40),(⟨762123381982,762123401311⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨71636992,71637056⟩ : DyadicInterval 40),(⟨-71641728,-71641664⟩ : DyadicInterval 40),(⟨762123381252,762123400581⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4672,-3200⟩ : DyadicInterval 40),(⟨762123385216,762123405216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨186735251273,186974770265⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172472115520,172472115584⟩ : DyadicInterval 40),(⟨-204652613312,-204652613248⟩ : DyadicInterval 40),(⟨746189195770,746189215099⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172676842496,172676842560⟩ : DyadicInterval 40),(⟨-204941170816,-204941170752⟩ : DyadicInterval 40),(⟨746148092227,746148111556⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32264328320,-32180497728⟩ : DyadicInterval 40),(⟨778213632480,778255567040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨172531999552,172726787008⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-205011585984,-204737004864⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1495_ok : ecellOkT e1495 = true := by decide +kernel
theorem e1495_pos {a z : ℝ} (ha1 : ((21747/128000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((696753/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1495 e1495_ok ha1 ha2 hz1 hz2 hz

-- box ['21747/128000', '696753/4096000', '1599/1600', '1999/2000']  interval_lower 11679539/549755813888
noncomputable def e1496 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1286316935348,0,true,172531999552,172531999616⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨912706320204,0,false,-204737004928,-204737004864⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1286544837051,0,true,172726786944,172726787008⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨912478418501,0,false,-205011585984,-205011585920⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1286200182030,0,true,172432197184,172432197248⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨912823073522,0,false,-204596364480,-204596364416⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1286451320447,0,true,172646862528,172646862592⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨912571935105,0,false,-204898906816,-204898906752⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099559326236,0,true,47697408,47697472⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099463929316,0,false,-47699520,-47699456⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571327461,0,true,59698048,59698112⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099451928091,0,false,-59701312,-59701248⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624534,0,false,-3264,-3200⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625707,0,false,-2112,-2048⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1286258554213,0,true,172482095680,172482095744⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨912764701339,0,false,-204666677056,-204666676992⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1286498087473,0,true,172686832960,172686833024⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨912525168079,0,false,-204955255488,-204955255424⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067712113130,0,false,-32268422464,-32268422400⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067793532531,0,false,-32184581376,-32184581312⟩
    { al := (21747/128000), au := (696753/4096000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨186805307572,187033209275⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172531999552,172531999616⟩ : DyadicInterval 40),(⟨-204737004928,-204737004864⟩ : DyadicInterval 40),(⟨746177179050,746177198380⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172726786944,172726787008⟩ : DyadicInterval 40),(⟨-205011585984,-205011585920⟩ : DyadicInterval 40),(⟨746138055465,746138074794⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172432197184,172432197248⟩ : DyadicInterval 40),(⟨-204596364480,-204596364416⟩ : DyadicInterval 40),(⟨746197203116,746197222445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172646862528,172646862592⟩ : DyadicInterval 40),(⟨-204898906816,-204898906752⟩ : DyadicInterval 40),(⟨746154115247,746154134576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨47698460,59699685⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨47697408,47697472⟩ : DyadicInterval 40),(⟨-47699520,-47699456⟩ : DyadicInterval 40),(⟨762123382538,762123401867⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59698048,59698112⟩ : DyadicInterval 40),(⟨-59701312,-59701248⟩ : DyadicInterval 40),(⟨762123381942,762123401271⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3264,-2048⟩ : DyadicInterval 40),(⟨762123384640,762123404512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨186746926437,186986459697⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172482095680,172482095744⟩ : DyadicInterval 40),(⟨-204666677056,-204666676992⟩ : DyadicInterval 40),(⟨746187193440,746187212769⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172686832960,172686833024⟩ : DyadicInterval 40),(⟨-204955255488,-204955255424⟩ : DyadicInterval 40),(⟨746146084865,746146104195⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32268422464,-32184581312⟩ : DyadicInterval 40),(⟨778215674272,778257614112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨172531999552,172726787008⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-205011585984,-204737004864⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1496_ok : ecellOkT e1496 = true := by decide +kernel
theorem e1496_pos {a z : ℝ} (ha1 : ((21747/128000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((696753/4096000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1496 e1496_ok ha1 ha2 hz1 hz2 hz

-- box ['696753/4096000', '348801/2048000', '3997/4000', '1599/1600']  interval_lower 13071671/549755813888
noncomputable def e1497 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1286544837050,0,true,172726786944,172726787008⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨912478418502,0,false,-205011585984,-205011585920⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1286772738753,0,true,172921539904,172921539968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨912250516799,0,false,-205286235648,-205286235584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1286404562143,0,true,172606898176,172606898240⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨912618693409,0,false,-204842571520,-204842571456⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1286655700559,0,true,172821529472,172821529536⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨912367554993,0,false,-205145181632,-205145181568⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571326623,0,true,59697216,59697280⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099451928929,0,false,-59700480,-59700416⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099583358210,0,true,71728064,71728128⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099439897342,0,false,-71732800,-71732736⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623096,0,false,-4736,-4672⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624535,0,false,-3264,-3200⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1286474695282,0,true,172666840512,172666840576⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨912548560270,0,false,-204927070336,-204927070272⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1286714228524,0,true,172871543360,172871543424⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨912309027028,0,false,-205215717056,-205215716992⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067638555366,0,false,-32344173632,-32344173568⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067720068935,0,false,-32260229760,-32260229696⟩
    { al := (696753/4096000), au := (348801/2048000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨187033209274,187261110977⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172726786944,172726787008⟩ : DyadicInterval 40),(⟨-205011585984,-205011585920⟩ : DyadicInterval 40),(⟨746138055465,746138074794⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172921539904,172921539968⟩ : DyadicInterval 40),(⟨-205286235648,-205286235584⟩ : DyadicInterval 40),(⟨746098883200,746098902530⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172606898176,172606898240⟩ : DyadicInterval 40),(⟨-204842571520,-204842571456⟩ : DyadicInterval 40),(⟨746162142028,746162161358⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172821529472,172821529536⟩ : DyadicInterval 40),(⟨-205145181632,-205145181568⟩ : DyadicInterval 40),(⟨746119006062,746119025391⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨59698847,71730434⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59697216,59697280⟩ : DyadicInterval 40),(⟨-59700480,-59700416⟩ : DyadicInterval 40),(⟨762123381942,762123401271⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨71728064,71728128⟩ : DyadicInterval 40),(⟨-71732800,-71732736⟩ : DyadicInterval 40),(⟨762123381240,762123400569⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4736,-3200⟩ : DyadicInterval 40),(⟨762123385216,762123405248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨186963067506,187202600748⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172666840512,172666840576⟩ : DyadicInterval 40),(⟨-204927070336,-204927070272⟩ : DyadicInterval 40),(⟨746150101800,746150121130⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172871543360,172871543424⟩ : DyadicInterval 40),(⟨-205215717056,-205215716992⟩ : DyadicInterval 40),(⟨746108944731,746108964061⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32344173632,-32260229696⟩ : DyadicInterval 40),(⟨778253498464,778295489696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨172726786944,172921539968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-205286235648,-205011585920⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1497_ok : ecellOkT e1497 = true := by decide +kernel
theorem e1497_pos {a z : ℝ} (ha1 : ((696753/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((348801/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1497 e1497_ok ha1 ha2 hz1 hz2 hz

-- box ['696753/4096000', '348801/2048000', '1599/1600', '1999/2000']  interval_lower 25896703/1099511627776
noncomputable def e1498 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1286544837050,0,true,172726786944,172726787008⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨912478418502,0,false,-205011585984,-205011585920⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1286772738753,0,true,172921539904,172921539968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨912250516799,0,false,-205286235648,-205286235584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1286427941294,0,true,172626880576,172626880640⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨912595314258,0,false,-204870738816,-204870738752⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1286679108198,0,true,172841532288,172841532352⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨912344147354,0,false,-205173390976,-205173390912⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099559386932,0,true,47758080,47758144⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099463868620,0,false,-47760256,-47760192⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571403342,0,true,59773888,59773952⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099451852210,0,false,-59777216,-59777152⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624526,0,false,-3264,-3200⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625702,0,false,-2112,-2048⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1286486384689,0,true,172676831040,172676831104⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨912536870863,0,false,-204941154752,-204941154688⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1286725932206,0,true,172881544256,172881544320⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨912297323346,0,false,-205229822400,-205229822336⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067634569909,0,false,-32348278080,-32348278016⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067716093432,0,false,-32264323648,-32264323584⟩
    { al := (696753/4096000), au := (348801/2048000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨187033209274,187261110977⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172726786944,172726787008⟩ : DyadicInterval 40),(⟨-205011585984,-205011585920⟩ : DyadicInterval 40),(⟨746138055465,746138074794⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172921539904,172921539968⟩ : DyadicInterval 40),(⟨-205286235648,-205286235584⟩ : DyadicInterval 40),(⟨746098883200,746098902530⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172626880576,172626880640⟩ : DyadicInterval 40),(⟨-204870738816,-204870738752⟩ : DyadicInterval 40),(⟨746158128873,746158148202⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172841532288,172841532352⟩ : DyadicInterval 40),(⟨-205173390976,-205173390912⟩ : DyadicInterval 40),(⟨746114982510,746115001839⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨47759156,59775566⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨47758080,47758144⟩ : DyadicInterval 40),(⟨-47760256,-47760192⟩ : DyadicInterval 40),(⟨762123382565,762123401894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59773888,59773952⟩ : DyadicInterval 40),(⟨-59777216,-59777152⟩ : DyadicInterval 40),(⟨762123381966,762123401295⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3264,-2048⟩ : DyadicInterval 40),(⟨762123384640,762123404512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨186974756913,187214304430⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172676831040,172676831104⟩ : DyadicInterval 40),(⟨-204941154752,-204941154688⟩ : DyadicInterval 40),(⟨746148094555,746148113885⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172881544256,172881544320⟩ : DyadicInterval 40),(⟨-205229822400,-205229822336⟩ : DyadicInterval 40),(⟨746106932402,746106951732⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32348278080,-32264323584⟩ : DyadicInterval 40),(⟨778255545408,778297541920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨172726786944,172921539968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-205286235648,-205011585920⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1498_ok : ecellOkT e1498 = true := by decide +kernel
theorem e1498_pos {a z : ℝ} (ha1 : ((696753/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((348801/2048000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1498 e1498_ok ha1 ha2 hz1 hz2 hz

-- box ['348801/2048000', '698451/4096000', '999/1000', '7993/8000']  interval_lower 14595261/549755813888
noncomputable def e1499 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1286772738752,0,true,172921539904,172921539968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨912250516800,0,false,-205286235648,-205286235584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1287000640455,0,true,173116258368,173116258432⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨912022615097,0,false,-205560953920,-205560953856⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1286585477640,0,true,172761518848,172761518912⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨912437777912,0,false,-205060557888,-205060557824⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1286836587569,0,true,172976095616,172976095680⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨912186667983,0,false,-205363193600,-205363193536⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099595312047,0,true,83681024,83681088⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099427943505,0,false,-83687488,-83687424⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099607389179,0,true,95757184,95757248⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099415866373,0,false,-95765632,-95765568⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619435,0,false,-8384,-8320⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621407,0,false,-6400,-6336⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1286679104313,0,true,172841528960,172841529024⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨912344151239,0,false,-205173386304,-205173386240⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1286918623258,0,true,173046187072,173046187136⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨912104632294,0,false,-205462080448,-205462080384⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067568916968,0,false,-32415893312,-32415893248⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067650514726,0,false,-32331857280,-32331857216⟩
    { al := (348801/2048000), au := (698451/4096000), zl := (999/1000), zu := (7993/8000),
      A := ⟨187261110976,187489012679⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172921539904,172921539968⟩ : DyadicInterval 40),(⟨-205286235648,-205286235584⟩ : DyadicInterval 40),(⟨746098883200,746098902530⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173116258368,173116258432⟩ : DyadicInterval 40),(⟨-205560953920,-205560953856⟩ : DyadicInterval 40),(⟨746059662284,746059681614⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172761518848,172761518912⟩ : DyadicInterval 40),(⟨-205060557888,-205060557824⟩ : DyadicInterval 40),(⟨746131073611,746131092941⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172976095616,172976095680⟩ : DyadicInterval 40),(⟨-205363193600,-205363193536⟩ : DyadicInterval 40),(⟨746087899966,746087919296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨83684271,95761403⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨83681024,83681088⟩ : DyadicInterval 40),(⟨-83687488,-83687424⟩ : DyadicInterval 40),(⟨762123380414,762123399744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨95757184,95757248⟩ : DyadicInterval 40),(⟨-95765632,-95765568⟩ : DyadicInterval 40),(⟨762123379435,762123398765⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8384,-6336⟩ : DyadicInterval 40),(⟨762123386784,762123407072⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨187167476537,187406995482⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172841528960,172841529024⟩ : DyadicInterval 40),(⟨-205173386304,-205173386240⟩ : DyadicInterval 40),(⟨746114983187,746115002516⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173046187072,173046187136⟩ : DyadicInterval 40),(⟨-205462080448,-205462080384⟩ : DyadicInterval 40),(⟨746073782712,746073802041⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32415893312,-32331857216⟩ : DyadicInterval 40),(⟨778289312224,778331349536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨172921539904,173116258432⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-205560953920,-205286235584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1499_ok : ecellOkT e1499 = true := by decide +kernel
theorem e1499_pos {a z : ℝ} (ha1 : ((348801/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((698451/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1499 e1499_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B024

end


