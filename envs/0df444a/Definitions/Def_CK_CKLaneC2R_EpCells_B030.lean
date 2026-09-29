-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B030
-- name    : CK_CKLaneC2R_EpCells_B030
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T15:28:14.316275+00:00
-- url     : https://prove2.me/theorems/49ec82e4-a90c-4b52-8aeb-c3cb226f4a65
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B030` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B030` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B030` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B030 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B030.lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheckT

-- ===== source module CKLaneC2R.EpCells.B030 =====
section

namespace CKLaneC2R.EpCells.B030

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['314841/2048000', '1260213/8192000', '999/1000', '7993/8000']  interval_lower 149610701/1099511627776
noncomputable def e1800 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268540602580,0,true,157231263808,157231263872⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930482652972,0,false,-183528229376,-183528229312⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268654553433,0,true,157330026624,157330026688⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930368702119,0,false,-183662888512,-183662888448⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268371573605,0,true,157084747648,157084747712⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930651681947,0,false,-183328513216,-183328513152⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268506553374,0,true,157201751168,157201751232⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930516702178,0,false,-183487995648,-183487995584⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586864117,0,true,75233728,75233792⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436391435,0,false,-75238976,-75238912⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099597672900,0,true,86041728,86041792⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099425582652,0,false,-86048512,-86048448⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621042,0,false,-6784,-6720⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622628,0,false,-5184,-5120⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268456084611,0,true,157158005120,157158005184⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930567170941,0,false,-183428362688,-183428362624⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268580558319,0,true,157265895040,157265895104⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930442697233,0,false,-183575444416,-183575444352⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073514355393,0,false,-26309549376,-26309549312⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073552621274,0,false,-26270357504,-26270357440⟩
    { al := (314841/2048000), au := (1260213/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨169028974804,169142925657⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157231263808,157231263872⟩ : DyadicInterval 40),(⟨-183528229376,-183528229312⟩ : DyadicInterval 40),(⟨749079224833,749079244162⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157330026624,157330026688⟩ : DyadicInterval 40),(⟨-183662888512,-183662888448⟩ : DyadicInterval 40),(⟨749061561043,749061580372⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157084747648,157084747712⟩ : DyadicInterval 40),(⟨-183328513216,-183328513152⟩ : DyadicInterval 40),(⟨749105404174,749105423504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157201751168,157201751232⟩ : DyadicInterval 40),(⟨-183487995648,-183487995584⟩ : DyadicInterval 40),(⟨749084500544,749084519874⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨75236341,86045124⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75233728,75233792⟩ : DyadicInterval 40),(⟨-75238976,-75238912⟩ : DyadicInterval 40),(⟨762123381027,762123400356⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨86041728,86041792⟩ : DyadicInterval 40),(⟨-86048512,-86048448⟩ : DyadicInterval 40),(⟨762123380210,762123399539⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6784,-5120⟩ : DyadicInterval 40),(⟨762123386176,762123406272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168944456835,169068930543⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157158005120,157158005184⟩ : DyadicInterval 40),(⟨-183428362688,-183428362624⟩ : DyadicInterval 40),(⟨749092318404,749092337734⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157265895040,157265895104⟩ : DyadicInterval 40),(⟨-183575444416,-183575444352⟩ : DyadicInterval 40),(⟨749073032577,749073051906⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26309549376,-26270357440⟩ : DyadicInterval 40),(⟨775258562336,775278177568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157231263808,157330026688⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183662888512,-183528229312⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1800_ok : ecellOkT e1800 = true := by decide +kernel
theorem e1800_pos {a z : ℝ} (ha1 : ((314841/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1260213/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1800 e1800_ok ha1 ha2 hz1 hz2 hz

-- box ['1260213/8192000', '630531/4096000', '999/1000', '7993/8000']  interval_lower 37659371/274877906944
noncomputable def e1801 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268654553432,0,true,157330026624,157330026688⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930368702120,0,false,-183662888512,-183662888448⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268768504284,0,true,157428780608,157428780672⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930254751268,0,false,-183797564096,-183797564032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268485410506,0,true,157183424832,157183424896⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930537845046,0,false,-183463013248,-183463013184⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268620404518,0,true,157300430208,157300430272⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930402851034,0,false,-183622531968,-183622531904⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586916610,0,true,75286208,75286272⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436338942,0,false,-75291456,-75291392⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099597732899,0,true,86101696,86101760⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099425522653,0,false,-86108544,-86108480⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621032,0,false,-6784,-6720⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622621,0,false,-5184,-5120⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268569978225,0,true,157256724928,157256724992⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930453277327,0,false,-183562941888,-183562941824⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268694459319,0,true,157364611520,157364611584⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930328796233,0,false,-183710050368,-183710050304⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073479315096,0,false,-26345438784,-26345438720⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073517609037,0,false,-26306216896,-26306216832⟩
    { al := (1260213/8192000), au := (630531/4096000), zl := (999/1000), zu := (7993/8000),
      A := ⟨169142925656,169256876508⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157330026624,157330026688⟩ : DyadicInterval 40),(⟨-183662888512,-183662888448⟩ : DyadicInterval 40),(⟨749061561043,749061580372⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157428780608,157428780672⟩ : DyadicInterval 40),(⟨-183797564096,-183797564032⟩ : DyadicInterval 40),(⟨749043885115,749043904445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157183424832,157183424896⟩ : DyadicInterval 40),(⟨-183463013248,-183463013184⟩ : DyadicInterval 40),(⟨749087775989,749087795319⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157300430208,157300430272⟩ : DyadicInterval 40),(⟨-183622531968,-183622531904⟩ : DyadicInterval 40),(⟨749066855808,749066875137⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨75288834,86105123⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75286208,75286272⟩ : DyadicInterval 40),(⟨-75291456,-75291392⟩ : DyadicInterval 40),(⟨762123381020,762123400349⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨86101696,86101760⟩ : DyadicInterval 40),(⟨-86108544,-86108480⟩ : DyadicInterval 40),(⟨762123380232,762123399562⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6784,-5120⟩ : DyadicInterval 40),(⟨762123386176,762123406272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169058350449,169182831543⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157256724928,157256724992⟩ : DyadicInterval 40),(⟨-183562941888,-183562941824⟩ : DyadicInterval 40),(⟨749074672416,749074691745⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157364611520,157364611584⟩ : DyadicInterval 40),(⟨-183710050368,-183710050304⟩ : DyadicInterval 40),(⟨749055372269,749055391598⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26345438784,-26306216832⟩ : DyadicInterval 40),(⟨775276492032,775296122272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157330026624,157428780672⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183797564096,-183662888448⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1801_ok : ecellOkT e1801 = true := by decide +kernel
theorem e1801_pos {a z : ℝ} (ha1 : ((1260213/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((630531/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1801 e1801_ok ha1 ha2 hz1 hz2 hz

-- box ['314841/2048000', '1260213/8192000', '7993/8000', '3997/4000']  interval_lower 37365681/274877906944
noncomputable def e1802 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268540602580,0,true,157231263808,157231263872⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930482652972,0,false,-183528229376,-183528229312⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268654553433,0,true,157330026624,157330026688⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930368702119,0,false,-183662888512,-183662888448⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268392702226,0,true,157103063232,157103063296⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930630553326,0,false,-183353475776,-183353475712⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268527696239,0,true,157220077120,157220077184⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930495559313,0,false,-183512978624,-183512978560⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576116172,0,true,64486464,64486528⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447139380,0,false,-64490304,-64490240⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586917457,0,true,75287040,75287104⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436338095,0,false,-75292288,-75292224⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622620,0,false,-5184,-5120⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623994,0,false,-3840,-3776⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268466648495,0,true,157167161984,157167162048⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930556607057,0,false,-183440844480,-183440844416⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268591129602,0,true,157275057408,157275057472⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930432125950,0,false,-183587936640,-183587936576⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073511104256,0,false,-26312879232,-26312879168⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073549374804,0,false,-26273682432,-26273682368⟩
    { al := (314841/2048000), au := (1260213/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨169028974804,169142925657⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157231263808,157231263872⟩ : DyadicInterval 40),(⟨-183528229376,-183528229312⟩ : DyadicInterval 40),(⟨749079224833,749079244162⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157330026624,157330026688⟩ : DyadicInterval 40),(⟨-183662888512,-183662888448⟩ : DyadicInterval 40),(⟨749061561043,749061580372⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157103063232,157103063296⟩ : DyadicInterval 40),(⟨-183353475776,-183353475712⟩ : DyadicInterval 40),(⟨749102133224,749102152554⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157220077120,157220077184⟩ : DyadicInterval 40),(⟨-183512978624,-183512978560⟩ : DyadicInterval 40),(⟨749081224732,749081244062⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨64488396,75289681⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64486464,64486528⟩ : DyadicInterval 40),(⟨-64490304,-64490240⟩ : DyadicInterval 40),(⟨762123381689,762123401018⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75287040,75287104⟩ : DyadicInterval 40),(⟨-75292288,-75292224⟩ : DyadicInterval 40),(⟨762123381020,762123400349⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5184,-3776⟩ : DyadicInterval 40),(⟨762123385504,762123405472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168955020719,169079501826⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157167161984,157167162048⟩ : DyadicInterval 40),(⟨-183440844480,-183440844416⟩ : DyadicInterval 40),(⟨749090682188,749090701518⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157275057408,157275057472⟩ : DyadicInterval 40),(⟨-183587936640,-183587936576⟩ : DyadicInterval 40),(⟨749071394003,749071413332⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26312879232,-26273682368⟩ : DyadicInterval 40),(⟨775260224800,775279842496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157231263808,157330026688⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183662888512,-183528229312⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1802_ok : ecellOkT e1802 = true := by decide +kernel
theorem e1802_pos {a z : ℝ} (ha1 : ((314841/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1260213/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1802 e1802_ok ha1 ha2 hz1 hz2 hz

-- box ['1260213/8192000', '630531/4096000', '7993/8000', '3997/4000']  interval_lower 37622329/274877906944
noncomputable def e1803 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268654553432,0,true,157330026624,157330026688⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930368702120,0,false,-183662888512,-183662888448⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268768504284,0,true,157428780608,157428780672⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930254751268,0,false,-183797564096,-183797564032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268506553371,0,true,157201751168,157201751232⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930516702181,0,false,-183487995648,-183487995584⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268641561627,0,true,157318766912,157318766976⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930381693925,0,false,-183647534848,-183647534784⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576161167,0,true,64531456,64531520⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447094385,0,false,-64535296,-64535232⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586969955,0,true,75339584,75339648⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436285597,0,false,-75344768,-75344704⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622613,0,false,-5184,-5120⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623989,0,false,-3840,-3776⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268580549491,0,true,157265887360,157265887424⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930442706061,0,false,-183575433984,-183575433920⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268705037728,0,true,157373779264,157373779328⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930318217824,0,false,-183722552576,-183722552512⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073476059576,0,false,-26348773248,-26348773184⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073514358109,0,false,-26309546560,-26309546496⟩
    { al := (1260213/8192000), au := (630531/4096000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨169142925656,169256876508⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157330026624,157330026688⟩ : DyadicInterval 40),(⟨-183662888512,-183662888448⟩ : DyadicInterval 40),(⟨749061561043,749061580372⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157428780608,157428780672⟩ : DyadicInterval 40),(⟨-183797564096,-183797564032⟩ : DyadicInterval 40),(⟨749043885115,749043904445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157201751168,157201751232⟩ : DyadicInterval 40),(⟨-183487995648,-183487995584⟩ : DyadicInterval 40),(⟨749084500545,749084519874⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157318766912,157318766976⟩ : DyadicInterval 40),(⟨-183647534848,-183647534784⟩ : DyadicInterval 40),(⟨749063575521,749063594851⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨64533391,75342179⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64531456,64531520⟩ : DyadicInterval 40),(⟨-64535296,-64535232⟩ : DyadicInterval 40),(⟨762123381684,762123401013⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75339584,75339648⟩ : DyadicInterval 40),(⟨-75344768,-75344704⟩ : DyadicInterval 40),(⟨762123380981,762123400310⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5184,-3776⟩ : DyadicInterval 40),(⟨762123385504,762123405472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169068921715,169193409952⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157265887360,157265887424⟩ : DyadicInterval 40),(⟨-183575433984,-183575433920⟩ : DyadicInterval 40),(⟨749073033961,749073053291⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157373779264,157373779328⟩ : DyadicInterval 40),(⟨-183722552576,-183722552512⟩ : DyadicInterval 40),(⟨749053731468,749053750798⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26348773248,-26309546496⟩ : DyadicInterval 40),(⟨775278156864,775297789504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157330026624,157428780672⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183797564096,-183662888448⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1803_ok : ecellOkT e1803 = true := by decide +kernel
theorem e1803_pos {a z : ℝ} (ha1 : ((1260213/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((630531/4096000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1803 e1803_ok ha1 ha2 hz1 hz2 hz

-- box ['630531/4096000', '1261911/8192000', '999/1000', '7993/8000']  interval_lower 2369799/17179869184
noncomputable def e1804 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268768504283,0,true,157428780608,157428780672⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930254751269,0,false,-183797564096,-183797564032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268882455135,0,true,157527525696,157527525760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930140800417,0,false,-183932256192,-183932256128⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268599247406,0,true,157282093248,157282093312⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930424008146,0,false,-183597529664,-183597529600⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268734255662,0,true,157399100416,157399100480⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930288999890,0,false,-183757084800,-183757084736⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586969108,0,true,75338688,75338752⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436286444,0,false,-75343936,-75343872⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099597792900,0,true,86161728,86161792⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099425462652,0,false,-86168512,-86168448⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621023,0,false,-6784,-6720⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622614,0,false,-5184,-5120⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268683872106,0,true,157355436096,157355436160⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930339383446,0,false,-183697537920,-183697537856⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268808360317,0,true,157463319168,157463319232⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930214895235,0,false,-183844672832,-183844672768⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073444251201,0,false,-26381353600,-26381353536⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073482573123,0,false,-26342101760,-26342101696⟩
    { al := (630531/4096000), au := (1261911/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨169256876507,169370827359⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157428780608,157428780672⟩ : DyadicInterval 40),(⟨-183797564096,-183797564032⟩ : DyadicInterval 40),(⟨749043885116,749043904445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157527525696,157527525760⟩ : DyadicInterval 40),(⟨-183932256192,-183932256128⟩ : DyadicInterval 40),(⟨749026197113,749026216443⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157282093248,157282093312⟩ : DyadicInterval 40),(⟨-183597529664,-183597529600⟩ : DyadicInterval 40),(⟨749070135653,749070154982⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157399100416,157399100480⟩ : DyadicInterval 40),(⟨-183757084800,-183757084736⟩ : DyadicInterval 40),(⟨749049199004,749049218334⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨75341332,86165124⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75338688,75338752⟩ : DyadicInterval 40),(⟨-75343936,-75343872⟩ : DyadicInterval 40),(⟨762123381013,762123400342⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨86161728,86161792⟩ : DyadicInterval 40),(⟨-86168512,-86168448⟩ : DyadicInterval 40),(⟨762123380191,762123399520⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6784,-5120⟩ : DyadicInterval 40),(⟨762123386176,762123406272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169172244330,169296732541⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157355436096,157355436160⟩ : DyadicInterval 40),(⟨-183697537920,-183697537856⟩ : DyadicInterval 40),(⟨749057014325,749057033655⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157463319168,157463319232⟩ : DyadicInterval 40),(⟨-183844672832,-183844672768⟩ : DyadicInterval 40),(⟨749037699872,749037719201⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26381353600,-26342101696⟩ : DyadicInterval 40),(⟨775294434464,775314079680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157428780608,157527525760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183932256192,-183797564032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1804_ok : ecellOkT e1804 = true := by decide +kernel
theorem e1804_pos {a z : ℝ} (ha1 : ((630531/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1261911/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1804 e1804_ok ha1 ha2 hz1 hz2 hz

-- box ['1261911/8192000', '31569/204800', '999/1000', '7993/8000']  interval_lower 152699761/1099511627776
noncomputable def e1805 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268882455134,0,true,157527525696,157527525760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930140800418,0,false,-183932256192,-183932256128⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268996405986,0,true,157626261888,157626261952⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930026849566,0,false,-184066964800,-184066964736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268713084306,0,true,157380752704,157380752768⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930310171246,0,false,-183732062592,-183732062528⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268848106806,0,true,157497761792,157497761856⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930175148746,0,false,-183891654080,-183891654016⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587021610,0,true,75391232,75391296⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436233942,0,false,-75396480,-75396416⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099597852907,0,true,86221696,86221760⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099425402645,0,false,-86228544,-86228480⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621014,0,false,-6784,-6720⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622607,0,false,-5184,-5120⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268797765977,0,true,157454138432,157454138496⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930225489575,0,false,-183832150400,-183832150336⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268922261314,0,true,157562017984,157562018048⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930100994238,0,false,-183979311744,-183979311680⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073409163708,0,false,-26417293760,-26417293696⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073447513616,0,false,-26378011968,-26378011904⟩
    { al := (1261911/8192000), au := (31569/204800), zl := (999/1000), zu := (7993/8000),
      A := ⟨169370827358,169484778210⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157527525696,157527525760⟩ : DyadicInterval 40),(⟨-183932256192,-183932256128⟩ : DyadicInterval 40),(⟨749026197114,749026216443⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157626261888,157626261952⟩ : DyadicInterval 40),(⟨-184066964800,-184066964736⟩ : DyadicInterval 40),(⟨749008497035,749008516365⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157380752704,157380752768⟩ : DyadicInterval 40),(⟨-183732062592,-183732062528⟩ : DyadicInterval 40),(⟨749052483329,749052502658⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157497761792,157497761856⟩ : DyadicInterval 40),(⟨-183891654080,-183891654016⟩ : DyadicInterval 40),(⟨749031530104,749031549433⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨75393834,86225131⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75391232,75391296⟩ : DyadicInterval 40),(⟨-75396480,-75396416⟩ : DyadicInterval 40),(⟨762123381006,762123400335⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨86221696,86221760⟩ : DyadicInterval 40),(⟨-86228544,-86228480⟩ : DyadicInterval 40),(⟨762123380213,762123399543⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6784,-5120⟩ : DyadicInterval 40),(⟨762123386176,762123406272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169286138201,169410633538⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157454138432,157454138496⟩ : DyadicInterval 40),(⟨-183832150400,-183832150336⟩ : DyadicInterval 40),(⟨749039344122,749039363452⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157562017984,157562018048⟩ : DyadicInterval 40),(⟨-183979311744,-183979311680⟩ : DyadicInterval 40),(⟨749020015357,749020034687⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26417293760,-26378011904⟩ : DyadicInterval 40),(⟨775312389568,775332049760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157527525696,157626261952⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184066964800,-183932256128⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1805_ok : ecellOkT e1805 = true := by decide +kernel
theorem e1805_pos {a z : ℝ} (ha1 : ((1261911/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((31569/204800 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1805 e1805_ok ha1 ha2 hz1 hz2 hz

-- box ['630531/4096000', '1261911/8192000', '7993/8000', '3997/4000']  interval_lower 151519005/1099511627776
noncomputable def e1806 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268768504283,0,true,157428780608,157428780672⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930254751269,0,false,-183797564096,-183797564032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268882455135,0,true,157527525696,157527525760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930140800417,0,false,-183932256192,-183932256128⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268620404515,0,true,157300430208,157300430272⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930402851037,0,false,-183622531968,-183622531904⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268755427015,0,true,157417447808,157417447872⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930267828537,0,false,-183782107584,-183782107520⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576206166,0,true,64576448,64576512⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447049386,0,false,-64580288,-64580224⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587022458,0,true,75392064,75392128⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436233094,0,false,-75397312,-75397248⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622606,0,false,-5184,-5120⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623984,0,false,-3840,-3776⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268694450489,0,true,157364603904,157364603968⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930328805063,0,false,-183710039936,-183710039872⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268818945845,0,true,157472492288,157472492352⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930204309707,0,false,-183857184960,-183857184896⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073440991297,0,false,-26384692672,-26384692608⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073479317814,0,false,-26345436032,-26345435968⟩
    { al := (630531/4096000), au := (1261911/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨169256876507,169370827359⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157428780608,157428780672⟩ : DyadicInterval 40),(⟨-183797564096,-183797564032⟩ : DyadicInterval 40),(⟨749043885116,749043904445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157527525696,157527525760⟩ : DyadicInterval 40),(⟨-183932256192,-183932256128⟩ : DyadicInterval 40),(⟨749026197113,749026216443⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157300430208,157300430272⟩ : DyadicInterval 40),(⟨-183622531968,-183622531904⟩ : DyadicInterval 40),(⟨749066855809,749066875138⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157417447808,157417447872⟩ : DyadicInterval 40),(⟨-183782107584,-183782107520⟩ : DyadicInterval 40),(⟨749045914273,749045933602⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨64578390,75394682⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64576448,64576512⟩ : DyadicInterval 40),(⟨-64580288,-64580224⟩ : DyadicInterval 40),(⟨762123381678,762123401008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75392064,75392128⟩ : DyadicInterval 40),(⟨-75397312,-75397248⟩ : DyadicInterval 40),(⟨762123381005,762123400335⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5184,-3776⟩ : DyadicInterval 40),(⟨762123385504,762123405472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169182822713,169307318069⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157364603904,157364603968⟩ : DyadicInterval 40),(⟨-183710039936,-183710039872⟩ : DyadicInterval 40),(⟨749055373619,749055392948⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157472492288,157472492352⟩ : DyadicInterval 40),(⟨-183857184960,-183857184896⟩ : DyadicInterval 40),(⟨749036056816,749036076145⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26384692672,-26345435968⟩ : DyadicInterval 40),(⟨775296101600,775315749216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157428780608,157527525760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183932256192,-183797564032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1806_ok : ecellOkT e1806 = true := by decide +kernel
theorem e1806_pos {a z : ℝ} (ha1 : ((630531/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1261911/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1806 e1806_ok ha1 ha2 hz1 hz2 hz

-- box ['1261911/8192000', '31569/204800', '7993/8000', '3997/4000']  interval_lower 152550881/1099511627776
noncomputable def e1807 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268882455134,0,true,157527525696,157527525760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930140800418,0,false,-183932256192,-183932256128⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268996405986,0,true,157626261888,157626261952⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930026849566,0,false,-184066964800,-184066964736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268734255659,0,true,157399100416,157399100480⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930288999893,0,false,-183757084800,-183757084736⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268869292403,0,true,157516119872,157516119936⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930153963149,0,false,-183916696768,-183916696704⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576251168,0,true,64621440,64621504⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447004384,0,false,-64625344,-64625280⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587074964,0,true,75444544,75444608⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436180588,0,false,-75449792,-75449728⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622598,0,false,-5184,-5120⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623978,0,false,-3840,-3776⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268808351483,0,true,157463311552,157463311616⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930214904069,0,false,-183844662400,-183844662336⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268932853964,0,true,157571196416,157571196480⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930090401588,0,false,-183991833856,-183991833792⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073405899416,0,false,-26420637440,-26420637376⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073444253923,0,false,-26381350784,-26381350720⟩
    { al := (1261911/8192000), au := (31569/204800), zl := (7993/8000), zu := (3997/4000),
      A := ⟨169370827358,169484778210⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157527525696,157527525760⟩ : DyadicInterval 40),(⟨-183932256192,-183932256128⟩ : DyadicInterval 40),(⟨749026197114,749026216443⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157626261888,157626261952⟩ : DyadicInterval 40),(⟨-184066964800,-184066964736⟩ : DyadicInterval 40),(⟨749008497035,749008516365⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157399100416,157399100480⟩ : DyadicInterval 40),(⟨-183757084800,-183757084736⟩ : DyadicInterval 40),(⟨749049199004,749049218334⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157516119872,157516119936⟩ : DyadicInterval 40),(⟨-183916696768,-183916696704⟩ : DyadicInterval 40),(⟨749028240922,749028260252⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨64623392,75447188⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64621440,64621504⟩ : DyadicInterval 40),(⟨-64625344,-64625280⟩ : DyadicInterval 40),(⟨762123381705,762123401034⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75444544,75444608⟩ : DyadicInterval 40),(⟨-75449792,-75449728⟩ : DyadicInterval 40),(⟨762123380998,762123400328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5184,-3776⟩ : DyadicInterval 40),(⟨762123385504,762123405472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169296723707,169421226188⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157463311552,157463311616⟩ : DyadicInterval 40),(⟨-183844662400,-183844662336⟩ : DyadicInterval 40),(⟨749037701225,749037720554⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157571196416,157571196480⟩ : DyadicInterval 40),(⟨-183991833856,-183991833792⟩ : DyadicInterval 40),(⟨749018370106,749018389435⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26420637440,-26381350720⟩ : DyadicInterval 40),(⟨775314058976,775333721600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157527525696,157626261952⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184066964800,-183932256128⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1807_ok : ecellOkT e1807 = true := by decide +kernel
theorem e1807_pos {a z : ℝ} (ha1 : ((1261911/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((31569/204800 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1807 e1807_ok ha1 ha2 hz1 hz2 hz

-- box ['314841/2048000', '1260213/8192000', '3997/4000', '1599/1600']  interval_lower 74657463/549755813888
noncomputable def e1808 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268540602580,0,true,157231263808,157231263872⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930482652972,0,false,-183528229376,-183528229312⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268654553433,0,true,157330026624,157330026688⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930368702119,0,false,-183662888512,-183662888448⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268413830848,0,true,157121378496,157121378560⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930609424704,0,false,-183378438848,-183378438784⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268548839105,0,true,157238402816,157238402880⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930474416447,0,false,-183537962176,-183537962112⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565368180,0,true,53739072,53739136⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457887372,0,false,-53741760,-53741696⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576161966,0,true,64532288,64532352⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447093586,0,false,-64536128,-64536064⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623988,0,false,-3840,-3776⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625150,0,false,-2688,-2624⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268477212659,0,true,157176319040,157176319104⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930546042893,0,false,-183453326784,-183453326720⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268601700911,0,true,157284219712,157284219776⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930421554641,0,false,-183600429056,-183600428992⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073507852908,0,false,-26316209344,-26316209280⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073546128046,0,false,-26277007744,-26277007680⟩
    { al := (314841/2048000), au := (1260213/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨169028974804,169142925657⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157231263808,157231263872⟩ : DyadicInterval 40),(⟨-183528229376,-183528229312⟩ : DyadicInterval 40),(⟨749079224833,749079244162⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157330026624,157330026688⟩ : DyadicInterval 40),(⟨-183662888512,-183662888448⟩ : DyadicInterval 40),(⟨749061561043,749061580372⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157121378496,157121378560⟩ : DyadicInterval 40),(⟨-183378438848,-183378438784⟩ : DyadicInterval 40),(⟨749098861844,749098881173⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157238402816,157238402880⟩ : DyadicInterval 40),(⟨-183537962176,-183537962112⟩ : DyadicInterval 40),(⟨749077948479,749077967808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨53740404,64534190⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53739072,53739136⟩ : DyadicInterval 40),(⟨-53741760,-53741696⟩ : DyadicInterval 40),(⟨762123382269,762123401598⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64532288,64532352⟩ : DyadicInterval 40),(⟨-64536128,-64536064⟩ : DyadicInterval 40),(⟨762123381684,762123401013⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3840,-2624⟩ : DyadicInterval 40),(⟨762123384928,762123404800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168965584883,169090073135⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157176319040,157176319104⟩ : DyadicInterval 40),(⟨-183453326784,-183453326720⟩ : DyadicInterval 40),(⟨749089045827,749089065156⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157284219712,157284219776⟩ : DyadicInterval 40),(⟨-183600429056,-183600428992⟩ : DyadicInterval 40),(⟨749069755334,749069774664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26316209344,-26277007680⟩ : DyadicInterval 40),(⟨775261887456,775281507552⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157231263808,157330026688⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183662888512,-183528229312⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1808_ok : ecellOkT e1808 = true := by decide +kernel
theorem e1808_pos {a z : ℝ} (ha1 : ((314841/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1260213/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1808 e1808_ok ha1 ha2 hz1 hz2 hz

-- box ['1260213/8192000', '630531/4096000', '3997/4000', '1599/1600']  interval_lower 9396321/68719476736
noncomputable def e1809 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268654553432,0,true,157330026624,157330026688⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930368702120,0,false,-183662888512,-183662888448⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268768504284,0,true,157428780608,157428780672⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930254751268,0,false,-183797564096,-183797564032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268527696237,0,true,157220077120,157220077184⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930495559315,0,false,-183512978624,-183512978560⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268662718737,0,true,157337103296,157337103360⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930360536815,0,false,-183672538304,-183672538240⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565405677,0,true,53776576,53776640⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457849875,0,false,-53779264,-53779200⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576206965,0,true,64577280,64577344⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447048587,0,false,-64581120,-64581056⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623982,0,false,-3840,-3776⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625146,0,false,-2688,-2624⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268591120775,0,true,157275049728,157275049792⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930432134777,0,false,-183587926208,-183587926144⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268715616157,0,true,157382946944,157382947008⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930307639395,0,false,-183735054912,-183735054848⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073472803846,0,false,-26352107968,-26352107904⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073511106972,0,false,-26312876416,-26312876352⟩
    { al := (1260213/8192000), au := (630531/4096000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨169142925656,169256876508⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157330026624,157330026688⟩ : DyadicInterval 40),(⟨-183662888512,-183662888448⟩ : DyadicInterval 40),(⟨749061561043,749061580372⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157428780608,157428780672⟩ : DyadicInterval 40),(⟨-183797564096,-183797564032⟩ : DyadicInterval 40),(⟨749043885115,749043904445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157220077120,157220077184⟩ : DyadicInterval 40),(⟨-183512978624,-183512978560⟩ : DyadicInterval 40),(⟨749081224732,749081244062⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157337103296,157337103360⟩ : DyadicInterval 40),(⟨-183672538304,-183672538240⟩ : DyadicInterval 40),(⟨749060294828,749060314158⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨53777901,64579189⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53776576,53776640⟩ : DyadicInterval 40),(⟨-53779264,-53779200⟩ : DyadicInterval 40),(⟨762123382265,762123401594⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64577280,64577344⟩ : DyadicInterval 40),(⟨-64581120,-64581056⟩ : DyadicInterval 40),(⟨762123381678,762123401008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3840,-2624⟩ : DyadicInterval 40),(⟨762123384928,762123404800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169079492999,169203988381⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157275049728,157275049792⟩ : DyadicInterval 40),(⟨-183587926208,-183587926144⟩ : DyadicInterval 40),(⟨749071395388,749071414717⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157382946944,157382947008⟩ : DyadicInterval 40),(⟨-183735054912,-183735054848⟩ : DyadicInterval 40),(⟨749052090548,749052109877⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26352107968,-26312876352⟩ : DyadicInterval 40),(⟨775279821792,775299456864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157330026624,157428780672⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183797564096,-183662888448⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1809_ok : ecellOkT e1809 = true := by decide +kernel
theorem e1809_pos {a z : ℝ} (ha1 : ((1260213/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((630531/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1809 e1809_ok ha1 ha2 hz1 hz2 hz

-- box ['314841/2048000', '1260213/8192000', '1599/1600', '1999/2000']  interval_lower 149166925/1099511627776
noncomputable def e1810 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268540602580,0,true,157231263808,157231263872⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930482652972,0,false,-183528229376,-183528229312⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268654553433,0,true,157330026624,157330026688⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930368702119,0,false,-183662888512,-183662888448⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268434959470,0,true,157139693504,157139693568⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930588296082,0,false,-183403402560,-183403402496⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268569981971,0,true,157256728192,157256728256⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930453273581,0,false,-183562946304,-183562946240⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554620142,0,true,42991488,42991552⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468635410,0,false,-42993216,-42993152⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565406428,0,true,53777280,53777344⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457849124,0,false,-53779968,-53779904⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625145,0,false,-2688,-2624⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626095,0,false,-1728,-1664⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268487776845,0,true,157185475968,157185476032⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930535478707,0,false,-183465809280,-183465809216⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268612272242,0,true,157293381952,157293382016⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930410983310,0,false,-183612921664,-183612921600⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073504601350,0,false,-26319539648,-26319539584⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073542881078,0,false,-26280333248,-26280333184⟩
    { al := (314841/2048000), au := (1260213/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨169028974804,169142925657⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157231263808,157231263872⟩ : DyadicInterval 40),(⟨-183528229376,-183528229312⟩ : DyadicInterval 40),(⟨749079224833,749079244162⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157330026624,157330026688⟩ : DyadicInterval 40),(⟨-183662888512,-183662888448⟩ : DyadicInterval 40),(⟨749061561043,749061580372⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157139693504,157139693568⟩ : DyadicInterval 40),(⟨-183403402560,-183403402496⟩ : DyadicInterval 40),(⟨749095590050,749095609380⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157256728192,157256728256⟩ : DyadicInterval 40),(⟨-183562946304,-183562946240⟩ : DyadicInterval 40),(⟨749074671820,749074691150⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨42992366,53778652⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42991488,42991552⟩ : DyadicInterval 40),(⟨-42993216,-42993152⟩ : DyadicInterval 40),(⟨762123382734,762123402063⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53777280,53777344⟩ : DyadicInterval 40),(⟨-53779968,-53779904⟩ : DyadicInterval 40),(⟨762123382265,762123401594⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2688,-1664⟩ : DyadicInterval 40),(⟨762123384448,762123404224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168976149069,169100644466⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157185475968,157185476032⟩ : DyadicInterval 40),(⟨-183465809280,-183465809216⟩ : DyadicInterval 40),(⟨749087409409,749087428738⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157293381952,157293382016⟩ : DyadicInterval 40),(⟨-183612921664,-183612921600⟩ : DyadicInterval 40),(⟨749068116573,749068135902⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26319539648,-26280333184⟩ : DyadicInterval 40),(⟨775263550208,775283172704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157231263808,157330026688⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183662888512,-183528229312⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1810_ok : ecellOkT e1810 = true := by decide +kernel
theorem e1810_pos {a z : ℝ} (ha1 : ((314841/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1260213/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1810 e1810_ok ha1 ha2 hz1 hz2 hz

-- box ['1260213/8192000', '630531/4096000', '1599/1600', '1999/2000']  interval_lower 150192939/1099511627776
noncomputable def e1811 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268654553432,0,true,157330026624,157330026688⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930368702120,0,false,-183662888512,-183662888448⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268768504284,0,true,157428780608,157428780672⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930254751268,0,false,-183797564096,-183797564032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268548839103,0,true,157238402816,157238402880⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930474416449,0,false,-183537962176,-183537962112⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268683875846,0,true,157355439360,157355439424⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930339379706,0,false,-183697542336,-183697542272⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554650139,0,true,43021504,43021568⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468605413,0,false,-43023232,-43023168⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565443928,0,true,53814784,53814848⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457811624,0,false,-53817472,-53817408⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625141,0,false,-2688,-2624⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626093,0,false,-1728,-1664⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268601692084,0,true,157284212032,157284212096⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930421563468,0,false,-183600418624,-183600418560⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268726194608,0,true,157392114496,157392114560⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930297060944,0,false,-183747557440,-183747557376⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073469547906,0,false,-26355442880,-26355442816⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073507855624,0,false,-26316206528,-26316206464⟩
    { al := (1260213/8192000), au := (630531/4096000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨169142925656,169256876508⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157330026624,157330026688⟩ : DyadicInterval 40),(⟨-183662888512,-183662888448⟩ : DyadicInterval 40),(⟨749061561043,749061580372⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157428780608,157428780672⟩ : DyadicInterval 40),(⟨-183797564096,-183797564032⟩ : DyadicInterval 40),(⟨749043885115,749043904445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157238402816,157238402880⟩ : DyadicInterval 40),(⟨-183537962176,-183537962112⟩ : DyadicInterval 40),(⟨749077948479,749077967808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157355439360,157355439424⟩ : DyadicInterval 40),(⟨-183697542336,-183697542272⟩ : DyadicInterval 40),(⟨749057013730,749057033059⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨43022363,53816152⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43021504,43021568⟩ : DyadicInterval 40),(⟨-43023232,-43023168⟩ : DyadicInterval 40),(⟨762123382732,762123402061⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53814784,53814848⟩ : DyadicInterval 40),(⟨-53817472,-53817408⟩ : DyadicInterval 40),(⟨762123382261,762123401591⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2688,-1664⟩ : DyadicInterval 40),(⟨762123384448,762123404224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169090064308,169214566832⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157284212032,157284212096⟩ : DyadicInterval 40),(⟨-183600418624,-183600418560⟩ : DyadicInterval 40),(⟨749069756719,749069776049⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157392114496,157392114560⟩ : DyadicInterval 40),(⟨-183747557440,-183747557376⟩ : DyadicInterval 40),(⟨749050449570,749050468899⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26355442880,-26316206464⟩ : DyadicInterval 40),(⟨775281486848,775301124320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157330026624,157428780672⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183797564096,-183662888448⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1811_ok : ecellOkT e1811 = true := by decide +kernel
theorem e1811_pos {a z : ℝ} (ha1 : ((1260213/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((630531/4096000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1811 e1811_ok ha1 ha2 hz1 hz2 hz

-- box ['630531/4096000', '1261911/8192000', '3997/4000', '1599/1600']  interval_lower 151370261/1099511627776
noncomputable def e1812 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268768504283,0,true,157428780608,157428780672⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930254751269,0,false,-183797564096,-183797564032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268882455135,0,true,157527525696,157527525760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930140800417,0,false,-183932256192,-183932256128⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268641561625,0,true,157318766912,157318766976⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930381693927,0,false,-183647534848,-183647534784⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268776598368,0,true,157435794880,157435794944⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930246657184,0,false,-183807130944,-183807130880⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565443175,0,true,53814080,53814144⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457812377,0,false,-53816768,-53816704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576251968,0,true,64622272,64622336⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447003584,0,false,-64626112,-64626048⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623977,0,false,-3840,-3776⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625143,0,false,-2688,-2624⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268705028897,0,true,157373771584,157373771648⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930318226655,0,false,-183722542144,-183722542080⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268829531396,0,true,157481665280,157481665344⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930193724156,0,false,-183869697280,-183869697216⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073437731182,0,false,-26388031936,-26388031872⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073476062295,0,false,-26348770496,-26348770432⟩
    { al := (630531/4096000), au := (1261911/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨169256876507,169370827359⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157428780608,157428780672⟩ : DyadicInterval 40),(⟨-183797564096,-183797564032⟩ : DyadicInterval 40),(⟨749043885116,749043904445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157527525696,157527525760⟩ : DyadicInterval 40),(⟨-183932256192,-183932256128⟩ : DyadicInterval 40),(⟨749026197113,749026216443⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157318766912,157318766976⟩ : DyadicInterval 40),(⟨-183647534848,-183647534784⟩ : DyadicInterval 40),(⟨749063575521,749063594851⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157435794880,157435794944⟩ : DyadicInterval 40),(⟨-183807130944,-183807130880⟩ : DyadicInterval 40),(⟨749042629135,749042648464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨53815399,64624192⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53814080,53814144⟩ : DyadicInterval 40),(⟨-53816768,-53816704⟩ : DyadicInterval 40),(⟨762123382261,762123401591⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64622272,64622336⟩ : DyadicInterval 40),(⟨-64626112,-64626048⟩ : DyadicInterval 40),(⟨762123381673,762123401002⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3840,-2624⟩ : DyadicInterval 40),(⟨762123384928,762123404800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169193401121,169317903620⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157373771584,157373771648⟩ : DyadicInterval 40),(⟨-183722542144,-183722542080⟩ : DyadicInterval 40),(⟨749053732856,749053752185⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157481665280,157481665344⟩ : DyadicInterval 40),(⟨-183869697280,-183869697216⟩ : DyadicInterval 40),(⟨749034413703,749034433032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26388031936,-26348770432⟩ : DyadicInterval 40),(⟨775297768832,775317418848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157428780608,157527525760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183932256192,-183797564032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1812_ok : ecellOkT e1812 = true := by decide +kernel
theorem e1812_pos {a z : ℝ} (ha1 : ((630531/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1261911/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1812 e1812_ok ha1 ha2 hz1 hz2 hz

-- box ['1261911/8192000', '31569/204800', '3997/4000', '1599/1600']  interval_lower 76200949/549755813888
noncomputable def e1813 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268882455134,0,true,157527525696,157527525760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930140800418,0,false,-183932256192,-183932256128⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268996405986,0,true,157626261888,157626261952⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930026849566,0,false,-184066964800,-184066964736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268755427013,0,true,157417447808,157417447872⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930267828539,0,false,-183782107584,-183782107520⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268890478000,0,true,157534477632,157534477696⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930132777552,0,false,-183941739968,-183941739904⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565480677,0,true,53851520,53851584⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457774875,0,false,-53854272,-53854208⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576296972,0,true,64667264,64667328⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446958580,0,false,-64671104,-64671040⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623972,0,false,-3840,-3776⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625139,0,false,-2688,-2624⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268818937012,0,true,157472484608,157472484672⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930204318540,0,false,-183857174528,-183857174464⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268943446638,0,true,157580374784,157580374848⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930079808914,0,false,-184004356096,-184004356032⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073402634912,0,false,-26423981312,-26423981248⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073440994018,0,false,-26384689856,-26384689792⟩
    { al := (1261911/8192000), au := (31569/204800), zl := (3997/4000), zu := (1599/1600),
      A := ⟨169370827358,169484778210⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157527525696,157527525760⟩ : DyadicInterval 40),(⟨-183932256192,-183932256128⟩ : DyadicInterval 40),(⟨749026197114,749026216443⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157626261888,157626261952⟩ : DyadicInterval 40),(⟨-184066964800,-184066964736⟩ : DyadicInterval 40),(⟨749008497035,749008516365⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157417447808,157417447872⟩ : DyadicInterval 40),(⟨-183782107584,-183782107520⟩ : DyadicInterval 40),(⟨749045914273,749045933603⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157534477632,157534477696⟩ : DyadicInterval 40),(⟨-183941739968,-183941739904⟩ : DyadicInterval 40),(⟨749024951305,749024970635⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨53852901,64669196⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53851520,53851584⟩ : DyadicInterval 40),(⟨-53854272,-53854208⟩ : DyadicInterval 40),(⟨762123382290,762123401619⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64667264,64667328⟩ : DyadicInterval 40),(⟨-64671104,-64671040⟩ : DyadicInterval 40),(⟨762123381668,762123400997⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3840,-2624⟩ : DyadicInterval 40),(⟨762123384928,762123404800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169307309236,169431818862⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157472484608,157472484672⟩ : DyadicInterval 40),(⟨-183857174528,-183857174464⟩ : DyadicInterval 40),(⟨749036058205,749036077535⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157580374784,157580374848⟩ : DyadicInterval 40),(⟨-184004356096,-184004356032⟩ : DyadicInterval 40),(⟨749016724733,749016744062⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26423981312,-26384689792⟩ : DyadicInterval 40),(⟨775315728512,775335393536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157527525696,157626261952⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184066964800,-183932256128⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1813_ok : ecellOkT e1813 = true := by decide +kernel
theorem e1813_pos {a z : ℝ} (ha1 : ((1261911/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((31569/204800 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1813 e1813_ok ha1 ha2 hz1 hz2 hz

-- box ['630531/4096000', '1261911/8192000', '1599/1600', '1999/2000']  interval_lower 75610883/549755813888
noncomputable def e1814 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268768504283,0,true,157428780608,157428780672⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930254751269,0,false,-183797564096,-183797564032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268882455135,0,true,157527525696,157527525760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930140800417,0,false,-183932256192,-183932256128⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268662718735,0,true,157337103296,157337103360⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930360536817,0,false,-183672538304,-183672538240⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268797769722,0,true,157454141632,157454141696⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930225485830,0,false,-183832154816,-183832154752⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554680139,0,true,43051520,43051584⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468575413,0,false,-43053248,-43053184⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565481430,0,true,53852288,53852352⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457774122,0,false,-53854976,-53854912⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625138,0,false,-2688,-2624⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626091,0,false,-1728,-1664⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268715607327,0,true,157382939264,157382939328⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930307648225,0,false,-183735044480,-183735044416⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268840116971,0,true,157490838208,157490838272⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930183138581,0,false,-183882209728,-183882209664⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073434470855,0,false,-26391371520,-26391371456⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073472806565,0,false,-26352105216,-26352105152⟩
    { al := (630531/4096000), au := (1261911/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨169256876507,169370827359⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157428780608,157428780672⟩ : DyadicInterval 40),(⟨-183797564096,-183797564032⟩ : DyadicInterval 40),(⟨749043885116,749043904445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157527525696,157527525760⟩ : DyadicInterval 40),(⟨-183932256192,-183932256128⟩ : DyadicInterval 40),(⟨749026197113,749026216443⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157337103296,157337103360⟩ : DyadicInterval 40),(⟨-183672538304,-183672538240⟩ : DyadicInterval 40),(⟨749060294829,749060314158⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157454141632,157454141696⟩ : DyadicInterval 40),(⟨-183832154816,-183832154752⟩ : DyadicInterval 40),(⟨749039343563,749039362892⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨43052363,53853654⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43051520,43051584⟩ : DyadicInterval 40),(⟨-43053248,-43053184⟩ : DyadicInterval 40),(⟨762123382730,762123402059⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53852288,53852352⟩ : DyadicInterval 40),(⟨-53854976,-53854912⟩ : DyadicInterval 40),(⟨762123382258,762123401587⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2688,-1664⟩ : DyadicInterval 40),(⟨762123384448,762123404224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169203979551,169328489195⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157382939264,157382939328⟩ : DyadicInterval 40),(⟨-183735044480,-183735044416⟩ : DyadicInterval 40),(⟨749052091935,749052111265⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157490838208,157490838272⟩ : DyadicInterval 40),(⟨-183882209728,-183882209664⟩ : DyadicInterval 40),(⟨749032770468,749032789798⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26391371520,-26352105152⟩ : DyadicInterval 40),(⟨775299436192,775319088640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157428780608,157527525760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183932256192,-183797564032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1814_ok : ecellOkT e1814 = true := by decide +kernel
theorem e1814_pos {a z : ℝ} (ha1 : ((630531/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1261911/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1814 e1814_ok ha1 ha2 hz1 hz2 hz

-- box ['1261911/8192000', '31569/204800', '1599/1600', '1999/2000']  interval_lower 152252941/1099511627776
noncomputable def e1815 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268882455134,0,true,157527525696,157527525760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930140800418,0,false,-183932256192,-183932256128⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268996405986,0,true,157626261888,157626261952⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930026849566,0,false,-184066964800,-184066964736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268776598366,0,true,157435794880,157435794944⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930246657186,0,false,-183807130944,-183807130880⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268911663598,0,true,157552835136,157552835200⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930111591954,0,false,-183966783808,-183966783744⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554710140,0,true,43081472,43081536⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468545412,0,false,-43083264,-43083200⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565518935,0,true,53889792,53889856⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457736617,0,false,-53892480,-53892416⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625134,0,false,-2688,-2624⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626088,0,false,-1728,-1664⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268829522563,0,true,157481657600,157481657664⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930193732989,0,false,-183869686848,-183869686784⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268954039335,0,true,157589553088,157589553152⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930069216217,0,false,-184016878528,-184016878464⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073399370197,0,false,-26427325440,-26427325376⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073437733903,0,false,-26388029184,-26388029120⟩
    { al := (1261911/8192000), au := (31569/204800), zl := (1599/1600), zu := (1999/2000),
      A := ⟨169370827358,169484778210⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157527525696,157527525760⟩ : DyadicInterval 40),(⟨-183932256192,-183932256128⟩ : DyadicInterval 40),(⟨749026197114,749026216443⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157626261888,157626261952⟩ : DyadicInterval 40),(⟨-184066964800,-184066964736⟩ : DyadicInterval 40),(⟨749008497035,749008516365⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157435794880,157435794944⟩ : DyadicInterval 40),(⟨-183807130944,-183807130880⟩ : DyadicInterval 40),(⟨749042629135,749042648465⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157552835136,157552835200⟩ : DyadicInterval 40),(⟨-183966783808,-183966783744⟩ : DyadicInterval 40),(⟨749021661271,749021680600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨43082364,53891159⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43081472,43081536⟩ : DyadicInterval 40),(⟨-43083264,-43083200⟩ : DyadicInterval 40),(⟨762123382759,762123402088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53889792,53889856⟩ : DyadicInterval 40),(⟨-53892480,-53892416⟩ : DyadicInterval 40),(⟨762123382254,762123401583⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2688,-1664⟩ : DyadicInterval 40),(⟨762123384448,762123404224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169317894787,169442411559⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157481657600,157481657664⟩ : DyadicInterval 40),(⟨-183869686848,-183869686784⟩ : DyadicInterval 40),(⟨749034415092,749034434422⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157589553088,157589553152⟩ : DyadicInterval 40),(⟨-184016878528,-184016878464⟩ : DyadicInterval 40),(⟨749015079266,749015098595⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26427325440,-26388029120⟩ : DyadicInterval 40),(⟨775317398176,775337065600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157527525696,157626261952⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184066964800,-183932256128⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1815_ok : ecellOkT e1815 = true := by decide +kernel
theorem e1815_pos {a z : ℝ} (ha1 : ((1261911/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((31569/204800 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1815 e1815_ok ha1 ha2 hz1 hz2 hz

-- box ['39249/256000', '1256817/8192000', '1999/2000', '7997/8000']  interval_lower 144942537/1099511627776
noncomputable def e1816 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268084799176,0,true,156836123776,156836123840⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930938456376,0,false,-182989757824,-182989757760⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268198750028,0,true,156934922112,156934922176⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930824505524,0,false,-183124351040,-183124350976⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268000512590,0,true,156763039424,156763039488⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931022742962,0,false,-182890213248,-182890213184⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268135492358,0,true,156880077120,156880077184⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930887763194,0,false,-183049632128,-183049632064⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543782080,0,true,32153792,32153856⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479473472,0,false,-32154816,-32154752⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554530865,0,true,42902208,42902272⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468724687,0,false,-42903936,-42903872⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626101,0,false,-1728,-1664⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626836,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268042651614,0,true,156799578496,156799578560⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930980603938,0,false,-182939979392,-182939979328⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268167125652,0,true,156907503808,156907503872⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930856129900,0,false,-183086996224,-183086996160⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073641344783,0,false,-26179492352,-26179492288⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073679517157,0,false,-26140400896,-26140400832⟩
    { al := (39249/256000), au := (1256817/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨168573171400,168687122252⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156836123776,156836123840⟩ : DyadicInterval 40),(⟨-182989757824,-182989757760⟩ : DyadicInterval 40),(⟨749149759116,749149778446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156934922112,156934922176⟩ : DyadicInterval 40),(⟨-183124351040,-183124350976⟩ : DyadicInterval 40),(⟨749132143700,749132163029⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156763039424,156763039488⟩ : DyadicInterval 40),(⟨-182890213248,-182890213184⟩ : DyadicInterval 40),(⟨749162781032,749162800361⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156880077120,156880077184⟩ : DyadicInterval 40),(⟨-183049632128,-183049632064⟩ : DyadicInterval 40),(⟨749141924095,749141943425⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32154304,42903089⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32153792,32153856⟩ : DyadicInterval 40),(⟨-32154816,-32154752⟩ : DyadicInterval 40),(⟨762123383123,762123402452⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42902208,42902272⟩ : DyadicInterval 40),(⟨-42903936,-42903872⟩ : DyadicInterval 40),(⟨762123382741,762123402070⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1728,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168531023838,168655497876⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156799578496,156799578560⟩ : DyadicInterval 40),(⟨-182939979392,-182939979328⟩ : DyadicInterval 40),(⟨749156271577,749156290906⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156907503808,156907503872⟩ : DyadicInterval 40),(⟨-183086996224,-183086996160⟩ : DyadicInterval 40),(⟨749137033686,749137053016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26179492352,-26140400832⟩ : DyadicInterval 40),(⟨775193584032,775213149056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156836123776,156934922176⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183124351040,-182989757760⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1816_ok : ecellOkT e1816 = true := by decide +kernel
theorem e1816_pos {a z : ℝ} (ha1 : ((39249/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1256817/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1816 e1816_ok ha1 ha2 hz1 hz2 hz

-- box ['1256817/8192000', '628833/4096000', '1999/2000', '7997/8000']  interval_lower 145957661/1099511627776
noncomputable def e1817 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268198750027,0,true,156934922112,156934922176⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930824505525,0,false,-183124351040,-183124350976⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268312700879,0,true,157033711552,157033711616⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930710554673,0,false,-183258960640,-183258960576⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268114406465,0,true,156861794880,156861794944⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930908849087,0,false,-183024726976,-183024726912⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268249400477,0,true,156978834496,156978834560⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930773855075,0,false,-183184182144,-183184182080⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543804572,0,true,32176320,32176384⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479450980,0,false,-32177280,-32177216⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554560857,0,true,42932224,42932288⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468694695,0,false,-42933952,-42933888⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626099,0,false,-1728,-1664⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626835,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268156573969,0,true,156898355392,156898355456⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930866681583,0,false,-183074532800,-183074532736⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268281055142,0,true,157006277248,157006277312⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930742200410,0,false,-183221576064,-183221576000⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073606381397,0,false,-26215298816,-26215298752⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073644581755,0,false,-26176177408,-26176177344⟩
    { al := (1256817/8192000), au := (628833/4096000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨168687122251,168801073103⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156934922112,156934922176⟩ : DyadicInterval 40),(⟨-183124351040,-183124350976⟩ : DyadicInterval 40),(⟨749132143700,749132163030⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157033711552,157033711616⟩ : DyadicInterval 40),(⟨-183258960640,-183258960576⟩ : DyadicInterval 40),(⟨749114516160,749114535489⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156861794880,156861794944⟩ : DyadicInterval 40),(⟨-183024726976,-183024726912⟩ : DyadicInterval 40),(⟨749145183391,749145202721⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156978834496,156978834560⟩ : DyadicInterval 40),(⟨-183184182144,-183184182080⟩ : DyadicInterval 40),(⟨749124309866,749124329196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32176796,42933081⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32176320,32176384⟩ : DyadicInterval 40),(⟨-32177280,-32177216⟩ : DyadicInterval 40),(⟨762123383090,762123402419⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42932224,42932288⟩ : DyadicInterval 40),(⟨-42933952,-42933888⟩ : DyadicInterval 40),(⟨762123382739,762123402068⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1728,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168644946193,168769427366⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156898355392,156898355456⟩ : DyadicInterval 40),(⟨-183074532800,-183074532736⟩ : DyadicInterval 40),(⟨749138665025,749138684355⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157006277248,157006277312⟩ : DyadicInterval 40),(⟨-183221576064,-183221576000⟩ : DyadicInterval 40),(⟨749119412797,749119432126⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26215298816,-26176177344⟩ : DyadicInterval 40),(⟨775211472288,775231052288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156934922112,157033711616⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183258960640,-183124350976⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1817_ok : ecellOkT e1817 = true := by decide +kernel
theorem e1817_pos {a z : ℝ} (ha1 : ((1256817/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((628833/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1817 e1817_ok ha1 ha2 hz1 hz2 hz

-- box ['39249/256000', '1256817/8192000', '7997/8000', '3999/4000']  interval_lower 4524871/34359738368
noncomputable def e1818 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268084799176,0,true,156836123776,156836123840⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930938456376,0,false,-182989757824,-182989757760⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268198750028,0,true,156934922112,156934922176⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930824505524,0,false,-183124351040,-183124350976⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268021584236,0,true,156781310912,156781310976⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨931001671316,0,false,-182915098560,-182915098496⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268156578248,0,true,156898359104,156898359168⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930866677304,0,false,-183074537856,-183074537792⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533063940,0,true,21435904,21435968⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490191612,0,false,-21436416,-21436352⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543805227,0,true,32176960,32177024⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479450325,0,false,-32177984,-32177920⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626834,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627359,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268053187354,0,true,156808713920,156808713984⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930970068198,0,false,-182952422464,-182952422400⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268177668543,0,true,156916644544,156916644608⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930845587009,0,false,-183099449344,-183099449280⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073638110307,0,false,-26182804800,-26182804736⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073676287260,0,false,-26143708480,-26143708416⟩
    { al := (39249/256000), au := (1256817/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨168573171400,168687122252⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156836123776,156836123840⟩ : DyadicInterval 40),(⟨-182989757824,-182989757760⟩ : DyadicInterval 40),(⟨749149759116,749149778446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156934922112,156934922176⟩ : DyadicInterval 40),(⟨-183124351040,-183124350976⟩ : DyadicInterval 40),(⟨749132143700,749132163029⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156781310912,156781310976⟩ : DyadicInterval 40),(⟨-182915098560,-182915098496⟩ : DyadicInterval 40),(⟨749159526211,749159545541⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156898359104,156898359168⟩ : DyadicInterval 40),(⟨-183074537856,-183074537792⟩ : DyadicInterval 40),(⟨749138664363,749138683693⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21436164,32177451⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21435904,21435968⟩ : DyadicInterval 40),(⟨-21436416,-21436352⟩ : DyadicInterval 40),(⟨762123383390,762123402719⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32176960,32177024⟩ : DyadicInterval 40),(⟨-32177984,-32177920⟩ : DyadicInterval 40),(⟨762123383122,762123402451⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168541559578,168666040767⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156808713920,156808713984⟩ : DyadicInterval 40),(⟨-182952422464,-182952422400⟩ : DyadicInterval 40),(⟨749154643816,749154663145⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156916644544,156916644608⟩ : DyadicInterval 40),(⟨-183099449344,-183099449280⟩ : DyadicInterval 40),(⟨749135403567,749135422897⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26182804800,-26143708416⟩ : DyadicInterval 40),(⟨775195237824,775214805280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156836123776,156934922176⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183124351040,-182989757760⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1818_ok : ecellOkT e1818 = true := by decide +kernel
theorem e1818_pos {a z : ℝ} (ha1 : ((39249/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1256817/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1818 e1818_ok ha1 ha2 hz1 hz2 hz

-- box ['1256817/8192000', '628833/4096000', '7997/8000', '3999/4000']  interval_lower 145810901/1099511627776
noncomputable def e1819 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268198750027,0,true,156934922112,156934922176⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930824505525,0,false,-183124351040,-183124350976⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268312700879,0,true,157033711552,157033711616⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930710554673,0,false,-183258960640,-183258960576⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268135492356,0,true,156880077120,156880077184⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930887763196,0,false,-183049632128,-183049632064⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268270500611,0,true,156997127104,156997127168⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930752754941,0,false,-183209107776,-183209107712⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533078934,0,true,21450944,21451008⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490176618,0,false,-21451392,-21451328⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543827721,0,true,32199424,32199488⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479427831,0,false,-32200448,-32200384⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626833,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627358,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268167116834,0,true,156907496192,156907496256⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930856138718,0,false,-183086985792,-183086985728⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268291605148,0,true,157015423296,157015423360⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930731650404,0,false,-183234039104,-183234039040⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073603142552,0,false,-26218615808,-26218615744⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073641347489,0,false,-26179489600,-26179489536⟩
    { al := (1256817/8192000), au := (628833/4096000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨168687122251,168801073103⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156934922112,156934922176⟩ : DyadicInterval 40),(⟨-183124351040,-183124350976⟩ : DyadicInterval 40),(⟨749132143700,749132163030⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157033711552,157033711616⟩ : DyadicInterval 40),(⟨-183258960640,-183258960576⟩ : DyadicInterval 40),(⟨749114516160,749114535489⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156880077120,156880077184⟩ : DyadicInterval 40),(⟨-183049632128,-183049632064⟩ : DyadicInterval 40),(⟨749141924096,749141943425⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156997127104,156997127168⟩ : DyadicInterval 40),(⟨-183209107776,-183209107712⟩ : DyadicInterval 40),(⟨749121045754,749121065083⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21451158,32199945⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21450944,21451008⟩ : DyadicInterval 40),(⟨-21451392,-21451328⟩ : DyadicInterval 40),(⟨762123383357,762123402686⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32199424,32199488⟩ : DyadicInterval 40),(⟨-32200448,-32200384⟩ : DyadicInterval 40),(⟨762123383120,762123402450⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168655489058,168779977372⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156907496192,156907496256⟩ : DyadicInterval 40),(⟨-183086985792,-183086985728⟩ : DyadicInterval 40),(⟨749137035026,749137054356⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157015423296,157015423360⟩ : DyadicInterval 40),(⟨-183234039104,-183234039040⟩ : DyadicInterval 40),(⟨749117780474,749117799803⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26218615808,-26179489536⟩ : DyadicInterval 40),(⟨775213128384,775232710784⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156934922112,157033711616⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183258960640,-183124350976⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1819_ok : ecellOkT e1819 = true := by decide +kernel
theorem e1819_pos {a z : ℝ} (ha1 : ((1256817/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((628833/4096000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1819 e1819_ok ha1 ha2 hz1 hz2 hz

-- box ['628833/4096000', '251703/1638400', '1999/2000', '7997/8000']  interval_lower 146975765/1099511627776
noncomputable def e1820 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268312700878,0,true,157033711552,157033711616⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930710554674,0,false,-183258960640,-183258960576⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268426651730,0,true,157132492096,157132492160⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930596603822,0,false,-183393586816,-183393586752⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268228300341,0,true,156960541504,156960541568⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930794955211,0,false,-183159257088,-183159257024⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268363308597,0,true,157077582912,157077582976⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930659946955,0,false,-183318748608,-183318748544⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543827065,0,true,32198784,32198848⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479428487,0,false,-32199808,-32199744⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554590849,0,true,42962176,42962240⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468664703,0,false,-42963968,-42963904⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626097,0,false,-1728,-1664⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626834,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268270496332,0,true,156997123456,156997123520⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930752759220,0,false,-183209102720,-183209102656⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268394984622,0,true,157105041728,157105041792⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930628270930,0,false,-183356172352,-183356172288⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073571394404,0,false,-26251130560,-26251130496⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073609622744,0,false,-26211979264,-26211979200⟩
    { al := (628833/4096000), au := (251703/1638400), zl := (1999/2000), zu := (7997/8000),
      A := ⟨168801073102,168915023954⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157033711552,157033711616⟩ : DyadicInterval 40),(⟨-183258960640,-183258960576⟩ : DyadicInterval 40),(⟨749114516160,749114535490⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157132492096,157132492160⟩ : DyadicInterval 40),(⟨-183393586816,-183393586752⟩ : DyadicInterval 40),(⟨749096876577,749096895907⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156960541504,156960541568⟩ : DyadicInterval 40),(⟨-183159257088,-183159257024⟩ : DyadicInterval 40),(⟨749127573615,749127592945⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157077582912,157077582976⟩ : DyadicInterval 40),(⟨-183318748608,-183318748544⟩ : DyadicInterval 40),(⟨749106683595,749106702925⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32199289,42963073⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32198784,32198848⟩ : DyadicInterval 40),(⟨-32199808,-32199744⟩ : DyadicInterval 40),(⟨762123383121,762123402450⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42962176,42962240⟩ : DyadicInterval 40),(⟨-42963968,-42963904⟩ : DyadicInterval 40),(⟨762123382769,762123402098⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1728,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168758868556,168883356846⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156997123456,156997123520⟩ : DyadicInterval 40),(⟨-183209102720,-183209102656⟩ : DyadicInterval 40),(⟨749121046380,749121065709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157105041728,157105041792⟩ : DyadicInterval 40),(⟨-183356172352,-183356172288⟩ : DyadicInterval 40),(⟨749101779858,749101799187⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26251130560,-26211979200⟩ : DyadicInterval 40),(⟨775229373216,775248968160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157033711552,157132492160⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183393586816,-183258960576⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1820_ok : ecellOkT e1820 = true := by decide +kernel
theorem e1820_pos {a z : ℝ} (ha1 : ((628833/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((251703/1638400 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1820 e1820_ok ha1 ha2 hz1 hz2 hz

-- box ['251703/1638400', '314841/2048000', '1999/2000', '7997/8000']  interval_lower 73997983/549755813888
noncomputable def e1821 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268426651729,0,true,157132492096,157132492160⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930596603823,0,false,-183393586816,-183393586752⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268540602581,0,true,157231263808,157231263872⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930482652971,0,false,-183528229376,-183528229312⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268342194217,0,true,157059279296,157059279360⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930681061335,0,false,-183293803712,-183293803648⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268477216716,0,true,157176322560,157176322624⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930546038836,0,false,-183453331584,-183453331520⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543849559,0,true,32221248,32221312⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479405993,0,false,-32222272,-32222208⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554620845,0,true,42992192,42992256⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468634707,0,false,-42993920,-42993856⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626094,0,false,-1728,-1664⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626832,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268384418691,0,true,157095882560,157095882624⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930638836861,0,false,-183343689024,-183343688960⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268508914113,0,true,157203797376,157203797440⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930514341439,0,false,-183490785152,-183490785088⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073536383796,0,false,-26286987712,-26286987648⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073574640126,0,false,-26247806464,-26247806400⟩
    { al := (251703/1638400), au := (314841/2048000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨168915023953,169028974805⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157132492096,157132492160⟩ : DyadicInterval 40),(⟨-183393586816,-183393586752⟩ : DyadicInterval 40),(⟨749096876578,749096895907⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157231263808,157231263872⟩ : DyadicInterval 40),(⟨-183528229376,-183528229312⟩ : DyadicInterval 40),(⟨749079224833,749079244162⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157059279296,157059279360⟩ : DyadicInterval 40),(⟨-183293803712,-183293803648⟩ : DyadicInterval 40),(⟨749109951757,749109971087⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157176322560,157176322624⟩ : DyadicInterval 40),(⟨-183453331584,-183453331520⟩ : DyadicInterval 40),(⟨749089045199,749089064529⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32221783,42993069⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32221248,32221312⟩ : DyadicInterval 40),(⟨-32222272,-32222208⟩ : DyadicInterval 40),(⟨762123383119,762123402448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42992192,42992256⟩ : DyadicInterval 40),(⟨-42993920,-42993856⟩ : DyadicInterval 40),(⟨762123382734,762123402063⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1728,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168872790915,168997286337⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157095882560,157095882624⟩ : DyadicInterval 40),(⟨-183343689024,-183343688960⟩ : DyadicInterval 40),(⟨749103415659,749103434989⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157203797376,157203797440⟩ : DyadicInterval 40),(⟨-183490785152,-183490785088⟩ : DyadicInterval 40),(⟨749084134819,749084154148⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26286987712,-26247806400⟩ : DyadicInterval 40),(⟨775247286816,775266896736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157132492096,157231263872⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183528229376,-183393586752⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1821_ok : ecellOkT e1821 = true := by decide +kernel
theorem e1821_pos {a z : ℝ} (ha1 : ((251703/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((314841/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1821 e1821_ok ha1 ha2 hz1 hz2 hz

-- box ['628833/4096000', '251703/1638400', '7997/8000', '3999/4000']  interval_lower 146828335/1099511627776
noncomputable def e1822 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268312700878,0,true,157033711552,157033711616⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930710554674,0,false,-183258960640,-183258960576⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268426651730,0,true,157132492096,157132492160⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930596603822,0,false,-183393586816,-183393586752⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268249400475,0,true,156978834496,156978834560⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930773855077,0,false,-183184182144,-183184182080⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268384422975,0,true,157095886272,157095886336⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930638832577,0,false,-183343694144,-183343694080⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533093930,0,true,21465920,21465984⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490161622,0,false,-21466368,-21466304⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543850216,0,true,32221952,32222016⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479405336,0,false,-32222976,-32222912⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626831,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627357,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268281046322,0,true,157006269568,157006269632⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930742209230,0,false,-183221565632,-183221565568⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268405541752,0,true,157114193152,157114193216⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930617713800,0,false,-183368645376,-183368645312⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073568151183,0,false,-26254452160,-26254452096⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073606384106,0,false,-26215296000,-26215295936⟩
    { al := (628833/4096000), au := (251703/1638400), zl := (7997/8000), zu := (3999/4000),
      A := ⟨168801073102,168915023954⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157033711552,157033711616⟩ : DyadicInterval 40),(⟨-183258960640,-183258960576⟩ : DyadicInterval 40),(⟨749114516160,749114535490⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157132492096,157132492160⟩ : DyadicInterval 40),(⟨-183393586816,-183393586752⟩ : DyadicInterval 40),(⟨749096876577,749096895907⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156978834496,156978834560⟩ : DyadicInterval 40),(⟨-183184182144,-183184182080⟩ : DyadicInterval 40),(⟨749124309867,749124329196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157095886272,157095886336⟩ : DyadicInterval 40),(⟨-183343694144,-183343694080⟩ : DyadicInterval 40),(⟨749103415022,749103434352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21466154,32222440⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21465920,21465984⟩ : DyadicInterval 40),(⟨-21466368,-21466304⟩ : DyadicInterval 40),(⟨762123383356,762123402685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32221952,32222016⟩ : DyadicInterval 40),(⟨-32222976,-32222912⟩ : DyadicInterval 40),(⟨762123383119,762123402448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168769418546,168893913976⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157006269568,157006269632⟩ : DyadicInterval 40),(⟨-183221565632,-183221565568⟩ : DyadicInterval 40),(⟨749119414176,749119433505⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157114193152,157114193216⟩ : DyadicInterval 40),(⟨-183368645376,-183368645312⟩ : DyadicInterval 40),(⟨749100145317,749100164646⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26254452160,-26215295936⟩ : DyadicInterval 40),(⟨775231031584,775250628960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157033711552,157132492160⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183393586816,-183258960576⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1822_ok : ecellOkT e1822 = true := by decide +kernel
theorem e1822_pos {a z : ℝ} (ha1 : ((628833/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((251703/1638400 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1822 e1822_ok ha1 ha2 hz1 hz2 hz

-- box ['251703/1638400', '314841/2048000', '7997/8000', '3999/4000']  interval_lower 147848467/1099511627776
noncomputable def e1823 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268426651729,0,true,157132492096,157132492160⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930596603823,0,false,-183393586816,-183393586752⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268540602581,0,true,157231263808,157231263872⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930482652971,0,false,-183528229376,-183528229312⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268363308594,0,true,157077582912,157077582976⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930659946958,0,false,-183318748608,-183318748544⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268498345338,0,true,157194636608,157194636672⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930524910214,0,false,-183478296960,-183478296896⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533108926,0,true,21480896,21480960⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490146626,0,false,-21481408,-21481344⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543872713,0,true,32244416,32244480⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479382839,0,false,-32245440,-32245376⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626830,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627357,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268394975799,0,true,157105034112,157105034176⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930628279753,0,false,-183356161920,-183356161856⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268519478366,0,true,157212954176,157212954240⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930503777186,0,false,-183503268096,-183503268032⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073533136198,0,false,-26290313920,-26290313856⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073571397115,0,false,-26251127808,-26251127744⟩
    { al := (251703/1638400), au := (314841/2048000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨168915023953,169028974805⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157132492096,157132492160⟩ : DyadicInterval 40),(⟨-183393586816,-183393586752⟩ : DyadicInterval 40),(⟨749096876578,749096895907⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157231263808,157231263872⟩ : DyadicInterval 40),(⟨-183528229376,-183528229312⟩ : DyadicInterval 40),(⟨749079224833,749079244162⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157077582912,157077582976⟩ : DyadicInterval 40),(⟨-183318748608,-183318748544⟩ : DyadicInterval 40),(⟨749106683596,749106702925⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157194636608,157194636672⟩ : DyadicInterval 40),(⟨-183478296960,-183478296896⟩ : DyadicInterval 40),(⟨749085772168,749085791498⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21481150,32244937⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21480896,21480960⟩ : DyadicInterval 40),(⟨-21481408,-21481344⟩ : DyadicInterval 40),(⟨762123383388,762123402717⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32244416,32244480⟩ : DyadicInterval 40),(⟨-32245440,-32245376⟩ : DyadicInterval 40),(⟨762123383118,762123402447⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168883348023,169007850590⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157105034112,157105034176⟩ : DyadicInterval 40),(⟨-183356161920,-183356161856⟩ : DyadicInterval 40),(⟨749101781202,749101800531⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157212954176,157212954240⟩ : DyadicInterval 40),(⟨-183503268096,-183503268032⟩ : DyadicInterval 40),(⟨749082498030,749082517359⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26290313920,-26251127744⟩ : DyadicInterval 40),(⟨775248947488,775268559840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157132492096,157231263872⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183528229376,-183393586752⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1823_ok : ecellOkT e1823 = true := by decide +kernel
theorem e1823_pos {a z : ℝ} (ha1 : ((251703/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((314841/2048000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1823 e1823_ok ha1 ha2 hz1 hz2 hz

-- box ['39249/256000', '1256817/8192000', '3999/4000', '7999/8000']  interval_lower 72324591/549755813888
noncomputable def e1824 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268084799176,0,true,156836123776,156836123840⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930938456376,0,false,-182989757824,-182989757760⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268198750028,0,true,156934922112,156934922176⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930824505524,0,false,-183124351040,-183124350976⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268042655883,0,true,156799582208,156799582272⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930980599669,0,false,-182939984448,-182939984384⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268177664138,0,true,156916640768,156916640832⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930845591414,0,false,-183099444160,-183099444096⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522345753,0,true,10717888,10717952⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500909799,0,false,-10718080,-10718016⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533079543,0,true,21451520,21451584⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490176009,0,false,-21452032,-21451968⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627357,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627672,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268063723123,0,true,156817849280,156817849344⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930959532429,0,false,-182964865664,-182964865600⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268188211455,0,true,156925785216,156925785280⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930835044097,0,false,-183111902656,-183111902592⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073634875622,0,false,-26186117440,-26186117376⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073673057153,0,false,-26147016320,-26147016256⟩
    { al := (39249/256000), au := (1256817/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨168573171400,168687122252⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156836123776,156836123840⟩ : DyadicInterval 40),(⟨-182989757824,-182989757760⟩ : DyadicInterval 40),(⟨749149759116,749149778446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156934922112,156934922176⟩ : DyadicInterval 40),(⟨-183124351040,-183124350976⟩ : DyadicInterval 40),(⟨749132143700,749132163029⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156799582208,156799582272⟩ : DyadicInterval 40),(⟨-182939984448,-182939984384⟩ : DyadicInterval 40),(⟨749156270917,749156290247⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156916640768,156916640832⟩ : DyadicInterval 40),(⟨-183099444160,-183099444096⟩ : DyadicInterval 40),(⟨749135404231,749135423561⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10717977,21451767⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10717888,10717952⟩ : DyadicInterval 40),(⟨-10718080,-10718016⟩ : DyadicInterval 40),(⟨762123383543,762123402872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21451520,21451584⟩ : DyadicInterval 40),(⟨-21452032,-21451968⟩ : DyadicInterval 40),(⟨762123383389,762123402718⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168552095347,168676583679⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156817849280,156817849344⟩ : DyadicInterval 40),(⟨-182964865664,-182964865600⟩ : DyadicInterval 40),(⟨749153015935,749153035265⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156925785216,156925785280⟩ : DyadicInterval 40),(⟨-183111902656,-183111902592⟩ : DyadicInterval 40),(⟨749133773356,749133792685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26186117440,-26147016256⟩ : DyadicInterval 40),(⟨775196891744,775216461600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156836123776,156934922176⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183124351040,-182989757760⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1824_ok : ecellOkT e1824 = true := by decide +kernel
theorem e1824_pos {a z : ℝ} (ha1 : ((39249/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1256817/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1824 e1824_ok ha1 ha2 hz1 hz2 hz

-- box ['1256817/8192000', '628833/4096000', '3999/4000', '7999/8000']  interval_lower 36415945/274877906944
noncomputable def e1825 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268198750027,0,true,156934922112,156934922176⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930824505525,0,false,-183124351040,-183124350976⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268312700879,0,true,157033711552,157033711616⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930710554673,0,false,-183258960640,-183258960576⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268156578246,0,true,156898359104,156898359168⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930866677306,0,false,-183074537856,-183074537792⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268291600745,0,true,157015419456,157015419520⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930731654807,0,false,-183234033920,-183234033856⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522353250,0,true,10725376,10725440⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500902302,0,false,-10725568,-10725504⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533094539,0,true,21466496,21466560⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490161013,0,false,-21467008,-21466944⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627356,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627672,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268177659726,0,true,156916636928,156916636992⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930845595826,0,false,-183099438976,-183099438912⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268302155183,0,true,157024569344,157024569408⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930721100369,0,false,-183246502400,-183246502336⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073599903495,0,false,-26221932992,-26221932928⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073638113013,0,false,-26182801984,-26182801920⟩
    { al := (1256817/8192000), au := (628833/4096000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨168687122251,168801073103⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156934922112,156934922176⟩ : DyadicInterval 40),(⟨-183124351040,-183124350976⟩ : DyadicInterval 40),(⟨749132143700,749132163030⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157033711552,157033711616⟩ : DyadicInterval 40),(⟨-183258960640,-183258960576⟩ : DyadicInterval 40),(⟨749114516160,749114535489⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156898359104,156898359168⟩ : DyadicInterval 40),(⟨-183074537856,-183074537792⟩ : DyadicInterval 40),(⟨749138664363,749138683693⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157015419456,157015419520⟩ : DyadicInterval 40),(⟨-183234033920,-183234033856⟩ : DyadicInterval 40),(⟨749117781176,749117800505⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10725474,21466763⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10725376,10725440⟩ : DyadicInterval 40),(⟨-10725568,-10725504⟩ : DyadicInterval 40),(⟨762123383543,762123402872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21466496,21466560⟩ : DyadicInterval 40),(⟨-21467008,-21466944⟩ : DyadicInterval 40),(⟨762123383388,762123402717⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168666031950,168790527407⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156916636928,156916636992⟩ : DyadicInterval 40),(⟨-183099438976,-183099438912⟩ : DyadicInterval 40),(⟨749135404934,749135424264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157024569344,157024569408⟩ : DyadicInterval 40),(⟨-183246502400,-183246502336⟩ : DyadicInterval 40),(⟨749116148048,749116167377⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26221932992,-26182801920⟩ : DyadicInterval 40),(⟨775214784576,775234369376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨156934922112,157033711616⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183258960640,-183124350976⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1825_ok : ecellOkT e1825 = true := by decide +kernel
theorem e1825_pos {a z : ℝ} (ha1 : ((1256817/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((628833/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1825 e1825_ok ha1 ha2 hz1 hz2 hz

-- box ['39249/256000', '1256817/8192000', '7999/8000', '1']  interval_lower 35279/268435456
noncomputable def e1826 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268084799176,0,true,156836123776,156836123840⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930938456376,0,false,-182989757824,-182989757760⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268198750028,0,true,156934922112,156934922176⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930824505524,0,false,-183124351040,-183124350976⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268063727529,0,true,156817853120,156817853184⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930959528023,0,false,-182964870848,-182964870784⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522353811,0,true,10725952,10726016⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500901741,0,false,-10726144,-10726080⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627671,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1268074258912,0,true,156826984640,156826984704⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨930948996640,0,false,-182977309056,-182977308992⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1268198754388,0,true,156934925888,156934925952⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨930824501164,0,false,-183124356160,-183124356096⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1073631640729,0,false,-26189430272,-26189430208⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1073669826837,0,false,-26150324416,-26150324352⟩
    { al := (39249/256000), au := (1256817/8192000), zl := (7999/8000), zu := 1,
      A := ⟨168573171400,168687122252⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156836123776,156836123840⟩ : DyadicInterval 40),(⟨-182989757824,-182989757760⟩ : DyadicInterval 40),(⟨749149759116,749149778446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156934922112,156934922176⟩ : DyadicInterval 40),(⟨-183124351040,-183124350976⟩ : DyadicInterval 40),(⟨749132143700,749132163029⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156817853120,156817853184⟩ : DyadicInterval 40),(⟨-182964870848,-182964870784⟩ : DyadicInterval 40),(⟨749153015235,749153034564⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156934922112,156934922176⟩ : DyadicInterval 40),(⟨-183124351040,-183124350976⟩ : DyadicInterval 40),(⟨749132143700,749132163029⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10726035⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10725952,10726016⟩ : DyadicInterval 40),(⟨-10726144,-10726080⟩ : DyadicInterval 40),(⟨762123383543,762123402872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨168562631136,168687126612⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156826984640,156826984704⟩ : DyadicInterval 40),(⟨-182977309056,-182977308992⟩ : DyadicInterval 40),(⟨749151387926,749151407255⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156934925888,156934925952⟩ : DyadicInterval 40),(⟨-183124356160,-183124356096⟩ : DyadicInterval 40),(⟨749132143015,749132162345⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26189430272,-26150324352⟩ : DyadicInterval 40),(⟨775198545792,775218118016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨156836123776,156934922176⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183124351040,-182989757760⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1826_ok : ecellOkT e1826 = true := by decide +kernel
theorem e1826_pos {a z : ℝ} (ha1 : ((39249/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1256817/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1826 e1826_ok ha1 ha2 hz1 hz2 hz

-- box ['1256817/8192000', '628833/4096000', '7999/8000', '1']  interval_lower 72758385/549755813888
noncomputable def e1827 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268198750027,0,true,156934922112,156934922176⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930824505525,0,false,-183124351040,-183124350976⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268312700879,0,true,157033711552,157033711616⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930710554673,0,false,-183258960640,-183258960576⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268177664136,0,true,156916640768,156916640832⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930845591416,0,false,-183099444160,-183099444096⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522361310,0,true,10733440,10733504⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500894242,0,false,-10733632,-10733568⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627671,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1268188202638,0,true,156925777600,156925777664⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨930835052914,0,false,-183111892288,-183111892224⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1268312705243,0,true,157033715328,157033715392⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨930710550309,0,false,-183258965824,-183258965760⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1073596664228,0,false,-26225250496,-26225250432⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1073634878328,0,false,-26186114624,-26186114560⟩
    { al := (1256817/8192000), au := (628833/4096000), zl := (7999/8000), zu := 1,
      A := ⟨168687122251,168801073103⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156934922112,156934922176⟩ : DyadicInterval 40),(⟨-183124351040,-183124350976⟩ : DyadicInterval 40),(⟨749132143700,749132163030⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157033711552,157033711616⟩ : DyadicInterval 40),(⟨-183258960640,-183258960576⟩ : DyadicInterval 40),(⟨749114516160,749114535489⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156916640768,156916640832⟩ : DyadicInterval 40),(⟨-183099444160,-183099444096⟩ : DyadicInterval 40),(⟨749135404232,749135423561⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157033711552,157033711616⟩ : DyadicInterval 40),(⟨-183258960640,-183258960576⟩ : DyadicInterval 40),(⟨749114516160,749114535489⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10733534⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10733440,10733504⟩ : DyadicInterval 40),(⟨-10733632,-10733568⟩ : DyadicInterval 40),(⟨762123383543,762123402872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨168676574862,168801077467⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156925777600,156925777664⟩ : DyadicInterval 40),(⟨-183111892288,-183111892224⟩ : DyadicInterval 40),(⟨749133774722,749133794052⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157033715328,157033715392⟩ : DyadicInterval 40),(⟨-183258965824,-183258965760⟩ : DyadicInterval 40),(⟨749114515501,749114534830⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26225250496,-26186114560⟩ : DyadicInterval 40),(⟨775216440896,775236028128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨156934922112,157033711616⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183258960640,-183124350976⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1827_ok : ecellOkT e1827 = true := by decide +kernel
theorem e1827_pos {a z : ℝ} (ha1 : ((1256817/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((628833/4096000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1827 e1827_ok ha1 ha2 hz1 hz2 hz

-- box ['628833/4096000', '251703/1638400', '3999/4000', '7999/8000']  interval_lower 73340393/549755813888
noncomputable def e1828 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268312700878,0,true,157033711552,157033711616⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930710554674,0,false,-183258960640,-183258960576⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268426651730,0,true,157132492096,157132492160⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930596603822,0,false,-183393586816,-183393586752⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268270500609,0,true,156997127104,156997127168⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930752754943,0,false,-183209107776,-183209107712⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268405537353,0,true,157114189376,157114189440⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930617718199,0,false,-183368640192,-183368640128⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522360748,0,true,10732864,10732928⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500894804,0,false,-10733056,-10732992⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533109535,0,true,21481536,21481600⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490146017,0,false,-21481984,-21481920⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627356,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627672,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268291596328,0,true,157015415680,157015415744⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930731659224,0,false,-183234028736,-183234028672⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268416098911,0,true,157123344576,157123344640⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930607156641,0,false,-183381118592,-183381118528⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073564907751,0,false,-26257773952,-26257773888⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073603145260,0,false,-26218612992,-26218612928⟩
    { al := (628833/4096000), au := (251703/1638400), zl := (3999/4000), zu := (7999/8000),
      A := ⟨168801073102,168915023954⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157033711552,157033711616⟩ : DyadicInterval 40),(⟨-183258960640,-183258960576⟩ : DyadicInterval 40),(⟨749114516160,749114535490⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157132492096,157132492160⟩ : DyadicInterval 40),(⟨-183393586816,-183393586752⟩ : DyadicInterval 40),(⟨749096876577,749096895907⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156997127104,156997127168⟩ : DyadicInterval 40),(⟨-183209107776,-183209107712⟩ : DyadicInterval 40),(⟨749121045754,749121065083⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157114189376,157114189440⟩ : DyadicInterval 40),(⟨-183368640192,-183368640128⟩ : DyadicInterval 40),(⟨749100145982,749100165312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10732972,21481759⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10732864,10732928⟩ : DyadicInterval 40),(⟨-10733056,-10732992⟩ : DyadicInterval 40),(⟨762123383543,762123402872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21481536,21481600⟩ : DyadicInterval 40),(⟨-21481984,-21481920⟩ : DyadicInterval 40),(⟨762123383356,762123402685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168779968552,168904471135⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157015415680,157015415744⟩ : DyadicInterval 40),(⟨-183234028736,-183234028672⟩ : DyadicInterval 40),(⟨749117781843,749117801172⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157123344576,157123344640⟩ : DyadicInterval 40),(⟨-183381118592,-183381118528⟩ : DyadicInterval 40),(⟨749098510645,749098529975⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26257773952,-26218612928⟩ : DyadicInterval 40),(⟨775232690080,775252289856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157033711552,157132492160⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183393586816,-183258960576⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1828_ok : ecellOkT e1828 = true := by decide +kernel
theorem e1828_pos {a z : ℝ} (ha1 : ((628833/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((251703/1638400 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1828 e1828_ok ha1 ha2 hz1 hz2 hz

-- box ['251703/1638400', '314841/2048000', '3999/4000', '7999/8000']  interval_lower 36925183/274877906944
noncomputable def e1829 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268426651729,0,true,157132492096,157132492160⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930596603823,0,false,-183393586816,-183393586752⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268540602581,0,true,157231263808,157231263872⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930482652971,0,false,-183528229376,-183528229312⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268384422973,0,true,157095886272,157095886336⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930638832579,0,false,-183343694144,-183343694080⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268519473960,0,true,157212950336,157212950400⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930503781592,0,false,-183503262912,-183503262848⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522368245,0,true,10740416,10740480⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500887307,0,false,-10740544,-10740480⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533124533,0,true,21496512,21496576⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490131019,0,false,-21497024,-21496960⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627355,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627672,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268405532929,0,true,157114185536,157114185600⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930617722623,0,false,-183368634944,-183368634880⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268530042640,0,true,157222110912,157222110976⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930493212912,0,false,-183515751232,-183515751168⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073529888391,0,false,-26293640320,-26293640256⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073568153895,0,false,-26254449408,-26254449344⟩
    { al := (251703/1638400), au := (314841/2048000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨168915023953,169028974805⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157132492096,157132492160⟩ : DyadicInterval 40),(⟨-183393586816,-183393586752⟩ : DyadicInterval 40),(⟨749096876578,749096895907⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157231263808,157231263872⟩ : DyadicInterval 40),(⟨-183528229376,-183528229312⟩ : DyadicInterval 40),(⟨749079224833,749079244162⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157095886272,157095886336⟩ : DyadicInterval 40),(⟨-183343694144,-183343694080⟩ : DyadicInterval 40),(⟨749103415022,749103434352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157212950336,157212950400⟩ : DyadicInterval 40),(⟨-183503262912,-183503262848⟩ : DyadicInterval 40),(⟨749082498734,749082518064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10740469,21496757⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10740416,10740480⟩ : DyadicInterval 40),(⟨-10740544,-10740480⟩ : DyadicInterval 40),(⟨762123383511,762123402840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21496512,21496576⟩ : DyadicInterval 40),(⟨-21497024,-21496960⟩ : DyadicInterval 40),(⟨762123383387,762123402716⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168893905153,169018414864⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157114185536,157114185600⟩ : DyadicInterval 40),(⟨-183368634944,-183368634880⟩ : DyadicInterval 40),(⟨749100146661,749100165991⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157222110912,157222110976⟩ : DyadicInterval 40),(⟨-183515751232,-183515751168⟩ : DyadicInterval 40),(⟨749080861148,749080880478⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26293640320,-26254449344⟩ : DyadicInterval 40),(⟨775250608288,775270223040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157132492096,157231263872⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183528229376,-183393586752⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1829_ok : ecellOkT e1829 = true := by decide +kernel
theorem e1829_pos {a z : ℝ} (ha1 : ((251703/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((314841/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1829 e1829_ok ha1 ha2 hz1 hz2 hz

-- box ['628833/4096000', '251703/1638400', '7999/8000', '1']  interval_lower 146533631/1099511627776
noncomputable def e1830 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268312700878,0,true,157033711552,157033711616⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930710554674,0,false,-183258960640,-183258960576⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268426651730,0,true,157132492096,157132492160⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930596603822,0,false,-183393586816,-183393586752⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268291600743,0,true,157015419456,157015419520⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930731654809,0,false,-183234033920,-183234033856⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522368808,0,true,10740928,10740992⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500886744,0,false,-10741120,-10741056⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627671,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1268302146363,0,true,157024561664,157024561728⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨930721109189,0,false,-183246491968,-183246491904⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1268426656085,0,true,157132495872,157132495936⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨930596599467,0,false,-183393591936,-183393591872⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1073561664112,0,false,-26261096000,-26261095936⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1073599906204,0,false,-26221930240,-26221930176⟩
    { al := (628833/4096000), au := (251703/1638400), zl := (7999/8000), zu := 1,
      A := ⟨168801073102,168915023954⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157033711552,157033711616⟩ : DyadicInterval 40),(⟨-183258960640,-183258960576⟩ : DyadicInterval 40),(⟨749114516160,749114535490⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157132492096,157132492160⟩ : DyadicInterval 40),(⟨-183393586816,-183393586752⟩ : DyadicInterval 40),(⟨749096876577,749096895907⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157015419456,157015419520⟩ : DyadicInterval 40),(⟨-183234033920,-183234033856⟩ : DyadicInterval 40),(⟨749117781176,749117800506⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157132492096,157132492160⟩ : DyadicInterval 40),(⟨-183393586816,-183393586752⟩ : DyadicInterval 40),(⟨749096876577,749096895907⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10741032⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10740928,10740992⟩ : DyadicInterval 40),(⟨-10741120,-10741056⟩ : DyadicInterval 40),(⟨762123383543,762123402872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨168790518587,168915028309⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157024561664,157024561728⟩ : DyadicInterval 40),(⟨-183246491968,-183246491904⟩ : DyadicInterval 40),(⟨749116149426,749116168756⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157132495872,157132495936⟩ : DyadicInterval 40),(⟨-183393591936,-183393591872⟩ : DyadicInterval 40),(⟨749096875892,749096895222⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26261096000,-26221930176⟩ : DyadicInterval 40),(⟨775234348704,775253950880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨157033711552,157132492160⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183393586816,-183258960576⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1830_ok : ecellOkT e1830 = true := by decide +kernel
theorem e1830_pos {a z : ℝ} (ha1 : ((628833/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((251703/1638400 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1830 e1830_ok ha1 ha2 hz1 hz2 hz

-- box ['251703/1638400', '314841/2048000', '7999/8000', '1']  interval_lower 73776485/549755813888
noncomputable def e1831 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268426651729,0,true,157132492096,157132492160⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930596603823,0,false,-183393586816,-183393586752⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268540602581,0,true,157231263808,157231263872⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930482652971,0,false,-183528229376,-183528229312⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268405537350,0,true,157114189376,157114189440⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930617718202,0,false,-183368640192,-183368640128⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522376307,0,true,10748416,10748480⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500879245,0,false,-10748608,-10748544⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627670,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1268416090086,0,true,157123336896,157123336960⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨930607165466,0,false,-183381108160,-183381108096⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1268540606942,0,true,157231267584,157231267648⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨930482648610,0,false,-183528234560,-183528234496⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1073526640372,0,false,-26296966912,-26296966848⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1073564910464,0,false,-26257771200,-26257771136⟩
    { al := (251703/1638400), au := (314841/2048000), zl := (7999/8000), zu := 1,
      A := ⟨168915023953,169028974805⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157132492096,157132492160⟩ : DyadicInterval 40),(⟨-183393586816,-183393586752⟩ : DyadicInterval 40),(⟨749096876578,749096895907⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157231263808,157231263872⟩ : DyadicInterval 40),(⟨-183528229376,-183528229312⟩ : DyadicInterval 40),(⟨749079224833,749079244162⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157114189376,157114189440⟩ : DyadicInterval 40),(⟨-183368640192,-183368640128⟩ : DyadicInterval 40),(⟨749100145983,749100165312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157231263808,157231263872⟩ : DyadicInterval 40),(⟨-183528229376,-183528229312⟩ : DyadicInterval 40),(⟨749079224833,749079244162⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10748531⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10748416,10748480⟩ : DyadicInterval 40),(⟨-10748608,-10748544⟩ : DyadicInterval 40),(⟨762123383542,762123402871⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨168904462310,169028979166⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157123336896,157123336960⟩ : DyadicInterval 40),(⟨-183381108160,-183381108096⟩ : DyadicInterval 40),(⟨749098512027,749098531357⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157231267584,157231267648⟩ : DyadicInterval 40),(⟨-183528234560,-183528234496⟩ : DyadicInterval 40),(⟨749079224172,749079243502⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26296966912,-26257771136⟩ : DyadicInterval 40),(⟨775252269184,775271886336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨157132492096,157231263872⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183528229376,-183393586752⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1831_ok : ecellOkT e1831 = true := by decide +kernel
theorem e1831_pos {a z : ℝ} (ha1 : ((251703/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((314841/2048000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1831 e1831_ok ha1 ha2 hz1 hz2 hz

-- box ['314841/2048000', '1260213/8192000', '1999/2000', '7997/8000']  interval_lower 149019117/1099511627776
noncomputable def e1832 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268540602580,0,true,157231263808,157231263872⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930482652972,0,false,-183528229376,-183528229312⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268654553433,0,true,157330026624,157330026688⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930368702119,0,false,-183662888512,-183662888448⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268456088092,0,true,157158008192,157158008256⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930567167460,0,false,-183428366784,-183428366720⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268591124836,0,true,157275053248,157275053312⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930432130716,0,false,-183587931008,-183587930944⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543872056,0,true,32243776,32243840⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479383496,0,false,-32244800,-32244736⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554650843,0,true,43022208,43022272⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468604709,0,false,-43023936,-43023872⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626092,0,false,-1728,-1664⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626831,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268498341056,0,true,157194632896,157194632960⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930524914496,0,false,-183478291904,-183478291840⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268622843595,0,true,157302544192,157302544256⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930400411957,0,false,-183625414400,-183625414336⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073501349582,0,false,-26322870208,-26322870144⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073539633899,0,false,-26283659008,-26283658944⟩
    { al := (314841/2048000), au := (1260213/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨169028974804,169142925657⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157231263808,157231263872⟩ : DyadicInterval 40),(⟨-183528229376,-183528229312⟩ : DyadicInterval 40),(⟨749079224833,749079244162⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157330026624,157330026688⟩ : DyadicInterval 40),(⟨-183662888512,-183662888448⟩ : DyadicInterval 40),(⟨749061561043,749061580372⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157158008192,157158008256⟩ : DyadicInterval 40),(⟨-183428366784,-183428366720⟩ : DyadicInterval 40),(⟨749092317826,749092337156⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157275053248,157275053312⟩ : DyadicInterval 40),(⟨-183587931008,-183587930944⟩ : DyadicInterval 40),(⟨749071394758,749071414088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32244280,43023067⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32243776,32243840⟩ : DyadicInterval 40),(⟨-32244800,-32244736⟩ : DyadicInterval 40),(⟨762123383118,762123402447⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43022208,43022272⟩ : DyadicInterval 40),(⟨-43023936,-43023872⟩ : DyadicInterval 40),(⟨762123382732,762123402061⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1728,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168986713280,169111215819⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157194632896,157194632960⟩ : DyadicInterval 40),(⟨-183478291904,-183478291840⟩ : DyadicInterval 40),(⟨749085772833,749085792163⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157302544192,157302544256⟩ : DyadicInterval 40),(⟨-183625414400,-183625414336⟩ : DyadicInterval 40),(⟨749066477654,749066496983⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26322870208,-26283658944⟩ : DyadicInterval 40),(⟨775265213088,775284837984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157231263808,157330026688⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183662888512,-183528229312⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1832_ok : ecellOkT e1832 = true := by decide +kernel
theorem e1832_pos {a z : ℝ} (ha1 : ((314841/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1260213/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1832 e1832_ok ha1 ha2 hz1 hz2 hz

-- box ['1260213/8192000', '630531/4096000', '1999/2000', '7997/8000']  interval_lower 1172225/8589934592
noncomputable def e1833 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268654553432,0,true,157330026624,157330026688⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930368702120,0,false,-183662888512,-183662888448⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268768504284,0,true,157428780608,157428780672⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930254751268,0,false,-183797564096,-183797564032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268569981969,0,true,157256728192,157256728256⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930453273583,0,false,-183562946304,-183562946240⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268705032956,0,true,157373775104,157373775168⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930318222596,0,false,-183722546944,-183722546880⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543894555,0,true,32266304,32266368⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479360997,0,false,-32267264,-32267200⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554680844,0,true,43052224,43052288⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468574708,0,false,-43053952,-43053888⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626090,0,false,-1728,-1664⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626830,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268612263414,0,true,157293374336,157293374400⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930410992138,0,false,-183612911232,-183612911168⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268736773081,0,true,157401282048,157401282112⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930286482471,0,false,-183760060160,-183760060096⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073466291755,0,false,-26358778048,-26358777984⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073504604066,0,false,-26319536896,-26319536832⟩
    { al := (1260213/8192000), au := (630531/4096000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨169142925656,169256876508⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157330026624,157330026688⟩ : DyadicInterval 40),(⟨-183662888512,-183662888448⟩ : DyadicInterval 40),(⟨749061561043,749061580372⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157428780608,157428780672⟩ : DyadicInterval 40),(⟨-183797564096,-183797564032⟩ : DyadicInterval 40),(⟨749043885115,749043904445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157256728192,157256728256⟩ : DyadicInterval 40),(⟨-183562946304,-183562946240⟩ : DyadicInterval 40),(⟨749074671821,749074691151⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157373775104,157373775168⟩ : DyadicInterval 40),(⟨-183722546944,-183722546880⟩ : DyadicInterval 40),(⟨749053732226,749053751555⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32266779,43053068⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32266304,32266368⟩ : DyadicInterval 40),(⟨-32267264,-32267200⟩ : DyadicInterval 40),(⟨762123383085,762123402414⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43052224,43052288⟩ : DyadicInterval 40),(⟨-43053952,-43053888⟩ : DyadicInterval 40),(⟨762123382730,762123402059⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1728,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169100635638,169225145305⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157293374336,157293374400⟩ : DyadicInterval 40),(⟨-183612911232,-183612911168⟩ : DyadicInterval 40),(⟨749068117921,749068137251⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157401282048,157401282112⟩ : DyadicInterval 40),(⟨-183760060160,-183760060096⟩ : DyadicInterval 40),(⟨749048808461,749048827791⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26358778048,-26319536832⟩ : DyadicInterval 40),(⟨775283152032,775302791904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157330026624,157428780672⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183797564096,-183662888448⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1833_ok : ecellOkT e1833 = true := by decide +kernel
theorem e1833_pos {a z : ℝ} (ha1 : ((1260213/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((630531/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1833 e1833_ok ha1 ha2 hz1 hz2 hz

-- box ['314841/2048000', '1260213/8192000', '7997/8000', '3999/4000']  interval_lower 9304455/68719476736
noncomputable def e1834 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268540602580,0,true,157231263808,157231263872⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930482652972,0,false,-183528229376,-183528229312⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268654553433,0,true,157330026624,157330026688⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930368702119,0,false,-183662888512,-183662888448⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268477216714,0,true,157176322560,157176322624⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930546038838,0,false,-183453331584,-183453331520⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268612267702,0,true,157293378048,157293378112⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930410987850,0,false,-183612916288,-183612916224⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533123924,0,true,21495936,21496000⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490131628,0,false,-21496384,-21496320⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543895211,0,true,32266944,32267008⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479360341,0,false,-32267968,-32267904⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626829,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627356,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268508905287,0,true,157203789760,157203789824⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930514350265,0,false,-183490774720,-183490774656⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268633414972,0,true,157311706304,157311706368⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930389840580,0,false,-183637907328,-183637907264⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073498097603,0,false,-26326200960,-26326200896⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073536386511,0,false,-26286984960,-26286984896⟩
    { al := (314841/2048000), au := (1260213/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨169028974804,169142925657⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157231263808,157231263872⟩ : DyadicInterval 40),(⟨-183528229376,-183528229312⟩ : DyadicInterval 40),(⟨749079224833,749079244162⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157330026624,157330026688⟩ : DyadicInterval 40),(⟨-183662888512,-183662888448⟩ : DyadicInterval 40),(⟨749061561043,749061580372⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157176322560,157176322624⟩ : DyadicInterval 40),(⟨-183453331584,-183453331520⟩ : DyadicInterval 40),(⟨749089045199,749089064529⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157293378048,157293378112⟩ : DyadicInterval 40),(⟨-183612916288,-183612916224⟩ : DyadicInterval 40),(⟨749068117254,749068136584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21496148,32267435⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21495936,21496000⟩ : DyadicInterval 40),(⟨-21496384,-21496320⟩ : DyadicInterval 40),(⟨762123383355,762123402684⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32266944,32267008⟩ : DyadicInterval 40),(⟨-32267968,-32267904⟩ : DyadicInterval 40),(⟨762123383117,762123402446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨168997277511,169121787196⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157203789760,157203789824⟩ : DyadicInterval 40),(⟨-183490774720,-183490774656⟩ : DyadicInterval 40),(⟨749084136165,749084155495⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157311706304,157311706368⟩ : DyadicInterval 40),(⟨-183637907328,-183637907264⟩ : DyadicInterval 40),(⟨749064838678,749064858007⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26326200960,-26286984896⟩ : DyadicInterval 40),(⟨775266876064,775286503360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157231263808,157330026688⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183662888512,-183528229312⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1834_ok : ecellOkT e1834 = true := by decide +kernel
theorem e1834_pos {a z : ℝ} (ha1 : ((314841/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1260213/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1834 e1834_ok ha1 ha2 hz1 hz2 hz

-- box ['1260213/8192000', '630531/4096000', '7997/8000', '3999/4000']  interval_lower 74948203/549755813888
noncomputable def e1835 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268654553432,0,true,157330026624,157330026688⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930368702120,0,false,-183662888512,-183662888448⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268768504284,0,true,157428780608,157428780672⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930254751268,0,false,-183797564096,-183797564032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268591124834,0,true,157275053248,157275053312⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930432130718,0,false,-183587931008,-183587930944⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268726190066,0,true,157392110592,157392110656⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930297065486,0,false,-183747552064,-183747552000⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533138923,0,true,21510912,21510976⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490116629,0,false,-21511360,-21511296⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543917712,0,true,32289408,32289472⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479337840,0,false,-32290432,-32290368⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626827,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627356,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268622834767,0,true,157302536512,157302536576⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930400420785,0,false,-183625403968,-183625403904⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268747351582,0,true,157410449536,157410449600⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930275903970,0,false,-183772563008,-183772562944⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073463035393,0,false,-26362113408,-26362113344⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073501352298,0,false,-26322867392,-26322867328⟩
    { al := (1260213/8192000), au := (630531/4096000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨169142925656,169256876508⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157330026624,157330026688⟩ : DyadicInterval 40),(⟨-183662888512,-183662888448⟩ : DyadicInterval 40),(⟨749061561043,749061580372⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157428780608,157428780672⟩ : DyadicInterval 40),(⟨-183797564096,-183797564032⟩ : DyadicInterval 40),(⟨749043885115,749043904445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157275053248,157275053312⟩ : DyadicInterval 40),(⟨-183587931008,-183587930944⟩ : DyadicInterval 40),(⟨749071394759,749071414088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157392110592,157392110656⟩ : DyadicInterval 40),(⟨-183747552064,-183747552000⟩ : DyadicInterval 40),(⟨749050450253,749050469582⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21511147,32289936⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21510912,21510976⟩ : DyadicInterval 40),(⟨-21511360,-21511296⟩ : DyadicInterval 40),(⟨762123383355,762123402684⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32289408,32289472⟩ : DyadicInterval 40),(⟨-32290432,-32290368⟩ : DyadicInterval 40),(⟨762123383115,762123402444⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169111206991,169235723806⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157302536512,157302536576⟩ : DyadicInterval 40),(⟨-183625403968,-183625403904⟩ : DyadicInterval 40),(⟨749066479039,749066498369⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157410449536,157410449600⟩ : DyadicInterval 40),(⟨-183772563008,-183772562944⟩ : DyadicInterval 40),(⟨749047167231,749047186561⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26362113408,-26322867328⟩ : DyadicInterval 40),(⟨775284817280,775304459584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157330026624,157428780672⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183797564096,-183662888448⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1835_ok : ecellOkT e1835 = true := by decide +kernel
theorem e1835_pos {a z : ℝ} (ha1 : ((1260213/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((630531/4096000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1835 e1835_ok ha1 ha2 hz1 hz2 hz

-- box ['630531/4096000', '1261911/8192000', '1999/2000', '7997/8000']  interval_lower 151073257/1099511627776
noncomputable def e1836 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268768504283,0,true,157428780608,157428780672⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930254751269,0,false,-183797564096,-183797564032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268882455135,0,true,157527525696,157527525760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930140800417,0,false,-183932256192,-183932256128⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268683875844,0,true,157355439360,157355439424⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930339379708,0,false,-183697542336,-183697542272⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268818941075,0,true,157472488128,157472488192⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930204314477,0,false,-183857179328,-183857179264⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543917054,0,true,32288768,32288832⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479338498,0,false,-32289792,-32289728⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554710845,0,true,43082176,43082240⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468544707,0,false,-43083968,-43083904⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626087,0,false,-1728,-1664⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626828,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268726185777,0,true,157392106880,157392106944⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930297069775,0,false,-183747547008,-183747546944⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268850702568,0,true,157500011136,157500011200⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930172552984,0,false,-183894722368,-183894722304⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073431210318,0,false,-26394711232,-26394711168⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073469550625,0,false,-26355440128,-26355440064⟩
    { al := (630531/4096000), au := (1261911/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨169256876507,169370827359⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157428780608,157428780672⟩ : DyadicInterval 40),(⟨-183797564096,-183797564032⟩ : DyadicInterval 40),(⟨749043885116,749043904445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157527525696,157527525760⟩ : DyadicInterval 40),(⟨-183932256192,-183932256128⟩ : DyadicInterval 40),(⟨749026197113,749026216443⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157355439360,157355439424⟩ : DyadicInterval 40),(⟨-183697542336,-183697542272⟩ : DyadicInterval 40),(⟨749057013731,749057033060⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157472488128,157472488192⟩ : DyadicInterval 40),(⟨-183857179328,-183857179264⟩ : DyadicInterval 40),(⟨749036057574,749036076904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32289278,43083069⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32288768,32288832⟩ : DyadicInterval 40),(⟨-32289792,-32289728⟩ : DyadicInterval 40),(⟨762123383115,762123402444⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43082176,43082240⟩ : DyadicInterval 40),(⟨-43083968,-43083904⟩ : DyadicInterval 40),(⟨762123382759,762123402088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1728,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169214558001,169339074792⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157392106880,157392106944⟩ : DyadicInterval 40),(⟨-183747547008,-183747546944⟩ : DyadicInterval 40),(⟨749050450921,749050470250⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157500011136,157500011200⟩ : DyadicInterval 40),(⟨-183894722368,-183894722304⟩ : DyadicInterval 40),(⟨749031127102,749031146431⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26394711232,-26355440064⟩ : DyadicInterval 40),(⟨775301103648,775320758496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157428780608,157527525760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183932256192,-183797564032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1836_ok : ecellOkT e1836 = true := by decide +kernel
theorem e1836_pos {a z : ℝ} (ha1 : ((630531/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1261911/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1836 e1836_ok ha1 ha2 hz1 hz2 hz

-- box ['1261911/8192000', '31569/204800', '1999/2000', '7997/8000']  interval_lower 19013011/137438953472
noncomputable def e1837 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268882455134,0,true,157527525696,157527525760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930140800418,0,false,-183932256192,-183932256128⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268996405986,0,true,157626261888,157626261952⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930026849566,0,false,-184066964800,-184066964736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268797769720,0,true,157454141632,157454141696⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930225485832,0,false,-183832154816,-183832154752⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268932849195,0,true,157571192256,157571192320⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930090406357,0,false,-183991828224,-183991828160⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543939556,0,true,32311296,32311360⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479315996,0,false,-32312256,-32312192⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554740849,0,true,43112192,43112256⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468514703,0,false,-43113920,-43113856⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626085,0,false,-1728,-1664⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626827,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268840108137,0,true,157490830592,157490830656⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930183147415,0,false,-183882199296,-183882199232⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268964632050,0,true,157598731328,157598731392⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930058623502,0,false,-184029401152,-184029401088⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073396105273,0,false,-26430669824,-26430669760⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073434473577,0,false,-26391368704,-26391368640⟩
    { al := (1261911/8192000), au := (31569/204800), zl := (1999/2000), zu := (7997/8000),
      A := ⟨169370827358,169484778210⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157527525696,157527525760⟩ : DyadicInterval 40),(⟨-183932256192,-183932256128⟩ : DyadicInterval 40),(⟨749026197114,749026216443⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157626261888,157626261952⟩ : DyadicInterval 40),(⟨-184066964800,-184066964736⟩ : DyadicInterval 40),(⟨749008497035,749008516365⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157454141632,157454141696⟩ : DyadicInterval 40),(⟨-183832154816,-183832154752⟩ : DyadicInterval 40),(⟨749039343563,749039362893⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157571192256,157571192320⟩ : DyadicInterval 40),(⟨-183991828224,-183991828160⟩ : DyadicInterval 40),(⟨749018370865,749018390195⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32311780,43113073⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32311296,32311360⟩ : DyadicInterval 40),(⟨-32312256,-32312192⟩ : DyadicInterval 40),(⟨762123383082,762123402411⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43112192,43112256⟩ : DyadicInterval 40),(⟨-43113920,-43113856⟩ : DyadicInterval 40),(⟨762123382725,762123402054⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1728,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169328480361,169453004274⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157490830592,157490830656⟩ : DyadicInterval 40),(⟨-183882199296,-183882199232⟩ : DyadicInterval 40),(⟨749032771821,749032791151⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157598731328,157598731392⟩ : DyadicInterval 40),(⟨-184029401152,-184029401088⟩ : DyadicInterval 40),(⟨749013433705,749013453034⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26430669824,-26391368640⟩ : DyadicInterval 40),(⟨775319067936,775338737792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157527525696,157626261952⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184066964800,-183932256128⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1837_ok : ecellOkT e1837 = true := by decide +kernel
theorem e1837_pos {a z : ℝ} (ha1 : ((1261911/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((31569/204800 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1837 e1837_ok ha1 ha2 hz1 hz2 hz

-- box ['630531/4096000', '1261911/8192000', '7997/8000', '3999/4000']  interval_lower 150924391/1099511627776
noncomputable def e1838 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268768504283,0,true,157428780608,157428780672⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930254751269,0,false,-183797564096,-183797564032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268882455135,0,true,157527525696,157527525760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930140800417,0,false,-183932256192,-183932256128⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268705032954,0,true,157373775104,157373775168⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930318222598,0,false,-183722546944,-183722546880⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268840112429,0,true,157490834304,157490834368⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930183143123,0,false,-183882204352,-183882204288⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533153923,0,true,21525888,21525952⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490101629,0,false,-21526400,-21526336⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543940213,0,true,32311936,32312000⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479315339,0,false,-32312960,-32312896⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626826,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627355,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268736764249,0,true,157401274432,157401274496⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930286491303,0,false,-183760049728,-183760049664⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268861288190,0,true,157509183936,157509184000⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930161967362,0,false,-183907235200,-183907235136⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073427949570,0,false,-26398051200,-26398051136⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073466294475,0,false,-26358775232,-26358775168⟩
    { al := (630531/4096000), au := (1261911/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨169256876507,169370827359⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157428780608,157428780672⟩ : DyadicInterval 40),(⟨-183797564096,-183797564032⟩ : DyadicInterval 40),(⟨749043885116,749043904445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157527525696,157527525760⟩ : DyadicInterval 40),(⟨-183932256192,-183932256128⟩ : DyadicInterval 40),(⟨749026197113,749026216443⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157373775104,157373775168⟩ : DyadicInterval 40),(⟨-183722546944,-183722546880⟩ : DyadicInterval 40),(⟨749053732226,749053751556⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157490834304,157490834368⟩ : DyadicInterval 40),(⟨-183882204352,-183882204288⟩ : DyadicInterval 40),(⟨749032771152,749032790481⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21526147,32312437⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21525888,21525952⟩ : DyadicInterval 40),(⟨-21526400,-21526336⟩ : DyadicInterval 40),(⟨762123383386,762123402715⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32311936,32312000⟩ : DyadicInterval 40),(⟨-32312960,-32312896⟩ : DyadicInterval 40),(⟨762123383114,762123402443⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169225136473,169349660414⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157401274432,157401274496⟩ : DyadicInterval 40),(⟨-183760049728,-183760049664⟩ : DyadicInterval 40),(⟨749048809812,749048829142⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157509183936,157509184000⟩ : DyadicInterval 40),(⟨-183907235200,-183907235136⟩ : DyadicInterval 40),(⟨749029483679,749029503009⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26398051200,-26358775168⟩ : DyadicInterval 40),(⟨775302771200,775322428480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157428780608,157527525760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183932256192,-183797564032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1838_ok : ecellOkT e1838 = true := by decide +kernel
theorem e1838_pos {a z : ℝ} (ha1 : ((630531/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1261911/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1838 e1838_ok ha1 ha2 hz1 hz2 hz

-- box ['1261911/8192000', '31569/204800', '7997/8000', '3999/4000']  interval_lower 37988751/274877906944
noncomputable def e1839 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268882455134,0,true,157527525696,157527525760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930140800418,0,false,-183932256192,-183932256128⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268996405986,0,true,157626261888,157626261952⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930026849566,0,false,-184066964800,-184066964736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268818941073,0,true,157472488128,157472488192⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930204314479,0,false,-183857179328,-183857179264⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268954034792,0,true,157589549120,157589549184⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930069220760,0,false,-184016873152,-184016873088⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533168924,0,true,21540928,21540992⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490086628,0,false,-21541376,-21541312⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543962716,0,true,32334464,32334528⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479292836,0,false,-32335424,-32335360⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626825,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627354,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268850693734,0,true,157500003456,157500003520⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930172561818,0,false,-183894711936,-183894711872⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268975224793,0,true,157607909504,157607909568⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930048030759,0,false,-184041923904,-184041923840⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073392840135,0,false,-26434014400,-26434014336⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073431213040,0,false,-26394708480,-26394708416⟩
    { al := (1261911/8192000), au := (31569/204800), zl := (7997/8000), zu := (3999/4000),
      A := ⟨169370827358,169484778210⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157527525696,157527525760⟩ : DyadicInterval 40),(⟨-183932256192,-183932256128⟩ : DyadicInterval 40),(⟨749026197114,749026216443⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157626261888,157626261952⟩ : DyadicInterval 40),(⟨-184066964800,-184066964736⟩ : DyadicInterval 40),(⟨749008497035,749008516365⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157472488128,157472488192⟩ : DyadicInterval 40),(⟨-183857179328,-183857179264⟩ : DyadicInterval 40),(⟨749036057574,749036076904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157589549120,157589549184⟩ : DyadicInterval 40),(⟨-184016873152,-184016873088⟩ : DyadicInterval 40),(⟨749015079988,749015099317⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21541148,32334940⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21540928,21540992⟩ : DyadicInterval 40),(⟨-21541376,-21541312⟩ : DyadicInterval 40),(⟨762123383353,762123402682⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32334464,32334528⟩ : DyadicInterval 40),(⟨-32335424,-32335360⟩ : DyadicInterval 40),(⟨762123383081,762123402410⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169339065958,169463597017⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157500003456,157500003520⟩ : DyadicInterval 40),(⟨-183894711936,-183894711872⟩ : DyadicInterval 40),(⟨749031128492,749031147822⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157607909504,157607909568⟩ : DyadicInterval 40),(⟨-184041923904,-184041923840⟩ : DyadicInterval 40),(⟨749011788021,749011807351⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26434014400,-26394708416⟩ : DyadicInterval 40),(⟨775320737824,775340410080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157527525696,157626261952⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184066964800,-183932256128⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1839_ok : ecellOkT e1839 = true := by decide +kernel
theorem e1839_pos {a z : ℝ} (ha1 : ((1261911/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((31569/204800 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1839 e1839_ok ha1 ha2 hz1 hz2 hz

-- box ['314841/2048000', '1260213/8192000', '3999/4000', '7999/8000']  interval_lower 9295189/68719476736
noncomputable def e1840 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268540602580,0,true,157231263808,157231263872⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930482652972,0,false,-183528229376,-183528229312⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268654553433,0,true,157330026624,157330026688⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930368702119,0,false,-183662888512,-183662888448⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268498345336,0,true,157194636608,157194636672⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930524910216,0,false,-183478296960,-183478296896⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268633410568,0,true,157311702464,157311702528⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930389844984,0,false,-183637902080,-183637902016⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522375745,0,true,10747904,10747968⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500879807,0,false,-10748032,-10747968⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533139532,0,true,21511488,21511552⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490116020,0,false,-21512000,-21511936⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627355,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627671,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268519469540,0,true,157212946496,157212946560⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930503786012,0,false,-183503257664,-183503257600⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268643986371,0,true,157320868416,157320868480⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930379269181,0,false,-183650400384,-183650400320⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073494845414,0,false,-26329531968,-26329531904⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073533138913,0,false,-26290311104,-26290311040⟩
    { al := (314841/2048000), au := (1260213/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨169028974804,169142925657⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157231263808,157231263872⟩ : DyadicInterval 40),(⟨-183528229376,-183528229312⟩ : DyadicInterval 40),(⟨749079224833,749079244162⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157330026624,157330026688⟩ : DyadicInterval 40),(⟨-183662888512,-183662888448⟩ : DyadicInterval 40),(⟨749061561043,749061580372⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157194636608,157194636672⟩ : DyadicInterval 40),(⟨-183478296960,-183478296896⟩ : DyadicInterval 40),(⟨749085772168,749085791498⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157311702464,157311702528⟩ : DyadicInterval 40),(⟨-183637902080,-183637902016⟩ : DyadicInterval 40),(⟨749064839356,749064858685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10747969,21511756⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10747904,10747968⟩ : DyadicInterval 40),(⟨-10748032,-10747968⟩ : DyadicInterval 40),(⟨762123383510,762123402839⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21511488,21511552⟩ : DyadicInterval 40),(⟨-21512000,-21511936⟩ : DyadicInterval 40),(⟨762123383387,762123402716⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169007841764,169132358595⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157212946496,157212946560⟩ : DyadicInterval 40),(⟨-183503257664,-183503257600⟩ : DyadicInterval 40),(⟨749082499413,749082518743⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157320868416,157320868480⟩ : DyadicInterval 40),(⟨-183650400384,-183650400320⟩ : DyadicInterval 40),(⟨749063199544,749063218874⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26329531968,-26290311040⟩ : DyadicInterval 40),(⟨775268539136,775288168864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157231263808,157330026688⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183662888512,-183528229312⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1840_ok : ecellOkT e1840 = true := by decide +kernel
theorem e1840_pos {a z : ℝ} (ha1 : ((314841/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1260213/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1840 e1840_ok ha1 ha2 hz1 hz2 hz

-- box ['1260213/8192000', '630531/4096000', '3999/4000', '7999/8000']  interval_lower 74873917/549755813888
noncomputable def e1841 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268654553432,0,true,157330026624,157330026688⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930368702120,0,false,-183662888512,-183662888448⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268768504284,0,true,157428780608,157428780672⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930254751268,0,false,-183797564096,-183797564032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268612267700,0,true,157293378048,157293378112⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930410987852,0,false,-183612916288,-183612916224⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268747347175,0,true,157410445760,157410445824⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930275908377,0,false,-183772557824,-183772557760⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522383244,0,true,10755392,10755456⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500872308,0,false,-10755584,-10755520⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533154533,0,true,21526528,21526592⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490101019,0,false,-21526976,-21526912⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627354,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627671,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268633406144,0,true,157311698624,157311698688⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930389849408,0,false,-183637896896,-183637896832⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268757930102,0,true,157419617024,157419617088⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930265325450,0,false,-183785066048,-183785065984⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073459778821,0,false,-26365449024,-26365448960⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073498100320,0,false,-26326198208,-26326198144⟩
    { al := (1260213/8192000), au := (630531/4096000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨169142925656,169256876508⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157330026624,157330026688⟩ : DyadicInterval 40),(⟨-183662888512,-183662888448⟩ : DyadicInterval 40),(⟨749061561043,749061580372⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157428780608,157428780672⟩ : DyadicInterval 40),(⟨-183797564096,-183797564032⟩ : DyadicInterval 40),(⟨749043885115,749043904445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157293378048,157293378112⟩ : DyadicInterval 40),(⟨-183612916288,-183612916224⟩ : DyadicInterval 40),(⟨749068117254,749068136584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157410445760,157410445824⟩ : DyadicInterval 40),(⟨-183772557824,-183772557760⟩ : DyadicInterval 40),(⟨749047167900,749047187230⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10755468,21526757⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10755392,10755456⟩ : DyadicInterval 40),(⟨-10755584,-10755520⟩ : DyadicInterval 40),(⟨762123383542,762123402871⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21526528,21526592⟩ : DyadicInterval 40),(⟨-21526976,-21526912⟩ : DyadicInterval 40),(⟨762123383354,762123402683⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169121778368,169246302326⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157311698624,157311698688⟩ : DyadicInterval 40),(⟨-183637896896,-183637896832⟩ : DyadicInterval 40),(⟨749064840063,749064859393⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157419617024,157419617088⟩ : DyadicInterval 40),(⟨-183785066048,-183785065984⟩ : DyadicInterval 40),(⟨749045525870,749045545200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26365449024,-26326198144⟩ : DyadicInterval 40),(⟨775286482688,775306127392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157330026624,157428780672⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183797564096,-183662888448⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1841_ok : ecellOkT e1841 = true := by decide +kernel
theorem e1841_pos {a z : ℝ} (ha1 : ((1260213/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((630531/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1841 e1841_ok ha1 ha2 hz1 hz2 hz

-- box ['314841/2048000', '1260213/8192000', '7999/8000', '1']  interval_lower 148574849/1099511627776
noncomputable def e1842 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268540602580,0,true,157231263808,157231263872⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930482652972,0,false,-183528229376,-183528229312⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268654553433,0,true,157330026624,157330026688⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930368702119,0,false,-183662888512,-183662888448⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268519473958,0,true,157212950336,157212950400⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930503781594,0,false,-183503262912,-183503262848⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522383806,0,true,10755968,10756032⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500871746,0,false,-10756096,-10756032⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627670,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1268530033815,0,true,157222103232,157222103296⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨930493221737,0,false,-183515740800,-183515740736⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1268654557790,0,true,157330030400,157330030464⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨930368697762,0,false,-183662893632,-183662893568⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1073491593016,0,false,-26332863232,-26332863168⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1073529891105,0,false,-26293637504,-26293637440⟩
    { al := (314841/2048000), au := (1260213/8192000), zl := (7999/8000), zu := 1,
      A := ⟨169028974804,169142925657⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157231263808,157231263872⟩ : DyadicInterval 40),(⟨-183528229376,-183528229312⟩ : DyadicInterval 40),(⟨749079224833,749079244162⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157330026624,157330026688⟩ : DyadicInterval 40),(⟨-183662888512,-183662888448⟩ : DyadicInterval 40),(⟨749061561043,749061580372⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157212950336,157212950400⟩ : DyadicInterval 40),(⟨-183503262912,-183503262848⟩ : DyadicInterval 40),(⟨749082498734,749082518064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157330026624,157330026688⟩ : DyadicInterval 40),(⟨-183662888512,-183662888448⟩ : DyadicInterval 40),(⟨749061561043,749061580372⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10756030⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10755968,10756032⟩ : DyadicInterval 40),(⟨-10756096,-10756032⟩ : DyadicInterval 40),(⟨762123383510,762123402839⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨169018406039,169142930014⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157222103232,157222103296⟩ : DyadicInterval 40),(⟨-183515740800,-183515740736⟩ : DyadicInterval 40),(⟨749080862532,749080881861⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157330030400,157330030464⟩ : DyadicInterval 40),(⟨-183662893632,-183662893568⟩ : DyadicInterval 40),(⟨749061560355,749061579684⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26332863232,-26293637440⟩ : DyadicInterval 40),(⟨775270202336,775289834496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨157231263808,157330026688⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183662888512,-183528229312⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1842_ok : ecellOkT e1842 = true := by decide +kernel
theorem e1842_pos {a z : ℝ} (ha1 : ((314841/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1260213/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1842 e1842_ok ha1 ha2 hz1 hz2 hz

-- box ['1260213/8192000', '630531/4096000', '7999/8000', '1']  interval_lower 74799813/549755813888
noncomputable def e1843 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268654553432,0,true,157330026624,157330026688⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930368702120,0,false,-183662888512,-183662888448⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268768504284,0,true,157428780608,157428780672⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930254751268,0,false,-183797564096,-183797564032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268633410566,0,true,157311702464,157311702528⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930389844986,0,false,-183637902080,-183637902016⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522391306,0,true,10763456,10763520⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500864246,0,false,-10763584,-10763520⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627670,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1268643977542,0,true,157320860736,157320860800⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨930379278010,0,false,-183650389952,-183650389888⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1268768508645,0,true,157428784384,157428784448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨930254746907,0,false,-183797569280,-183797569216⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1073456522038,0,false,-26368784832,-26368784768⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1073494848131,0,false,-26329529216,-26329529152⟩
    { al := (1260213/8192000), au := (630531/4096000), zl := (7999/8000), zu := 1,
      A := ⟨169142925656,169256876508⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157330026624,157330026688⟩ : DyadicInterval 40),(⟨-183662888512,-183662888448⟩ : DyadicInterval 40),(⟨749061561043,749061580372⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157428780608,157428780672⟩ : DyadicInterval 40),(⟨-183797564096,-183797564032⟩ : DyadicInterval 40),(⟨749043885115,749043904445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157311702464,157311702528⟩ : DyadicInterval 40),(⟨-183637902080,-183637902016⟩ : DyadicInterval 40),(⟨749064839356,749064858685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157428780608,157428780672⟩ : DyadicInterval 40),(⟨-183797564096,-183797564032⟩ : DyadicInterval 40),(⟨749043885115,749043904445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10763530⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10763456,10763520⟩ : DyadicInterval 40),(⟨-10763584,-10763520⟩ : DyadicInterval 40),(⟨762123383510,762123402839⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨169132349766,169256880869⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157320860736,157320860800⟩ : DyadicInterval 40),(⟨-183650389952,-183650389888⟩ : DyadicInterval 40),(⟨749063200931,749063220260⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157428784384,157428784448⟩ : DyadicInterval 40),(⟨-183797569280,-183797569216⟩ : DyadicInterval 40),(⟨749043884453,749043903783⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26368784832,-26329529152⟩ : DyadicInterval 40),(⟨775288148192,775307795296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨157330026624,157428780672⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183797564096,-183662888448⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1843_ok : ecellOkT e1843 = true := by decide +kernel
theorem e1843_pos {a z : ℝ} (ha1 : ((1260213/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((630531/4096000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1843 e1843_ok ha1 ha2 hz1 hz2 hz

-- box ['630531/4096000', '1261911/8192000', '3999/4000', '7999/8000']  interval_lower 150775761/1099511627776
noncomputable def e1844 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268768504283,0,true,157428780608,157428780672⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930254751269,0,false,-183797564096,-183797564032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268882455135,0,true,157527525696,157527525760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930140800417,0,false,-183932256192,-183932256128⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268726190063,0,true,157392110592,157392110656⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930297065489,0,false,-183747552064,-183747552000⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268861283782,0,true,157509180160,157509180224⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930161971770,0,false,-183907230016,-183907229952⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522390744,0,true,10762880,10762944⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500864808,0,false,-10763072,-10763008⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533169534,0,true,21541504,21541568⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490086018,0,false,-21542016,-21541952⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627353,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627671,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268747342751,0,true,157410441920,157410441984⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930275912801,0,false,-183772552576,-183772552512⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268871873831,0,true,157518356736,157518356800⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930151381721,0,false,-183919748224,-183919748160⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073424688612,0,false,-26401391424,-26401391360⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073463038112,0,false,-26362110656,-26362110592⟩
    { al := (630531/4096000), au := (1261911/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨169256876507,169370827359⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157428780608,157428780672⟩ : DyadicInterval 40),(⟨-183797564096,-183797564032⟩ : DyadicInterval 40),(⟨749043885116,749043904445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157527525696,157527525760⟩ : DyadicInterval 40),(⟨-183932256192,-183932256128⟩ : DyadicInterval 40),(⟨749026197113,749026216443⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157392110592,157392110656⟩ : DyadicInterval 40),(⟨-183747552064,-183747552000⟩ : DyadicInterval 40),(⟨749050450253,749050469582⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157509180160,157509180224⟩ : DyadicInterval 40),(⟨-183907230016,-183907229952⟩ : DyadicInterval 40),(⟨749029484349,749029503679⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10762968,21541758⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10762880,10762944⟩ : DyadicInterval 40),(⟨-10763072,-10763008⟩ : DyadicInterval 40),(⟨762123383542,762123402871⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21541504,21541568⟩ : DyadicInterval 40),(⟨-21542016,-21541952⟩ : DyadicInterval 40),(⟨762123383385,762123402714⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169235714975,169360246055⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157410441920,157410441984⟩ : DyadicInterval 40),(⟨-183772552576,-183772552512⟩ : DyadicInterval 40),(⟨749047168582,749047187911⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157518356736,157518356800⟩ : DyadicInterval 40),(⟨-183919748224,-183919748160⟩ : DyadicInterval 40),(⟨749027840125,749027859455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26401391424,-26362110592⟩ : DyadicInterval 40),(⟨775304438912,775324098592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157428780608,157527525760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183932256192,-183797564032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1844_ok : ecellOkT e1844 = true := by decide +kernel
theorem e1844_pos {a z : ℝ} (ha1 : ((630531/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1261911/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1844 e1844_ok ha1 ha2 hz1 hz2 hz

-- box ['1261911/8192000', '31569/204800', '3999/4000', '7999/8000']  interval_lower 151805943/1099511627776
noncomputable def e1845 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268882455134,0,true,157527525696,157527525760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930140800418,0,false,-183932256192,-183932256128⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268996405986,0,true,157626261888,157626261952⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930026849566,0,false,-184066964800,-184066964736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268840112427,0,true,157490834304,157490834368⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930183143125,0,false,-183882204352,-183882204288⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268975220389,0,true,157607905664,157607905728⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930048035163,0,false,-184041918720,-184041918656⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522398245,0,true,10770368,10770432⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500857307,0,false,-10770560,-10770496⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533184536,0,true,21556544,21556608⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490071016,0,false,-21556992,-21556928⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627353,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627671,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268861279356,0,true,157509176320,157509176384⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930161976196,0,false,-183907224768,-183907224704⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1268985817556,0,true,157617087616,157617087680⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨930037437996,0,false,-184054446848,-184054446784⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073389574788,0,false,-26437359168,-26437359104⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073427952292,0,false,-26398048448,-26398048384⟩
    { al := (1261911/8192000), au := (31569/204800), zl := (3999/4000), zu := (7999/8000),
      A := ⟨169370827358,169484778210⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157527525696,157527525760⟩ : DyadicInterval 40),(⟨-183932256192,-183932256128⟩ : DyadicInterval 40),(⟨749026197114,749026216443⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157626261888,157626261952⟩ : DyadicInterval 40),(⟨-184066964800,-184066964736⟩ : DyadicInterval 40),(⟨749008497035,749008516365⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157490834304,157490834368⟩ : DyadicInterval 40),(⟨-183882204352,-183882204288⟩ : DyadicInterval 40),(⟨749032771152,749032790482⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157607905664,157607905728⟩ : DyadicInterval 40),(⟨-184041918720,-184041918656⟩ : DyadicInterval 40),(⟨749011788729,749011808058⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10770469,21556760⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10770368,10770432⟩ : DyadicInterval 40),(⟨-10770560,-10770496⟩ : DyadicInterval 40),(⟨762123383542,762123402871⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21556544,21556608⟩ : DyadicInterval 40),(⟨-21556992,-21556928⟩ : DyadicInterval 40),(⟨762123383353,762123402682⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169349651580,169474189780⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157509176320,157509176384⟩ : DyadicInterval 40),(⟨-183907224768,-183907224704⟩ : DyadicInterval 40),(⟨749029485033,749029504362⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157617087616,157617087680⟩ : DyadicInterval 40),(⟨-184054446848,-184054446784⟩ : DyadicInterval 40),(⟨749010142244,749010161573⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26437359168,-26398048384⟩ : DyadicInterval 40),(⟨775322407808,775342082464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157527525696,157626261952⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184066964800,-183932256128⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1845_ok : ecellOkT e1845 = true := by decide +kernel
theorem e1845_pos {a z : ℝ} (ha1 : ((1261911/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((31569/204800 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1845 e1845_ok ha1 ha2 hz1 hz2 hz

-- box ['630531/4096000', '1261911/8192000', '7999/8000', '1']  interval_lower 150626915/1099511627776
noncomputable def e1846 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268768504283,0,true,157428780608,157428780672⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930254751269,0,false,-183797564096,-183797564032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268882455135,0,true,157527525696,157527525760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930140800417,0,false,-183932256192,-183932256128⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268747347173,0,true,157410445760,157410445824⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930275908379,0,false,-183772557824,-183772557760⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522398807,0,true,10770944,10771008⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500856745,0,false,-10771136,-10771072⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627670,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1268757921271,0,true,157419609344,157419609408⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨930265334281,0,false,-183785055616,-183785055552⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1268882459496,0,true,157527529472,157527529536⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨930140796056,0,false,-183932261376,-183932261312⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1073421427442,0,false,-26404731840,-26404731776⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1073459781540,0,false,-26365446208,-26365446144⟩
    { al := (630531/4096000), au := (1261911/8192000), zl := (7999/8000), zu := 1,
      A := ⟨169256876507,169370827359⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157428780608,157428780672⟩ : DyadicInterval 40),(⟨-183797564096,-183797564032⟩ : DyadicInterval 40),(⟨749043885116,749043904445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157527525696,157527525760⟩ : DyadicInterval 40),(⟨-183932256192,-183932256128⟩ : DyadicInterval 40),(⟨749026197113,749026216443⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157410445760,157410445824⟩ : DyadicInterval 40),(⟨-183772557824,-183772557760⟩ : DyadicInterval 40),(⟨749047167900,749047187230⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157527525696,157527525760⟩ : DyadicInterval 40),(⟨-183932256192,-183932256128⟩ : DyadicInterval 40),(⟨749026197113,749026216443⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10771031⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10770944,10771008⟩ : DyadicInterval 40),(⟨-10771136,-10771072⟩ : DyadicInterval 40),(⟨762123383542,762123402871⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨169246293495,169370831720⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157419609344,157419609408⟩ : DyadicInterval 40),(⟨-183785055616,-183785055552⟩ : DyadicInterval 40),(⟨749045527259,749045546588⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157527529472,157527529536⟩ : DyadicInterval 40),(⟨-183932261376,-183932261312⟩ : DyadicInterval 40),(⟨749026196450,749026215780⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26404731840,-26365446144⟩ : DyadicInterval 40),(⟨775306106688,775325768800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨157428780608,157527525760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-183932256192,-183797564032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1846_ok : ecellOkT e1846 = true := by decide +kernel
theorem e1846_pos {a z : ℝ} (ha1 : ((630531/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1261911/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1846 e1846_ok ha1 ha2 hz1 hz2 hz

-- box ['1261911/8192000', '31569/204800', '7999/8000', '1']  interval_lower 151656813/1099511627776
noncomputable def e1847 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268882455134,0,true,157527525696,157527525760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930140800418,0,false,-183932256192,-183932256128⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1268996405986,0,true,157626261888,157626261952⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨930026849566,0,false,-184066964800,-184066964736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268861283780,0,true,157509180160,157509180224⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930161971772,0,false,-183907230016,-183907229952⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522406308,0,true,10778432,10778496⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500849244,0,false,-10778624,-10778560⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627670,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1268871864997,0,true,157518349056,157518349120⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨930151390555,0,false,-183919737728,-183919737664⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1268996410342,0,true,157626265664,157626265728⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨930026845210,0,false,-184066969920,-184066969856⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1073386309229,0,false,-26440704256,-26440704192⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1073424691334,0,false,-26401388608,-26401388544⟩
    { al := (1261911/8192000), au := (31569/204800), zl := (7999/8000), zu := 1,
      A := ⟨169370827358,169484778210⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157527525696,157527525760⟩ : DyadicInterval 40),(⟨-183932256192,-183932256128⟩ : DyadicInterval 40),(⟨749026197114,749026216443⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157626261888,157626261952⟩ : DyadicInterval 40),(⟨-184066964800,-184066964736⟩ : DyadicInterval 40),(⟨749008497035,749008516365⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157509180160,157509180224⟩ : DyadicInterval 40),(⟨-183907230016,-183907229952⟩ : DyadicInterval 40),(⟨749029484349,749029503679⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157626261888,157626261952⟩ : DyadicInterval 40),(⟨-184066964800,-184066964736⟩ : DyadicInterval 40),(⟨749008497035,749008516365⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10778532⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10778432,10778496⟩ : DyadicInterval 40),(⟨-10778624,-10778560⟩ : DyadicInterval 40),(⟨762123383542,762123402871⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨169360237221,169484782566⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157518349056,157518349120⟩ : DyadicInterval 40),(⟨-183919737728,-183919737664⟩ : DyadicInterval 40),(⟨749027841489,749027860818⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157626265664,157626265728⟩ : DyadicInterval 40),(⟨-184066969920,-184066969856⟩ : DyadicInterval 40),(⟨749008496345,749008515674⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26440704256,-26401388544⟩ : DyadicInterval 40),(⟨775324077888,775343755008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨157527525696,157626261952⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184066964800,-183932256128⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1847_ok : ecellOkT e1847 = true := by decide +kernel
theorem e1847_pos {a z : ℝ} (ha1 : ((1261911/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((31569/204800 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1847 e1847_ok ha1 ha2 hz1 hz2 hz

-- box ['31569/204800', '1263609/8192000', '999/1000', '7993/8000']  interval_lower 153734807/1099511627776
noncomputable def e1848 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268996405985,0,true,157626261888,157626261952⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930026849567,0,false,-184066964800,-184066964736⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269110356837,0,true,157724989248,157724989312⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929912898715,0,false,-184201689920,-184201689856⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268826921206,0,true,157479403392,157479403456⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930196334346,0,false,-183866611968,-183866611904⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268961957950,0,true,157596414272,157596414336⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930061297602,0,false,-184026239808,-184026239744⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587074116,0,true,75443712,75443776⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436181436,0,false,-75448960,-75448896⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099597912918,0,true,86281728,86281792⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099425342634,0,false,-86288576,-86288512⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621004,0,false,-6784,-6720⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622600,0,false,-5184,-5120⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268911659851,0,true,157552831872,157552831936⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930111595701,0,false,-183966779392,-183966779328⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269036162312,0,true,157660707904,157660707968⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929987093240,0,false,-184113967168,-184113967104⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073374052616,0,false,-26453259200,-26453259136⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073412430513,0,false,-26413947520,-26413947456⟩
    { al := (31569/204800), au := (1263609/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨169484778209,169598729061⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157626261888,157626261952⟩ : DyadicInterval 40),(⟨-184066964800,-184066964736⟩ : DyadicInterval 40),(⟨749008497035,749008516365⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157724989248,157724989312⟩ : DyadicInterval 40),(⟨-184201689920,-184201689856⟩ : DyadicInterval 40),(⟨748990784843,748990804173⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157479403392,157479403456⟩ : DyadicInterval 40),(⟨-183866611968,-183866611904⟩ : DyadicInterval 40),(⟨749034818878,749034838207⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157596414272,157596414336⟩ : DyadicInterval 40),(⟨-184026239808,-184026239744⟩ : DyadicInterval 40),(⟨749013849144,749013868473⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨75446340,86285142⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75443712,75443776⟩ : DyadicInterval 40),(⟨-75448960,-75448896⟩ : DyadicInterval 40),(⟨762123380998,762123400328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨86281728,86281792⟩ : DyadicInterval 40),(⟨-86288576,-86288512⟩ : DyadicInterval 40),(⟨762123380204,762123399533⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6784,-5120⟩ : DyadicInterval 40),(⟨762123386176,762123406272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169400032075,169524534536⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157552831872,157552831936⟩ : DyadicInterval 40),(⟨-183966779392,-183966779328⟩ : DyadicInterval 40),(⟨749021661868,749021681198⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157660707904,157660707968⟩ : DyadicInterval 40),(⟨-184113967168,-184113967104⟩ : DyadicInterval 40),(⟨749002318787,749002338116⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26453259200,-26413947456⟩ : DyadicInterval 40),(⟨775330357344,775350032480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157626261888,157724989312⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184201689920,-184066964736⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1848_ok : ecellOkT e1848 = true := by decide +kernel
theorem e1848_pos {a z : ℝ} (ha1 : ((31569/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1263609/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1848 e1848_ok ha1 ha2 hz1 hz2 hz

-- box ['1263609/8192000', '632229/4096000', '999/1000', '7993/8000']  interval_lower 154772305/1099511627776
noncomputable def e1849 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269110356836,0,true,157724989248,157724989312⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929912898716,0,false,-184201689920,-184201689856⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269224307688,0,true,157823707776,157823707840⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929798947864,0,false,-184336431488,-184336431424⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268940758106,0,true,157578045184,157578045248⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930082497446,0,false,-184001177792,-184001177728⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269075809094,0,true,157695057920,157695057984⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929947446458,0,false,-184160842048,-184160841984⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587126624,0,true,75496256,75496320⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436128928,0,false,-75501504,-75501440⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099597972932,0,true,86341760,86341824⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099425282620,0,false,-86348608,-86348544⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620995,0,false,-6784,-6720⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622592,0,false,-5248,-5184⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269025553724,0,true,157651516416,157651516480⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929997701828,0,false,-184101424832,-184101424768⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269150063314,0,true,157759388992,157759389056⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929873192238,0,false,-184248639104,-184248639040⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073338917924,0,false,-26489250048,-26489249984⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073377323814,0,false,-26449908352,-26449908288⟩
    { al := (1263609/8192000), au := (632229/4096000), zl := (999/1000), zu := (7993/8000),
      A := ⟨169598729060,169712679912⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157724989248,157724989312⟩ : DyadicInterval 40),(⟨-184201689920,-184201689856⟩ : DyadicInterval 40),(⟨748990784843,748990804173⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157823707776,157823707840⟩ : DyadicInterval 40),(⟨-184336431488,-184336431424⟩ : DyadicInterval 40),(⟨748973060509,748973079838⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157578045184,157578045248⟩ : DyadicInterval 40),(⟨-184001177792,-184001177728⟩ : DyadicInterval 40),(⟨749017142373,749017161703⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157695057920,157695057984⟩ : DyadicInterval 40),(⟨-184160842048,-184160841984⟩ : DyadicInterval 40),(⟨748996156112,748996175441⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨75498848,86345156⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75496256,75496320⟩ : DyadicInterval 40),(⟨-75501504,-75501440⟩ : DyadicInterval 40),(⟨762123380991,762123400320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨86341760,86341824⟩ : DyadicInterval 40),(⟨-86348608,-86348544⟩ : DyadicInterval 40),(⟨762123380195,762123399524⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6784,-5184⟩ : DyadicInterval 40),(⟨762123386208,762123406272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169513925948,169638435538⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157651516416,157651516480⟩ : DyadicInterval 40),(⟨-184101424832,-184101424768⟩ : DyadicInterval 40),(⟨749003967536,749003986865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157759388992,157759389056⟩ : DyadicInterval 40),(⟨-184248639104,-184248639040⟩ : DyadicInterval 40),(⟨748984610123,748984629452⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26489250048,-26449908288⟩ : DyadicInterval 40),(⟨775348337760,775368027904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157724989248,157823707840⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184336431488,-184201689856⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1849_ok : ecellOkT e1849 = true := by decide +kernel
theorem e1849_pos {a z : ℝ} (ha1 : ((1263609/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((632229/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1849 e1849_ok ha1 ha2 hz1 hz2 hz

-- box ['31569/204800', '1263609/8192000', '7993/8000', '3997/4000']  interval_lower 153585411/1099511627776
noncomputable def e1850 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268996405985,0,true,157626261888,157626261952⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930026849567,0,false,-184066964800,-184066964736⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269110356837,0,true,157724989248,157724989312⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929912898715,0,false,-184201689920,-184201689856⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268848106803,0,true,157497761792,157497761856⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930175148749,0,false,-183891654080,-183891654016⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1268983157791,0,true,157614783040,157614783104⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930040097761,0,false,-184051302400,-184051302336⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576296172,0,true,64666432,64666496⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446959380,0,false,-64670336,-64670272⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587127474,0,true,75497088,75497152⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436128078,0,false,-75502336,-75502272⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622591,0,false,-5248,-5184⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623973,0,false,-3840,-3776⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268922252478,0,true,157562010304,157562010368⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930101003074,0,false,-183979301312,-183979301248⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269046762082,0,true,157669891648,157669891712⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929976493470,0,false,-184126499200,-184126499136⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073370783934,0,false,-26456607488,-26456607424⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073409166432,0,false,-26417290944,-26417290880⟩
    { al := (31569/204800), au := (1263609/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨169484778209,169598729061⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157626261888,157626261952⟩ : DyadicInterval 40),(⟨-184066964800,-184066964736⟩ : DyadicInterval 40),(⟨749008497035,749008516365⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157724989248,157724989312⟩ : DyadicInterval 40),(⟨-184201689920,-184201689856⟩ : DyadicInterval 40),(⟨748990784843,748990804173⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157497761792,157497761856⟩ : DyadicInterval 40),(⟨-183891654080,-183891654016⟩ : DyadicInterval 40),(⟨749031530104,749031549434⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157614783040,157614783104⟩ : DyadicInterval 40),(⟨-184051302400,-184051302336⟩ : DyadicInterval 40),(⟨749010555505,749010574835⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨64668396,75499698⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64666432,64666496⟩ : DyadicInterval 40),(⟨-64670336,-64670272⟩ : DyadicInterval 40),(⟨762123381700,762123401029⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75497088,75497152⟩ : DyadicInterval 40),(⟨-75502336,-75502272⟩ : DyadicInterval 40),(⟨762123380991,762123400320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5248,-3776⟩ : DyadicInterval 40),(⟨762123385504,762123405504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169410624702,169535134306⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157562010304,157562010368⟩ : DyadicInterval 40),(⟨-183979301312,-183979301248⟩ : DyadicInterval 40),(⟨749020016749,749020036078⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157669891648,157669891712⟩ : DyadicInterval 40),(⟨-184126499200,-184126499136⟩ : DyadicInterval 40),(⟨749000671311,749000690640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26456607488,-26417290880⟩ : DyadicInterval 40),(⟨775332029056,775351706624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157626261888,157724989312⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184201689920,-184066964736⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1850_ok : ecellOkT e1850 = true := by decide +kernel
theorem e1850_pos {a z : ℝ} (ha1 : ((31569/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1263609/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1850 e1850_ok ha1 ha2 hz1 hz2 hz

-- box ['1263609/8192000', '632229/4096000', '7993/8000', '3997/4000']  interval_lower 154622819/1099511627776
noncomputable def e1851 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269110356836,0,true,157724989248,157724989312⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929912898716,0,false,-184201689920,-184201689856⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269224307688,0,true,157823707776,157823707840⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929798947864,0,false,-184336431488,-184336431424⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268961957947,0,true,157596414272,157596414336⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930061297605,0,false,-184026239808,-184026239744⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269097023179,0,true,157713437376,157713437440⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929926232373,0,false,-184185924544,-184185924480⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576341180,0,true,64711488,64711552⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446914372,0,false,-64715328,-64715264⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587179987,0,true,75549568,75549632⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436075565,0,false,-75554816,-75554752⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622584,0,false,-5248,-5184⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623968,0,false,-3840,-3776⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269036153473,0,true,157660700288,157660700352⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929987102079,0,false,-184113956736,-184113956672⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269160670206,0,true,157768578112,157768578176⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929862585346,0,false,-184261181120,-184261181056⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073335644848,0,false,-26492602944,-26492602880⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073374055343,0,false,-26453256448,-26453256384⟩
    { al := (1263609/8192000), au := (632229/4096000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨169598729060,169712679912⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157724989248,157724989312⟩ : DyadicInterval 40),(⟨-184201689920,-184201689856⟩ : DyadicInterval 40),(⟨748990784843,748990804173⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157823707776,157823707840⟩ : DyadicInterval 40),(⟨-184336431488,-184336431424⟩ : DyadicInterval 40),(⟨748973060509,748973079838⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157596414272,157596414336⟩ : DyadicInterval 40),(⟨-184026239808,-184026239744⟩ : DyadicInterval 40),(⟨749013849144,749013868473⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157713437376,157713437440⟩ : DyadicInterval 40),(⟨-184185924544,-184185924480⟩ : DyadicInterval 40),(⟨748992858010,748992877340⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨64713404,75552211⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64711488,64711552⟩ : DyadicInterval 40),(⟨-64715328,-64715264⟩ : DyadicInterval 40),(⟨762123381663,762123400992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75549568,75549632⟩ : DyadicInterval 40),(⟨-75554816,-75554752⟩ : DyadicInterval 40),(⟨762123380984,762123400313⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5248,-3776⟩ : DyadicInterval 40),(⟨762123385504,762123405504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169524525697,169649042430⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157660700288,157660700352⟩ : DyadicInterval 40),(⟨-184113956736,-184113956672⟩ : DyadicInterval 40),(⟨749002320144,749002339474⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157768578112,157768578176⟩ : DyadicInterval 40),(⟨-184261181120,-184261181056⟩ : DyadicInterval 40),(⟨748982960408,748982979738⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26492602944,-26453256384⟩ : DyadicInterval 40),(⟨775350011808,775369704352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157724989248,157823707840⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184336431488,-184201689856⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1851_ok : ecellOkT e1851 = true := by decide +kernel
theorem e1851_pos {a z : ℝ} (ha1 : ((1263609/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((632229/4096000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1851 e1851_ok ha1 ha2 hz1 hz2 hz

-- box ['632229/4096000', '1265307/8192000', '999/1000', '7993/8000']  interval_lower 155812639/1099511627776
noncomputable def e1852 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269224307687,0,true,157823707776,157823707840⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929798947865,0,false,-184336431488,-184336431424⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269338258539,0,true,157922417408,157922417472⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929684997013,0,false,-184471189632,-184471189568⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269054595007,0,true,157676678144,157676678208⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929968660545,0,false,-184135760128,-184135760064⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269189660238,0,true,157793692736,157793692800⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929833595314,0,false,-184295460736,-184295460672⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587179138,0,true,75548736,75548800⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436076414,0,false,-75553984,-75553920⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099598032952,0,true,86401728,86401792⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099425222600,0,false,-86408576,-86408512⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620985,0,false,-6848,-6784⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622585,0,false,-5248,-5184⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269139447603,0,true,157750192192,157750192256⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929883807949,0,false,-184236086784,-184236086720⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269263964314,0,true,157858061184,157858061248⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929759291238,0,false,-184383327488,-184383327424⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073303759635,0,false,-26525266240,-26525266176⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073342193518,0,false,-26485894592,-26485894528⟩
    { al := (632229/4096000), au := (1265307/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨169712679911,169826630763⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157823707776,157823707840⟩ : DyadicInterval 40),(⟨-184336431488,-184336431424⟩ : DyadicInterval 40),(⟨748973060509,748973079839⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157922417408,157922417472⟩ : DyadicInterval 40),(⟨-184471189632,-184471189568⟩ : DyadicInterval 40),(⟨748955324122,748955343452⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157676678144,157676678208⟩ : DyadicInterval 40),(⟨-184135760128,-184135760064⟩ : DyadicInterval 40),(⟨748999453804,748999473133⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157793692736,157793692800⟩ : DyadicInterval 40),(⟨-184295460736,-184295460672⟩ : DyadicInterval 40),(⟨748978450981,748978470310⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨75551362,86405176⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75548736,75548800⟩ : DyadicInterval 40),(⟨-75553984,-75553920⟩ : DyadicInterval 40),(⟨762123380984,762123400313⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨86401728,86401792⟩ : DyadicInterval 40),(⟨-86408576,-86408512⟩ : DyadicInterval 40),(⟨762123380185,762123399515⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6848,-5184⟩ : DyadicInterval 40),(⟨762123386208,762123406304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169627819827,169752336538⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157750192192,157750192256⟩ : DyadicInterval 40),(⟨-184236086784,-184236086720⟩ : DyadicInterval 40),(⟨748986261075,748986280404⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157858061184,157858061248⟩ : DyadicInterval 40),(⟨-184383327488,-184383327424⟩ : DyadicInterval 40),(⟨748966889374,748966908704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26525266240,-26485894528⟩ : DyadicInterval 40),(⟨775366330880,775386036000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157823707776,157922417472⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184471189632,-184336431424⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1852_ok : ecellOkT e1852 = true := by decide +kernel
theorem e1852_pos {a z : ℝ} (ha1 : ((632229/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1265307/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1852 e1852_ok ha1 ha2 hz1 hz2 hz

-- box ['1265307/8192000', '316539/2048000', '999/1000', '7993/8000']  interval_lower 19606953/137438953472
noncomputable def e1853 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269338258538,0,true,157922417408,157922417472⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929684997014,0,false,-184471189632,-184471189568⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269452209390,0,true,158021118144,158021118208⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929571046162,0,false,-184605964288,-184605964224⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269168431907,0,true,157775302272,157775302336⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929854823645,0,false,-184270358912,-184270358848⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269303511382,0,true,157892318720,157892318784⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929719744170,0,false,-184430095936,-184430095872⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587231654,0,true,75601216,75601280⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436023898,0,false,-75606528,-75606464⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099598092975,0,true,86461760,86461824⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099425162577,0,false,-86468608,-86468544⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620976,0,false,-6848,-6784⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622578,0,false,-5248,-5184⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269253341478,0,true,157848859072,157848859136⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929769914074,0,false,-184370765248,-184370765184⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269377865311,0,true,157956724608,157956724672⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929645390241,0,false,-184518032384,-184518032320⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073268577747,0,false,-26561307776,-26561307712⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073307039628,0,false,-26521906176,-26521906112⟩
    { al := (1265307/8192000), au := (316539/2048000), zl := (999/1000), zu := (7993/8000),
      A := ⟨169826630762,169940581614⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157922417408,157922417472⟩ : DyadicInterval 40),(⟨-184471189632,-184471189568⟩ : DyadicInterval 40),(⟨748955324122,748955343452⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158021118144,158021118208⟩ : DyadicInterval 40),(⟨-184605964288,-184605964224⟩ : DyadicInterval 40),(⟨748937575655,748937594984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157775302272,157775302336⟩ : DyadicInterval 40),(⟨-184270358912,-184270358848⟩ : DyadicInterval 40),(⟨748981753140,748981772470⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157892318720,157892318784⟩ : DyadicInterval 40),(⟨-184430095936,-184430095872⟩ : DyadicInterval 40),(⟨748960733776,748960753106⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨75603878,86465199⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75601216,75601280⟩ : DyadicInterval 40),(⟨-75606528,-75606464⟩ : DyadicInterval 40),(⟨762123381009,762123400338⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨86461760,86461824⟩ : DyadicInterval 40),(⟨-86468608,-86468544⟩ : DyadicInterval 40),(⟨762123380176,762123399505⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6848,-5184⟩ : DyadicInterval 40),(⟨762123386208,762123406304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169741713702,169866237535⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157848859072,157848859136⟩ : DyadicInterval 40),(⟨-184370765248,-184370765184⟩ : DyadicInterval 40),(⟨748968542560,748968561889⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157956724608,157956724672⟩ : DyadicInterval 40),(⟨-184518032384,-184518032320⟩ : DyadicInterval 40),(⟨748949156494,748949175824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26561307776,-26521906112⟩ : DyadicInterval 40),(⟨775384336672,775404056768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157922417408,158021118208⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184605964288,-184471189568⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1853_ok : ecellOkT e1853 = true := by decide +kernel
theorem e1853_pos {a z : ℝ} (ha1 : ((1265307/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((316539/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1853 e1853_ok ha1 ha2 hz1 hz2 hz

-- box ['632229/4096000', '1265307/8192000', '7993/8000', '3997/4000']  interval_lower 155662755/1099511627776
noncomputable def e1854 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269224307687,0,true,157823707776,157823707840⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929798947865,0,false,-184336431488,-184336431424⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269338258539,0,true,157922417408,157922417472⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929684997013,0,false,-184471189632,-184471189568⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269075809091,0,true,157695057920,157695057984⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929947446461,0,false,-184160842048,-184160841984⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269210888567,0,true,157812082880,157812082944⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929812366985,0,false,-184320563136,-184320563072⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576386191,0,true,64756480,64756544⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446869361,0,false,-64760384,-64760320⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587232504,0,true,75602112,75602176⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436023048,0,false,-75607360,-75607296⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622577,0,false,-5248,-5184⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623962,0,false,-3840,-3776⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269150054472,0,true,157759381312,157759381376⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929873201080,0,false,-184248628608,-184248628544⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269274578328,0,true,157867255680,157867255744⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929748677224,0,false,-184395879488,-184395879424⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073300482161,0,false,-26528623744,-26528623680⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073338920654,0,false,-26489247296,-26489247232⟩
    { al := (632229/4096000), au := (1265307/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨169712679911,169826630763⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157823707776,157823707840⟩ : DyadicInterval 40),(⟨-184336431488,-184336431424⟩ : DyadicInterval 40),(⟨748973060509,748973079839⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157922417408,157922417472⟩ : DyadicInterval 40),(⟨-184471189632,-184471189568⟩ : DyadicInterval 40),(⟨748955324122,748955343452⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157695057920,157695057984⟩ : DyadicInterval 40),(⟨-184160842048,-184160841984⟩ : DyadicInterval 40),(⟨748996156113,748996175442⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157812082880,157812082944⟩ : DyadicInterval 40),(⟨-184320563136,-184320563072⟩ : DyadicInterval 40),(⟨748975148410,748975167739⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨64758415,75604728⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64756480,64756544⟩ : DyadicInterval 40),(⟨-64760384,-64760320⟩ : DyadicInterval 40),(⟨762123381689,762123401019⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75602112,75602176⟩ : DyadicInterval 40),(⟨-75607360,-75607296⟩ : DyadicInterval 40),(⟨762123380977,762123400306⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5248,-3776⟩ : DyadicInterval 40),(⟨762123385504,762123405504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169638426696,169762950552⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157759381312,157759381376⟩ : DyadicInterval 40),(⟨-184248628608,-184248628544⟩ : DyadicInterval 40),(⟨748984611492,748984630822⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157867255680,157867255744⟩ : DyadicInterval 40),(⟨-184395879488,-184395879424⟩ : DyadicInterval 40),(⟨748965237419,748965256748⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26528623744,-26489247232⟩ : DyadicInterval 40),(⟨775368007232,775387714752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157823707776,157922417472⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184471189632,-184336431424⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1854_ok : ecellOkT e1854 = true := by decide +kernel
theorem e1854_pos {a z : ℝ} (ha1 : ((632229/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1265307/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1854 e1854_ok ha1 ha2 hz1 hz2 hz

-- box ['1265307/8192000', '316539/2048000', '7993/8000', '3997/4000']  interval_lower 156705501/1099511627776
noncomputable def e1855 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269338258538,0,true,157922417408,157922417472⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929684997014,0,false,-184471189632,-184471189568⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269452209390,0,true,158021118144,158021118208⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929571046162,0,false,-184605964288,-184605964224⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269189660235,0,true,157793692736,157793692800⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929833595317,0,false,-184295460736,-184295460672⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269324753954,0,true,157910719552,157910719616⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929698501598,0,false,-184455218240,-184455218176⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576431206,0,true,64801472,64801536⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446824346,0,false,-64805376,-64805312⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587285025,0,true,75654592,75654656⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435970527,0,false,-75659904,-75659840⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622570,0,false,-5248,-5184⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623957,0,false,-3840,-3776⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269263955469,0,true,157858053568,157858053632⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929759300083,0,false,-184383317056,-184383316992⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269388486447,0,true,157965924352,157965924416⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929634769105,0,false,-184530594304,-184530594240⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073265295874,0,false,-26564669952,-26564669888⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073303762367,0,false,-26525263488,-26525263424⟩
    { al := (1265307/8192000), au := (316539/2048000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨169826630762,169940581614⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157922417408,157922417472⟩ : DyadicInterval 40),(⟨-184471189632,-184471189568⟩ : DyadicInterval 40),(⟨748955324122,748955343452⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158021118144,158021118208⟩ : DyadicInterval 40),(⟨-184605964288,-184605964224⟩ : DyadicInterval 40),(⟨748937575655,748937594984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157793692736,157793692800⟩ : DyadicInterval 40),(⟨-184295460736,-184295460672⟩ : DyadicInterval 40),(⟨748978450981,748978470311⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157910719552,157910719616⟩ : DyadicInterval 40),(⟨-184455218240,-184455218176⟩ : DyadicInterval 40),(⟨748957426730,748957446059⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨64803430,75657249⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64801472,64801536⟩ : DyadicInterval 40),(⟨-64805376,-64805312⟩ : DyadicInterval 40),(⟨762123381684,762123401013⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75654592,75654656⟩ : DyadicInterval 40),(⟨-75659904,-75659840⟩ : DyadicInterval 40),(⟨762123381001,762123400331⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5248,-3776⟩ : DyadicInterval 40),(⟨762123385504,762123405504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169752327693,169876858671⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157858053568,157858053632⟩ : DyadicInterval 40),(⟨-184383317056,-184383316992⟩ : DyadicInterval 40),(⟨748966890736,748966910066⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157965924352,157965924416⟩ : DyadicInterval 40),(⟨-184530594304,-184530594240⟩ : DyadicInterval 40),(⟨748947502340,748947521670⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26564669952,-26525263424⟩ : DyadicInterval 40),(⟨775386015328,775405737856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157922417408,158021118208⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184605964288,-184471189568⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1855_ok : ecellOkT e1855 = true := by decide +kernel
theorem e1855_pos {a z : ℝ} (ha1 : ((1265307/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((316539/2048000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1855 e1855_ok ha1 ha2 hz1 hz2 hz

-- box ['31569/204800', '1263609/8192000', '3997/4000', '1599/1600']  interval_lower 153436309/1099511627776
noncomputable def e1856 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268996405985,0,true,157626261888,157626261952⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930026849567,0,false,-184066964800,-184066964736⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269110356837,0,true,157724989248,157724989312⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929912898715,0,false,-184201689920,-184201689856⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268869292401,0,true,157516119872,157516119936⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930153963151,0,false,-183916696768,-183916696704⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269004357632,0,true,157633151552,157633151616⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨930018897920,0,false,-184076365568,-184076365504⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565518182,0,true,53889024,53889088⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457737370,0,false,-53891776,-53891712⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576341982,0,true,64712256,64712320⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446913570,0,false,-64716160,-64716096⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623967,0,false,-3840,-3776⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625135,0,false,-2688,-2624⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268932845128,0,true,157571188736,157571188800⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930090410424,0,false,-183991823424,-183991823360⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269057361879,0,true,157679075392,157679075456⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929965893673,0,false,-184139031424,-184139031360⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073367515038,0,false,-26459956032,-26459955968⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073405902140,0,false,-26420634624,-26420634560⟩
    { al := (31569/204800), au := (1263609/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨169484778209,169598729061⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157626261888,157626261952⟩ : DyadicInterval 40),(⟨-184066964800,-184066964736⟩ : DyadicInterval 40),(⟨749008497035,749008516365⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157724989248,157724989312⟩ : DyadicInterval 40),(⟨-184201689920,-184201689856⟩ : DyadicInterval 40),(⟨748990784843,748990804173⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157516119872,157516119936⟩ : DyadicInterval 40),(⟨-183916696768,-183916696704⟩ : DyadicInterval 40),(⟨749028240922,749028260252⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157633151552,157633151616⟩ : DyadicInterval 40),(⟨-184076365568,-184076365504⟩ : DyadicInterval 40),(⟨749007261421,749007280750⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨53890406,64714206⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53889024,53889088⟩ : DyadicInterval 40),(⟨-53891776,-53891712⟩ : DyadicInterval 40),(⟨762123382286,762123401615⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64712256,64712320⟩ : DyadicInterval 40),(⟨-64716160,-64716096⟩ : DyadicInterval 40),(⟨762123381694,762123401024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3840,-2624⟩ : DyadicInterval 40),(⟨762123384928,762123404800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169421217352,169545734103⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157571188736,157571188800⟩ : DyadicInterval 40),(⟨-183991823424,-183991823360⟩ : DyadicInterval 40),(⟨749018371498,749018390827⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157679075392,157679075456⟩ : DyadicInterval 40),(⟨-184139031424,-184139031360⟩ : DyadicInterval 40),(⟨748999023702,748999043032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26459956032,-26420634560⟩ : DyadicInterval 40),(⟨775333700896,775353380896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157626261888,157724989312⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184201689920,-184066964736⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1856_ok : ecellOkT e1856 = true := by decide +kernel
theorem e1856_pos {a z : ℝ} (ha1 : ((31569/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1263609/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1856 e1856_ok ha1 ha2 hz1 hz2 hz

-- box ['1263609/8192000', '632229/4096000', '3997/4000', '1599/1600']  interval_lower 154473349/1099511627776
noncomputable def e1857 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269110356836,0,true,157724989248,157724989312⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929912898716,0,false,-184201689920,-184201689856⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269224307688,0,true,157823707776,157823707840⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929798947864,0,false,-184336431488,-184336431424⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268983157789,0,true,157614783040,157614783104⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930040097763,0,false,-184051302400,-184051302336⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269118237264,0,true,157731816576,157731816640⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929905018288,0,false,-184211007616,-184211007552⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565555688,0,true,53926528,53926592⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457699864,0,false,-53929280,-53929216⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576386993,0,true,64757248,64757312⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446868559,0,false,-64761152,-64761088⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623961,0,false,-3840,-3776⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625131,0,false,-2688,-2624⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269046753244,0,true,157669884032,157669884096⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929976502308,0,false,-184126488768,-184126488704⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269171277125,0,true,157777767168,157777767232⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929851978427,0,false,-184273723264,-184273723200⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073332371558,0,false,-26495956096,-26495956032⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073370786660,0,false,-26456604736,-26456604672⟩
    { al := (1263609/8192000), au := (632229/4096000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨169598729060,169712679912⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157724989248,157724989312⟩ : DyadicInterval 40),(⟨-184201689920,-184201689856⟩ : DyadicInterval 40),(⟨748990784843,748990804173⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157823707776,157823707840⟩ : DyadicInterval 40),(⟨-184336431488,-184336431424⟩ : DyadicInterval 40),(⟨748973060509,748973079838⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157614783040,157614783104⟩ : DyadicInterval 40),(⟨-184051302400,-184051302336⟩ : DyadicInterval 40),(⟨749010555506,749010574835⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157731816576,157731816640⟩ : DyadicInterval 40),(⟨-184211007616,-184211007552⟩ : DyadicInterval 40),(⟨748989559462,748989578791⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨53927912,64759217⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53926528,53926592⟩ : DyadicInterval 40),(⟨-53929280,-53929216⟩ : DyadicInterval 40),(⟨762123382282,762123401612⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨64757248,64757312⟩ : DyadicInterval 40),(⟨-64761152,-64761088⟩ : DyadicInterval 40),(⟨762123381689,762123401018⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3840,-2624⟩ : DyadicInterval 40),(⟨762123384928,762123404800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169535125468,169659649349⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157669884032,157669884096⟩ : DyadicInterval 40),(⟨-184126488768,-184126488704⟩ : DyadicInterval 40),(⟨749000672668,749000691998⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157777767168,157777767232⟩ : DyadicInterval 40),(⟨-184273723264,-184273723200⟩ : DyadicInterval 40),(⟨748981310571,748981329900⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26495956096,-26456604672⟩ : DyadicInterval 40),(⟨775351685952,775371380928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157724989248,157823707840⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184336431488,-184201689856⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1857_ok : ecellOkT e1857 = true := by decide +kernel
theorem e1857_pos {a z : ℝ} (ha1 : ((1263609/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((632229/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1857 e1857_ok ha1 ha2 hz1 hz2 hz

-- box ['31569/204800', '1263609/8192000', '1599/1600', '1999/2000']  interval_lower 76643529/549755813888
noncomputable def e1858 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1268996405985,0,true,157626261888,157626261952⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨930026849567,0,false,-184066964800,-184066964736⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269110356837,0,true,157724989248,157724989312⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929912898715,0,false,-184201689920,-184201689856⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1268890477998,0,true,157534477632,157534477696⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930132777554,0,false,-183941739968,-183941739904⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269025557473,0,true,157651519680,157651519744⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929997698079,0,false,-184101429312,-184101429248⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554740144,0,true,43111488,43111552⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468515408,0,false,-43113216,-43113152⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565556442,0,true,53927296,53927360⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457699110,0,false,-53930048,-53929984⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625130,0,false,-2688,-2624⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626086,0,false,-1728,-1664⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1268943437802,0,true,157580367104,157580367168⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨930079817750,0,false,-184004345664,-184004345600⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269067961694,0,true,157688259008,157688259072⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929955293858,0,false,-184151563840,-184151563776⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073364245933,0,false,-26463304768,-26463304704⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073402637636,0,false,-26423978496,-26423978432⟩
    { al := (31569/204800), au := (1263609/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨169484778209,169598729061⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157626261888,157626261952⟩ : DyadicInterval 40),(⟨-184066964800,-184066964736⟩ : DyadicInterval 40),(⟨749008497035,749008516365⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157724989248,157724989312⟩ : DyadicInterval 40),(⟨-184201689920,-184201689856⟩ : DyadicInterval 40),(⟨748990784843,748990804173⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157534477632,157534477696⟩ : DyadicInterval 40),(⟨-183941739968,-183941739904⟩ : DyadicInterval 40),(⟨749024951306,749024970635⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157651519680,157651519744⟩ : DyadicInterval 40),(⟨-184101429312,-184101429248⟩ : DyadicInterval 40),(⟨749003966964,749003986293⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨43112368,53928666⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43111488,43111552⟩ : DyadicInterval 40),(⟨-43113216,-43113152⟩ : DyadicInterval 40),(⟨762123382725,762123402054⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53927296,53927360⟩ : DyadicInterval 40),(⟨-53930048,-53929984⟩ : DyadicInterval 40),(⟨762123382282,762123401611⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2688,-1664⟩ : DyadicInterval 40),(⟨762123384448,762123404224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169431810026,169556333918⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157580367104,157580367168⟩ : DyadicInterval 40),(⟨-184004345664,-184004345600⟩ : DyadicInterval 40),(⟨749016726125,749016745455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157688259008,157688259072⟩ : DyadicInterval 40),(⟨-184151563840,-184151563776⟩ : DyadicInterval 40),(⟨748997376037,748997395366⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26463304768,-26423978432⟩ : DyadicInterval 40),(⟨775335372832,775355055264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157626261888,157724989312⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184201689920,-184066964736⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1858_ok : ecellOkT e1858 = true := by decide +kernel
theorem e1858_pos {a z : ℝ} (ha1 : ((31569/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1263609/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1858 e1858_ok ha1 ha2 hz1 hz2 hz

-- box ['1263609/8192000', '632229/4096000', '1599/1600', '1999/2000']  interval_lower 38580901/274877906944
noncomputable def e1859 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269110356836,0,true,157724989248,157724989312⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929912898716,0,false,-184201689920,-184201689856⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1269224307688,0,true,157823707776,157823707840⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929798947864,0,false,-184336431488,-184336431424⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269004357630,0,true,157633151552,157633151616⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨930018897922,0,false,-184076365568,-184076365504⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269139451349,0,true,157750195392,157750195456⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929883804203,0,false,-184236091264,-184236091200⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554770150,0,true,43141504,43141568⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468485402,0,false,-43143232,-43143168⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565593952,0,true,53964800,53964864⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457661600,0,false,-53967552,-53967488⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625127,0,false,-2688,-2624⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626084,0,false,-1728,-1664⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269057353041,0,true,157679067712,157679067776⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929965902511,0,false,-184139020992,-184139020928⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269181884062,0,true,157786956160,157786956224⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929841371490,0,false,-184286265600,-184286265536⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073329098059,0,false,-26499309440,-26499309376⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073367517765,0,false,-26459953216,-26459953152⟩
    { al := (1263609/8192000), au := (632229/4096000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨169598729060,169712679912⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157724989248,157724989312⟩ : DyadicInterval 40),(⟨-184201689920,-184201689856⟩ : DyadicInterval 40),(⟨748990784843,748990804173⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157823707776,157823707840⟩ : DyadicInterval 40),(⟨-184336431488,-184336431424⟩ : DyadicInterval 40),(⟨748973060509,748973079838⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157633151552,157633151616⟩ : DyadicInterval 40),(⟨-184076365568,-184076365504⟩ : DyadicInterval 40),(⟨749007261421,749007280750⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157750195392,157750195456⟩ : DyadicInterval 40),(⟨-184236091264,-184236091200⟩ : DyadicInterval 40),(⟨748986260540,748986279869⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨43142374,53966176⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43141504,43141568⟩ : DyadicInterval 40),(⟨-43143232,-43143168⟩ : DyadicInterval 40),(⟨762123382723,762123402052⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53964800,53964864⟩ : DyadicInterval 40),(⟨-53967552,-53967488⟩ : DyadicInterval 40),(⟨762123382279,762123401608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2688,-1664⟩ : DyadicInterval 40),(⟨762123384448,762123404224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨169545725265,169670256286⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157679067712,157679067776⟩ : DyadicInterval 40),(⟨-184139020992,-184139020928⟩ : DyadicInterval 40),(⟨748999025097,748999044426⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨157786956160,157786956224⟩ : DyadicInterval 40),(⟨-184286265600,-184286265536⟩ : DyadicInterval 40),(⟨748979660640,748979679969⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26499309440,-26459953152⟩ : DyadicInterval 40),(⟨775353360192,775373057600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨157724989248,157823707840⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-184336431488,-184201689856⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1859_ok : ecellOkT e1859 = true := by decide +kernel
theorem e1859_pos {a z : ℝ} (ha1 : ((1263609/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((632229/4096000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1859 e1859_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B030

end


