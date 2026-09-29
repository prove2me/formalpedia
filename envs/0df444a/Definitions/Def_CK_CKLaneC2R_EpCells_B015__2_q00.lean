-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B015__2_q00
-- name    : CK_CKLaneC2R_EpCells_B015__2_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T18:39:25.102822+00:00
-- url     : https://prove2.me/theorems/d52cc313-80e7-4592-9a41-0794ce8df939
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B015 (+1 modules: CKLaneC2R.EpCells.B016) (piece 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B015 (+1 modules: CKLaneC2R.EpCells.B016) (piece 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B015 (+1 modules: CKLaneC2R.EpCells.B016) (piece 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B015 (+1 modules: CKLaneC2R.EpCells.B016) (piece 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B015 (+1 modules: CKLaneC2R/EpCells/B016) (piece 1 of 2).lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheckT

-- ===== source module CKLaneC2R.EpCells.B015 =====
section

namespace CKLaneC2R.EpCells.B015

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['766371/4096000', '38361/204800', '3997/4000', '1999/2000']  interval_lower 60515369/274877906944
noncomputable def e900 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1305232776626,0,true,188583057088,188583057152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨893790478926,0,false,-227763835200,-227763835136⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1305460678329,0,true,188775021824,188775021888⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨893562577223,0,false,-228044228160,-228044228096⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1305078485764,0,true,188453076736,188453076800⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨893944769788,0,false,-227574048064,-227574048000⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1305357703804,0,true,188688289152,188688289216⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨893665551748,0,false,-227917527296,-227917527232⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564397242,0,true,52768192,52768256⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458858310,0,false,-52770752,-52770688⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590875432,0,true,79244800,79244864⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432380120,0,false,-79250560,-79250496⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622064,0,false,-5760,-5696⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625244,0,false,-2560,-2496⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1305155626654,0,true,188518065024,188518065088⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨893867628898,0,false,-227668931968,-227668931904⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1305409199903,0,true,188731663808,188731663872⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨893614055649,0,false,-227980886784,-227980886720⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1060954682004,0,false,-39249222912,-39249222848⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1061049593173,0,false,-39150866944,-39150866880⟩
    { al := (766371/4096000), au := (38361/204800), zl := (3997/4000), zu := (1999/2000),
      A := ⟨205721148850,205949050553⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188583057088,188583057152⟩ : DyadicInterval 40),(⟨-227763835200,-227763835136⟩ : DyadicInterval 40),(⟨742764043092,742764062421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188775021824,188775021888⟩ : DyadicInterval 40),(⟨-228044228160,-228044228096⟩ : DyadicInterval 40),(⟨742720869413,742720888742⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188453076736,188453076800⟩ : DyadicInterval 40),(⟨-227574048064,-227574048000⟩ : DyadicInterval 40),(⟨742793244177,742793263506⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188688289152,188688289216⟩ : DyadicInterval 40),(⟨-227917527296,-227917527232⟩ : DyadicInterval 40),(⟨742740382953,742740402282⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨52769466,79247656⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52768192,52768256⟩ : DyadicInterval 40),(⟨-52770752,-52770688⟩ : DyadicInterval 40),(⟨762123382299,762123401628⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79244800,79244864⟩ : DyadicInterval 40),(⟨-79250560,-79250496⟩ : DyadicInterval 40),(⟨762123380719,762123400049⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5760,-2496⟩ : DyadicInterval 40),(⟨762123384864,762123405760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨205643998878,205897572127⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188518065024,188518065088⟩ : DyadicInterval 40),(⟨-227668931968,-227668931904⟩ : DyadicInterval 40),(⟨742778647295,742778666625⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188731663808,188731663872⟩ : DyadicInterval 40),(⟨-227980886784,-227980886720⟩ : DyadicInterval 40),(⟨742730625748,742730645078⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39249222912,-39150866880⟩ : DyadicInterval 40),(⟨781698817056,781748014336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨188583057088,188775021888⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-228044228160,-227763835136⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e900_ok : ecellOkT e900 = true := by decide +kernel
theorem e900_pos {a z : ℝ} (ha1 : ((766371/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((38361/204800 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e900 e900_ok ha1 ha2 hz1 hz2 hz

-- box ['47739/256000', '764673/4096000', '1999/2000', '3999/4000']  interval_lower 230504205/1099511627776
noncomputable def e901 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1304549071519,0,true,188006961600,188006961664⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨894474184033,0,false,-226923085248,-226923085184⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1304776973222,0,true,188199027008,188199027072⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨894246282330,0,false,-227203263808,-227203263744⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1304446552797,0,true,187920552512,187920552576⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨894576702755,0,false,-226797073664,-226797073600⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1304725656886,0,true,188155782784,188155782848⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨894297598666,0,false,-227140170112,-227140170048⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537920292,0,true,26292160,26292224⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485335260,0,false,-26292864,-26292800⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564275421,0,true,52646336,52646400⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458980131,0,false,-52648960,-52648896⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625255,0,false,-2560,-2496⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627148,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1304497807216,0,true,187963753728,187963753792⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨894525448336,0,false,-226860071552,-226860071488⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1304751323645,0,true,188177412352,188177412416⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨894271931907,0,false,-227171727104,-227171727040⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1061200679809,0,false,-38994314688,-38994314624⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1061295266348,0,false,-38896317824,-38896317760⟩
    { al := (47739/256000), au := (764673/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨205037443743,205265345446⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188006961600,188006961664⟩ : DyadicInterval 40),(⟨-226923085248,-226923085184⟩ : DyadicInterval 40),(⟨742893270558,742893289887⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188199027008,188199027072⟩ : DyadicInterval 40),(⟨-227203263808,-227203263744⟩ : DyadicInterval 40),(⟨742850243660,742850262989⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187920552512,187920552576⟩ : DyadicInterval 40),(⟨-226797073664,-226797073600⟩ : DyadicInterval 40),(⟨742912609648,742912628977⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188155782784,188155782848⟩ : DyadicInterval 40),(⟨-227140170112,-227140170048⟩ : DyadicInterval 40),(⟨742859936250,742859955579⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨26292516,52647645⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26292160,26292224⟩ : DyadicInterval 40),(⟨-26292864,-26292800⟩ : DyadicInterval 40),(⟨762123383275,762123402604⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52646336,52646400⟩ : DyadicInterval 40),(⟨-52648960,-52648896⟩ : DyadicInterval 40),(⟨762123382343,762123401672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2560,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨204986179440,205239695869⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187963753728,187963753792⟩ : DyadicInterval 40),(⟨-226860071552,-226860071488⟩ : DyadicInterval 40),(⟨742902942270,742902961600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188177412352,188177412416⟩ : DyadicInterval 40),(⟨-227171727104,-227171727040⟩ : DyadicInterval 40),(⟨742855088654,742855107983⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-38994314688,-38896317760⟩ : DyadicInterval 40),(⟨781571542496,781620560224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨188006961600,188199027072⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-227203263808,-226923085184⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e901_ok : ecellOkT e901 = true := by decide +kernel
theorem e901_pos {a z : ℝ} (ha1 : ((47739/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((764673/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e901 e901_ok ha1 ha2 hz1 hz2 hz

-- box ['764673/4096000', '382761/2048000', '1999/2000', '3999/4000']  interval_lower 58527815/274877906944
noncomputable def e902 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1304776973221,0,true,188199027008,188199027072⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨894246282331,0,false,-227203263808,-227203263744⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1305004874925,0,true,188391058816,188391058880⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨894018380627,0,false,-227483513792,-227483513728⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1304674340548,0,true,188112536896,188112536960⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨894348915004,0,false,-227077080064,-227077080000⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1304953501614,0,true,188347774144,188347774208⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨894069753938,0,false,-227420333952,-227420333888⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537951040,0,true,26322944,26323008⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485304512,0,false,-26323584,-26323520⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564336930,0,true,52707840,52707904⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458918622,0,false,-52710464,-52710400⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625249,0,false,-2560,-2496⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627146,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1304725651937,0,true,188155778624,188155778688⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨894297603615,0,false,-227140164032,-227140163968⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1304979196861,0,true,188369423936,188369424000⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨894044058691,0,false,-227451934016,-227451933952⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1061115560941,0,false,-39082510016,-39082509952⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1061210263199,0,false,-38984385344,-38984385280⟩
    { al := (764673/4096000), au := (382761/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨205265345445,205493247149⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188199027008,188199027072⟩ : DyadicInterval 40),(⟨-227203263808,-227203263744⟩ : DyadicInterval 40),(⟨742850243660,742850262989⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188391058816,188391058880⟩ : DyadicInterval 40),(⟨-227483513792,-227483513728⟩ : DyadicInterval 40),(⟨742807167854,742807187183⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188112536896,188112536960⟩ : DyadicInterval 40),(⟨-227077080064,-227077080000⟩ : DyadicInterval 40),(⟨742869626348,742869645678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188347774144,188347774208⟩ : DyadicInterval 40),(⟨-227420333952,-227420333888⟩ : DyadicInterval 40),(⟨742816882237,742816901566⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨26323264,52709154⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26322944,26323008⟩ : DyadicInterval 40),(⟨-26323584,-26323520⟩ : DyadicInterval 40),(⟨762123383241,762123402570⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52707840,52707904⟩ : DyadicInterval 40),(⟨-52710464,-52710400⟩ : DyadicInterval 40),(⟨762123382337,762123401666⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2560,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨205214024161,205467569085⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188155778624,188155778688⟩ : DyadicInterval 40),(⟨-227140164032,-227140163968⟩ : DyadicInterval 40),(⟨742859937180,742859956509⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188369423936,188369424000⟩ : DyadicInterval 40),(⟨-227451934016,-227451933952⟩ : DyadicInterval 40),(⟨742812023742,742812043072⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39082510016,-38984385280⟩ : DyadicInterval 40),(⟨781615576256,781664657888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨188199027008,188391058880⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-227483513792,-227203263744⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e902_ok : ecellOkT e902 = true := by decide +kernel
theorem e902_pos {a z : ℝ} (ha1 : ((764673/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((382761/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e902 e902_ok ha1 ha2 hz1 hz2 hz

-- box ['47739/256000', '764673/4096000', '3999/4000', '1']  interval_lower 229824179/1099511627776
noncomputable def e903 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1304549071519,0,true,188006961600,188006961664⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨894474184033,0,false,-226923085248,-226923085184⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1304776973222,0,true,188199027008,188199027072⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨894246282330,0,false,-227203263808,-227203263744⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1304497812158,0,true,187963757888,187963757952⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨894525443394,0,false,-226860077632,-226860077568⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537951899,0,true,26323776,26323840⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485303653,0,false,-26324480,-26324416⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627145,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1304523436648,0,true,187985355584,187985355648⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨894499818904,0,false,-226891574592,-226891574528⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1304776981733,0,true,188199034176,188199034240⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨894246273819,0,false,-227203274240,-227203274176⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1061191100306,0,false,-39004240064,-39004240000⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1061285709364,0,false,-38906218944,-38906218880⟩
    { al := (47739/256000), au := (764673/4096000), zl := (3999/4000), zu := 1,
      A := ⟨205037443743,205265345446⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188006961600,188006961664⟩ : DyadicInterval 40),(⟨-226923085248,-226923085184⟩ : DyadicInterval 40),(⟨742893270558,742893289887⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188199027008,188199027072⟩ : DyadicInterval 40),(⟨-227203263808,-227203263744⟩ : DyadicInterval 40),(⟨742850243660,742850262989⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187963757888,187963757952⟩ : DyadicInterval 40),(⟨-226860077632,-226860077568⟩ : DyadicInterval 40),(⟨742902941343,742902960673⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188199027008,188199027072⟩ : DyadicInterval 40),(⟨-227203263808,-227203263744⟩ : DyadicInterval 40),(⟨742850243660,742850262989⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,26324123⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26323776,26323840⟩ : DyadicInterval 40),(⟨-26324480,-26324416⟩ : DyadicInterval 40),(⟨762123383273,762123402602⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨205011808872,205265353957⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨187985355584,187985355648⟩ : DyadicInterval 40),(⟨-226891574592,-226891574528⟩ : DyadicInterval 40),(⟨742898107231,742898126560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188199034176,188199034240⟩ : DyadicInterval 40),(⟨-227203274240,-227203274176⟩ : DyadicInterval 40),(⟨742850242041,742850261371⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39004240064,-38906218880⟩ : DyadicInterval 40),(⟨781576493056,781625522912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨188006961600,188199027072⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-227203263808,-226923085184⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e903_ok : ecellOkT e903 = true := by decide +kernel
theorem e903_pos {a z : ℝ} (ha1 : ((47739/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((764673/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e903 e903_ok ha1 ha2 hz1 hz2 hz

-- box ['764673/4096000', '382761/2048000', '3999/4000', '1']  interval_lower 233428593/1099511627776
noncomputable def e904 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1304776973221,0,true,188199027008,188199027072⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨894246282331,0,false,-227203263808,-227203263744⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1305004874925,0,true,188391058816,188391058880⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨894018380627,0,false,-227483513792,-227483513728⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1304725656884,0,true,188155782784,188155782848⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨894297598668,0,false,-227140170112,-227140170048⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537982653,0,true,26354560,26354624⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485272899,0,false,-26355200,-26355136⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627144,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1304751309861,0,true,188177400704,188177400768⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨894271945691,0,false,-227171710144,-227171710080⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1305004883436,0,true,188391065984,188391066048⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨894018372116,0,false,-227483524288,-227483524224⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1061105960155,0,false,-39092458240,-39092458176⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1061200684956,0,false,-38994309376,-38994309312⟩
    { al := (764673/4096000), au := (382761/2048000), zl := (3999/4000), zu := 1,
      A := ⟨205265345445,205493247149⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188199027008,188199027072⟩ : DyadicInterval 40),(⟨-227203263808,-227203263744⟩ : DyadicInterval 40),(⟨742850243660,742850262989⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188391058816,188391058880⟩ : DyadicInterval 40),(⟨-227483513792,-227483513728⟩ : DyadicInterval 40),(⟨742807167854,742807187183⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188155782784,188155782848⟩ : DyadicInterval 40),(⟨-227140170112,-227140170048⟩ : DyadicInterval 40),(⟨742859936250,742859955579⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188391058816,188391058880⟩ : DyadicInterval 40),(⟨-227483513792,-227483513728⟩ : DyadicInterval 40),(⟨742807167854,742807187183⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,26354877⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26354560,26354624⟩ : DyadicInterval 40),(⟨-26355200,-26355136⟩ : DyadicInterval 40),(⟨762123383240,762123402569⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨205239682085,205493255660⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188177400704,188177400768⟩ : DyadicInterval 40),(⟨-227171710144,-227171710080⟩ : DyadicInterval 40),(⟨742855091271,742855110601⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188391065984,188391066048⟩ : DyadicInterval 40),(⟨-227483524288,-227483524224⟩ : DyadicInterval 40),(⟨742807166258,742807185587⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39092458240,-38994309312⟩ : DyadicInterval 40),(⟨781620538272,781669632000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨188199027008,188391058880⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-227483513792,-227203263744⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e904_ok : ecellOkT e904 = true := by decide +kernel
theorem e904_pos {a z : ℝ} (ha1 : ((764673/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((382761/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e904 e904_ok ha1 ha2 hz1 hz2 hz

-- box ['382761/2048000', '766371/4096000', '1999/2000', '3999/4000']  interval_lower 59433627/274877906944
noncomputable def e905 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1305004874924,0,true,188391058816,188391058880⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨894018380628,0,false,-227483513792,-227483513728⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1305232776627,0,true,188583057088,188583057152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨893790478925,0,false,-227763835200,-227763835136⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1304902128300,0,true,188304487808,188304487872⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨894121127252,0,false,-227357157760,-227357157696⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1305181346340,0,true,188539732032,188539732096⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨893841909212,0,false,-227700569216,-227700569152⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537981794,0,true,26353664,26353728⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485273758,0,false,-26354368,-26354304⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564398449,0,true,52769344,52769408⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458857103,0,false,-52771968,-52771904⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625243,0,false,-2560,-2496⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627145,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1304953496662,0,true,188347769984,188347770048⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨894069758890,0,false,-227420327872,-227420327808⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1305207070078,0,true,188561401984,188561402048⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨893816185474,0,false,-227732212352,-227732212288⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1061030347619,0,false,-39170810304,-39170810240⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1061125165619,0,false,-39072557824,-39072557760⟩
    { al := (382761/2048000), au := (766371/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨205493247148,205721148851⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188391058816,188391058880⟩ : DyadicInterval 40),(⟨-227483513792,-227483513728⟩ : DyadicInterval 40),(⟨742807167854,742807187184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188583057088,188583057152⟩ : DyadicInterval 40),(⟨-227763835200,-227763835136⟩ : DyadicInterval 40),(⟨742764043092,742764062421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188304487808,188304487872⟩ : DyadicInterval 40),(⟨-227357157760,-227357157696⟩ : DyadicInterval 40),(⟨742826594117,742826613446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188539732032,188539732096⟩ : DyadicInterval 40),(⟨-227700569216,-227700569152⟩ : DyadicInterval 40),(⟨742773779281,742773798611⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨26354018,52770673⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26353664,26353728⟩ : DyadicInterval 40),(⟨-26354368,-26354304⟩ : DyadicInterval 40),(⟨762123383272,762123402601⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52769344,52769408⟩ : DyadicInterval 40),(⟨-52771968,-52771904⟩ : DyadicInterval 40),(⟨762123382331,762123401660⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2560,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨205441868886,205695442302⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188347769984,188347770048⟩ : DyadicInterval 40),(⟨-227420327872,-227420327808⟩ : DyadicInterval 40),(⟨742816883170,742816902500⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188561401984,188561402048⟩ : DyadicInterval 40),(⟨-227732212352,-227732212288⟩ : DyadicInterval 40),(⟨742768909899,742768929229⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39170810304,-39072557760⟩ : DyadicInterval 40),(⟨781659662496,781708808032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨188391058816,188583057152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-227763835200,-227483513728⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e905_ok : ecellOkT e905 = true := by decide +kernel
theorem e905_pos {a z : ℝ} (ha1 : ((382761/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((766371/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e905 e905_ok ha1 ha2 hz1 hz2 hz

-- box ['766371/4096000', '38361/204800', '1999/2000', '3999/4000']  interval_lower 120687003/549755813888
noncomputable def e906 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1305232776626,0,true,188583057088,188583057152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨893790478926,0,false,-227763835200,-227763835136⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1305460678329,0,true,188775021824,188775021888⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨893562577223,0,false,-228044228160,-228044228096⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1305129916051,0,true,188496405248,188496405312⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨893893339501,0,false,-227637306816,-227637306752⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1305409191067,0,true,188731656320,188731656384⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨893614064485,0,false,-227980875904,-227980875840⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538012553,0,true,26384448,26384512⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485242999,0,false,-26385152,-26385088⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564459979,0,true,52830912,52830976⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458795573,0,false,-52833536,-52833472⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625237,0,false,-2560,-2496⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627143,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1305181341387,0,true,188539727808,188539727872⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨893841914165,0,false,-227700563136,-227700563072⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1305434943285,0,true,188753346560,188753346624⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨893588312267,0,false,-228012562112,-228012562048⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1060945039848,0,false,-39259215552,-39259215488⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1061039973609,0,false,-39160835264,-39160835200⟩
    { al := (766371/4096000), au := (38361/204800), zl := (1999/2000), zu := (3999/4000),
      A := ⟨205721148850,205949050553⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188583057088,188583057152⟩ : DyadicInterval 40),(⟨-227763835200,-227763835136⟩ : DyadicInterval 40),(⟨742764043092,742764062421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188775021824,188775021888⟩ : DyadicInterval 40),(⟨-228044228160,-228044228096⟩ : DyadicInterval 40),(⟨742720869413,742720888742⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188496405248,188496405312⟩ : DyadicInterval 40),(⟨-227637306816,-227637306752⟩ : DyadicInterval 40),(⟨742783512968,742783532297⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188731656320,188731656384⟩ : DyadicInterval 40),(⟨-227980875904,-227980875840⟩ : DyadicInterval 40),(⟨742730627446,742730646776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨26384777,52832203⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26384448,26384512⟩ : DyadicInterval 40),(⟨-26385152,-26385088⟩ : DyadicInterval 40),(⟨762123383270,762123402599⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52830912,52830976⟩ : DyadicInterval 40),(⟨-52833536,-52833472⟩ : DyadicInterval 40),(⟨762123382325,762123401654⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2560,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨205669713611,205923315509⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188539727808,188539727872⟩ : DyadicInterval 40),(⟨-227700563136,-227700563072⟩ : DyadicInterval 40),(⟨742773780255,742773799584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188753346560,188753346624⟩ : DyadicInterval 40),(⟨-228012562112,-228012562048⟩ : DyadicInterval 40),(⟨742725747078,742725766407⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39259215552,-39160835200⟩ : DyadicInterval 40),(⟨781703801216,781753010656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨188583057088,188775021888⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-228044228160,-227763835136⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e906_ok : ecellOkT e906 = true := by decide +kernel
theorem e906_pos {a z : ℝ} (ha1 : ((766371/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((38361/204800 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e906 e906_ok ha1 ha2 hz1 hz2 hz

-- box ['382761/2048000', '766371/4096000', '3999/4000', '1']  interval_lower 237049271/1099511627776
noncomputable def e907 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1305004874924,0,true,188391058816,188391058880⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨894018380628,0,false,-227483513792,-227483513728⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1305232776627,0,true,188583057088,188583057152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨893790478925,0,false,-227763835200,-227763835136⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1304953501612,0,true,188347774144,188347774208⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨894069753940,0,false,-227420333952,-227420333888⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538013414,0,true,26385280,26385344⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485242138,0,false,-26385984,-26385920⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627142,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1304979183072,0,true,188369412288,188369412352⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨894044072480,0,false,-227451917056,-227451916992⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1305232785139,0,true,188583064256,188583064320⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨893790470413,0,false,-227763845696,-227763845632⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1061020725526,0,false,-39180781440,-39180781376⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1061115566095,0,false,-39082504704,-39082504640⟩
    { al := (382761/2048000), au := (766371/4096000), zl := (3999/4000), zu := 1,
      A := ⟨205493247148,205721148851⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188391058816,188391058880⟩ : DyadicInterval 40),(⟨-227483513792,-227483513728⟩ : DyadicInterval 40),(⟨742807167854,742807187184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188583057088,188583057152⟩ : DyadicInterval 40),(⟨-227763835200,-227763835136⟩ : DyadicInterval 40),(⟨742764043092,742764062421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188347774144,188347774208⟩ : DyadicInterval 40),(⟨-227420333952,-227420333888⟩ : DyadicInterval 40),(⟨742816882238,742816901567⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188583057088,188583057152⟩ : DyadicInterval 40),(⟨-227763835200,-227763835136⟩ : DyadicInterval 40),(⟨742764043092,742764062421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,26385638⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26385280,26385344⟩ : DyadicInterval 40),(⟨-26385984,-26385920⟩ : DyadicInterval 40),(⟨762123383270,762123402599⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨205467555296,205721157363⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188369412288,188369412352⟩ : DyadicInterval 40),(⟨-227451917056,-227451916992⟩ : DyadicInterval 40),(⟨742812026367,742812045696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188583064256,188583064320⟩ : DyadicInterval 40),(⟨-227763845696,-227763845632⟩ : DyadicInterval 40),(⟨742764041492,742764060821⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39180781440,-39082504640⟩ : DyadicInterval 40),(⟨781664635936,781713793600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨188391058816,188583057152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-227763835200,-227483513728⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e907_ok : ecellOkT e907 = true := by decide +kernel
theorem e907_pos {a z : ℝ} (ha1 : ((382761/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((766371/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e907 e907_ok ha1 ha2 hz1 hz2 hz

-- box ['766371/4096000', '38361/204800', '3999/4000', '1']  interval_lower 120343039/549755813888
noncomputable def e908 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1305232776626,0,true,188583057088,188583057152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨893790478926,0,false,-227763835200,-227763835136⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1305460678329,0,true,188775021824,188775021888⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨893562577223,0,false,-228044228160,-228044228096⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1305181346338,0,true,188539732032,188539732096⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨893841909214,0,false,-227700569216,-227700569152⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538044180,0,true,26416064,26416128⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485211372,0,false,-26416768,-26416704⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627141,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1305207056284,0,true,188561390400,188561390464⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨893816199268,0,false,-227732195392,-227732195328⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1305460686834,0,true,188775028992,188775029056⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨893562568718,0,false,-228044238592,-228044238528⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1060935396424,0,false,-39269209600,-39269209536⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1061030352781,0,false,-39170804928,-39170804864⟩
    { al := (766371/4096000), au := (38361/204800), zl := (3999/4000), zu := 1,
      A := ⟨205721148850,205949050553⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188583057088,188583057152⟩ : DyadicInterval 40),(⟨-227763835200,-227763835136⟩ : DyadicInterval 40),(⟨742764043092,742764062421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188775021824,188775021888⟩ : DyadicInterval 40),(⟨-228044228160,-228044228096⟩ : DyadicInterval 40),(⟨742720869413,742720888742⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188539732032,188539732096⟩ : DyadicInterval 40),(⟨-227700569216,-227700569152⟩ : DyadicInterval 40),(⟨742773779282,742773798611⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188775021824,188775021888⟩ : DyadicInterval 40),(⟨-228044228160,-228044228096⟩ : DyadicInterval 40),(⟨742720869413,742720888742⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,26416404⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26416064,26416128⟩ : DyadicInterval 40),(⟨-26416768,-26416704⟩ : DyadicInterval 40),(⟨762123383269,762123402598⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨205695428508,205949059058⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188561390400,188561390464⟩ : DyadicInterval 40),(⟨-227732195392,-227732195328⟩ : DyadicInterval 40),(⟨742768912493,742768931822⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188775028992,188775029056⟩ : DyadicInterval 40),(⟨-228044238592,-228044238528⟩ : DyadicInterval 40),(⟨742720867784,742720887114⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39269209600,-39170804864⟩ : DyadicInterval 40),(⟨781708786048,781758007680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨188583057088,188775021888⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-228044228160,-227763835136⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e908_ok : ecellOkT e908 = true := by decide +kernel
theorem e908_pos {a z : ℝ} (ha1 : ((766371/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((38361/204800 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e908 e908_ok ha1 ha2 hz1 hz2 hz

-- box ['38361/204800', '768069/4096000', '999/1000', '3997/4000']  interval_lower 123204515/549755813888
noncomputable def e909 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1305460678328,0,true,188775021824,188775021888⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨893562577224,0,false,-228044228160,-228044228096⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1305688580031,0,true,188966953088,188966953152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨893334675521,0,false,-228324692608,-228324692544⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1305254729277,0,true,188601549568,188601549632⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨893768526275,0,false,-227790840960,-227790840896⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1305533947317,0,true,188836730240,188836730304⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨893489308235,0,false,-228134387904,-228134387840⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590873875,0,true,79243200,79243264⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432381677,0,false,-79248960,-79248896⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099617413615,0,true,105780736,105780800⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099405841937,0,false,-105790976,-105790912⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511617598,0,false,-10240,-10176⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622065,0,false,-5760,-5696⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1305357699831,0,true,188688285760,188688285824⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨893665555721,0,false,-227917522368,-227917522304⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1305611272929,0,true,188901851392,188901851456⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨893411982623,0,false,-228229547520,-228229547456⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1060878963364,0,false,-39327696128,-39327696064⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1060973967683,0,false,-39229236544,-39229236480⟩
    { al := (38361/204800), au := (768069/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨205949050552,206176952255⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188775021824,188775021888⟩ : DyadicInterval 40),(⟨-228044228160,-228044228096⟩ : DyadicInterval 40),(⟨742720869413,742720888743⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188966953088,188966953152⟩ : DyadicInterval 40),(⟨-228324692608,-228324692544⟩ : DyadicInterval 40),(⟨742677646741,742677666071⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188601549568,188601549632⟩ : DyadicInterval 40),(⟨-227790840960,-227790840896⟩ : DyadicInterval 40),(⟨742759886512,742759905841⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188836730240,188836730304⟩ : DyadicInterval 40),(⟨-228134387904,-228134387840⟩ : DyadicInterval 40),(⟨742706978887,742706998217⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨79246099,105785839⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79243200,79243264⟩ : DyadicInterval 40),(⟨-79248960,-79248896⟩ : DyadicInterval 40),(⟨762123380720,762123400049⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨105780736,105780800⟩ : DyadicInterval 40),(⟨-105790976,-105790912⟩ : DyadicInterval 40),(⟨762123378493,762123397823⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-10240,-5696⟩ : DyadicInterval 40),(⟨762123386464,762123408000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨205846072055,206099645153⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188688285760,188688285824⟩ : DyadicInterval 40),(⟨-227917522368,-227917522304⟩ : DyadicInterval 40),(⟨742740383716,742740403046⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188901851392,188901851456⟩ : DyadicInterval 40),(⟨-228229547520,-228229547456⟩ : DyadicInterval 40),(⟨742692313869,742692333199⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39327696128,-39229236480⟩ : DyadicInterval 40),(⟨781738001856,781787250944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨188775021824,188966953152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-228324692608,-228044228096⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e909_ok : ecellOkT e909 = true := by decide +kernel
theorem e909_pos {a z : ℝ} (ha1 : ((38361/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((768069/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e909 e909_ok ha1 ha2 hz1 hz2 hz

-- box ['768069/4096000', '384459/2048000', '999/1000', '3997/4000']  interval_lower 125043121/549755813888
noncomputable def e910 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1305688580030,0,true,188966953088,188966953152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨893334675522,0,false,-228324692608,-228324692544⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1305916481733,0,true,189158850880,189158850944⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨893106773819,0,false,-228605228608,-228605228544⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1305482403077,0,true,188793319168,188793319232⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨893540852475,0,false,-228070960384,-228070960320⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1305761678093,0,true,189028506752,189028506816⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨893261577459,0,false,-228414664960,-228414664896⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590966181,0,true,79335488,79335552⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432289371,0,false,-79341312,-79341248⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099617536712,0,true,105903808,105903872⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099405718840,0,false,-105914048,-105913984⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511617574,0,false,-10240,-10176⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622052,0,false,-5760,-5696⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1305585487580,0,true,188880136192,188880136256⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨893437767972,0,false,-228197814272,-228197814208⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1305839089171,0,true,189093688512,189093688576⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨893184166381,0,false,-228509954048,-228509953984⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1060793509431,0,false,-39416265472,-39416265408⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1060888629509,0,false,-39317678016,-39317677952⟩
    { al := (768069/4096000), au := (384459/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨206176952254,206404853957⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188966953088,188966953152⟩ : DyadicInterval 40),(⟨-228324692608,-228324692544⟩ : DyadicInterval 40),(⟨742677646742,742677666071⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189158850880,189158850944⟩ : DyadicInterval 40),(⟨-228605228608,-228605228544⟩ : DyadicInterval 40),(⟨742634375092,742634394422⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188793319168,188793319232⟩ : DyadicInterval 40),(⟨-228070960384,-228070960320⟩ : DyadicInterval 40),(⟨742716751303,742716770632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189028506752,189028506816⟩ : DyadicInterval 40),(⟨-228414664960,-228414664896⟩ : DyadicInterval 40),(⟨742663772954,742663792283⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨79338405,105908936⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79335488,79335552⟩ : DyadicInterval 40),(⟨-79341312,-79341248⟩ : DyadicInterval 40),(⟨762123380738,762123400068⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨105903808,105903872⟩ : DyadicInterval 40),(⟨-105914048,-105913984⟩ : DyadicInterval 40),(⟨762123378469,762123397799⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-10240,-5696⟩ : DyadicInterval 40),(⟨762123386464,762123408000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨206073859804,206327461395⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188880136192,188880136256⟩ : DyadicInterval 40),(⟨-228197814272,-228197814208⟩ : DyadicInterval 40),(⟨742697204789,742697224118⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189093688512,189093688576⟩ : DyadicInterval 40),(⟨-228509954048,-228509953984⟩ : DyadicInterval 40),(⟨742649075105,742649094435⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39416265472,-39317677952⟩ : DyadicInterval 40),(⟨781782222592,781831535616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨188966953088,189158850944⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-228605228608,-228324692544⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e910_ok : ecellOkT e910 = true := by decide +kernel
theorem e910_pos {a z : ℝ} (ha1 : ((768069/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((384459/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e910 e910_ok ha1 ha2 hz1 hz2 hz

-- box ['38361/204800', '768069/4096000', '3997/4000', '1999/2000']  interval_lower 245719487/1099511627776
noncomputable def e911 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1305460678328,0,true,188775021824,188775021888⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨893562577224,0,false,-228044228160,-228044228096⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1305688580031,0,true,188966953088,188966953152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨893334675521,0,false,-228324692608,-228324692544⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1305306216540,0,true,188644920192,188644920256⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨893717039012,0,false,-227854182272,-227854182208⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1305585491556,0,true,188880139584,188880139648⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨893437763996,0,false,-228197819136,-228197819072⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564458770,0,true,52829696,52829760⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458796782,0,false,-52832320,-52832256⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590967742,0,true,79337088,79337152⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432287810,0,false,-79342848,-79342784⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622050,0,false,-5760,-5696⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625238,0,false,-2560,-2496⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1305383442886,0,true,188709969088,188709969152⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨893639812666,0,false,-227949195520,-227949195456⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1305637044636,0,true,188923554624,188923554688⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨893386210916,0,false,-228261264896,-228261264832⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1060869301126,0,false,-39337710272,-39337710208⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1060964328061,0,false,-39239226368,-39239226304⟩
    { al := (38361/204800), au := (768069/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨205949050552,206176952255⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188775021824,188775021888⟩ : DyadicInterval 40),(⟨-228044228160,-228044228096⟩ : DyadicInterval 40),(⟨742720869413,742720888743⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188966953088,188966953152⟩ : DyadicInterval 40),(⟨-228324692608,-228324692544⟩ : DyadicInterval 40),(⟨742677646741,742677666071⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188644920192,188644920256⟩ : DyadicInterval 40),(⟨-227854182272,-227854182208⟩ : DyadicInterval 40),(⟨742750135983,742750155312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188880139584,188880139648⟩ : DyadicInterval 40),(⟨-228197819136,-228197819072⟩ : DyadicInterval 40),(⟨742697203997,742697223326⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨52830994,79339966⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52829696,52829760⟩ : DyadicInterval 40),(⟨-52832320,-52832256⟩ : DyadicInterval 40),(⟨762123382325,762123401654⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79337088,79337152⟩ : DyadicInterval 40),(⟨-79342848,-79342784⟩ : DyadicInterval 40),(⟨762123380706,762123400036⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5760,-2496⟩ : DyadicInterval 40),(⟨762123384864,762123405760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨205871815110,206125416860⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188709969088,188709969152⟩ : DyadicInterval 40),(⟨-227949195520,-227949195456⟩ : DyadicInterval 40),(⟨742735506381,742735525710⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188923554624,188923554688⟩ : DyadicInterval 40),(⟨-228261264896,-228261264832⟩ : DyadicInterval 40),(⟨742687424941,742687444271⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39337710272,-39239226304⟩ : DyadicInterval 40),(⟨781742996768,781792258016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨188775021824,188966953152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-228324692608,-228044228096⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e911_ok : ecellOkT e911 = true := by decide +kernel
theorem e911_pos {a z : ℝ} (ha1 : ((38361/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((768069/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e911 e911_ok ha1 ha2 hz1 hz2 hz

-- box ['768069/4096000', '384459/2048000', '3997/4000', '1999/2000']  interval_lower 249394191/1099511627776
noncomputable def e912 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1305688580030,0,true,188966953088,188966953152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨893334675522,0,false,-228324692608,-228324692544⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1305916481733,0,true,189158850880,189158850944⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨893106773819,0,false,-228605228608,-228605228544⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1305533947315,0,true,188836730240,188836730304⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨893489308237,0,false,-228134387904,-228134387840⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1305813279307,0,true,189071956480,189071956544⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨893209976245,0,false,-228478182528,-228478182464⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564520307,0,true,52891200,52891264⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458735245,0,false,-52893824,-52893760⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591060067,0,true,79429376,79429440⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432195485,0,false,-79435200,-79435136⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622037,0,false,-5760,-5696⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625232,0,false,-2560,-2496⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1305611259125,0,true,188901839744,188901839808⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨893411996427,0,false,-228229530560,-228229530496⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1305864889360,0,true,189115411968,189115412032⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨893158366192,0,false,-228541714624,-228541714560⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1060783825822,0,false,-39426302592,-39426302528⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1060878968540,0,false,-39327690752,-39327690688⟩
    { al := (768069/4096000), au := (384459/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨206176952254,206404853957⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188966953088,188966953152⟩ : DyadicInterval 40),(⟨-228324692608,-228324692544⟩ : DyadicInterval 40),(⟨742677646742,742677666071⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189158850880,189158850944⟩ : DyadicInterval 40),(⟨-228605228608,-228605228544⟩ : DyadicInterval 40),(⟨742634375092,742634394422⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188836730240,188836730304⟩ : DyadicInterval 40),(⟨-228134387904,-228134387840⟩ : DyadicInterval 40),(⟨742706978887,742706998217⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189071956480,189071956544⟩ : DyadicInterval 40),(⟨-228478182528,-228478182464⟩ : DyadicInterval 40),(⟨742653976204,742653995534⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨52892531,79432291⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52891200,52891264⟩ : DyadicInterval 40),(⟨-52893824,-52893760⟩ : DyadicInterval 40),(⟨762123382319,762123401648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79429376,79429440⟩ : DyadicInterval 40),(⟨-79435200,-79435136⟩ : DyadicInterval 40),(⟨762123380725,762123400054⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5760,-2496⟩ : DyadicInterval 40),(⟨762123384864,762123405760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨206099631349,206353261584⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188901839744,188901839808⟩ : DyadicInterval 40),(⟨-228229530560,-228229530496⟩ : DyadicInterval 40),(⟨742692316513,742692335842⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189115411968,189115412032⟩ : DyadicInterval 40),(⟨-228541714624,-228541714560⟩ : DyadicInterval 40),(⟨742644175236,742644194565⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39426302592,-39327690688⟩ : DyadicInterval 40),(⟨781787228960,781836554176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨188966953088,189158850944⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-228605228608,-228324692544⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e912_ok : ecellOkT e912 = true := by decide +kernel
theorem e912_pos {a z : ℝ} (ha1 : ((768069/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((384459/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e912 e912_ok ha1 ha2 hz1 hz2 hz

-- box ['384459/2048000', '769767/4096000', '999/1000', '3997/4000']  interval_lower 63445013/274877906944
noncomputable def e913 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1305916481732,0,true,189158850880,189158850944⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨893106773820,0,false,-228605228608,-228605228544⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1306144383435,0,true,189350715136,189350715200⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨892878872117,0,false,-228885836224,-228885836160⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1305710076878,0,true,188985055296,188985055360⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨893313178674,0,false,-228351151104,-228351151040⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1305989408869,0,true,189220249856,189220249920⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨893033846683,0,false,-228695013504,-228695013440⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591058503,0,true,79427840,79427904⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432197049,0,false,-79433600,-79433536⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099617659832,0,true,106026880,106026944⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099405595720,0,false,-106037184,-106037120⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511617550,0,false,-10240,-10176⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622038,0,false,-5760,-5696⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1305813275336,0,true,189071953152,189071953216⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨893209980216,0,false,-228478177600,-228478177536⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1306066905409,0,true,189285492224,189285492288⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨892956350143,0,false,-228790432128,-228790432064⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1060707961093,0,false,-39504939840,-39504939776⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1060803196951,0,false,-39406224448,-39406224384⟩
    { al := (384459/2048000), au := (769767/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨206404853956,206632755659⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189158850880,189158850944⟩ : DyadicInterval 40),(⟨-228605228608,-228605228544⟩ : DyadicInterval 40),(⟨742634375092,742634394422⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189350715136,189350715200⟩ : DyadicInterval 40),(⟨-228885836224,-228885836160⟩ : DyadicInterval 40),(⟨742591054516,742591073846⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188985055296,188985055360⟩ : DyadicInterval 40),(⟨-228351151104,-228351151040⟩ : DyadicInterval 40),(⟨742673567218,742673586548⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189220249856,189220249920⟩ : DyadicInterval 40),(⟨-228695013504,-228695013440⟩ : DyadicInterval 40),(⟨742620518122,742620537451⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨79430727,106032056⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79427840,79427904⟩ : DyadicInterval 40),(⟨-79433600,-79433536⟩ : DyadicInterval 40),(⟨762123380693,762123400022⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨106026880,106026944⟩ : DyadicInterval 40),(⟨-106037184,-106037120⟩ : DyadicInterval 40),(⟨762123378478,762123397808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-10240,-5696⟩ : DyadicInterval 40),(⟨762123386464,762123408000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨206301647560,206555277633⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189071953152,189071953216⟩ : DyadicInterval 40),(⟨-228478177600,-228478177536⟩ : DyadicInterval 40),(⟨742653976933,742653996262⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189285492224,189285492288⟩ : DyadicInterval 40),(⟨-228790432128,-228790432064⟩ : DyadicInterval 40),(⟨742605787392,742605806721⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39504939840,-39406224384⟩ : DyadicInterval 40),(⟨781826495808,781875872800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨189158850880,189350715200⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-228885836224,-228605228544⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e913_ok : ecellOkT e913 = true := by decide +kernel
theorem e913_pos {a z : ℝ} (ha1 : ((384459/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((769767/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e913 e913_ok ha1 ha2 hz1 hz2 hz

-- box ['769767/4096000', '96327/512000', '999/1000', '3997/4000']  interval_lower 257489673/1099511627776
noncomputable def e914 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1306144383434,0,true,189350715136,189350715200⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨892878872118,0,false,-228885836224,-228885836160⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1306372285137,0,true,189542545920,189542545984⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨892650970415,0,false,-229166515456,-229166515392⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1305937750678,0,true,189176758016,189176758080⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨893085504874,0,false,-228631413312,-228631413248⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1306217139645,0,true,189411959552,189411959616⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨892806115907,0,false,-228975433536,-228975433472⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591150840,0,true,79520128,79520192⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432104712,0,false,-79525952,-79525888⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099617782972,0,true,106150016,106150080⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099405472580,0,false,-106160384,-106160320⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511617526,0,false,-10304,-10240⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622025,0,false,-5760,-5696⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1306041063083,0,true,189263736640,189263736704⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨892982192469,0,false,-228758612480,-228758612416⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1306294721651,0,true,189477262464,189477262528⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨892728533901,0,false,-229070981696,-229070981632⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1060622318347,0,false,-39593719232,-39593719168⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1060717670013,0,false,-39494875776,-39494875712⟩
    { al := (769767/4096000), au := (96327/512000), zl := (999/1000), zu := (3997/4000),
      A := ⟨206632755658,206860657361⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189350715136,189350715200⟩ : DyadicInterval 40),(⟨-228885836224,-228885836160⟩ : DyadicInterval 40),(⟨742591054517,742591073846⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189542545920,189542545984⟩ : DyadicInterval 40),(⟨-229166515456,-229166515392⟩ : DyadicInterval 40),(⟨742547684964,742547704294⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189176758016,189176758080⟩ : DyadicInterval 40),(⟨-228631413312,-228631413248⟩ : DyadicInterval 40),(⟨742630334286,742630353616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189411959552,189411959616⟩ : DyadicInterval 40),(⟨-228975433536,-228975433472⟩ : DyadicInterval 40),(⟨742577214379,742577233708⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨79523064,106155196⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79520128,79520192⟩ : DyadicInterval 40),(⟨-79525952,-79525888⟩ : DyadicInterval 40),(⟨762123380712,762123400041⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨106150016,106150080⟩ : DyadicInterval 40),(⟨-106160384,-106160320⟩ : DyadicInterval 40),(⟨762123378486,762123397816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-10304,-5696⟩ : DyadicInterval 40),(⟨762123386464,762123408032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨206529435307,206783093875⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189263736640,189263736704⟩ : DyadicInterval 40),(⟨-228758612480,-228758612416⟩ : DyadicInterval 40),(⟨742610700192,742610719521⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189477262464,189477262528⟩ : DyadicInterval 40),(⟨-229070981696,-229070981632⟩ : DyadicInterval 40),(⟨742562450727,742562470056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39593719232,-39494875712⟩ : DyadicInterval 40),(⟨781870821472,781920262496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨189350715136,189542545984⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-229166515456,-228885836160⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e914_ok : ecellOkT e914 = true := by decide +kernel
theorem e914_pos {a z : ℝ} (ha1 : ((769767/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((96327/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e914 e914_ok ha1 ha2 hz1 hz2 hz

-- box ['384459/2048000', '769767/4096000', '3997/4000', '1999/2000']  interval_lower 126542479/549755813888
noncomputable def e915 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1305916481732,0,true,189158850880,189158850944⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨893106773820,0,false,-228605228608,-228605228544⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1306144383435,0,true,189350715136,189350715200⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨892878872117,0,false,-228885836224,-228885836160⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1305761678091,0,true,189028506752,189028506816⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨893261577461,0,false,-228414664960,-228414664896⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1306041067058,0,true,189263740032,189263740096⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨892982188494,0,false,-228758617408,-228758617344⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564581857,0,true,52952768,52952832⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458673695,0,false,-52955392,-52955328⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591152408,0,true,79521728,79521792⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432103144,0,false,-79527552,-79527488⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622024,0,false,-5760,-5696⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625226,0,false,-2560,-2496⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1305839075362,0,true,189093676928,189093676992⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨893184180190,0,false,-228509937088,-228509937024⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1306092734091,0,true,189307235840,189307235904⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨892930521461,0,false,-228822235840,-228822235776⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1060698256086,0,false,-39514999936,-39514999872⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1060793514614,0,false,-39416260096,-39416260032⟩
    { al := (384459/2048000), au := (769767/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨206404853956,206632755659⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189158850880,189158850944⟩ : DyadicInterval 40),(⟨-228605228608,-228605228544⟩ : DyadicInterval 40),(⟨742634375092,742634394422⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189350715136,189350715200⟩ : DyadicInterval 40),(⟨-228885836224,-228885836160⟩ : DyadicInterval 40),(⟨742591054516,742591073846⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189028506752,189028506816⟩ : DyadicInterval 40),(⟨-228414664960,-228414664896⟩ : DyadicInterval 40),(⟨742663772955,742663792284⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189263740032,189263740096⟩ : DyadicInterval 40),(⟨-228758617408,-228758617344⟩ : DyadicInterval 40),(⟨742610699423,742610718752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨52954081,79524632⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52952768,52952832⟩ : DyadicInterval 40),(⟨-52955392,-52955328⟩ : DyadicInterval 40),(⟨762123382313,762123401642⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79521728,79521792⟩ : DyadicInterval 40),(⟨-79527552,-79527488⟩ : DyadicInterval 40),(⟨762123380711,762123400041⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5760,-2496⟩ : DyadicInterval 40),(⟨762123384864,762123405760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨206327447586,206581106315⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189093676928,189093676992⟩ : DyadicInterval 40),(⟨-228509937088,-228509937024⟩ : DyadicInterval 40),(⟨742649077718,742649097047⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189307235840,189307235904⟩ : DyadicInterval 40),(⟨-228822235840,-228822235776⟩ : DyadicInterval 40),(⟨742600876564,742600895894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39514999936,-39416260032⟩ : DyadicInterval 40),(⟨781831513632,781880902848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨189158850880,189350715200⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-228885836224,-228605228544⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e915_ok : ecellOkT e915 = true := by decide +kernel
theorem e915_pos {a z : ℝ} (ha1 : ((384459/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((769767/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e915 e915_ok ha1 ha2 hz1 hz2 hz

-- box ['769767/4096000', '96327/512000', '3997/4000', '1999/2000']  interval_lower 256791813/1099511627776
noncomputable def e916 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1306144383434,0,true,189350715136,189350715200⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨892878872118,0,false,-228885836224,-228885836160⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1306372285137,0,true,189542545920,189542545984⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨892650970415,0,false,-229166515456,-229166515392⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1305989408867,0,true,189220249856,189220249920⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨893033846685,0,false,-228695013504,-228695013440⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1306268854809,0,true,189455490048,189455490112⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨892754400743,0,false,-229039123776,-229039123712⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564643417,0,true,53014336,53014400⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458612135,0,false,-53016960,-53016896⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591244765,0,true,79614080,79614144⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432010787,0,false,-79619904,-79619840⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622010,0,false,-5824,-5760⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625220,0,false,-2560,-2496⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1306066891594,0,true,189285480576,189285480640⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨892956363958,0,false,-228790415104,-228790415040⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1306320578817,0,true,189499026304,189499026368⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨892702676735,0,false,-229102828672,-229102828608⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1060612591922,0,false,-39603802368,-39603802304⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1060707966284,0,false,-39504934464,-39504934400⟩
    { al := (769767/4096000), au := (96327/512000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨206632755658,206860657361⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189350715136,189350715200⟩ : DyadicInterval 40),(⟨-228885836224,-228885836160⟩ : DyadicInterval 40),(⟨742591054517,742591073846⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189542545920,189542545984⟩ : DyadicInterval 40),(⟨-229166515456,-229166515392⟩ : DyadicInterval 40),(⟨742547684964,742547704294⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189220249856,189220249920⟩ : DyadicInterval 40),(⟨-228695013504,-228695013440⟩ : DyadicInterval 40),(⟨742620518122,742620537452⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189455490048,189455490112⟩ : DyadicInterval 40),(⟨-229039123776,-229039123712⟩ : DyadicInterval 40),(⟨742567373754,742567393084⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨53015641,79616989⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53014336,53014400⟩ : DyadicInterval 40),(⟨-53016960,-53016896⟩ : DyadicInterval 40),(⟨762123382307,762123401636⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79614080,79614144⟩ : DyadicInterval 40),(⟨-79619904,-79619840⟩ : DyadicInterval 40),(⟨762123380698,762123400028⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5824,-2496⟩ : DyadicInterval 40),(⟨762123384864,762123405792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨206555263818,206808951041⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189285480576,189285480640⟩ : DyadicInterval 40),(⟨-228790415104,-228790415040⟩ : DyadicInterval 40),(⟨742605790023,742605809353⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189499026304,189499026368⟩ : DyadicInterval 40),(⟨-229102828672,-229102828608⟩ : DyadicInterval 40),(⟨742557528931,742557548261⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39603802368,-39504934400⟩ : DyadicInterval 40),(⟨781875850816,781925304064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨189350715136,189542545984⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-229166515456,-228885836160⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e916_ok : ecellOkT e916 = true := by decide +kernel
theorem e916_pos {a z : ℝ} (ha1 : ((769767/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((96327/512000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e916 e916_ok ha1 ha2 hz1 hz2 hz

-- box ['38361/204800', '768069/4096000', '1999/2000', '3999/4000']  interval_lower 245029591/1099511627776
noncomputable def e917 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1305460678328,0,true,188775021824,188775021888⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨893562577224,0,false,-228044228160,-228044228096⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1305688580031,0,true,188966953088,188966953152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨893334675521,0,false,-228324692608,-228324692544⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1305357703802,0,true,188688289152,188688289216⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨893665551750,0,false,-227917527296,-227917527232⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1305637035794,0,true,188923547200,188923547264⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨893386219758,0,false,-228261254016,-228261253952⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538043318,0,true,26415168,26415232⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485212234,0,false,-26415872,-26415808⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564521521,0,true,52892416,52892480⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458734031,0,false,-52895040,-52894976⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625231,0,false,-2560,-2496⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627142,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1305409186104,0,true,188731652160,188731652224⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨893614069448,0,false,-227980869760,-227980869696⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1305662816507,0,true,188945257600,188945257664⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨893360439045,0,false,-228292983424,-228292983360⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1060859637618,0,false,-39347725824,-39347725760⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1060954687173,0,false,-39249217600,-39249217536⟩
    { al := (38361/204800), au := (768069/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨205949050552,206176952255⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188775021824,188775021888⟩ : DyadicInterval 40),(⟨-228044228160,-228044228096⟩ : DyadicInterval 40),(⟨742720869413,742720888743⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188966953088,188966953152⟩ : DyadicInterval 40),(⟨-228324692608,-228324692544⟩ : DyadicInterval 40),(⟨742677646741,742677666071⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188688289152,188688289216⟩ : DyadicInterval 40),(⟨-227917527296,-227917527232⟩ : DyadicInterval 40),(⟨742740382953,742740402283⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188923547200,188923547264⟩ : DyadicInterval 40),(⟨-228261254016,-228261253952⟩ : DyadicInterval 40),(⟨742687426606,742687445936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨26415542,52893745⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26415168,26415232⟩ : DyadicInterval 40),(⟨-26415872,-26415808⟩ : DyadicInterval 40),(⟨762123383269,762123402598⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52892416,52892480⟩ : DyadicInterval 40),(⟨-52895040,-52894976⟩ : DyadicInterval 40),(⟨762123382319,762123401648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2560,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨205897558328,206151188731⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188731652160,188731652224⟩ : DyadicInterval 40),(⟨-227980869760,-227980869696⟩ : DyadicInterval 40),(⟨742730628360,742730647689⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188945257600,188945257664⟩ : DyadicInterval 40),(⟨-228292983424,-228292983360⟩ : DyadicInterval 40),(⟨742682535350,742682554680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39347725824,-39249217536⟩ : DyadicInterval 40),(⟨781747992384,781797265792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨188775021824,188966953152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-228324692608,-228044228096⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e917_ok : ecellOkT e917 = true := by decide +kernel
theorem e917_pos {a z : ℝ} (ha1 : ((38361/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((768069/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e917 e917_ok ha1 ha2 hz1 hz2 hz

-- box ['768069/4096000', '384459/2048000', '1999/2000', '3999/4000']  interval_lower 248701243/1099511627776
noncomputable def e918 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1305688580030,0,true,188966953088,188966953152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨893334675522,0,false,-228324692608,-228324692544⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1305916481733,0,true,189158850880,189158850944⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨893106773819,0,false,-228605228608,-228605228544⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1305585491553,0,true,188880139584,188880139648⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨893437763999,0,false,-228197819136,-228197819072⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1305864880520,0,true,189115404544,189115404608⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨893158375032,0,false,-228541703744,-228541703680⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538074087,0,true,26445952,26446016⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485181465,0,false,-26446656,-26446592⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564583072,0,true,52953984,52954048⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458672480,0,false,-52956608,-52956544⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625225,0,false,-2560,-2496⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627140,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1305637030831,0,true,188923542976,188923543040⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨893386224721,0,false,-228261247936,-228261247872⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1305890689721,0,true,189137135168,189137135232⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨893132565831,0,false,-228573476288,-228573476224⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1060774140937,0,false,-39436341120,-39436341056⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1060869306303,0,false,-39337704896,-39337704832⟩
    { al := (768069/4096000), au := (384459/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨206176952254,206404853957⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188966953088,188966953152⟩ : DyadicInterval 40),(⟨-228324692608,-228324692544⟩ : DyadicInterval 40),(⟨742677646742,742677666071⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189158850880,189158850944⟩ : DyadicInterval 40),(⟨-228605228608,-228605228544⟩ : DyadicInterval 40),(⟨742634375092,742634394422⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188880139584,188880139648⟩ : DyadicInterval 40),(⟨-228197819136,-228197819072⟩ : DyadicInterval 40),(⟨742697203998,742697223327⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189115404544,189115404608⟩ : DyadicInterval 40),(⟨-228541703744,-228541703680⟩ : DyadicInterval 40),(⟨742644176904,742644196234⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨26446311,52955296⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26445952,26446016⟩ : DyadicInterval 40),(⟨-26446656,-26446592⟩ : DyadicInterval 40),(⟨762123383267,762123402596⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52953984,52954048⟩ : DyadicInterval 40),(⟨-52956608,-52956544⟩ : DyadicInterval 40),(⟨762123382313,762123401642⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2560,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨206125403055,206379061945⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188923542976,188923543040⟩ : DyadicInterval 40),(⟨-228261247936,-228261247872⟩ : DyadicInterval 40),(⟨742687427586,742687446916⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189137135168,189137135232⟩ : DyadicInterval 40),(⟨-228573476288,-228573476224⟩ : DyadicInterval 40),(⟨742639274673,742639294002⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39436341120,-39337704832⟩ : DyadicInterval 40),(⟨781792236032,781841573440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨188966953088,189158850944⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-228605228608,-228324692544⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e918_ok : ecellOkT e918 = true := by decide +kernel
theorem e918_pos {a z : ℝ} (ha1 : ((768069/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((384459/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e918 e918_ok ha1 ha2 hz1 hz2 hz

-- box ['38361/204800', '768069/4096000', '3999/4000', '1']  interval_lower 61084709/274877906944
noncomputable def e919 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1305460678328,0,true,188775021824,188775021888⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨893562577224,0,false,-228044228160,-228044228096⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1305688580031,0,true,188966953088,188966953152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨893334675521,0,false,-228324692608,-228324692544⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1305409191065,0,true,188731656320,188731656384⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨893614064487,0,false,-227980875904,-227980875840⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538074952,0,true,26446848,26446912⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485180600,0,false,-26447552,-26447488⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627139,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1305434929485,0,true,188753334912,188753334976⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨893588326067,0,false,-228012545152,-228012545088⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1305688588538,0,true,188966960256,188966960320⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨893334667014,0,false,-228324703040,-228324702976⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1060849972841,0,false,-39357742784,-39357742720⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1060945045018,0,false,-39259210176,-39259210112⟩
    { al := (38361/204800), au := (768069/4096000), zl := (3999/4000), zu := 1,
      A := ⟨205949050552,206176952255⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188775021824,188775021888⟩ : DyadicInterval 40),(⟨-228044228160,-228044228096⟩ : DyadicInterval 40),(⟨742720869413,742720888743⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188966953088,188966953152⟩ : DyadicInterval 40),(⟨-228324692608,-228324692544⟩ : DyadicInterval 40),(⟨742677646741,742677666071⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188731656320,188731656384⟩ : DyadicInterval 40),(⟨-227980875904,-227980875840⟩ : DyadicInterval 40),(⟨742730627447,742730646776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188966953088,188966953152⟩ : DyadicInterval 40),(⟨-228324692608,-228324692544⟩ : DyadicInterval 40),(⟨742677646741,742677666071⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,26447176⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26446848,26446912⟩ : DyadicInterval 40),(⟨-26447552,-26447488⟩ : DyadicInterval 40),(⟨762123383267,762123402596⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨205923301709,206176960762⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188753334912,188753334976⟩ : DyadicInterval 40),(⟨-228012545152,-228012545088⟩ : DyadicInterval 40),(⟨742725749716,742725769046⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188966960256,188966960320⟩ : DyadicInterval 40),(⟨-228324703040,-228324702976⟩ : DyadicInterval 40),(⟨742677645109,742677664439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39357742784,-39259210112⟩ : DyadicInterval 40),(⟨781752988672,781802274272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨188775021824,188966953152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-228324692608,-228044228096⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e919_ok : ecellOkT e919 = true := by decide +kernel
theorem e919_pos {a z : ℝ} (ha1 : ((38361/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((768069/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e919 e919_ok ha1 ha2 hz1 hz2 hz

-- box ['768069/4096000', '384459/2048000', '3999/4000', '1']  interval_lower 248007745/1099511627776
noncomputable def e920 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1305688580030,0,true,188966953088,188966953152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨893334675522,0,false,-228324692608,-228324692544⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1305916481733,0,true,189158850880,189158850944⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨893106773819,0,false,-228605228608,-228605228544⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1305637035791,0,true,188923547200,188923547264⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨893386219761,0,false,-228261254016,-228261253952⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538105727,0,true,26477632,26477696⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485149825,0,false,-26478272,-26478208⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627138,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1305662802701,0,true,188945245952,188945246016⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨893360452851,0,false,-228292966464,-228292966400⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1305916490246,0,true,189158858048,189158858112⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨893106765306,0,false,-228605239104,-228605239040⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1060764454781,0,false,-39446381056,-39446380992⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1060859642796,0,false,-39347720448,-39347720384⟩
    { al := (768069/4096000), au := (384459/2048000), zl := (3999/4000), zu := 1,
      A := ⟨206176952254,206404853957⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188966953088,188966953152⟩ : DyadicInterval 40),(⟨-228324692608,-228324692544⟩ : DyadicInterval 40),(⟨742677646742,742677666071⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189158850880,189158850944⟩ : DyadicInterval 40),(⟨-228605228608,-228605228544⟩ : DyadicInterval 40),(⟨742634375092,742634394422⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188923547200,188923547264⟩ : DyadicInterval 40),(⟨-228261254016,-228261253952⟩ : DyadicInterval 40),(⟨742687426607,742687445937⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189158850880,189158850944⟩ : DyadicInterval 40),(⟨-228605228608,-228605228544⟩ : DyadicInterval 40),(⟨742634375092,742634394422⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,26477951⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26477632,26477696⟩ : DyadicInterval 40),(⟨-26478272,-26478208⟩ : DyadicInterval 40),(⟨762123383234,762123402563⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨206151174925,206404862470⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨188945245952,188945246016⟩ : DyadicInterval 40),(⟨-228292966464,-228292966400⟩ : DyadicInterval 40),(⟨742682537996,742682557325⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189158858048,189158858112⟩ : DyadicInterval 40),(⟨-228605239104,-228605239040⟩ : DyadicInterval 40),(⟨742634373481,742634392810⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39446381056,-39347720384⟩ : DyadicInterval 40),(⟨781797243808,781846593408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨188966953088,189158850944⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-228605228608,-228324692544⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e920_ok : ecellOkT e920 = true := by decide +kernel
theorem e920_pos {a z : ℝ} (ha1 : ((768069/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((384459/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e920 e920_ok ha1 ha2 hz1 hz2 hz

-- box ['384459/2048000', '769767/4096000', '1999/2000', '3999/4000']  interval_lower 126194725/549755813888
noncomputable def e921 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1305916481732,0,true,189158850880,189158850944⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨893106773820,0,false,-228605228608,-228605228544⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1306144383435,0,true,189350715136,189350715200⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨892878872117,0,false,-228885836224,-228885836160⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1305813279305,0,true,189071956480,189071956544⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨893209976247,0,false,-228478182528,-228478182464⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1306092725247,0,true,189307228416,189307228480⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨892930530305,0,false,-228822224960,-228822224896⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538104862,0,true,26476736,26476800⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485150690,0,false,-26477440,-26477376⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564644633,0,true,53015552,53015616⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458610919,0,false,-53018176,-53018112⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625219,0,false,-2560,-2496⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627139,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1305864875551,0,true,189115400384,189115400448⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨893158380001,0,false,-228541697600,-228541697536⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1306118562934,0,true,189328979200,189328979264⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨892904692618,0,false,-228854040704,-228854040640⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1060688549804,0,false,-39525061440,-39525061376⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1060783831006,0,false,-39426297216,-39426297152⟩
    { al := (384459/2048000), au := (769767/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨206404853956,206632755659⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189158850880,189158850944⟩ : DyadicInterval 40),(⟨-228605228608,-228605228544⟩ : DyadicInterval 40),(⟨742634375092,742634394422⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189350715136,189350715200⟩ : DyadicInterval 40),(⟨-228885836224,-228885836160⟩ : DyadicInterval 40),(⟨742591054516,742591073846⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189071956480,189071956544⟩ : DyadicInterval 40),(⟨-228478182528,-228478182464⟩ : DyadicInterval 40),(⟨742653976204,742653995534⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189307228416,189307228480⟩ : DyadicInterval 40),(⟨-228822224960,-228822224896⟩ : DyadicInterval 40),(⟨742600878237,742600897567⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨26477086,53016857⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26476736,26476800⟩ : DyadicInterval 40),(⟨-26477440,-26477376⟩ : DyadicInterval 40),(⟨762123383266,762123402595⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53015552,53015616⟩ : DyadicInterval 40),(⟨-53018176,-53018112⟩ : DyadicInterval 40),(⟨762123382307,762123401636⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2560,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨206353247775,206606935158⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189115400384,189115400448⟩ : DyadicInterval 40),(⟨-228541697600,-228541697536⟩ : DyadicInterval 40),(⟨742644177823,742644197152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189328979200,189328979264⟩ : DyadicInterval 40),(⟨-228854040704,-228854040640⟩ : DyadicInterval 40),(⟨742595965068,742595984398⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39525061440,-39426297152⟩ : DyadicInterval 40),(⟨781836532192,781885933600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨189158850880,189350715200⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-228885836224,-228605228544⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e921_ok : ecellOkT e921 = true := by decide +kernel
theorem e921_pos {a z : ℝ} (ha1 : ((384459/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((769767/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e921 e921_ok ha1 ha2 hz1 hz2 hz

-- box ['769767/4096000', '96327/512000', '1999/2000', '3999/4000']  interval_lower 256093695/1099511627776
noncomputable def e922 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1306144383434,0,true,189350715136,189350715200⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨892878872118,0,false,-228885836224,-228885836160⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1306372285137,0,true,189542545920,189542545984⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨892650970415,0,false,-229166515456,-229166515392⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1306041067056,0,true,189263740032,189263740096⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨892982188496,0,false,-228758617408,-228758617344⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1306320569973,0,true,189499018816,189499018880⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨892702685579,0,false,-229102817792,-229102817728⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538135643,0,true,26507520,26507584⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485119909,0,false,-26508224,-26508160⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564706207,0,true,53077120,53077184⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458549345,0,false,-53079744,-53079680⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625213,0,false,-2624,-2560⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627137,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1306092720276,0,true,189307224256,189307224320⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨892930535276,0,false,-228822218816,-228822218752⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1306346436145,0,true,189520789824,189520789888⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨892676819407,0,false,-229134676736,-229134676672⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1060602864219,0,false,-39613886848,-39613886784⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1060698261278,0,false,-39514994560,-39514994496⟩
    { al := (769767/4096000), au := (96327/512000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨206632755658,206860657361⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189350715136,189350715200⟩ : DyadicInterval 40),(⟨-228885836224,-228885836160⟩ : DyadicInterval 40),(⟨742591054517,742591073846⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189542545920,189542545984⟩ : DyadicInterval 40),(⟨-229166515456,-229166515392⟩ : DyadicInterval 40),(⟨742547684964,742547704294⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189263740032,189263740096⟩ : DyadicInterval 40),(⟨-228758617408,-228758617344⟩ : DyadicInterval 40),(⟨742610699423,742610718753⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189499018816,189499018880⟩ : DyadicInterval 40),(⟨-229102817792,-229102817728⟩ : DyadicInterval 40),(⟨742557530646,742557549976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨26507867,53078431⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26507520,26507584⟩ : DyadicInterval 40),(⟨-26508224,-26508160⟩ : DyadicInterval 40),(⟨762123383264,762123402593⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53077120,53077184⟩ : DyadicInterval 40),(⟨-53079744,-53079680⟩ : DyadicInterval 40),(⟨762123382301,762123401630⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2624,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨206581092500,206834808369⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189307224256,189307224320⟩ : DyadicInterval 40),(⟨-228822218816,-228822218752⟩ : DyadicInterval 40),(⟨742600879159,742600898488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189520789824,189520789888⟩ : DyadicInterval 40),(⟨-229134676736,-229134676672⟩ : DyadicInterval 40),(⟨742552606476,742552625805⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39613886848,-39514994496⟩ : DyadicInterval 40),(⟨781880880864,781930346304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨189350715136,189542545984⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-229166515456,-228885836160⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e922_ok : ecellOkT e922 = true := by decide +kernel
theorem e922_pos {a z : ℝ} (ha1 : ((769767/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((96327/512000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e922 e922_ok ha1 ha2 hz1 hz2 hz

-- box ['384459/2048000', '769767/4096000', '3999/4000', '1']  interval_lower 62923309/274877906944
noncomputable def e923 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1305916481732,0,true,189158850880,189158850944⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨893106773820,0,false,-228605228608,-228605228544⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1306144383435,0,true,189350715136,189350715200⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨892878872117,0,false,-228885836224,-228885836160⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1305864880518,0,true,189115404544,189115404608⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨893158375034,0,false,-228541703744,-228541703680⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538136509,0,true,26508352,26508416⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485119043,0,false,-26509056,-26508992⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627136,0,false,-704,-640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1305890675911,0,true,189137123520,189137123584⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨893132579641,0,false,-228573459264,-228573459200⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1306144391946,0,true,189350722304,189350722368⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨892878863606,0,false,-228885846656,-228885846592⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1060678842246,0,false,-39535124352,-39535124288⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1060774146123,0,false,-39436335744,-39436335680⟩
    { al := (384459/2048000), au := (769767/4096000), zl := (3999/4000), zu := 1,
      A := ⟨206404853956,206632755659⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189158850880,189158850944⟩ : DyadicInterval 40),(⟨-228605228608,-228605228544⟩ : DyadicInterval 40),(⟨742634375092,742634394422⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189350715136,189350715200⟩ : DyadicInterval 40),(⟨-228885836224,-228885836160⟩ : DyadicInterval 40),(⟨742591054516,742591073846⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189115404544,189115404608⟩ : DyadicInterval 40),(⟨-228541703744,-228541703680⟩ : DyadicInterval 40),(⟨742644176905,742644196234⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189350715136,189350715200⟩ : DyadicInterval 40),(⟨-228885836224,-228885836160⟩ : DyadicInterval 40),(⟨742591054516,742591073846⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,26508733⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26508352,26508416⟩ : DyadicInterval 40),(⟨-26509056,-26508992⟩ : DyadicInterval 40),(⟨762123383264,762123402593⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-704,0⟩ : DyadicInterval 40),(⟨762123383616,762123403232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨206379048135,206632764170⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189137123520,189137123584⟩ : DyadicInterval 40),(⟨-228573459264,-228573459200⟩ : DyadicInterval 40),(⟨742639277299,742639296628⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189350722304,189350722368⟩ : DyadicInterval 40),(⟨-228885846656,-228885846592⟩ : DyadicInterval 40),(⟨742591052876,742591072205⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39535124352,-39436335680⟩ : DyadicInterval 40),(⟨781841551456,781890965056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨189158850880,189350715200⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-228885836224,-228605228544⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e923_ok : ecellOkT e923 = true := by decide +kernel
theorem e923_pos {a z : ℝ} (ha1 : ((384459/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((769767/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e923 e923_ok ha1 ha2 hz1 hz2 hz

-- box ['769767/4096000', '96327/512000', '3999/4000', '1']  interval_lower 63848747/274877906944
noncomputable def e924 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1306144383434,0,true,189350715136,189350715200⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨892878872118,0,false,-228885836224,-228885836160⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1306372285137,0,true,189542545920,189542545984⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨892650970415,0,false,-229166515456,-229166515392⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1306092725245,0,true,189307228416,189307228480⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨892930530307,0,false,-228822224960,-228822224896⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538167296,0,true,26539136,26539200⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485088256,0,false,-26539904,-26539840⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627135,0,false,-704,-640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1306118549118,0,true,189328967616,189328967680⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨892904706434,0,false,-228854023680,-228854023616⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1306372293646,0,true,189542553088,189542553152⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨892650961906,0,false,-229166525888,-229166525824⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1060593135235,0,false,-39623972800,-39623972736⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1060688554998,0,false,-39525056064,-39525056000⟩
    { al := (769767/4096000), au := (96327/512000), zl := (3999/4000), zu := 1,
      A := ⟨206632755658,206860657361⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189350715136,189350715200⟩ : DyadicInterval 40),(⟨-228885836224,-228885836160⟩ : DyadicInterval 40),(⟨742591054517,742591073846⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189542545920,189542545984⟩ : DyadicInterval 40),(⟨-229166515456,-229166515392⟩ : DyadicInterval 40),(⟨742547684964,742547704294⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189307228416,189307228480⟩ : DyadicInterval 40),(⟨-228822224960,-228822224896⟩ : DyadicInterval 40),(⟨742600878238,742600897567⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189542545920,189542545984⟩ : DyadicInterval 40),(⟨-229166515456,-229166515392⟩ : DyadicInterval 40),(⟨742547684964,742547704294⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,26539520⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26539136,26539200⟩ : DyadicInterval 40),(⟨-26539904,-26539840⟩ : DyadicInterval 40),(⟨762123383295,762123402624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-704,0⟩ : DyadicInterval 40),(⟨762123383616,762123403232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨206606921342,206860665870⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189328967616,189328967680⟩ : DyadicInterval 40),(⟨-228854023680,-228854023616⟩ : DyadicInterval 40),(⟨742595967663,742595986993⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189542553088,189542553152⟩ : DyadicInterval 40),(⟨-229166525888,-229166525824⟩ : DyadicInterval 40),(⟨742547683321,742547702650⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39623972800,-39525056000⟩ : DyadicInterval 40),(⟨781885911616,781935389280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨189350715136,189542545984⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-229166515456,-228885836160⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e924_ok : ecellOkT e924 = true := by decide +kernel
theorem e924_pos {a z : ℝ} (ha1 : ((769767/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((96327/512000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e924 e924_ok ha1 ha2 hz1 hz2 hz

-- box ['96327/512000', '154293/819200', '999/1000', '3997/4000']  interval_lower 8162993/34359738368
noncomputable def e925 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1306372285136,0,true,189542545920,189542545984⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨892650970416,0,false,-229166515456,-229166515392⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1306600186840,0,true,189734343232,189734343296⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨892423068712,0,false,-229447266304,-229447266240⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1306165424478,0,true,189368427328,189368427392⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨892857831074,0,false,-228911746944,-228911746880⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1306444870421,0,true,189603635776,189603635840⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨892578385131,0,false,-229255925056,-229255924992⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591243194,0,true,79612480,79612544⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432012358,0,false,-79618304,-79618240⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099617906135,0,true,106273216,106273280⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099405349417,0,false,-106283520,-106283456⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511617503,0,false,-10304,-10240⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622012,0,false,-5824,-5760⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1306268850833,0,true,189455486720,189455486784⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨892754404719,0,false,-229039118912,-229039118848⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1306522537894,0,true,189668999232,189668999296⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨892500717658,0,false,-229351602944,-229351602880⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1060536581195,0,false,-39682603648,-39682603584⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1060632048692,0,false,-39583632128,-39583632064⟩
    { al := (96327/512000), au := (154293/819200), zl := (999/1000), zu := (3997/4000),
      A := ⟨206860657360,207088559064⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189542545920,189542545984⟩ : DyadicInterval 40),(⟨-229166515456,-229166515392⟩ : DyadicInterval 40),(⟨742547684965,742547704294⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189734343232,189734343296⟩ : DyadicInterval 40),(⟨-229447266304,-229447266240⟩ : DyadicInterval 40),(⟨742504266425,742504285754⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189368427328,189368427392⟩ : DyadicInterval 40),(⟨-228911746944,-228911746880⟩ : DyadicInterval 40),(⟨742587052468,742587071798⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189603635776,189603635840⟩ : DyadicInterval 40),(⟨-229255925056,-229255924992⟩ : DyadicInterval 40),(⟨742533861751,742533881080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨79615418,106278359⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79612480,79612544⟩ : DyadicInterval 40),(⟨-79618304,-79618240⟩ : DyadicInterval 40),(⟨762123380698,762123400028⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨106273216,106273280⟩ : DyadicInterval 40),(⟨-106283520,-106283456⟩ : DyadicInterval 40),(⟨762123378430,762123397760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-10304,-5760⟩ : DyadicInterval 40),(⟨762123386496,762123408032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨206757223057,207010910118⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189455486720,189455486784⟩ : DyadicInterval 40),(⟨-229039118912,-229039118848⟩ : DyadicInterval 40),(⟨742567374513,742567393843⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189668999232,189668999296⟩ : DyadicInterval 40),(⟨-229351602944,-229351602880⟩ : DyadicInterval 40),(⟨742519065177,742519084507⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39682603648,-39583632064⟩ : DyadicInterval 40),(⟨781915199648,781964704704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨189542545920,189734343296⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-229447266304,-229166515392⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e925_ok : ecellOkT e925 = true := by decide +kernel
theorem e925_pos {a z : ℝ} (ha1 : ((96327/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((154293/819200 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e925 e925_ok ha1 ha2 hz1 hz2 hz

-- box ['154293/819200', '386157/2048000', '999/1000', '3997/4000']  interval_lower 264958453/1099511627776
noncomputable def e926 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1306600186839,0,true,189734343232,189734343296⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨892423068713,0,false,-229447266304,-229447266240⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1306828088542,0,true,189926107136,189926107200⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨892195167010,0,false,-229728088960,-229728088896⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1306393098279,0,true,189560063232,189560063296⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨892630157273,0,false,-229192152064,-229192152000⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1306672601197,0,true,189795278656,189795278720⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨892350654355,0,false,-229536488192,-229536488128⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591335563,0,true,79704896,79704960⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431919989,0,false,-79710720,-79710656⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099618029318,0,true,106396352,106396416⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099405226234,0,false,-106406720,-106406656⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511617479,0,false,-10304,-10240⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621998,0,false,-5824,-5760⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1306496638588,0,true,189647203328,189647203392⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨892526616964,0,false,-229319696896,-229319696832⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1306750354138,0,true,189860702656,189860702720⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨892272901414,0,false,-229632295808,-229632295744⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1060450749637,0,false,-39771593152,-39771593088⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1060546332987,0,false,-39672493504,-39672493440⟩
    { al := (154293/819200), au := (386157/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨207088559063,207316460766⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189734343232,189734343296⟩ : DyadicInterval 40),(⟨-229447266304,-229447266240⟩ : DyadicInterval 40),(⟨742504266425,742504285755⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189926107136,189926107200⟩ : DyadicInterval 40),(⟨-229728088960,-229728088896⟩ : DyadicInterval 40),(⟨742460798925,742460818255⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189560063232,189560063296⟩ : DyadicInterval 40),(⟨-229192152064,-229192152000⟩ : DyadicInterval 40),(⟨742543721779,742543741108⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189795278656,189795278720⟩ : DyadicInterval 40),(⟨-229536488192,-229536488128⟩ : DyadicInterval 40),(⟨742490460202,742490479531⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨79707787,106401542⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79704896,79704960⟩ : DyadicInterval 40),(⟨-79710720,-79710656⟩ : DyadicInterval 40),(⟨762123380685,762123400014⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨106396352,106396416⟩ : DyadicInterval 40),(⟨-106406720,-106406656⟩ : DyadicInterval 40),(⟨762123378438,762123397768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-10304,-5760⟩ : DyadicInterval 40),(⟨762123386496,762123408032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨206985010812,207238726362⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189647203328,189647203392⟩ : DyadicInterval 40),(⟨-229319696896,-229319696832⟩ : DyadicInterval 40),(⟨742523999923,742524019253⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189860702656,189860702720⟩ : DyadicInterval 40),(⟨-229632295808,-229632295744⟩ : DyadicInterval 40),(⟨742475630630,742475649959⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39771593152,-39672493440⟩ : DyadicInterval 40),(⟨781959630336,782009199456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨189734343232,189926107200⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-229728088960,-229447266240⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e926_ok : ecellOkT e926 = true := by decide +kernel
theorem e926_pos {a z : ℝ} (ha1 : ((154293/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((386157/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e926 e926_ok ha1 ha2 hz1 hz2 hz

-- box ['96327/512000', '154293/819200', '3997/4000', '1999/2000']  interval_lower 130257673/549755813888
noncomputable def e927 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1306372285136,0,true,189542545920,189542545984⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨892650970416,0,false,-229166515456,-229166515392⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1306600186840,0,true,189734343232,189734343296⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨892423068712,0,false,-229447266304,-229447266240⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1306217139642,0,true,189411959552,189411959616⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨892806115910,0,false,-228975433536,-228975433472⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1306496642561,0,true,189647206656,189647206720⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨892526612991,0,false,-229319701824,-229319701760⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564704988,0,true,53075904,53075968⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458550564,0,false,-53078528,-53078464⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591337139,0,true,79706432,79706496⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431918413,0,false,-79712256,-79712192⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621997,0,false,-5824,-5760⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625214,0,false,-2624,-2560⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1306294707831,0,true,189477250816,189477250880⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨892728547721,0,false,-229070964736,-229070964672⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1306548423544,0,true,189690783296,189690783360⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨892474832008,0,false,-229383493120,-229383493056⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1060526833328,0,false,-39692709824,-39692709760⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1060622323546,0,false,-39593713856,-39593713792⟩
    { al := (96327/512000), au := (154293/819200), zl := (3997/4000), zu := (1999/2000),
      A := ⟨206860657360,207088559064⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189542545920,189542545984⟩ : DyadicInterval 40),(⟨-229166515456,-229166515392⟩ : DyadicInterval 40),(⟨742547684965,742547704294⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189734343232,189734343296⟩ : DyadicInterval 40),(⟨-229447266304,-229447266240⟩ : DyadicInterval 40),(⟨742504266425,742504285754⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189411959552,189411959616⟩ : DyadicInterval 40),(⟨-228975433536,-228975433472⟩ : DyadicInterval 40),(⟨742577214379,742577233709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189647206656,189647206720⟩ : DyadicInterval 40),(⟨-229319701824,-229319701760⟩ : DyadicInterval 40),(⟨742523999190,742524018519⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨53077212,79709363⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53075904,53075968⟩ : DyadicInterval 40),(⟨-53078528,-53078464⟩ : DyadicInterval 40),(⟨762123382301,762123401630⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79706432,79706496⟩ : DyadicInterval 40),(⟨-79712256,-79712192⟩ : DyadicInterval 40),(⟨762123380685,762123400014⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5824,-2560⟩ : DyadicInterval 40),(⟨762123384896,762123405792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨206783080055,207036795768⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189477250816,189477250880⟩ : DyadicInterval 40),(⟨-229070964736,-229070964672⟩ : DyadicInterval 40),(⟨742562453391,742562472721⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189690783296,189690783360⟩ : DyadicInterval 40),(⟨-229383493120,-229383493056⟩ : DyadicInterval 40),(⟨742514132362,742514151692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39692709824,-39593713792⟩ : DyadicInterval 40),(⟨781920240512,781969757792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨189542545920,189734343296⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-229447266304,-229166515392⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e927_ok : ecellOkT e927 = true := by decide +kernel
theorem e927_pos {a z : ℝ} (ha1 : ((96327/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((154293/819200 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e927 e927_ok ha1 ha2 hz1 hz2 hz

-- box ['154293/819200', '386157/2048000', '3997/4000', '1999/2000']  interval_lower 132127657/549755813888
noncomputable def e928 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1306600186839,0,true,189734343232,189734343296⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨892423068713,0,false,-229447266304,-229447266240⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1306828088542,0,true,189926107136,189926107200⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨892195167010,0,false,-229728088960,-229728088896⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1306444870419,0,true,189603635776,189603635840⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨892578385133,0,false,-229255925056,-229255924992⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1306724430312,0,true,189838889856,189838889920⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨892298825240,0,false,-229600351424,-229600351360⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564766568,0,true,53137472,53137536⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458488984,0,false,-53140096,-53140032⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591429528,0,true,79798848,79798912⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431826024,0,false,-79804672,-79804608⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621984,0,false,-5824,-5760⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625208,0,false,-2624,-2560⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1306522524069,0,true,189668987648,189668987712⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨892500731483,0,false,-229351585920,-229351585856⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1306776268272,0,true,189882506816,189882506880⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨892246987280,0,false,-229664229184,-229664229120⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1060440980304,0,false,-39781722368,-39781722304⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1060536586402,0,false,-39682598272,-39682598208⟩
    { al := (154293/819200), au := (386157/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨207088559063,207316460766⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189734343232,189734343296⟩ : DyadicInterval 40),(⟨-229447266304,-229447266240⟩ : DyadicInterval 40),(⟨742504266425,742504285755⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189926107136,189926107200⟩ : DyadicInterval 40),(⟨-229728088960,-229728088896⟩ : DyadicInterval 40),(⟨742460798925,742460818255⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189603635776,189603635840⟩ : DyadicInterval 40),(⟨-229255925056,-229255924992⟩ : DyadicInterval 40),(⟨742533861751,742533881081⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189838889856,189838889920⟩ : DyadicInterval 40),(⟨-229600351424,-229600351360⟩ : DyadicInterval 40),(⟨742480575664,742480594994⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨53138792,79801752⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53137472,53137536⟩ : DyadicInterval 40),(⟨-53140096,-53140032⟩ : DyadicInterval 40),(⟨762123382295,762123401624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79798848,79798912⟩ : DyadicInterval 40),(⟨-79804672,-79804608⟩ : DyadicInterval 40),(⟨762123380671,762123400001⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5824,-2560⟩ : DyadicInterval 40),(⟨762123384896,762123405792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨207010896293,207264640496⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189668987648,189668987712⟩ : DyadicInterval 40),(⟨-229351585920,-229351585856⟩ : DyadicInterval 40),(⟨742519067785,742519087114⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189882506816,189882506880⟩ : DyadicInterval 40),(⟨-229664229184,-229664229120⟩ : DyadicInterval 40),(⟨742470686845,742470706174⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39781722368,-39682598208⟩ : DyadicInterval 40),(⟨781964682720,782014264064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨189734343232,189926107200⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-229728088960,-229447266240⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e928_ok : ecellOkT e928 = true := by decide +kernel
theorem e928_pos {a z : ℝ} (ha1 : ((154293/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((386157/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e928 e928_ok ha1 ha2 hz1 hz2 hz

-- box ['386157/2048000', '773163/4096000', '999/1000', '3997/4000']  interval_lower 268717453/1099511627776
noncomputable def e929 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1306828088541,0,true,189926107136,189926107200⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨892195167011,0,false,-229728088960,-229728088896⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1307055990244,0,true,190117837568,190117837632⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨891967265308,0,false,-230008983296,-230008983232⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1306620772080,0,true,189751665728,189751665792⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨892402483472,0,false,-229472628736,-229472628672⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1306900331973,0,true,189986888128,189986888192⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨892122923579,0,false,-229817122944,-229817122880⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591427949,0,true,79797248,79797312⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431827603,0,false,-79803072,-79803008⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099618152524,0,true,106519552,106519616⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099405103028,0,false,-106529920,-106529856⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511617455,0,false,-10368,-10304⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621985,0,false,-5824,-5760⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1306724426336,0,true,189838886528,189838886592⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨892298829216,0,false,-229600346496,-229600346432⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1306978170380,0,true,190052372608,190052372672⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨892045085172,0,false,-229913060352,-229913060288⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1060364823674,0,false,-39860687744,-39860687680⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1060460522902,0,false,-39761459968,-39761459904⟩
    { al := (386157/2048000), au := (773163/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨207316460765,207544362468⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189926107136,189926107200⟩ : DyadicInterval 40),(⟨-229728088960,-229728088896⟩ : DyadicInterval 40),(⟨742460798926,742460818255⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190117837568,190117837632⟩ : DyadicInterval 40),(⟨-230008983296,-230008983232⟩ : DyadicInterval 40),(⟨742417282440,742417301770⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189751665728,189751665792⟩ : DyadicInterval 40),(⟨-229472628736,-229472628672⟩ : DyadicInterval 40),(⟨742500342233,742500361562⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189986888128,189986888192⟩ : DyadicInterval 40),(⟨-229817122944,-229817122880⟩ : DyadicInterval 40),(⟨742447009758,742447029088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨79800173,106524748⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79797248,79797312⟩ : DyadicInterval 40),(⟨-79803072,-79803008⟩ : DyadicInterval 40),(⟨762123380672,762123400001⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨106519552,106519616⟩ : DyadicInterval 40),(⟨-106529920,-106529856⟩ : DyadicInterval 40),(⟨762123378414,762123397744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-10368,-5760⟩ : DyadicInterval 40),(⟨762123386496,762123408064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨207212798560,207466542604⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189838886528,189838886592⟩ : DyadicInterval 40),(⟨-229600346496,-229600346432⟩ : DyadicInterval 40),(⟨742480576400,742480595730⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190052372608,190052372672⟩ : DyadicInterval 40),(⟨-229913060352,-229913060288⟩ : DyadicInterval 40),(⟨742432147174,742432166504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39860687744,-39761459904⟩ : DyadicInterval 40),(⟨782004113568,782053746752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨189926107136,190117837632⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-230008983296,-229728088896⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e929_ok : ecellOkT e929 = true := by decide +kernel
theorem e929_pos {a z : ℝ} (ha1 : ((386157/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((773163/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e929 e929_ok ha1 ha2 hz1 hz2 hz

-- box ['773163/4096000', '193503/1024000', '999/1000', '3997/4000']  interval_lower 136246555/549755813888
noncomputable def e930 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1307055990243,0,true,190117837568,190117837632⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨891967265309,0,false,-230008983296,-230008983232⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1307283891946,0,true,190309534592,190309534656⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨891739363606,0,false,-230289949440,-230289949376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1306848445880,0,true,189943234816,189943234880⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨892174809672,0,false,-229753176960,-229753176896⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1307128062749,0,true,190178464192,190178464256⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨891895192803,0,false,-230097829312,-230097829248⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591520351,0,true,79889664,79889728⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431735201,0,false,-79895488,-79895424⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099618275750,0,true,106642752,106642816⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099404979802,0,false,-106653184,-106653120⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511617431,0,false,-10368,-10304⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621971,0,false,-5824,-5760⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1306952214085,0,true,190030536320,190030536384⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨892071041467,0,false,-229881067776,-229881067712⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1307205986623,0,true,190244009152,190244009216⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨891817268929,0,false,-230193896640,-230193896576⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1060278803304,0,false,-39949887424,-39949887360⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1060374618434,0,false,-39850531456,-39850531392⟩
    { al := (773163/4096000), au := (193503/1024000), zl := (999/1000), zu := (3997/4000),
      A := ⟨207544362467,207772264170⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190117837568,190117837632⟩ : DyadicInterval 40),(⟨-230008983296,-230008983232⟩ : DyadicInterval 40),(⟨742417282441,742417301770⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190309534592,190309534656⟩ : DyadicInterval 40),(⟨-230289949440,-230289949376⟩ : DyadicInterval 40),(⟨742373716972,742373736302⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189943234816,189943234880⟩ : DyadicInterval 40),(⟨-229753176960,-229753176896⟩ : DyadicInterval 40),(⟨742456913818,742456933147⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190178464192,190178464256⟩ : DyadicInterval 40),(⟨-230097829312,-230097829248⟩ : DyadicInterval 40),(⟨742403510408,742403529738⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨79892575,106647974⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79889664,79889728⟩ : DyadicInterval 40),(⟨-79895488,-79895424⟩ : DyadicInterval 40),(⟨762123380658,762123399988⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨106642752,106642816⟩ : DyadicInterval 40),(⟨-106653184,-106653120⟩ : DyadicInterval 40),(⟨762123378423,762123397753⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-10368,-5760⟩ : DyadicInterval 40),(⟨762123386496,762123408064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨207440586309,207694358847⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190030536320,190030536384⟩ : DyadicInterval 40),(⟨-229881067776,-229881067712⟩ : DyadicInterval 40),(⟨742437103957,742437123286⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190244009152,190244009216⟩ : DyadicInterval 40),(⟨-230193896640,-230193896576⟩ : DyadicInterval 40),(⟨742388614786,742388634116⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39949887424,-39850531392⟩ : DyadicInterval 40),(⟨782048649312,782098346592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨190117837568,190309534656⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-230289949440,-230008983232⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e930_ok : ecellOkT e930 = true := by decide +kernel
theorem e930_pos {a z : ℝ} (ha1 : ((773163/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((193503/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e930 e930_ok ha1 ha2 hz1 hz2 hz

-- box ['386157/2048000', '773163/4096000', '3997/4000', '1999/2000']  interval_lower 134005849/549755813888
noncomputable def e931 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1306828088541,0,true,189926107136,189926107200⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨892195167011,0,false,-229728088960,-229728088896⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1307055990244,0,true,190117837568,190117837632⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨891967265308,0,false,-230008983296,-230008983232⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1306672601195,0,true,189795278656,189795278720⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨892350654357,0,false,-229536488192,-229536488128⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1306952218063,0,true,190030539648,190030539712⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨892071037489,0,false,-229881072640,-229881072576⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564828160,0,true,53199040,53199104⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458427392,0,false,-53201728,-53201664⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591521933,0,true,79891200,79891264⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431733619,0,false,-79897088,-79897024⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621970,0,false,-5824,-5760⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625202,0,false,-2624,-2560⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1306750340307,0,true,189860691008,189860691072⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨892272915245,0,false,-229632278784,-229632278720⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1307004113004,0,true,190074196928,190074196992⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨892019142548,0,false,-229945037056,-229945036992⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1060355032849,0,false,-39870840064,-39870840000⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1060450754852,0,false,-39771587776,-39771587712⟩
    { al := (386157/2048000), au := (773163/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨207316460765,207544362468⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189926107136,189926107200⟩ : DyadicInterval 40),(⟨-229728088960,-229728088896⟩ : DyadicInterval 40),(⟨742460798926,742460818255⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190117837568,190117837632⟩ : DyadicInterval 40),(⟨-230008983296,-230008983232⟩ : DyadicInterval 40),(⟨742417282440,742417301770⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189795278656,189795278720⟩ : DyadicInterval 40),(⟨-229536488192,-229536488128⟩ : DyadicInterval 40),(⟨742490460202,742490479532⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190030539648,190030539712⟩ : DyadicInterval 40),(⟨-229881072640,-229881072576⟩ : DyadicInterval 40),(⟨742437103193,742437122522⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨53200384,79894157⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53199040,53199104⟩ : DyadicInterval 40),(⟨-53201728,-53201664⟩ : DyadicInterval 40),(⟨762123382321,762123401650⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79891200,79891264⟩ : DyadicInterval 40),(⟨-79897088,-79897024⟩ : DyadicInterval 40),(⟨762123380690,762123400019⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5824,-2560⟩ : DyadicInterval 40),(⟨762123384896,762123405792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨207238712531,207492485228⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189860691008,189860691072⟩ : DyadicInterval 40),(⟨-229632278784,-229632278720⟩ : DyadicInterval 40),(⟨742475633282,742475652612⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190074196928,190074196992⟩ : DyadicInterval 40),(⟨-229945037056,-229945036992⟩ : DyadicInterval 40),(⟨742427192406,742427211736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39870840064,-39771587712⟩ : DyadicInterval 40),(⟨782009177472,782058822912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨189926107136,190117837632⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-230008983296,-229728088896⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e931_ok : ecellOkT e931 = true := by decide +kernel
theorem e931_pos {a z : ℝ} (ha1 : ((386157/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((773163/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e931 e931_ok ha1 ha2 hz1 hz2 hz

-- box ['773163/4096000', '193503/1024000', '3997/4000', '1999/2000']  interval_lower 135892151/549755813888
noncomputable def e932 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1307055990243,0,true,190117837568,190117837632⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨891967265309,0,false,-230008983296,-230008983232⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1307283891946,0,true,190309534592,190309534656⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨891739363606,0,false,-230289949440,-230289949376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1306900331971,0,true,189986888128,189986888192⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨892122923581,0,false,-229817122944,-229817122880⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1307180005815,0,true,190222156032,190222156096⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨891843249737,0,false,-230161865600,-230161865536⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564889763,0,true,53260672,53260736⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458365789,0,false,-53263296,-53263232⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591614356,0,true,79983616,79983680⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431641196,0,false,-79989504,-79989440⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621957,0,false,-5824,-5760⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625196,0,false,-2624,-2560⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1306978156545,0,true,190052360960,190052361024⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨892045099007,0,false,-229913043328,-229913043264⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1307231957732,0,true,190265853632,190265853696⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨891791297820,0,false,-230225916544,-230225916480⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1060268990966,0,false,-39960062912,-39960062848⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1060364828896,0,false,-39860682304,-39860682240⟩
    { al := (773163/4096000), au := (193503/1024000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨207544362467,207772264170⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190117837568,190117837632⟩ : DyadicInterval 40),(⟨-230008983296,-230008983232⟩ : DyadicInterval 40),(⟨742417282441,742417301770⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190309534592,190309534656⟩ : DyadicInterval 40),(⟨-230289949440,-230289949376⟩ : DyadicInterval 40),(⟨742373716972,742373736302⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189986888128,189986888192⟩ : DyadicInterval 40),(⟨-229817122944,-229817122880⟩ : DyadicInterval 40),(⟨742447009759,742447029088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190222156032,190222156096⟩ : DyadicInterval 40),(⟨-230161865600,-230161865536⟩ : DyadicInterval 40),(⟨742393581815,742393601144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨53261987,79986580⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53260672,53260736⟩ : DyadicInterval 40),(⟨-53263296,-53263232⟩ : DyadicInterval 40),(⟨762123382283,762123401612⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79983616,79983680⟩ : DyadicInterval 40),(⟨-79989504,-79989440⟩ : DyadicInterval 40),(⟨762123380676,762123400006⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5824,-2560⟩ : DyadicInterval 40),(⟨762123384896,762123405792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨207466528769,207720329956⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190052360960,190052361024⟩ : DyadicInterval 40),(⟨-229913043328,-229913043264⟩ : DyadicInterval 40),(⟨742432149833,742432169163⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190265853632,190265853696⟩ : DyadicInterval 40),(⟨-230225916544,-230225916480⟩ : DyadicInterval 40),(⟨742383648959,742383668289⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39960062912,-39860682240⟩ : DyadicInterval 40),(⟨782053724736,782103434336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨190117837568,190309534656⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-230289949440,-230008983232⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e932_ok : ecellOkT e932 = true := by decide +kernel
theorem e932_pos {a z : ℝ} (ha1 : ((773163/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((193503/1024000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e932 e932_ok ha1 ha2 hz1 hz2 hz

-- box ['96327/512000', '154293/819200', '1999/2000', '3999/4000']  interval_lower 129907117/549755813888
noncomputable def e933 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1306372285136,0,true,189542545920,189542545984⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨892650970416,0,false,-229166515456,-229166515392⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1306600186840,0,true,189734343232,189734343296⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨892423068712,0,false,-229447266304,-229447266240⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1306268854807,0,true,189455490048,189455490112⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨892754400745,0,false,-229039123776,-229039123712⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1306548414701,0,true,189690775808,189690775872⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨892474840851,0,false,-229383482240,-229383482176⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538166429,0,true,26538304,26538368⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485089123,0,false,-26539008,-26538944⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564767790,0,true,53138688,53138752⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458487762,0,false,-53141312,-53141248⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625207,0,false,-2624,-2560⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627136,0,false,-704,-640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1306320564997,0,true,189499014656,189499014720⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨892702690555,0,false,-229102811648,-229102811584⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1306574309364,0,true,189712566976,189712567040⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨892448946188,0,false,-229415384384,-229415384320⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1060517084177,0,false,-39702817408,-39702817344⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1060612597121,0,false,-39603796928,-39603796864⟩
    { al := (96327/512000), au := (154293/819200), zl := (1999/2000), zu := (3999/4000),
      A := ⟨206860657360,207088559064⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189542545920,189542545984⟩ : DyadicInterval 40),(⟨-229166515456,-229166515392⟩ : DyadicInterval 40),(⟨742547684965,742547704294⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189734343232,189734343296⟩ : DyadicInterval 40),(⟨-229447266304,-229447266240⟩ : DyadicInterval 40),(⟨742504266425,742504285754⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189455490048,189455490112⟩ : DyadicInterval 40),(⟨-229039123776,-229039123712⟩ : DyadicInterval 40),(⟨742567373755,742567393084⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189690775808,189690775872⟩ : DyadicInterval 40),(⟨-229383482240,-229383482176⟩ : DyadicInterval 40),(⟨742514134081,742514153410⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨26538653,53140014⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26538304,26538368⟩ : DyadicInterval 40),(⟨-26539008,-26538944⟩ : DyadicInterval 40),(⟨762123383263,762123402592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53138688,53138752⟩ : DyadicInterval 40),(⟨-53141312,-53141248⟩ : DyadicInterval 40),(⟨762123382295,762123401624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2624,-640⟩ : DyadicInterval 40),(⟨762123383936,762123404192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨206808937221,207062681588⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189499014656,189499014720⟩ : DyadicInterval 40),(⟨-229102811648,-229102811584⟩ : DyadicInterval 40),(⟨742557531571,742557550900⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189712566976,189712567040⟩ : DyadicInterval 40),(⟨-229415384384,-229415384320⟩ : DyadicInterval 40),(⟨742509198920,742509218250⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39702817408,-39603796864⟩ : DyadicInterval 40),(⟨781925282048,781974811584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨189542545920,189734343296⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-229447266304,-229166515392⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e933_ok : ecellOkT e933 = true := by decide +kernel
theorem e933_pos {a z : ℝ} (ha1 : ((96327/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((154293/819200 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e933 e933_ok ha1 ha2 hz1 hz2 hz

-- box ['154293/819200', '386157/2048000', '1999/2000', '3999/4000']  interval_lower 131775633/549755813888
noncomputable def e934 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1306600186839,0,true,189734343232,189734343296⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨892423068713,0,false,-229447266304,-229447266240⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1306828088542,0,true,189926107136,189926107200⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨892195167010,0,false,-229728088960,-229728088896⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1306496642559,0,true,189647206656,189647206720⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨892526612993,0,false,-229319701760,-229319701696⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1306776259427,0,true,189882499392,189882499456⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨892246996125,0,false,-229664218304,-229664218240⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538197219,0,true,26569088,26569152⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485058333,0,false,-26569792,-26569728⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564829385,0,true,53200320,53200384⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458426167,0,false,-53202944,-53202880⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625201,0,false,-2624,-2560⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627134,0,false,-704,-640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1306548409722,0,true,189690771648,189690771712⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨892474845830,0,false,-229383476096,-229383476032⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1306802182583,0,true,189904310720,189904310784⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨892221072969,0,false,-229696163776,-229696163712⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1060431209682,0,false,-39791853056,-39791852992⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1060526838534,0,false,-39692704384,-39692704320⟩
    { al := (154293/819200), au := (386157/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨207088559063,207316460766⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189734343232,189734343296⟩ : DyadicInterval 40),(⟨-229447266304,-229447266240⟩ : DyadicInterval 40),(⟨742504266425,742504285755⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189926107136,189926107200⟩ : DyadicInterval 40),(⟨-229728088960,-229728088896⟩ : DyadicInterval 40),(⟨742460798925,742460818255⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189647206656,189647206720⟩ : DyadicInterval 40),(⟨-229319701760,-229319701696⟩ : DyadicInterval 40),(⟨742523999164,742524018493⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189882499392,189882499456⟩ : DyadicInterval 40),(⟨-229664218304,-229664218240⟩ : DyadicInterval 40),(⟨742470688529,742470707859⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨26569443,53201609⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26569088,26569152⟩ : DyadicInterval 40),(⟨-26569792,-26569728⟩ : DyadicInterval 40),(⟨762123383261,762123402590⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53200320,53200384⟩ : DyadicInterval 40),(⟨-53202944,-53202880⟩ : DyadicInterval 40),(⟨762123382289,762123401618⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2624,-640⟩ : DyadicInterval 40),(⟨762123383936,762123404192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨207036781946,207290554807⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189690771648,189690771712⟩ : DyadicInterval 40),(⟨-229383476096,-229383476032⟩ : DyadicInterval 40),(⟨742514135008,742514154338⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189904310720,189904310784⟩ : DyadicInterval 40),(⟨-229696163776,-229696163712⟩ : DyadicInterval 40),(⟨742465742405,742465761734⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39791853056,-39692704320⟩ : DyadicInterval 40),(⟨781969735776,782019329408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨189734343232,189926107200⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-229728088960,-229447266240⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e934_ok : ecellOkT e934 = true := by decide +kernel
theorem e934_pos {a z : ℝ} (ha1 : ((154293/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((386157/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e934 e934_ok ha1 ha2 hz1 hz2 hz

-- box ['96327/512000', '154293/819200', '3999/4000', '1']  interval_lower 2024317/8589934592
noncomputable def e935 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1306372285136,0,true,189542545920,189542545984⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨892650970416,0,false,-229166515456,-229166515392⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1306600186840,0,true,189734343232,189734343296⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨892423068712,0,false,-229447266304,-229447266240⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1306320569971,0,true,189499018816,189499018880⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨892702685581,0,false,-229102817792,-229102817728⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538198088,0,true,26569984,26570048⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485057464,0,false,-26570688,-26570624⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627133,0,false,-704,-640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1306346422324,0,true,189520778176,189520778240⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨892676833228,0,false,-229134659712,-229134659648⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1306600195352,0,true,189734350400,189734350464⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨892423060200,0,false,-229447276800,-229447276736⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1060507333744,0,false,-39712926400,-39712926336⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1060602869420,0,false,-39613881472,-39613881408⟩
    { al := (96327/512000), au := (154293/819200), zl := (3999/4000), zu := 1,
      A := ⟨206860657360,207088559064⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189542545920,189542545984⟩ : DyadicInterval 40),(⟨-229166515456,-229166515392⟩ : DyadicInterval 40),(⟨742547684965,742547704294⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189734343232,189734343296⟩ : DyadicInterval 40),(⟨-229447266304,-229447266240⟩ : DyadicInterval 40),(⟨742504266425,742504285754⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189499018816,189499018880⟩ : DyadicInterval 40),(⟨-229102817792,-229102817728⟩ : DyadicInterval 40),(⟨742557530647,742557549977⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189734343232,189734343296⟩ : DyadicInterval 40),(⟨-229447266304,-229447266240⟩ : DyadicInterval 40),(⟨742504266425,742504285754⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,26570312⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26569984,26570048⟩ : DyadicInterval 40),(⟨-26570688,-26570624⟩ : DyadicInterval 40),(⟨762123383261,762123402590⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-704,0⟩ : DyadicInterval 40),(⟨762123383616,762123403232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨206834794548,207088567576⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189520778176,189520778240⟩ : DyadicInterval 40),(⟨-229134659712,-229134659648⟩ : DyadicInterval 40),(⟨742552609116,742552628446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189734350400,189734350464⟩ : DyadicInterval 40),(⟨-229447276800,-229447276736⟩ : DyadicInterval 40),(⟨742504264803,742504284133⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39712926400,-39613881408⟩ : DyadicInterval 40),(⟨781930324320,781979866080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨189542545920,189734343296⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-229447266304,-229166515392⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e935_ok : ecellOkT e935 = true := by decide +kernel
theorem e935_pos {a z : ℝ} (ha1 : ((96327/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((154293/819200 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e935 e935_ok ha1 ha2 hz1 hz2 hz

-- box ['154293/819200', '386157/2048000', '3999/4000', '1']  interval_lower 131423459/549755813888
noncomputable def e936 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1306600186839,0,true,189734343232,189734343296⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨892423068713,0,false,-229447266304,-229447266240⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1306828088542,0,true,189926107136,189926107200⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨892195167010,0,false,-229728088960,-229728088896⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1306548414699,0,true,189690775808,189690775872⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨892474840853,0,false,-229383482240,-229383482176⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538228886,0,true,26600768,26600832⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485026666,0,false,-26601472,-26601408⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627132,0,false,-704,-640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1306574295537,0,true,189712555328,189712555392⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨892448960015,0,false,-229415367360,-229415367296⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1306828097054,0,true,189926114304,189926114368⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨892195158498,0,false,-229728099456,-229728099392⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1060421437778,0,false,-39801985088,-39801985024⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1060517089386,0,false,-39702811968,-39702811904⟩
    { al := (154293/819200), au := (386157/2048000), zl := (3999/4000), zu := 1,
      A := ⟨207088559063,207316460766⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189734343232,189734343296⟩ : DyadicInterval 40),(⟨-229447266304,-229447266240⟩ : DyadicInterval 40),(⟨742504266425,742504285755⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189926107136,189926107200⟩ : DyadicInterval 40),(⟨-229728088960,-229728088896⟩ : DyadicInterval 40),(⟨742460798925,742460818255⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189690775808,189690775872⟩ : DyadicInterval 40),(⟨-229383482240,-229383482176⟩ : DyadicInterval 40),(⟨742514134081,742514153411⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189926107136,189926107200⟩ : DyadicInterval 40),(⟨-229728088960,-229728088896⟩ : DyadicInterval 40),(⟨742460798925,742460818255⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,26601110⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26600768,26600832⟩ : DyadicInterval 40),(⟨-26601472,-26601408⟩ : DyadicInterval 40),(⟨762123383260,762123402589⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-704,0⟩ : DyadicInterval 40),(⟨762123383616,762123403232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨207062667761,207316469278⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189712555328,189712555392⟩ : DyadicInterval 40),(⟨-229415367360,-229415367296⟩ : DyadicInterval 40),(⟨742509201568,742509220897⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189926114304,189926114368⟩ : DyadicInterval 40),(⟨-229728099456,-229728099392⟩ : DyadicInterval 40),(⟨742460797300,742460816629⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39801985088,-39702811904⟩ : DyadicInterval 40),(⟨781974789568,782024395424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨189734343232,189926107200⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-229728088960,-229447266240⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e936_ok : ecellOkT e936 = true := by decide +kernel
theorem e936_pos {a z : ℝ} (ha1 : ((154293/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((386157/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e936 e936_ok ha1 ha2 hz1 hz2 hz

-- box ['386157/2048000', '773163/4096000', '1999/2000', '3999/4000']  interval_lower 133652433/549755813888
noncomputable def e937 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1306828088541,0,true,189926107136,189926107200⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨892195167011,0,false,-229728088960,-229728088896⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1307055990244,0,true,190117837568,190117837632⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨891967265308,0,false,-230008983296,-230008983232⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1306724430310,0,true,189838889856,189838889920⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨892298825242,0,false,-229600351424,-229600351360⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1307004104154,0,true,190074189504,190074189568⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨892019151398,0,false,-229945026112,-229945026048⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538228016,0,true,26599872,26599936⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485027536,0,false,-26600576,-26600512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564890989,0,true,53261888,53261952⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458364563,0,false,-53264512,-53264448⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625195,0,false,-2624,-2560⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627133,0,false,-704,-640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1306776254441,0,true,189882495168,189882495232⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨892247001111,0,false,-229664212160,-229664212096⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1307030055798,0,true,190096020992,190096021056⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨891993199754,0,false,-229977014848,-229977014784⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1060345240735,0,false,-39880993856,-39880993792⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1060440985519,0,false,-39781716992,-39781716928⟩
    { al := (386157/2048000), au := (773163/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨207316460765,207544362468⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189926107136,189926107200⟩ : DyadicInterval 40),(⟨-229728088960,-229728088896⟩ : DyadicInterval 40),(⟨742460798926,742460818255⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190117837568,190117837632⟩ : DyadicInterval 40),(⟨-230008983296,-230008983232⟩ : DyadicInterval 40),(⟨742417282440,742417301770⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189838889856,189838889920⟩ : DyadicInterval 40),(⟨-229600351424,-229600351360⟩ : DyadicInterval 40),(⟨742480575665,742480594994⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190074189504,190074189568⟩ : DyadicInterval 40),(⟨-229945026112,-229945026048⟩ : DyadicInterval 40),(⟨742427194070,742427213399⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨26600240,53263213⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26599872,26599936⟩ : DyadicInterval 40),(⟨-26600576,-26600512⟩ : DyadicInterval 40),(⟨762123383260,762123402589⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53261888,53261952⟩ : DyadicInterval 40),(⟨-53264512,-53264448⟩ : DyadicInterval 40),(⟨762123382283,762123401612⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2624,-640⟩ : DyadicInterval 40),(⟨762123383936,762123404192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨207264626665,207518428022⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189882495168,189882495232⟩ : DyadicInterval 40),(⟨-229664212160,-229664212096⟩ : DyadicInterval 40),(⟨742470689498,742470708828⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190096020992,190096021056⟩ : DyadicInterval 40),(⟨-229977014848,-229977014784⟩ : DyadicInterval 40),(⟨742422236931,742422256260⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39880993856,-39781716928⟩ : DyadicInterval 40),(⟨782014242080,782063899808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨189926107136,190117837632⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-230008983296,-229728088896⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e937_ok : ecellOkT e937 = true := by decide +kernel
theorem e937_pos {a z : ℝ} (ha1 : ((386157/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((773163/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e937 e937_ok ha1 ha2 hz1 hz2 hz

-- box ['773163/4096000', '193503/1024000', '1999/2000', '3999/4000']  interval_lower 67768729/274877906944
noncomputable def e938 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1307055990243,0,true,190117837568,190117837632⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨891967265309,0,false,-230008983296,-230008983232⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1307283891946,0,true,190309534592,190309534656⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨891739363606,0,false,-230289949440,-230289949376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1306952218061,0,true,190030539648,190030539712⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨892071037491,0,false,-229881072640,-229881072576⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1307231948881,0,true,190265846144,190265846208⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨891791306671,0,false,-230225905664,-230225905600⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538258818,0,true,26630656,26630720⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484996734,0,false,-26631424,-26631360⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564952605,0,true,53323520,53323584⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458302947,0,false,-53326144,-53326080⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625189,0,false,-2624,-2560⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627131,0,false,-704,-640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1307004099167,0,true,190074185280,190074185344⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨892019156385,0,false,-229945019968,-229945019904⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1307257929008,0,true,190287697792,190287697856⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨891765326544,0,false,-230257937664,-230257937600⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1060259177337,0,false,-39970239808,-39970239744⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1060355038072,0,false,-39870834688,-39870834624⟩
    { al := (773163/4096000), au := (193503/1024000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨207544362467,207772264170⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190117837568,190117837632⟩ : DyadicInterval 40),(⟨-230008983296,-230008983232⟩ : DyadicInterval 40),(⟨742417282441,742417301770⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190309534592,190309534656⟩ : DyadicInterval 40),(⟨-230289949440,-230289949376⟩ : DyadicInterval 40),(⟨742373716972,742373736302⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190030539648,190030539712⟩ : DyadicInterval 40),(⟨-229881072640,-229881072576⟩ : DyadicInterval 40),(⟨742437103193,742437122523⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190265846144,190265846208⟩ : DyadicInterval 40),(⟨-230225905664,-230225905600⟩ : DyadicInterval 40),(⟨742383650690,742383670020⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨26631042,53324829⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26630656,26630720⟩ : DyadicInterval 40),(⟨-26631424,-26631360⟩ : DyadicInterval 40),(⟨762123383290,762123402619⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53323520,53323584⟩ : DyadicInterval 40),(⟨-53326144,-53326080⟩ : DyadicInterval 40),(⟨762123382277,762123401606⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2624,-640⟩ : DyadicInterval 40),(⟨762123383936,762123404192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨207492471391,207746301232⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190074185280,190074185344⟩ : DyadicInterval 40),(⟨-229945019968,-229945019904⟩ : DyadicInterval 40),(⟨742427195041,742427214371⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190287697792,190287697856⟩ : DyadicInterval 40),(⟨-230257937664,-230257937600⟩ : DyadicInterval 40),(⟨742378682511,742378701841⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39970239808,-39870834624⟩ : DyadicInterval 40),(⟨782058800928,782108522784⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨190117837568,190309534656⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-230289949440,-230008983232⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e938_ok : ecellOkT e938 = true := by decide +kernel
theorem e938_pos {a z : ℝ} (ha1 : ((773163/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((193503/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e938 e938_ok ha1 ha2 hz1 hz2 hz

-- box ['386157/2048000', '773163/4096000', '3999/4000', '1']  interval_lower 66649451/274877906944
noncomputable def e939 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1306828088541,0,true,189926107136,189926107200⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨892195167011,0,false,-229728088960,-229728088896⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1307055990244,0,true,190117837568,190117837632⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨891967265308,0,false,-230008983296,-230008983232⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1306776259425,0,true,189882499392,189882499456⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨892246996127,0,false,-229664218304,-229664218240⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538259689,0,true,26631552,26631616⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484995863,0,false,-26632256,-26632192⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627130,0,false,-704,-640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1306802168752,0,true,189904299072,189904299136⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨892221086800,0,false,-229696146688,-229696146624⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1307055998756,0,true,190117844736,190117844800⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨891967256796,0,false,-230008993792,-230008993728⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1060335447336,0,false,-39891149056,-39891148992⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1060431214898,0,false,-39791847616,-39791847552⟩
    { al := (386157/2048000), au := (773163/4096000), zl := (3999/4000), zu := 1,
      A := ⟨207316460765,207544362468⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189926107136,189926107200⟩ : DyadicInterval 40),(⟨-229728088960,-229728088896⟩ : DyadicInterval 40),(⟨742460798926,742460818255⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190117837568,190117837632⟩ : DyadicInterval 40),(⟨-230008983296,-230008983232⟩ : DyadicInterval 40),(⟨742417282440,742417301770⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189882499392,189882499456⟩ : DyadicInterval 40),(⟨-229664218304,-229664218240⟩ : DyadicInterval 40),(⟨742470688530,742470707860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190117837568,190117837632⟩ : DyadicInterval 40),(⟨-230008983296,-230008983232⟩ : DyadicInterval 40),(⟨742417282440,742417301770⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,26631913⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26631552,26631616⟩ : DyadicInterval 40),(⟨-26632256,-26632192⟩ : DyadicInterval 40),(⟨762123383258,762123402587⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-704,0⟩ : DyadicInterval 40),(⟨762123383616,762123403232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨207290540976,207544370980⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨189904299072,189904299136⟩ : DyadicInterval 40),(⟨-229696146688,-229696146624⟩ : DyadicInterval 40),(⟨742465745033,742465764362⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190117844736,190117844800⟩ : DyadicInterval 40),(⟨-230008993792,-230008993728⟩ : DyadicInterval 40),(⟨742417280811,742417300141⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39891149056,-39791847552⟩ : DyadicInterval 40),(⟨782019307392,782068977408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨189926107136,190117837632⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-230008983296,-229728088896⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e939_ok : ecellOkT e939 = true := by decide +kernel
theorem e939_pos {a z : ℝ} (ha1 : ((386157/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((773163/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e939 e939_ok ha1 ha2 hz1 hz2 hz

-- box ['773163/4096000', '193503/1024000', '3999/4000', '1']  interval_lower 135182561/549755813888
noncomputable def e940 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1307055990243,0,true,190117837568,190117837632⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨891967265309,0,false,-230008983296,-230008983232⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1307283891946,0,true,190309534592,190309534656⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨891739363606,0,false,-230289949440,-230289949376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1307004104152,0,true,190074189504,190074189568⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨892019151400,0,false,-229945026112,-229945026048⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538290498,0,true,26662336,26662400⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484965054,0,false,-26663104,-26663040⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627129,0,false,-704,-640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1307030041961,0,true,190096009344,190096009408⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨891993213591,0,false,-229976997760,-229976997696⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1307283900458,0,true,190309541760,190309541824⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨891739355094,0,false,-230289959936,-230289959872⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1060249362416,0,false,-39980418176,-39980418112⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1060345245959,0,false,-39880988416,-39880988352⟩
    { al := (773163/4096000), au := (193503/1024000), zl := (3999/4000), zu := 1,
      A := ⟨207544362467,207772264170⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190117837568,190117837632⟩ : DyadicInterval 40),(⟨-230008983296,-230008983232⟩ : DyadicInterval 40),(⟨742417282441,742417301770⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190309534592,190309534656⟩ : DyadicInterval 40),(⟨-230289949440,-230289949376⟩ : DyadicInterval 40),(⟨742373716972,742373736302⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190074189504,190074189568⟩ : DyadicInterval 40),(⟨-229945026112,-229945026048⟩ : DyadicInterval 40),(⟨742427194071,742427213400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190309534592,190309534656⟩ : DyadicInterval 40),(⟨-230289949440,-230289949376⟩ : DyadicInterval 40),(⟨742373716972,742373736302⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,26662722⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26662336,26662400⟩ : DyadicInterval 40),(⟨-26663104,-26663040⟩ : DyadicInterval 40),(⟨762123383289,762123402618⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-704,0⟩ : DyadicInterval 40),(⟨762123383616,762123403232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨207518414185,207772272682⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190096009344,190096009408⟩ : DyadicInterval 40),(⟨-229976997760,-229976997696⟩ : DyadicInterval 40),(⟨742422239566,742422258895⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190309541760,190309541824⟩ : DyadicInterval 40),(⟨-230289959936,-230289959872⟩ : DyadicInterval 40),(⟨742373715339,742373734668⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-39980418176,-39880988352⟩ : DyadicInterval 40),(⟨782063877792,782113611968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨190117837568,190309534656⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-230289949440,-230008983232⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e940_ok : ecellOkT e940 = true := by decide +kernel
theorem e940_pos {a z : ℝ} (ha1 : ((773163/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((193503/1024000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e940 e940_ok ha1 ha2 hz1 hz2 hz

-- box ['193503/1024000', '774861/4096000', '999/1000', '3997/4000']  interval_lower 69071229/274877906944
noncomputable def e941 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1307283891945,0,true,190309534592,190309534656⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨891739363607,0,false,-230289949440,-230289949376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1307511793648,0,true,190501198144,190501198208⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨891511461904,0,false,-230570987328,-230570987264⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1307076119680,0,true,190134770560,190134770624⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨891947135872,0,false,-230033796736,-230033796672⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1307355793524,0,true,190370006848,190370006912⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨891667462028,0,false,-230378607424,-230378607360⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591612769,0,true,79982080,79982144⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431642783,0,false,-79987904,-79987840⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099618398997,0,true,106766016,106766080⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099404856555,0,false,-106776448,-106776384⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511617407,0,false,-10432,-10368⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621958,0,false,-5824,-5760⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1307180001838,0,true,190222152704,190222152768⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨891843253714,0,false,-230161860736,-230161860672⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1307433802858,0,true,190435612288,190435612352⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨891589452694,0,false,-230474804608,-230474804544⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1060192688531,0,false,-40039192320,-40039192256⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1060288619583,0,false,-39939707968,-39939707904⟩
    { al := (193503/1024000), au := (774861/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨207772264169,208000165872⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190309534592,190309534656⟩ : DyadicInterval 40),(⟨-230289949440,-230289949376⟩ : DyadicInterval 40),(⟨742373716972,742373736302⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190501198144,190501198208⟩ : DyadicInterval 40),(⟨-230570987328,-230570987264⟩ : DyadicInterval 40),(⟨742330102520,742330121849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190134770560,190134770624⟩ : DyadicInterval 40),(⟨-230033796736,-230033796672⟩ : DyadicInterval 40),(⟨742413436484,742413455813⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190370006848,190370006912⟩ : DyadicInterval 40),(⟨-230378607424,-230378607360⟩ : DyadicInterval 40),(⟨742359962192,742359981521⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨79984993,106771221⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79982080,79982144⟩ : DyadicInterval 40),(⟨-79987904,-79987840⟩ : DyadicInterval 40),(⟨762123380645,762123399974⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨106766016,106766080⟩ : DyadicInterval 40),(⟨-106776448,-106776384⟩ : DyadicInterval 40),(⟨762123378399,762123397729⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-10432,-5760⟩ : DyadicInterval 40),(⟨762123386496,762123408096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨207668374062,207922175082⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190222152704,190222152768⟩ : DyadicInterval 40),(⟨-230161860736,-230161860672⟩ : DyadicInterval 40),(⟨742393582581,742393601910⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190435612288,190435612352⟩ : DyadicInterval 40),(⟨-230474804608,-230474804544⟩ : DyadicInterval 40),(⟨742345033430,742345052759⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40039192320,-39939707904⟩ : DyadicInterval 40),(⟨782093237568,782142999040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨190309534592,190501198208⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-230570987328,-230289949376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e941_ok : ecellOkT e941 = true := by decide +kernel
theorem e941_pos {a z : ℝ} (ha1 : ((193503/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((774861/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e941 e941_ok ha1 ha2 hz1 hz2 hz

-- box ['774861/4096000', '77571/409600', '999/1000', '3997/4000']  interval_lower 70023429/274877906944
noncomputable def e942 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1307511793647,0,true,190501198144,190501198208⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨891511461905,0,false,-230570987328,-230570987264⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1307739695350,0,true,190692828352,190692828416⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨891283560202,0,false,-230852097152,-230852097088⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1307303793481,0,true,190326272960,190326273024⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨891719462071,0,false,-230314488192,-230314488128⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1307583524300,0,true,190561516160,190561516224⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨891439731252,0,false,-230659457152,-230659457088⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591705203,0,true,80074496,80074560⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431550349,0,false,-80080384,-80080320⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099618522266,0,true,106889280,106889344⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099404733286,0,false,-106899712,-106899648⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511617383,0,false,-10432,-10368⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621944,0,false,-5888,-5824⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1307407789591,0,true,190413735680,190413735744⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨891615465961,0,false,-230442725376,-230442725312⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1307661619102,0,true,190627182016,190627182080⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨891361636450,0,false,-230755784384,-230755784320⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1060106479349,0,false,-40128602304,-40128602240⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1060202526349,0,false,-40028989696,-40028989632⟩
    { al := (774861/4096000), au := (77571/409600), zl := (999/1000), zu := (3997/4000),
      A := ⟨208000165871,208228067574⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190501198144,190501198208⟩ : DyadicInterval 40),(⟨-230570987328,-230570987264⟩ : DyadicInterval 40),(⟨742330102520,742330121850⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190692828352,190692828416⟩ : DyadicInterval 40),(⟨-230852097152,-230852097088⟩ : DyadicInterval 40),(⟨742286439074,742286458403⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190326272960,190326273024⟩ : DyadicInterval 40),(⟨-230314488192,-230314488128⟩ : DyadicInterval 40),(⟨742369910271,742369929600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190561516160,190561516224⟩ : DyadicInterval 40),(⟨-230659457152,-230659457088⟩ : DyadicInterval 40),(⟨742316365007,742316384336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨80077427,106894490⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80074496,80074560⟩ : DyadicInterval 40),(⟨-80080384,-80080320⟩ : DyadicInterval 40),(⟨762123380663,762123399993⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨106889280,106889344⟩ : DyadicInterval 40),(⟨-106899712,-106899648⟩ : DyadicInterval 40),(⟨762123378375,762123397705⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-10432,-5824⟩ : DyadicInterval 40),(⟨762123386528,762123408096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨207896161815,208149991326⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190413735680,190413735744⟩ : DyadicInterval 40),(⟨-230442725376,-230442725312⟩ : DyadicInterval 40),(⟨742350012260,742350031590⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190627182016,190627182080⟩ : DyadicInterval 40),(⟨-230755784384,-230755784320⟩ : DyadicInterval 40),(⟨742301403142,742301422472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40128602304,-40028989632⟩ : DyadicInterval 40),(⟨782137878432,782187704032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨190501198144,190692828416⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-230852097152,-230570987264⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e942_ok : ecellOkT e942 = true := by decide +kernel
theorem e942_pos {a z : ℝ} (ha1 : ((774861/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((77571/409600 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e942 e942_ok ha1 ha2 hz1 hz2 hz

-- box ['193503/1024000', '774861/4096000', '3997/4000', '1999/2000']  interval_lower 137786811/549755813888
noncomputable def e943 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1307283891945,0,true,190309534592,190309534656⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨891739363607,0,false,-230289949440,-230289949376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1307511793648,0,true,190501198144,190501198208⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨891511461904,0,false,-230570987328,-230570987264⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1307128062746,0,true,190178464192,190178464256⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨891895192806,0,false,-230097829312,-230097829248⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1307407793566,0,true,190413739008,190413739072⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨891615461986,0,false,-230442730304,-230442730240⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564951375,0,true,53322304,53322368⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458304177,0,false,-53324928,-53324864⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591706794,0,true,80076096,80076160⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431548758,0,false,-80081984,-80081920⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621943,0,false,-5888,-5824⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625190,0,false,-2624,-2560⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1307205972781,0,true,190243997504,190243997568⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨891817282771,0,false,-230193879552,-230193879488⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1307459802456,0,true,190457476928,190457476992⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨891563453096,0,false,-230506867904,-230506867840⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1060182854654,0,false,-40049390912,-40049390848⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1060278808534,0,false,-39949882048,-39949881984⟩
    { al := (193503/1024000), au := (774861/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨207772264169,208000165872⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190309534592,190309534656⟩ : DyadicInterval 40),(⟨-230289949440,-230289949376⟩ : DyadicInterval 40),(⟨742373716972,742373736302⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190501198144,190501198208⟩ : DyadicInterval 40),(⟨-230570987328,-230570987264⟩ : DyadicInterval 40),(⟨742330102520,742330121849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190178464192,190178464256⟩ : DyadicInterval 40),(⟨-230097829312,-230097829248⟩ : DyadicInterval 40),(⟨742403510409,742403529738⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190413739008,190413739072⟩ : DyadicInterval 40),(⟨-230442730304,-230442730240⟩ : DyadicInterval 40),(⟨742350011519,742350030848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨53323599,80079018⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53322304,53322368⟩ : DyadicInterval 40),(⟨-53324928,-53324864⟩ : DyadicInterval 40),(⟨762123382277,762123401606⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80076096,80076160⟩ : DyadicInterval 40),(⟨-80081984,-80081920⟩ : DyadicInterval 40),(⟨762123380663,762123399992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5888,-2560⟩ : DyadicInterval 40),(⟨762123384896,762123405824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨207694345005,207948174680⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190243997504,190243997568⟩ : DyadicInterval 40),(⟨-230193879552,-230193879488⟩ : DyadicInterval 40),(⟨742388617427,742388636756⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190457476928,190457476992⟩ : DyadicInterval 40),(⟨-230506867904,-230506867840⟩ : DyadicInterval 40),(⟨742340056595,742340075924⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40049390912,-39949881984⟩ : DyadicInterval 40),(⟨782098324608,782148098336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨190309534592,190501198208⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-230570987328,-230289949376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e943_ok : ecellOkT e943 = true := by decide +kernel
theorem e943_pos {a z : ℝ} (ha1 : ((193503/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((774861/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e943 e943_ok ha1 ha2 hz1 hz2 hz

-- box ['774861/4096000', '77571/409600', '3997/4000', '1999/2000']  interval_lower 17461213/68719476736
noncomputable def e944 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1307511793647,0,true,190501198144,190501198208⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨891511461905,0,false,-230570987328,-230570987264⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1307739695350,0,true,190692828352,190692828416⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨891283560202,0,false,-230852097152,-230852097088⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1307355793522,0,true,190370006848,190370006912⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨891667462030,0,false,-230378607360,-230378607296⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1307635581317,0,true,190605288640,190605288704⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨891387674235,0,false,-230723666752,-230723666688⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565012999,0,true,53383872,53383936⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458242553,0,false,-53386560,-53386496⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591799247,0,true,80168512,80168576⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431456305,0,false,-80174400,-80174336⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621930,0,false,-5888,-5824⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625184,0,false,-2624,-2560⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1307433789016,0,true,190435600640,190435600704⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨891589466536,0,false,-230474787520,-230474787456⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1307687647186,0,true,190649066816,190649066880⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨891335608366,0,false,-230787891008,-230787890944⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1060096623911,0,false,-40138824128,-40138824064⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1060192693767,0,false,-40039186880,-40039186816⟩
    { al := (774861/4096000), au := (77571/409600), zl := (3997/4000), zu := (1999/2000),
      A := ⟨208000165871,208228067574⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190501198144,190501198208⟩ : DyadicInterval 40),(⟨-230570987328,-230570987264⟩ : DyadicInterval 40),(⟨742330102520,742330121850⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190692828352,190692828416⟩ : DyadicInterval 40),(⟨-230852097152,-230852097088⟩ : DyadicInterval 40),(⟨742286439074,742286458403⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190370006848,190370006912⟩ : DyadicInterval 40),(⟨-230378607360,-230378607296⟩ : DyadicInterval 40),(⟨742359962166,742359981496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190605288640,190605288704⟩ : DyadicInterval 40),(⟨-230723666752,-230723666688⟩ : DyadicInterval 40),(⟨742306392255,742306411585⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨53385223,80171471⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53383872,53383936⟩ : DyadicInterval 40),(⟨-53386560,-53386496⟩ : DyadicInterval 40),(⟨762123382303,762123401633⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80168512,80168576⟩ : DyadicInterval 40),(⟨-80174400,-80174336⟩ : DyadicInterval 40),(⟨762123380650,762123399979⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5888,-2560⟩ : DyadicInterval 40),(⟨762123384896,762123405824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨207922161240,208176019410⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190435600640,190435600704⟩ : DyadicInterval 40),(⟨-230474787520,-230474787456⟩ : DyadicInterval 40),(⟨742345036076,742345055406⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190649066816,190649066880⟩ : DyadicInterval 40),(⟨-230787891008,-230787890944⟩ : DyadicInterval 40),(⟨742296415247,742296434577⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40138824128,-40039186816⟩ : DyadicInterval 40),(⟨782142977024,782192814944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨190501198144,190692828416⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-230852097152,-230570987264⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e944_ok : ecellOkT e944 = true := by decide +kernel
theorem e944_pos {a z : ℝ} (ha1 : ((774861/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((77571/409600 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e944 e944_ok ha1 ha2 hz1 hz2 hz

-- box ['77571/409600', '776559/4096000', '999/1000', '3997/4000']  interval_lower 141959521/549755813888
noncomputable def e945 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1307739695349,0,true,190692828352,190692828416⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨891283560203,0,false,-230852097152,-230852097088⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1307967597052,0,true,190884425152,190884425216⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨891055658500,0,false,-231133278848,-231133278784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1307531467281,0,true,190517741952,190517742016⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨891491788271,0,false,-230595251328,-230595251264⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1307811255076,0,true,190752992192,190752992256⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨891212000476,0,false,-230940378752,-230940378688⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591797653,0,true,80166912,80166976⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431457899,0,false,-80172800,-80172736⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099618645558,0,true,107012544,107012608⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099404609994,0,false,-107023040,-107022976⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511617359,0,false,-10432,-10368⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621931,0,false,-5888,-5824⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1307635577338,0,true,190605285312,190605285376⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨891387678214,0,false,-230723661824,-230723661760⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1307889435344,0,true,190818718400,190818718464⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨891133820208,0,false,-231036836032,-231036835968⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1060020175762,0,false,-40218117568,-40218117504⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1060116338734,0,false,-40118376512,-40118376448⟩
    { al := (77571/409600), au := (776559/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨208228067573,208455969276⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190692828352,190692828416⟩ : DyadicInterval 40),(⟨-230852097152,-230852097088⟩ : DyadicInterval 40),(⟨742286439074,742286458403⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190884425152,190884425216⟩ : DyadicInterval 40),(⟨-231133278848,-231133278784⟩ : DyadicInterval 40),(⟨742242726634,742242745964⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190517741952,190517742016⟩ : DyadicInterval 40),(⟨-230595251328,-230595251264⟩ : DyadicInterval 40),(⟨742326335205,742326354535⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190752992192,190752992256⟩ : DyadicInterval 40),(⟨-230940378752,-230940378688⟩ : DyadicInterval 40),(⟨742272718908,742272738237⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨80169877,107017782⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80166912,80166976⟩ : DyadicInterval 40),(⟨-80172800,-80172736⟩ : DyadicInterval 40),(⟨762123380650,762123399979⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨107012544,107012608⟩ : DyadicInterval 40),(⟨-107023040,-107022976⟩ : DyadicInterval 40),(⟨762123378383,762123397713⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-10432,-5824⟩ : DyadicInterval 40),(⟨762123386528,762123408096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨208123949562,208377807568⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190605285312,190605285376⟩ : DyadicInterval 40),(⟨-230723661824,-230723661760⟩ : DyadicInterval 40),(⟨742306392999,742306412328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190818718400,190818718464⟩ : DyadicInterval 40),(⟨-231036836032,-231036835968⟩ : DyadicInterval 40),(⟨742257723900,742257743230⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40218117568,-40118376448⟩ : DyadicInterval 40),(⟨782182571840,782232461664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨190692828352,190884425216⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-231133278848,-230852097088⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e945_ok : ecellOkT e945 = true := by decide +kernel
theorem e945_pos {a z : ℝ} (ha1 : ((77571/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((776559/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e945 e945_ok ha1 ha2 hz1 hz2 hz

-- box ['776559/4096000', '12147/64000', '999/1000', '3997/4000']  interval_lower 287760613/1099511627776
noncomputable def e946 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1307967597051,0,true,190884425152,190884425216⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨891055658501,0,false,-231133278848,-231133278784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1308195498755,0,true,191075988608,191075988672⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨890827756797,0,false,-231414532480,-231414532416⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1307759141081,0,true,190709177664,190709177728⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨891264114471,0,false,-230876086208,-230876086144⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1308038985852,0,true,190944434816,190944434880⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨890984269700,0,false,-231221372032,-231221371968⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591890120,0,true,80259392,80259456⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431365432,0,false,-80265280,-80265216⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099618768870,0,true,107135872,107135936⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099404486682,0,false,-107146368,-107146304⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511617335,0,false,-10496,-10432⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621917,0,false,-5888,-5824⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1307863365087,0,true,190796801536,190796801600⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨891159890465,0,false,-231004670080,-231004670016⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1308117251591,0,true,191010221440,191010221504⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨890906003961,0,false,-231317959488,-231317959424⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1059933777767,0,false,-40307737984,-40307737920⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1060030056737,0,false,-40207868480,-40207868416⟩
    { al := (776559/4096000), au := (12147/64000), zl := (999/1000), zu := (3997/4000),
      A := ⟨208455969275,208683870979⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190884425152,190884425216⟩ : DyadicInterval 40),(⟨-231133278848,-231133278784⟩ : DyadicInterval 40),(⟨742242726635,742242745964⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191075988608,191075988672⟩ : DyadicInterval 40),(⟨-231414532480,-231414532416⟩ : DyadicInterval 40),(⟨742198965177,742198984507⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190709177664,190709177728⟩ : DyadicInterval 40),(⟨-230876086208,-230876086144⟩ : DyadicInterval 40),(⟨742282711225,742282730554⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190944434816,190944434880⟩ : DyadicInterval 40),(⟨-231221372032,-231221371968⟩ : DyadicInterval 40),(⟨742229023880,742229043209⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨80262344,107141094⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80259392,80259456⟩ : DyadicInterval 40),(⟨-80265280,-80265216⟩ : DyadicInterval 40),(⟨762123380636,762123399966⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨107135872,107135936⟩ : DyadicInterval 40),(⟨-107146368,-107146304⟩ : DyadicInterval 40),(⟨762123378359,762123397689⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-10496,-5824⟩ : DyadicInterval 40),(⟨762123386528,762123408128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨208351737311,208605623815⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190796801536,190796801600⟩ : DyadicInterval 40),(⟨-231004670080,-231004670016⟩ : DyadicInterval 40),(⟨742262724821,742262744150⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191010221440,191010221504⟩ : DyadicInterval 40),(⟨-231317959488,-231317959424⟩ : DyadicInterval 40),(⟨742213995666,742214014995⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40307737984,-40207868416⟩ : DyadicInterval 40),(⟨782227317824,782277271872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨190884425152,191075988672⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-231414532480,-231133278784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e946_ok : ecellOkT e946 = true := by decide +kernel
theorem e946_pos {a z : ℝ} (ha1 : ((776559/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((12147/64000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e946 e946_ok ha1 ha2 hz1 hz2 hz

-- box ['77571/409600', '776559/4096000', '3997/4000', '1999/2000']  interval_lower 283201675/1099511627776
noncomputable def e947 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1307739695349,0,true,190692828352,190692828416⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨891283560203,0,false,-230852097152,-230852097088⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1307967597052,0,true,190884425152,190884425216⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨891055658500,0,false,-231133278848,-231133278784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1307583524298,0,true,190561516160,190561516224⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨891439731254,0,false,-230659457152,-230659457088⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1307863369068,0,true,190796804928,190796804992⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨891159886484,0,false,-231004675008,-231004674944⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565074634,0,true,53445504,53445568⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458180918,0,false,-53448192,-53448128⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591891717,0,true,80260992,80261056⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431363835,0,false,-80266880,-80266816⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621916,0,false,-5888,-5824⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625178,0,false,-2624,-2560⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1307661605250,0,true,190627170368,190627170432⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨891361650302,0,false,-230755767296,-230755767232⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1307915491914,0,true,190840623360,190840623424⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨891107763638,0,false,-231068985984,-231068985920⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1060010298740,0,false,-40228362560,-40228362496⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1060106484595,0,false,-40128596864,-40128596800⟩
    { al := (77571/409600), au := (776559/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨208228067573,208455969276⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190692828352,190692828416⟩ : DyadicInterval 40),(⟨-230852097152,-230852097088⟩ : DyadicInterval 40),(⟨742286439074,742286458403⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190884425152,190884425216⟩ : DyadicInterval 40),(⟨-231133278848,-231133278784⟩ : DyadicInterval 40),(⟨742242726634,742242745964⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190561516160,190561516224⟩ : DyadicInterval 40),(⟨-230659457152,-230659457088⟩ : DyadicInterval 40),(⟨742316365007,742316384337⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190796804928,190796804992⟩ : DyadicInterval 40),(⟨-231004675008,-231004674944⟩ : DyadicInterval 40),(⟨742262724037,742262743366⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨53446858,80263941⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53445504,53445568⟩ : DyadicInterval 40),(⟨-53448192,-53448128⟩ : DyadicInterval 40),(⟨762123382297,762123401627⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80260992,80261056⟩ : DyadicInterval 40),(⟨-80266880,-80266816⟩ : DyadicInterval 40),(⟨762123380636,762123399965⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5888,-2560⟩ : DyadicInterval 40),(⟨762123384896,762123405824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨208149977474,208403864138⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190627170368,190627170432⟩ : DyadicInterval 40),(⟨-230755767296,-230755767232⟩ : DyadicInterval 40),(⟨742301405796,742301425126⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190840623360,190840623424⟩ : DyadicInterval 40),(⟨-231068985984,-231068985920⟩ : DyadicInterval 40),(⟨742252724920,742252744250⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40228362560,-40128596800⟩ : DyadicInterval 40),(⟨782187682016,782237584160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨190692828352,190884425216⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-231133278848,-230852097088⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e947_ok : ecellOkT e947 = true := by decide +kernel
theorem e947_pos {a z : ℝ} (ha1 : ((77571/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((776559/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e947 e947_ok ha1 ha2 hz1 hz2 hz

-- box ['776559/4096000', '12147/64000', '3997/4000', '1999/2000']  interval_lower 287040887/1099511627776
noncomputable def e948 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1307967597051,0,true,190884425152,190884425216⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨891055658501,0,false,-231133278848,-231133278784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1308195498755,0,true,191075988608,191075988672⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨890827756797,0,false,-231414532480,-231414532416⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1307811255074,0,true,190752992192,190752992256⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨891212000478,0,false,-230940378688,-230940378624⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1308091156820,0,true,190988287808,190988287872⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨890932098732,0,false,-231285755072,-231285755008⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565136280,0,true,53507200,53507264⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458119272,0,false,-53509824,-53509760⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591984204,0,true,80353472,80353536⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431271348,0,false,-80359424,-80359360⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621903,0,false,-5888,-5824⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625172,0,false,-2624,-2560⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1307889421491,0,true,190818706752,190818706816⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨891133834061,0,false,-231036818880,-231036818816⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1308143336645,0,true,191032146496,191032146560⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨890879918907,0,false,-231350152832,-231350152768⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1059923879137,0,false,-40318006272,-40318006208⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1060020181014,0,false,-40218112064,-40218112000⟩
    { al := (776559/4096000), au := (12147/64000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨208455969275,208683870979⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190884425152,190884425216⟩ : DyadicInterval 40),(⟨-231133278848,-231133278784⟩ : DyadicInterval 40),(⟨742242726635,742242745964⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191075988608,191075988672⟩ : DyadicInterval 40),(⟨-231414532480,-231414532416⟩ : DyadicInterval 40),(⟨742198965177,742198984507⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190752992192,190752992256⟩ : DyadicInterval 40),(⟨-230940378688,-230940378624⟩ : DyadicInterval 40),(⟨742272718882,742272738211⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190988287808,190988287872⟩ : DyadicInterval 40),(⟨-231285755072,-231285755008⟩ : DyadicInterval 40),(⟨742219006890,742219026220⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨53508504,80356428⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53507200,53507264⟩ : DyadicInterval 40),(⟨-53509824,-53509760⟩ : DyadicInterval 40),(⟨762123382259,762123401589⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80353472,80353536⟩ : DyadicInterval 40),(⟨-80359424,-80359360⟩ : DyadicInterval 40),(⟨762123380655,762123399984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5888,-2560⟩ : DyadicInterval 40),(⟨762123384896,762123405824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨208377793715,208631708869⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190818706752,190818706816⟩ : DyadicInterval 40),(⟨-231036818880,-231036818816⟩ : DyadicInterval 40),(⟨742257726535,742257745865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191032146496,191032146560⟩ : DyadicInterval 40),(⟨-231350152832,-231350152768⟩ : DyadicInterval 40),(⟨742208985639,742209004968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40318006272,-40218112000⟩ : DyadicInterval 40),(⟨782232439616,782282406016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨190884425152,191075988672⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-231414532480,-231133278784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e948_ok : ecellOkT e948 = true := by decide +kernel
theorem e948_pos {a z : ℝ} (ha1 : ((776559/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((12147/64000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e948 e948_ok ha1 ha2 hz1 hz2 hz

-- box ['193503/1024000', '774861/4096000', '1999/2000', '3999/4000']  interval_lower 137430633/549755813888
noncomputable def e949 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1307283891945,0,true,190309534592,190309534656⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨891739363607,0,false,-230289949440,-230289949376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1307511793648,0,true,190501198144,190501198208⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨891511461904,0,false,-230570987328,-230570987264⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1307180005812,0,true,190222156032,190222156096⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨891843249740,0,false,-230161865600,-230161865536⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1307459793607,0,true,190457469504,190457469568⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨891563461945,0,false,-230506856960,-230506856896⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538289625,0,true,26661504,26661568⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484965927,0,false,-26662208,-26662144⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565014231,0,true,53385152,53385216⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458241321,0,false,-53387776,-53387712⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625183,0,false,-2624,-2560⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627130,0,false,-704,-640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1307231943889,0,true,190265841984,190265842048⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨891791311663,0,false,-230225899520,-230225899456⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1307485802228,0,true,190479341248,190479341312⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨891537453324,0,false,-230538932288,-230538932224⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1060173019482,0,false,-40059590976,-40059590912⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1060268996197,0,false,-39960057472,-39960057408⟩
    { al := (193503/1024000), au := (774861/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨207772264169,208000165872⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190309534592,190309534656⟩ : DyadicInterval 40),(⟨-230289949440,-230289949376⟩ : DyadicInterval 40),(⟨742373716972,742373736302⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190501198144,190501198208⟩ : DyadicInterval 40),(⟨-230570987328,-230570987264⟩ : DyadicInterval 40),(⟨742330102520,742330121849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190222156032,190222156096⟩ : DyadicInterval 40),(⟨-230161865600,-230161865536⟩ : DyadicInterval 40),(⟨742393581815,742393601145⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190457469504,190457469568⟩ : DyadicInterval 40),(⟨-230506856960,-230506856896⟩ : DyadicInterval 40),(⟨742340058265,742340077595⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨26661849,53386455⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26661504,26661568⟩ : DyadicInterval 40),(⟨-26662208,-26662144⟩ : DyadicInterval 40),(⟨762123383257,762123402586⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53385152,53385216⟩ : DyadicInterval 40),(⟨-53387776,-53387712⟩ : DyadicInterval 40),(⟨762123382271,762123401600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2624,-640⟩ : DyadicInterval 40),(⟨762123383936,762123404192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨207720316113,207974174452⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190265841984,190265842048⟩ : DyadicInterval 40),(⟨-230225899520,-230225899456⟩ : DyadicInterval 40),(⟨742383651626,742383670956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190479341248,190479341312⟩ : DyadicInterval 40),(⟨-230538932288,-230538932224⟩ : DyadicInterval 40),(⟨742335079082,742335098411⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40059590976,-39960057408⟩ : DyadicInterval 40),(⟨782103412320,782153198368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨190309534592,190501198208⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-230570987328,-230289949376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e949_ok : ecellOkT e949 = true := by decide +kernel
theorem e949_pos {a z : ℝ} (ha1 : ((193503/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((774861/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e949 e949_ok ha1 ha2 hz1 hz2 hz

-- box ['774861/4096000', '77571/409600', '1999/2000', '3999/4000']  interval_lower 34833033/137438953472
noncomputable def e950 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1307511793647,0,true,190501198144,190501198208⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨891511461905,0,false,-230570987328,-230570987264⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1307739695350,0,true,190692828352,190692828416⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨891283560202,0,false,-230852097152,-230852097088⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1307407793564,0,true,190413739008,190413739072⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨891615461988,0,false,-230442730304,-230442730240⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1307687638334,0,true,190649059392,190649059456⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨891335617218,0,false,-230787880064,-230787880000⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538320438,0,true,26692288,26692352⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484935114,0,false,-26692992,-26692928⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565075868,0,true,53446784,53446848⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458179684,0,false,-53449408,-53449344⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625177,0,false,-2624,-2560⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627128,0,false,-704,-640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1307459788609,0,true,190457465280,190457465344⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨891563466943,0,false,-230506850816,-230506850752⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1307713675441,0,true,190670951296,190670951360⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨891309580111,0,false,-230819998784,-230819998720⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1060086767177,0,false,-40149047424,-40149047360⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1060182859893,0,false,-40049385472,-40049385408⟩
    { al := (774861/4096000), au := (77571/409600), zl := (1999/2000), zu := (3999/4000),
      A := ⟨208000165871,208228067574⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190501198144,190501198208⟩ : DyadicInterval 40),(⟨-230570987328,-230570987264⟩ : DyadicInterval 40),(⟨742330102520,742330121850⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190692828352,190692828416⟩ : DyadicInterval 40),(⟨-230852097152,-230852097088⟩ : DyadicInterval 40),(⟨742286439074,742286458403⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190413739008,190413739072⟩ : DyadicInterval 40),(⟨-230442730304,-230442730240⟩ : DyadicInterval 40),(⟨742350011519,742350030849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190649059392,190649059456⟩ : DyadicInterval 40),(⟨-230787880064,-230787880000⟩ : DyadicInterval 40),(⟨742296416923,742296436252⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨26692662,53448092⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26692288,26692352⟩ : DyadicInterval 40),(⟨-26692992,-26692928⟩ : DyadicInterval 40),(⟨762123383255,762123402584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53446784,53446848⟩ : DyadicInterval 40),(⟨-53449408,-53449344⟩ : DyadicInterval 40),(⟨762123382265,762123401594⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2624,-640⟩ : DyadicInterval 40),(⟨762123383936,762123404192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨207948160833,208202047665⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190457465280,190457465344⟩ : DyadicInterval 40),(⟨-230506850816,-230506850752⟩ : DyadicInterval 40),(⟨742340059243,742340078572⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190670951296,190670951360⟩ : DyadicInterval 40),(⟨-230819998784,-230819998720⟩ : DyadicInterval 40),(⟨742291426699,742291446028⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40149047424,-40049385408⟩ : DyadicInterval 40),(⟨782148076320,782197926592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨190501198144,190692828416⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-230852097152,-230570987264⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e950_ok : ecellOkT e950 = true := by decide +kernel
theorem e950_pos {a z : ℝ} (ha1 : ((774861/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((77571/409600 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e950 e950_ok ha1 ha2 hz1 hz2 hz

-- box ['193503/1024000', '774861/4096000', '3999/4000', '1']  interval_lower 274148685/1099511627776
noncomputable def e951 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1307283891945,0,true,190309534592,190309534656⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨891739363607,0,false,-230289949440,-230289949376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1307511793648,0,true,190501198144,190501198208⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨891511461904,0,false,-230570987328,-230570987264⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1307231948878,0,true,190265846144,190265846208⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨891791306674,0,false,-230225905664,-230225905600⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538321311,0,true,26693184,26693248⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484934241,0,false,-26693888,-26693824⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627127,0,false,-704,-640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1307257915165,0,true,190287686208,190287686272⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨891765340387,0,false,-230257920576,-230257920512⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1307511802160,0,true,190501205312,190501205376⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨891511453392,0,false,-230570997888,-230570997824⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1060163183020,0,false,-40069792512,-40069792448⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1060259182569,0,false,-39970234368,-39970234304⟩
    { al := (193503/1024000), au := (774861/4096000), zl := (3999/4000), zu := 1,
      A := ⟨207772264169,208000165872⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190309534592,190309534656⟩ : DyadicInterval 40),(⟨-230289949440,-230289949376⟩ : DyadicInterval 40),(⟨742373716972,742373736302⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190501198144,190501198208⟩ : DyadicInterval 40),(⟨-230570987328,-230570987264⟩ : DyadicInterval 40),(⟨742330102520,742330121849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190265846144,190265846208⟩ : DyadicInterval 40),(⟨-230225905664,-230225905600⟩ : DyadicInterval 40),(⟨742383650691,742383670021⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190501198144,190501198208⟩ : DyadicInterval 40),(⟨-230570987328,-230570987264⟩ : DyadicInterval 40),(⟨742330102520,742330121849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,26693535⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26693184,26693248⟩ : DyadicInterval 40),(⟨-26693888,-26693824⟩ : DyadicInterval 40),(⟨762123383255,762123402584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-704,0⟩ : DyadicInterval 40),(⟨762123383616,762123403232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨207746287389,208000174384⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190287686208,190287686272⟩ : DyadicInterval 40),(⟨-230257920576,-230257920512⟩ : DyadicInterval 40),(⟨742378685115,742378704445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190501205312,190501205376⟩ : DyadicInterval 40),(⟨-230570997888,-230570997824⟩ : DyadicInterval 40),(⟨742330100909,742330120239⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40069792512,-39970234304⟩ : DyadicInterval 40),(⟨782108500768,782158299136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨190309534592,190501198208⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-230570987328,-230289949376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e951_ok : ecellOkT e951 = true := by decide +kernel
theorem e951_pos {a z : ℝ} (ha1 : ((193503/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((774861/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e951 e951_ok ha1 ha2 hz1 hz2 hz

-- box ['774861/4096000', '77571/409600', '3999/4000', '1']  interval_lower 69487225/274877906944
noncomputable def e952 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1307511793647,0,true,190501198144,190501198208⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨891511461905,0,false,-230570987328,-230570987264⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1307739695350,0,true,190692828352,190692828416⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨891283560202,0,false,-230852097152,-230852097088⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1307459793605,0,true,190457469440,190457469504⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨891563461947,0,false,-230506856960,-230506856896⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538352131,0,true,26723968,26724032⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484903421,0,false,-26724736,-26724672⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627126,0,false,-704,-640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1307485788375,0,true,190479329600,190479329664⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨891537467177,0,false,-230538915200,-230538915136⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1307739703862,0,true,190692835520,190692835584⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨891283551690,0,false,-230852107648,-230852107584⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1060076909147,0,false,-40159272128,-40159272064⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1060173024724,0,false,-40059585536,-40059585472⟩
    { al := (774861/4096000), au := (77571/409600), zl := (3999/4000), zu := 1,
      A := ⟨208000165871,208228067574⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190501198144,190501198208⟩ : DyadicInterval 40),(⟨-230570987328,-230570987264⟩ : DyadicInterval 40),(⟨742330102520,742330121850⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190692828352,190692828416⟩ : DyadicInterval 40),(⟨-230852097152,-230852097088⟩ : DyadicInterval 40),(⟨742286439074,742286458403⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190457469440,190457469504⟩ : DyadicInterval 40),(⟨-230506856960,-230506856896⟩ : DyadicInterval 40),(⟨742340058304,742340077634⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190692828352,190692828416⟩ : DyadicInterval 40),(⟨-230852097152,-230852097088⟩ : DyadicInterval 40),(⟨742286439074,742286458403⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,26724355⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26723968,26724032⟩ : DyadicInterval 40),(⟨-26724736,-26724672⟩ : DyadicInterval 40),(⟨762123383286,762123402615⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-704,0⟩ : DyadicInterval 40),(⟨762123383616,762123403232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨207974160599,208228076086⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190479329600,190479329664⟩ : DyadicInterval 40),(⟨-230538915200,-230538915136⟩ : DyadicInterval 40),(⟨742335081732,742335101062⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190692835520,190692835584⟩ : DyadicInterval 40),(⟨-230852107648,-230852107584⟩ : DyadicInterval 40),(⟨742286437433,742286456763⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40159272128,-40059585472⟩ : DyadicInterval 40),(⟨782153176352,782203038944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨190501198144,190692828416⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-230852097152,-230570987264⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e952_ok : ecellOkT e952 = true := by decide +kernel
theorem e952_pos {a z : ℝ} (ha1 : ((774861/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((77571/409600 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e952 e952_ok ha1 ha2 hz1 hz2 hz

-- box ['77571/409600', '776559/4096000', '1999/2000', '3999/4000']  interval_lower 282484041/1099511627776
noncomputable def e953 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1307739695349,0,true,190692828352,190692828416⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨891283560203,0,false,-230852097152,-230852097088⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1307967597052,0,true,190884425152,190884425216⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨891055658500,0,false,-231133278848,-231133278784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1307635581315,0,true,190605288640,190605288704⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨891387674237,0,false,-230723666752,-230723666688⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1307915483060,0,true,190840615936,190840616000⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨891107772492,0,false,-231068975040,-231068974976⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538351256,0,true,26723136,26723200⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484904296,0,false,-26723840,-26723776⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565137516,0,true,53508416,53508480⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458118036,0,false,-53511104,-53511040⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625171,0,false,-2624,-2560⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627127,0,false,-704,-640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1307687633333,0,true,190649055168,190649055232⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨891335622219,0,false,-230787873920,-230787873856⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1307941548656,0,true,190862528000,190862528064⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨891081706896,0,false,-231101137088,-231101137024⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1060000420417,0,false,-40238609088,-40238609024⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1060096629158,0,false,-40138818688,-40138818624⟩
    { al := (77571/409600), au := (776559/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨208228067573,208455969276⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190692828352,190692828416⟩ : DyadicInterval 40),(⟨-230852097152,-230852097088⟩ : DyadicInterval 40),(⟨742286439074,742286458403⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190884425152,190884425216⟩ : DyadicInterval 40),(⟨-231133278848,-231133278784⟩ : DyadicInterval 40),(⟨742242726634,742242745964⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190605288640,190605288704⟩ : DyadicInterval 40),(⟨-230723666752,-230723666688⟩ : DyadicInterval 40),(⟨742306392255,742306411585⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190840615936,190840616000⟩ : DyadicInterval 40),(⟨-231068975040,-231068974976⟩ : DyadicInterval 40),(⟨742252726600,742252745929⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨26723480,53509740⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26723136,26723200⟩ : DyadicInterval 40),(⟨-26723840,-26723776⟩ : DyadicInterval 40),(⟨762123383254,762123402583⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53508416,53508480⟩ : DyadicInterval 40),(⟨-53511104,-53511040⟩ : DyadicInterval 40),(⟨762123382291,762123401620⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2624,-640⟩ : DyadicInterval 40),(⟨762123383936,762123404192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨208176005557,208429920880⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190649055168,190649055232⟩ : DyadicInterval 40),(⟨-230787873920,-230787873856⟩ : DyadicInterval 40),(⟨742296417903,742296437232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190862528000,190862528064⟩ : DyadicInterval 40),(⟨-231101137088,-231101137024⟩ : DyadicInterval 40),(⟨742247725283,742247744613⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40238609088,-40138818624⟩ : DyadicInterval 40),(⟨782192792928,782242707424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨190692828352,190884425216⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-231133278848,-230852097088⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e953_ok : ecellOkT e953 = true := by decide +kernel
theorem e953_pos {a z : ℝ} (ha1 : ((77571/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((776559/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e953 e953_ok ha1 ha2 hz1 hz2 hz

-- box ['776559/4096000', '12147/64000', '1999/2000', '3999/4000']  interval_lower 143160167/549755813888
noncomputable def e954 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1307967597051,0,true,190884425152,190884425216⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨891055658501,0,false,-231133278848,-231133278784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1308195498755,0,true,191075988608,191075988672⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨890827756797,0,false,-231414532480,-231414532416⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1307863369066,0,true,190796804928,190796804992⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨891159886486,0,false,-231004675008,-231004674944⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1308143327788,0,true,191032139072,191032139136⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨890879927764,0,false,-231350141888,-231350141824⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538382079,0,true,26753920,26753984⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484873473,0,false,-26754688,-26754624⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565199175,0,true,53570048,53570112⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458056377,0,false,-53572736,-53572672⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625165,0,false,-2624,-2560⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627125,0,false,-704,-640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1307915478057,0,true,190840611712,190840611776⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨891107777495,0,false,-231068968896,-231068968832⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1308169421872,0,true,191054071296,191054071360⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨890853833680,0,false,-231382347328,-231382347264⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1059913979204,0,false,-40328276032,-40328275968⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1060010303994,0,false,-40228357120,-40228357056⟩
    { al := (776559/4096000), au := (12147/64000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨208455969275,208683870979⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190884425152,190884425216⟩ : DyadicInterval 40),(⟨-231133278848,-231133278784⟩ : DyadicInterval 40),(⟨742242726635,742242745964⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191075988608,191075988672⟩ : DyadicInterval 40),(⟨-231414532480,-231414532416⟩ : DyadicInterval 40),(⟨742198965177,742198984507⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190796804928,190796804992⟩ : DyadicInterval 40),(⟨-231004675008,-231004674944⟩ : DyadicInterval 40),(⟨742262724037,742262743367⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191032139072,191032139136⟩ : DyadicInterval 40),(⟨-231350141888,-231350141824⟩ : DyadicInterval 40),(⟨742208987323,742209006652⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨26754303,53571399⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26753920,26753984⟩ : DyadicInterval 40),(⟨-26754688,-26754624⟩ : DyadicInterval 40),(⟨762123383284,762123402613⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53570048,53570112⟩ : DyadicInterval 40),(⟨-53572736,-53572672⟩ : DyadicInterval 40),(⟨762123382285,762123401614⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2624,-640⟩ : DyadicInterval 40),(⟨762123383936,762123404192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨208403850281,208657794096⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190840611712,190840611776⟩ : DyadicInterval 40),(⟨-231068968896,-231068968832⟩ : DyadicInterval 40),(⟨742252727582,742252746912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191054071296,191054071360⟩ : DyadicInterval 40),(⟨-231382347328,-231382347264⟩ : DyadicInterval 40),(⟨742203974914,742203994243⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40328276032,-40228357056⟩ : DyadicInterval 40),(⟨782237562144,782287540896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨190884425152,191075988672⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-231414532480,-231133278784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e954_ok : ecellOkT e954 = true := by decide +kernel
theorem e954_pos {a z : ℝ} (ha1 : ((776559/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((12147/64000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e954 e954_ok ha1 ha2 hz1 hz2 hz

-- box ['77571/409600', '776559/4096000', '3999/4000', '1']  interval_lower 281765649/1099511627776
noncomputable def e955 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1307739695349,0,true,190692828352,190692828416⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨891283560203,0,false,-230852097152,-230852097088⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1307967597052,0,true,190884425152,190884425216⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨891055658500,0,false,-231133278848,-231133278784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1307687638332,0,true,190649059392,190649059456⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨891335617220,0,false,-230787880064,-230787880000⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538382956,0,true,26754816,26754880⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484872596,0,false,-26755520,-26755456⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627124,0,false,-704,-640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1307713661588,0,true,190670939648,190670939712⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨891309593964,0,false,-230819981696,-230819981632⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1307967605564,0,true,190884432320,190884432384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨891055649988,0,false,-231133289344,-231133289280⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1059990540797,0,false,-40248857024,-40248856960⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1060086772424,0,false,-40149041984,-40149041920⟩
    { al := (77571/409600), au := (776559/4096000), zl := (3999/4000), zu := 1,
      A := ⟨208228067573,208455969276⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190692828352,190692828416⟩ : DyadicInterval 40),(⟨-230852097152,-230852097088⟩ : DyadicInterval 40),(⟨742286439074,742286458403⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190884425152,190884425216⟩ : DyadicInterval 40),(⟨-231133278848,-231133278784⟩ : DyadicInterval 40),(⟨742242726634,742242745964⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190649059392,190649059456⟩ : DyadicInterval 40),(⟨-230787880064,-230787880000⟩ : DyadicInterval 40),(⟨742296416923,742296436252⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190884425152,190884425216⟩ : DyadicInterval 40),(⟨-231133278848,-231133278784⟩ : DyadicInterval 40),(⟨742242726634,742242745964⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,26755180⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26754816,26754880⟩ : DyadicInterval 40),(⟨-26755520,-26755456⟩ : DyadicInterval 40),(⟨762123383252,762123402581⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-704,0⟩ : DyadicInterval 40),(⟨762123383616,762123403232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨208202033812,208455977788⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190670939648,190670939712⟩ : DyadicInterval 40),(⟨-230819981696,-230819981632⟩ : DyadicInterval 40),(⟨742291429355,742291448684⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190884432320,190884432384⟩ : DyadicInterval 40),(⟨-231133289344,-231133289280⟩ : DyadicInterval 40),(⟨742242724990,742242744320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40248857024,-40149041920⟩ : DyadicInterval 40),(⟨782197904576,782247831392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨190692828352,190884425216⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-231133278848,-230852097088⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e955_ok : ecellOkT e955 = true := by decide +kernel
theorem e955_pos {a z : ℝ} (ha1 : ((77571/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((776559/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e955 e955_ok ha1 ha2 hz1 hz2 hz

-- box ['776559/4096000', '12147/64000', '3999/4000', '1']  interval_lower 285599257/1099511627776
noncomputable def e956 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1307967597051,0,true,190884425152,190884425216⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨891055658501,0,false,-231133278848,-231133278784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1308195498755,0,true,191075988608,191075988672⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨890827756797,0,false,-231414532480,-231414532416⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1307915483058,0,true,190840615936,190840616000⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨891107772494,0,false,-231068975040,-231068974976⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538413785,0,true,26785664,26785728⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484841767,0,false,-26786368,-26786304⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627123,0,false,-704,-640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1307941534798,0,true,190862516352,190862516416⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨891081720754,0,false,-231101120000,-231101119936⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1308195507271,0,true,191075995712,191075995776⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨890827748281,0,false,-231414542976,-231414542912⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1059904077968,0,false,-40338547200,-40338547136⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1060000425672,0,false,-40238603648,-40238603584⟩
    { al := (776559/4096000), au := (12147/64000), zl := (3999/4000), zu := 1,
      A := ⟨208455969275,208683870979⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190884425152,190884425216⟩ : DyadicInterval 40),(⟨-231133278848,-231133278784⟩ : DyadicInterval 40),(⟨742242726635,742242745964⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191075988608,191075988672⟩ : DyadicInterval 40),(⟨-231414532480,-231414532416⟩ : DyadicInterval 40),(⟨742198965177,742198984507⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190840615936,190840616000⟩ : DyadicInterval 40),(⟨-231068975040,-231068974976⟩ : DyadicInterval 40),(⟨742252726600,742252745929⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191075988608,191075988672⟩ : DyadicInterval 40),(⟨-231414532480,-231414532416⟩ : DyadicInterval 40),(⟨742198965177,742198984507⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,26786009⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26785664,26785728⟩ : DyadicInterval 40),(⟨-26786368,-26786304⟩ : DyadicInterval 40),(⟨762123383251,762123402580⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-704,0⟩ : DyadicInterval 40),(⟨762123383616,762123403232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨208429907022,208683879495⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190862516352,190862516416⟩ : DyadicInterval 40),(⟨-231101120000,-231101119936⟩ : DyadicInterval 40),(⟨742247727946,742247747276⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191075995712,191075995776⟩ : DyadicInterval 40),(⟨-231414542976,-231414542912⟩ : DyadicInterval 40),(⟨742198963567,742198982897⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40338547200,-40238603584⟩ : DyadicInterval 40),(⟨782242685408,782292676480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨190884425152,191075988672⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-231414532480,-231133278784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e956_ok : ecellOkT e956 = true := by decide +kernel
theorem e956_pos {a z : ℝ} (ha1 : ((776559/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((12147/64000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e956 e956_ok ha1 ha2 hz1 hz2 hz

-- box ['12147/64000', '778257/4096000', '999/1000', '3997/4000']  interval_lower 145809729/549755813888
noncomputable def e957 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1308195498754,0,true,191075988608,191075988672⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨890827756798,0,false,-231414532480,-231414532416⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1308423400457,0,true,191267518656,191267518720⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨890599855095,0,false,-231695858048,-231695857984⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1307986814882,0,true,190900580032,190900580096⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨891036440670,0,false,-231156992768,-231156992704⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1308266716628,0,true,191135844096,191135844160⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨890756538924,0,false,-231502437248,-231502437184⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591982602,0,true,80351872,80351936⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431272950,0,false,-80357824,-80357760⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099618892204,0,true,107259136,107259200⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099404363348,0,false,-107269696,-107269632⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511617311,0,false,-10496,-10432⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621904,0,false,-5888,-5824⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1308091152842,0,true,190988284480,190988284544⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨890932102710,0,false,-231285750208,-231285750144⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1308345067828,0,true,191201691136,191201691200⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨890678187724,0,false,-231599154816,-231599154752⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1059847285369,0,false,-40397463680,-40397463616⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1059943680355,0,false,-40297465664,-40297465600⟩
    { al := (12147/64000), au := (778257/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨208683870978,208911772681⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191075988608,191075988672⟩ : DyadicInterval 40),(⟨-231414532480,-231414532416⟩ : DyadicInterval 40),(⟨742198965177,742198984507⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191267518656,191267518720⟩ : DyadicInterval 40),(⟨-231695858048,-231695857984⟩ : DyadicInterval 40),(⟨742155154729,742155174058⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190900580032,190900580096⟩ : DyadicInterval 40),(⟨-231156992768,-231156992704⟩ : DyadicInterval 40),(⟨742239038330,742239057659⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191135844096,191135844160⟩ : DyadicInterval 40),(⟨-231502437248,-231502437184⟩ : DyadicInterval 40),(⟨742185279978,742185299307⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨80354826,107264428⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80351872,80351936⟩ : DyadicInterval 40),(⟨-80357824,-80357760⟩ : DyadicInterval 40),(⟨762123380655,762123399984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨107259136,107259200⟩ : DyadicInterval 40),(⟨-107269696,-107269632⟩ : DyadicInterval 40),(⟨762123378367,762123397697⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-10496,-5824⟩ : DyadicInterval 40),(⟨762123386528,762123408128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨208579525066,208833440052⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190988284480,190988284544⟩ : DyadicInterval 40),(⟨-231285750208,-231285750144⟩ : DyadicInterval 40),(⟨742219007663,742219026993⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191201691136,191201691200⟩ : DyadicInterval 40),(⟨-231599154816,-231599154752⟩ : DyadicInterval 40),(⟨742170218455,742170237785⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40397463680,-40297465600⟩ : DyadicInterval 40),(⟨782272116416,782322134720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨191075988608,191267518720⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-231695858048,-231414532416⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e957_ok : ecellOkT e957 = true := by decide +kernel
theorem e957_pos {a z : ℝ} (ha1 : ((12147/64000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((778257/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e957 e957_ok ha1 ha2 hz1 hz2 hz

-- box ['778257/4096000', '389553/2048000', '999/1000', '3997/4000']  interval_lower 295494877/1099511627776
noncomputable def e958 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1308423400456,0,true,191267518656,191267518720⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨890599855096,0,false,-231695858048,-231695857984⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1308651302159,0,true,191459015296,191459015360⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨890371953393,0,false,-231977255616,-231977255552⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1308214488683,0,true,191091949120,191091949184⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨890808766869,0,false,-231437971200,-231437971136⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1308494447404,0,true,191327220096,191327220160⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨890528808148,0,false,-231783574272,-231783574208⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592075101,0,true,80444352,80444416⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431180451,0,false,-80450304,-80450240⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099619015560,0,true,107382528,107382592⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099404239992,0,false,-107393088,-107393024⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511617287,0,false,-10496,-10432⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621890,0,false,-5888,-5824⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1308318940592,0,true,191179734016,191179734080⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨890704314960,0,false,-231566902144,-231566902080⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1308572884067,0,true,191393127488,191393127552⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨890450371485,0,false,-231880422144,-231880422080⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1059760698565,0,false,-40487294592,-40487294528⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1059857209593,0,false,-40387168064,-40387168000⟩
    { al := (778257/4096000), au := (389553/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨208911772680,209139674383⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191267518656,191267518720⟩ : DyadicInterval 40),(⟨-231695858048,-231695857984⟩ : DyadicInterval 40),(⟨742155154729,742155174058⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191459015296,191459015360⟩ : DyadicInterval 40),(⟨-231977255616,-231977255552⟩ : DyadicInterval 40),(⟨742111295302,742111314632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191091949120,191091949184⟩ : DyadicInterval 40),(⟨-231437971200,-231437971136⟩ : DyadicInterval 40),(⟨742195316548,742195335878⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191327220096,191327220160⟩ : DyadicInterval 40),(⟨-231783574272,-231783574208⟩ : DyadicInterval 40),(⟨742141487099,742141506429⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨80447325,107387784⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80444352,80444416⟩ : DyadicInterval 40),(⟨-80450304,-80450240⟩ : DyadicInterval 40),(⟨762123380641,762123399971⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨107382528,107382592⟩ : DyadicInterval 40),(⟨-107393088,-107393024⟩ : DyadicInterval 40),(⟨762123378343,762123397673⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-10496,-5824⟩ : DyadicInterval 40),(⟨762123386528,762123408128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨208807312816,209061256291⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191179734016,191179734080⟩ : DyadicInterval 40),(⟨-231566902144,-231566902080⟩ : DyadicInterval 40),(⟨742175241567,742175260896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191393127488,191393127552⟩ : DyadicInterval 40),(⟨-231880422144,-231880422080⟩ : DyadicInterval 40),(⟨742126392306,742126411636⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40487294592,-40387168000⟩ : DyadicInterval 40),(⟨782316967616,782367050176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨191267518656,191459015360⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-231977255616,-231695857984⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e958_ok : ecellOkT e958 = true := by decide +kernel
theorem e958_pos {a z : ℝ} (ha1 : ((778257/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((389553/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e958 e958_ok ha1 ha2 hz1 hz2 hz

-- box ['12147/64000', '778257/4096000', '3997/4000', '1999/2000']  interval_lower 290896903/1099511627776
noncomputable def e959 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1308195498754,0,true,191075988608,191075988672⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨890827756798,0,false,-231414532480,-231414532416⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1308423400457,0,true,191267518656,191267518720⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨890599855095,0,false,-231695858048,-231695857984⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1308038985850,0,true,190944434816,190944434880⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨890984269702,0,false,-231221372032,-231221371968⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1308318944571,0,true,191179737344,191179737408⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨890704310981,0,false,-231566907072,-231566907008⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565197936,0,true,53568832,53568896⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458057616,0,false,-53571520,-53571456⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592076705,0,true,80445952,80446016⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431178847,0,false,-80451904,-80451840⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621889,0,false,-5888,-5824⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625166,0,false,-2624,-2560⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1308117237729,0,true,191010209792,191010209856⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨890906017823,0,false,-231317942336,-231317942272⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1308371181369,0,true,191223636288,191223636352⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨890652074183,0,false,-231631391552,-231631391488⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1059837365107,0,false,-40407755200,-40407755136⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1059933783027,0,false,-40307732544,-40307732480⟩
    { al := (12147/64000), au := (778257/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨208683870978,208911772681⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191075988608,191075988672⟩ : DyadicInterval 40),(⟨-231414532480,-231414532416⟩ : DyadicInterval 40),(⟨742198965177,742198984507⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191267518656,191267518720⟩ : DyadicInterval 40),(⟨-231695858048,-231695857984⟩ : DyadicInterval 40),(⟨742155154729,742155174058⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190944434816,190944434880⟩ : DyadicInterval 40),(⟨-231221372032,-231221371968⟩ : DyadicInterval 40),(⟨742229023880,742229043210⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191179737344,191179737408⟩ : DyadicInterval 40),(⟨-231566907072,-231566907008⟩ : DyadicInterval 40),(⟨742175240818,742175260147⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨53570160,80448929⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53568832,53568896⟩ : DyadicInterval 40),(⟨-53571520,-53571456⟩ : DyadicInterval 40),(⟨762123382285,762123401615⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80445952,80446016⟩ : DyadicInterval 40),(⟨-80451904,-80451840⟩ : DyadicInterval 40),(⟨762123380641,762123399970⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5888,-2560⟩ : DyadicInterval 40),(⟨762123384896,762123405824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨208605609953,208859553593⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191010209792,191010209856⟩ : DyadicInterval 40),(⟨-231317942336,-231317942272⟩ : DyadicInterval 40),(⟨742213998308,742214017637⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191223636288,191223636352⟩ : DyadicInterval 40),(⟨-231631391552,-231631391488⟩ : DyadicInterval 40),(⟨742165197355,742165216685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40407755200,-40307732480⟩ : DyadicInterval 40),(⟨782277249856,782327280480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨191075988608,191267518720⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-231695858048,-231414532416⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e959_ok : ecellOkT e959 = true := by decide +kernel
theorem e959_pos {a z : ℝ} (ha1 : ((12147/64000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((778257/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e959 e959_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B015

end


