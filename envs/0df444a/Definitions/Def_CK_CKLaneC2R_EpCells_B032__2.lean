-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B032__2
-- name    : CK_CKLaneC2R_EpCells_B032__2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:28:34.746602+00:00
-- url     : https://prove2.me/theorems/75d8e063-2a1b-4321-a0a3-436272022c56
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B032 (+1 modules: CKLaneC2R.EpCells.B033)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B032 (+1 modules: CKLaneC2R.EpCells.B033)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B032 (+1 modules: CKLaneC2R.EpCells.B033)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B032 (+1 modules: CKLaneC2R.EpCells.B033) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B032 (+1 modules: CKLaneC2R/EpCells/B033).lean)

import Definitions.Def_CK_CKLaneC2R_EpCells_B032__2_q00

-- ===== source module CKLaneC2R.EpCells.B033 =====
section

namespace CKLaneC2R.EpCells.B033

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['639021/4096000', '1278891/8192000', '999/1000', '7993/8000']  interval_lower 86410327/549755813888
noncomputable def e1980 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271047521304,0,true,159401999424,159401999488⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927975734248,0,false,-186494545984,-186494545920⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271161472156,0,true,159500567488,159500567552⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927861783396,0,false,-186629568896,-186629568832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270875985410,0,true,159253603328,159253603392⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928147270142,0,false,-186291320512,-186291320448⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271011278543,0,true,159370647424,159370647488⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928011977009,0,false,-186451604608,-186451604544⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588019847,0,true,76389376,76389440⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435235705,0,false,-76394752,-76394688⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099598993838,0,true,87362560,87362624⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099424261714,0,false,-87369536,-87369472⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620833,0,false,-6976,-6912⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622469,0,false,-5312,-5248⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270961749595,0,true,159327800640,159327800704⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928061505957,0,false,-186392924096,-186392924032⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271086380296,0,true,159435613632,159435613696⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927936875256,0,false,-186540588992,-186540588928⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072738017603,0,false,-27104975360,-27104975296⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072776899803,0,false,-27065123456,-27065123392⟩
    { al := (639021/4096000), au := (1278891/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨171535893528,171649844380⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159401999424,159401999488⟩ : DyadicInterval 40),(⟨-186494545984,-186494545920⟩ : DyadicInterval 40),(⟨748687826223,748687845553⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159500567488,159500567552⟩ : DyadicInterval 40),(⟨-186629568896,-186629568832⟩ : DyadicInterval 40),(⟨748669896203,748669915533⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159253603328,159253603392⟩ : DyadicInterval 40),(⟨-186291320512,-186291320448⟩ : DyadicInterval 40),(⟨748714794351,748714813681⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159370647424,159370647488⟩ : DyadicInterval 40),(⟨-186451604608,-186451604544⟩ : DyadicInterval 40),(⟨748693526427,748693545756⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨76392071,87366062⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76389376,76389440⟩ : DyadicInterval 40),(⟨-76394752,-76394688⟩ : DyadicInterval 40),(⟨762123380932,762123400261⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨87362560,87362624⟩ : DyadicInterval 40),(⟨-87369536,-87369472⟩ : DyadicInterval 40),(⟨762123380097,762123399427⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6976,-5248⟩ : DyadicInterval 40),(⟨762123386240,762123406368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171450121819,171574752520⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159327800640,159327800704⟩ : DyadicInterval 40),(⟨-186392924096,-186392924032⟩ : DyadicInterval 40),(⟨748701314299,748701333628⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159435613632,159435613696⟩ : DyadicInterval 40),(⟨-186540588992,-186540588928⟩ : DyadicInterval 40),(⟨748681713169,748681732498⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27104975360,-27065123392⟩ : DyadicInterval 40),(⟨775655945312,775675890560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159401999424,159500567552⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186629568896,-186494545920⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1980_ok : ecellOkT e1980 = true := by decide +kernel
theorem e1980_pos {a z : ℝ} (ha1 : ((639021/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1278891/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1980 e1980_ok ha1 ha2 hz1 hz2 hz

-- box ['1278891/8192000', '63987/409600', '999/1000', '7993/8000']  interval_lower 173906683/1099511627776
noncomputable def e1981 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271161472155,0,true,159500567488,159500567552⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927861783397,0,false,-186629568896,-186629568832⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271275423007,0,true,159599126656,159599126720⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927747832545,0,false,-186764608384,-186764608320⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270989822310,0,true,159352086144,159352086208⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928033433242,0,false,-186426183488,-186426183424⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271125129687,0,true,159469132032,159469132096⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927898125865,0,false,-186586504064,-186586504000⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588072423,0,true,76441984,76442048⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435183129,0,false,-76447360,-76447296⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099599053929,0,true,87422656,87422720⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099424201623,0,false,-87429632,-87429568⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620824,0,false,-6976,-6912⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622462,0,false,-5376,-5312⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271075643471,0,true,159426326080,159426326144⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927947612081,0,false,-186527867008,-186527866944⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271200281294,0,true,159534135552,159534135616⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927822974258,0,false,-186675558464,-186675558400⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072702458139,0,false,-27141422912,-27141422848⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072741368383,0,false,-27101540928,-27101540864⟩
    { al := (1278891/8192000), au := (63987/409600), zl := (999/1000), zu := (7993/8000),
      A := ⟨171649844379,171763795231⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159500567488,159500567552⟩ : DyadicInterval 40),(⟨-186629568896,-186629568832⟩ : DyadicInterval 40),(⟨748669896203,748669915533⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159599126656,159599126720⟩ : DyadicInterval 40),(⟨-186764608384,-186764608320⟩ : DyadicInterval 40),(⟨748651954110,748651973439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159352086144,159352086208⟩ : DyadicInterval 40),(⟨-186426183488,-186426183424⟩ : DyadicInterval 40),(⟨748696900466,748696919796⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159469132032,159469132096⟩ : DyadicInterval 40),(⟨-186586504064,-186586504000⟩ : DyadicInterval 40),(⟨748675615944,748675635274⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨76444647,87426153⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76441984,76442048⟩ : DyadicInterval 40),(⟨-76447360,-76447296⟩ : DyadicInterval 40),(⟨762123380924,762123400254⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨87422656,87422720⟩ : DyadicInterval 40),(⟨-87429632,-87429568⟩ : DyadicInterval 40),(⟨762123380088,762123399417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6976,-5312⟩ : DyadicInterval 40),(⟨762123386272,762123406368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171564015695,171688653518⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159426326080,159426326144⟩ : DyadicInterval 40),(⟨-186527867008,-186527866944⟩ : DyadicInterval 40),(⟨748683402343,748683421672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159534135552,159534135616⟩ : DyadicInterval 40),(⟨-186675558464,-186675558400⟩ : DyadicInterval 40),(⟨748663786869,748663806198⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27141422912,-27101540864⟩ : DyadicInterval 40),(⟨775674154048,775694114336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159500567488,159599126720⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186764608384,-186629568832⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1981_ok : ecellOkT e1981 = true := by decide +kernel
theorem e1981_pos {a z : ℝ} (ha1 : ((1278891/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((63987/409600 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1981 e1981_ok ha1 ha2 hz1 hz2 hz

-- box ['639021/4096000', '1278891/8192000', '7993/8000', '3997/4000']  interval_lower 43166273/274877906944
noncomputable def e1982 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271047521304,0,true,159401999424,159401999488⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927975734248,0,false,-186494545984,-186494545920⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271161472156,0,true,159500567488,159500567552⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927861783396,0,false,-186629568896,-186629568832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270897427397,0,true,159272153984,159272154048⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928125828155,0,false,-186316721664,-186316721600⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271032734773,0,true,159389208320,159389208384⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927990520779,0,false,-186477026304,-186477026240⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577106805,0,true,65477056,65477120⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446148747,0,false,-65481024,-65480960⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588073284,0,true,76442816,76442880⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435182268,0,false,-76448192,-76448128⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622460,0,false,-5376,-5312⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623877,0,false,-3904,-3840⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270972470412,0,true,159337075200,159337075264⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928050785140,0,false,-186405625536,-186405625472⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271097108254,0,true,159444893440,159444893504⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927926147298,0,false,-186553300608,-186553300544⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072734669381,0,false,-27108407104,-27108407040⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072773556241,0,false,-27068550336,-27068550272⟩
    { al := (639021/4096000), au := (1278891/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨171535893528,171649844380⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159401999424,159401999488⟩ : DyadicInterval 40),(⟨-186494545984,-186494545920⟩ : DyadicInterval 40),(⟨748687826223,748687845553⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159500567488,159500567552⟩ : DyadicInterval 40),(⟨-186629568896,-186629568832⟩ : DyadicInterval 40),(⟨748669896203,748669915533⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159272153984,159272154048⟩ : DyadicInterval 40),(⟨-186316721664,-186316721600⟩ : DyadicInterval 40),(⟨748711424816,748711444146⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159389208320,159389208384⟩ : DyadicInterval 40),(⟨-186477026304,-186477026240⟩ : DyadicInterval 40),(⟨748690151994,748690171324⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨65479029,76445508⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65477056,65477120⟩ : DyadicInterval 40),(⟨-65481024,-65480960⟩ : DyadicInterval 40),(⟨762123381636,762123400965⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76442816,76442880⟩ : DyadicInterval 40),(⟨-76448192,-76448128⟩ : DyadicInterval 40),(⟨762123380924,762123400254⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5376,-3840⟩ : DyadicInterval 40),(⟨762123385536,762123405568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171460842636,171585480478⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159337075200,159337075264⟩ : DyadicInterval 40),(⟨-186405625536,-186405625472⟩ : DyadicInterval 40),(⟨748699628760,748699648090⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159444893440,159444893504⟩ : DyadicInterval 40),(⟨-186553300608,-186553300544⟩ : DyadicInterval 40),(⟨748680025277,748680044606⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27108407104,-27068550272⟩ : DyadicInterval 40),(⟨775657658752,775677606432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159401999424,159500567552⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186629568896,-186494545920⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1982_ok : ecellOkT e1982 = true := by decide +kernel
theorem e1982_pos {a z : ℝ} (ha1 : ((639021/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1278891/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1982 e1982_ok ha1 ha2 hz1 hz2 hz

-- box ['1278891/8192000', '63987/409600', '7993/8000', '3997/4000']  interval_lower 86875279/549755813888
noncomputable def e1983 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271161472155,0,true,159500567488,159500567552⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927861783397,0,false,-186629568896,-186629568832⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271275423007,0,true,159599126656,159599126720⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927747832545,0,false,-186764608384,-186764608320⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271011278541,0,true,159370647424,159370647488⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928011977011,0,false,-186451604608,-186451604544⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271146600161,0,true,159487703616,159487703680⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927876655391,0,false,-186611945792,-186611945728⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577151870,0,true,65522112,65522176⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446103682,0,false,-65526080,-65526016⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588125865,0,true,76495424,76495488⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435129687,0,false,-76500800,-76500736⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622453,0,false,-5376,-5312⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623872,0,false,-3968,-3904⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271086371409,0,true,159435605952,159435606016⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927936884143,0,false,-186540578496,-186540578432⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271211016373,0,true,159543420672,159543420736⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927812239179,0,false,-186688280128,-186688280064⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072699105470,0,false,-27144859392,-27144859328⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072738020377,0,false,-27104972480,-27104972416⟩
    { al := (1278891/8192000), au := (63987/409600), zl := (7993/8000), zu := (3997/4000),
      A := ⟨171649844379,171763795231⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159500567488,159500567552⟩ : DyadicInterval 40),(⟨-186629568896,-186629568832⟩ : DyadicInterval 40),(⟨748669896203,748669915533⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159599126656,159599126720⟩ : DyadicInterval 40),(⟨-186764608384,-186764608320⟩ : DyadicInterval 40),(⟨748651954110,748651973439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159370647424,159370647488⟩ : DyadicInterval 40),(⟨-186451604608,-186451604544⟩ : DyadicInterval 40),(⟨748693526427,748693545756⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159487703616,159487703680⟩ : DyadicInterval 40),(⟨-186611945792,-186611945728⟩ : DyadicInterval 40),(⟨748672236990,748672256320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨65524094,76498089⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65522112,65522176⟩ : DyadicInterval 40),(⟨-65526080,-65526016⟩ : DyadicInterval 40),(⟨762123381631,762123400960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76495424,76495488⟩ : DyadicInterval 40),(⟨-76500800,-76500736⟩ : DyadicInterval 40),(⟨762123380917,762123400246⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5376,-3904⟩ : DyadicInterval 40),(⟨762123385568,762123405568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171574743633,171699388597⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159435605952,159435606016⟩ : DyadicInterval 40),(⟨-186540578496,-186540578432⟩ : DyadicInterval 40),(⟨748681714577,748681733907⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159543420672,159543420736⟩ : DyadicInterval 40),(⟨-186688280128,-186688280064⟩ : DyadicInterval 40),(⟨748662096746,748662116076⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27144859392,-27104972416⟩ : DyadicInterval 40),(⟨775675869824,775695832576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159500567488,159599126720⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186764608384,-186629568832⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1983_ok : ecellOkT e1983 = true := by decide +kernel
theorem e1983_pos {a z : ℝ} (ha1 : ((1278891/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((63987/409600 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1983 e1983_ok ha1 ha2 hz1 hz2 hz

-- box ['159543/1024000', '1277193/8192000', '3997/4000', '1599/1600']  interval_lower 170347189/1099511627776
noncomputable def e1984 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270819619602,0,true,159204836800,159204836864⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928203635950,0,false,-186224549888,-186224549824⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270933570454,0,true,159303422528,159303422592⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928089685098,0,false,-186359539648,-186359539584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270691138608,0,true,159093669568,159093669632⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928332116944,0,false,-186072367168,-186072367104⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270826431740,0,true,159210730624,159210730688⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928196823812,0,false,-186232619328,-186232619264⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566118612,0,true,54489472,54489536⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457136940,0,false,-54492224,-54492160⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577062553,0,true,65432768,65432832⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446192999,0,false,-65436736,-65436672⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623881,0,false,-3904,-3840⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625076,0,false,-2752,-2688⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270755375013,0,true,159149251072,159149251136⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928267880539,0,false,-186148451072,-186148451008⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270880005753,0,true,159257081600,159257081664⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928143249799,0,false,-186296083136,-186296083072⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072802386847,0,false,-27039001536,-27039001472⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072841222274,0,false,-26999199936,-26999199872⟩
    { al := (159543/1024000), au := (1277193/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨171307991826,171421942678⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159204836800,159204836864⟩ : DyadicInterval 40),(⟨-186224549888,-186224549824⟩ : DyadicInterval 40),(⟨748723649939,748723669268⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159303422528,159303422592⟩ : DyadicInterval 40),(⟨-186359539648,-186359539584⟩ : DyadicInterval 40),(⟨748705744134,748705763464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159093669568,159093669632⟩ : DyadicInterval 40),(⟨-186072367168,-186072367104⟩ : DyadicInterval 40),(⟨748743824451,748743843780⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159210730624,159210730688⟩ : DyadicInterval 40),(⟨-186232619328,-186232619264⟩ : DyadicInterval 40),(⟨748722579868,748722599197⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54490836,65434777⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54489472,54489536⟩ : DyadicInterval 40),(⟨-54492224,-54492160⟩ : DyadicInterval 40),(⟨762123382227,762123401556⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65432768,65432832⟩ : DyadicInterval 40),(⟨-65436736,-65436672⟩ : DyadicInterval 40),(⟨762123381641,762123400970⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3904,-2688⟩ : DyadicInterval 40),(⟨762123384960,762123404832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171243747237,171368377977⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159149251072,159149251136⟩ : DyadicInterval 40),(⟨-186148451072,-186148451008⟩ : DyadicInterval 40),(⟨748733739757,748733759086⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159257081600,159257081664⟩ : DyadicInterval 40),(⟨-186296083136,-186296083072⟩ : DyadicInterval 40),(⟨748714162580,748714181910⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27039001536,-26999199872⟩ : DyadicInterval 40),(⟨775622983552,775642903648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159204836800,159303422592⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186359539648,-186224549824⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1984_ok : ecellOkT e1984 = true := by decide +kernel
theorem e1984_pos {a z : ℝ} (ha1 : ((159543/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1277193/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1984 e1984_ok ha1 ha2 hz1 hz2 hz

-- box ['1277193/8192000', '639021/4096000', '3997/4000', '1599/1600']  interval_lower 85713395/549755813888
noncomputable def e1985 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270933570453,0,true,159303422528,159303422592⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928089685099,0,false,-186359539648,-186359539584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271047521305,0,true,159401999424,159401999488⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927975734247,0,false,-186494545984,-186494545920⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270805003995,0,true,159192191360,159192191424⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928218251557,0,false,-186207236992,-186207236928⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270940311372,0,true,159309254208,159309254272⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928082944180,0,false,-186367525696,-186367525632⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566156162,0,true,54526976,54527040⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457099390,0,false,-54529792,-54529728⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577107616,0,true,65477888,65477952⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446147936,0,false,-65481792,-65481728⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623876,0,false,-3904,-3840⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625072,0,false,-2752,-2688⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270869283134,0,true,159247804800,159247804864⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928153972418,0,false,-186283380864,-186283380800⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270993920996,0,true,159355631808,159355631872⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928029334556,0,false,-186431039488,-186431039424⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072766865696,0,false,-27075407680,-27075407616⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072805729168,0,false,-27035576000,-27035575936⟩
    { al := (1277193/8192000), au := (639021/4096000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨171421942677,171535893529⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159303422528,159303422592⟩ : DyadicInterval 40),(⟨-186359539648,-186359539584⟩ : DyadicInterval 40),(⟨748705744135,748705763464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159401999424,159401999488⟩ : DyadicInterval 40),(⟨-186494545984,-186494545920⟩ : DyadicInterval 40),(⟨748687826223,748687845553⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159192191360,159192191424⟩ : DyadicInterval 40),(⟨-186207236992,-186207236928⟩ : DyadicInterval 40),(⟨748725945687,748725965016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159309254208,159309254272⟩ : DyadicInterval 40),(⟨-186367525696,-186367525632⟩ : DyadicInterval 40),(⟨748704684533,748704703862⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54528386,65479840⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54526976,54527040⟩ : DyadicInterval 40),(⟨-54529792,-54529728⟩ : DyadicInterval 40),(⟨762123382255,762123401584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65477888,65477952⟩ : DyadicInterval 40),(⟨-65481792,-65481728⟩ : DyadicInterval 40),(⟨762123381604,762123400933⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3904,-2688⟩ : DyadicInterval 40),(⟨762123384960,762123404832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171357655358,171482293220⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159247804800,159247804864⟩ : DyadicInterval 40),(⟨-186283380864,-186283380800⟩ : DyadicInterval 40),(⟨748715847497,748715866827⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159355631808,159355631872⟩ : DyadicInterval 40),(⟨-186431039488,-186431039424⟩ : DyadicInterval 40),(⟨748696255978,748696275308⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27075407680,-27035575936⟩ : DyadicInterval 40),(⟨775641171584,775661106720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159303422528,159401999488⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186494545984,-186359539584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1985_ok : ecellOkT e1985 = true := by decide +kernel
theorem e1985_pos {a z : ℝ} (ha1 : ((1277193/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((639021/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1985 e1985_ok ha1 ha2 hz1 hz2 hz

-- box ['159543/1024000', '1277193/8192000', '1599/1600', '1999/2000']  interval_lower 85096053/549755813888
noncomputable def e1986 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270819619602,0,true,159204836800,159204836864⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928203635950,0,false,-186224549888,-186224549824⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270933570454,0,true,159303422528,159303422592⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928089685098,0,false,-186359539648,-186359539584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270712552107,0,true,159112198208,159112198272⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928310703445,0,false,-186097729472,-186097729408⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270847859483,0,true,159229269632,159229269696⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928175396069,0,false,-186258002176,-186258002112⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555220490,0,true,43591808,43591872⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468035062,0,false,-43593600,-43593536⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566156923,0,true,54527744,54527808⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457098629,0,false,-54530560,-54530496⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625071,0,false,-2752,-2688⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626048,0,false,-1792,-1728⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270766081632,0,true,159158514816,159158514880⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928257173920,0,false,-186161132864,-186161132800⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270890719521,0,true,159266350656,159266350720⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928132536031,0,false,-186308775168,-186308775104⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072799047076,0,false,-27042424448,-27042424384⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072837887159,0,false,-27002617984,-27002617920⟩
    { al := (159543/1024000), au := (1277193/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨171307991826,171421942678⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159204836800,159204836864⟩ : DyadicInterval 40),(⟨-186224549888,-186224549824⟩ : DyadicInterval 40),(⟨748723649939,748723669268⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159303422528,159303422592⟩ : DyadicInterval 40),(⟨-186359539648,-186359539584⟩ : DyadicInterval 40),(⟨748705744134,748705763464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159112198208,159112198272⟩ : DyadicInterval 40),(⟨-186097729472,-186097729408⟩ : DyadicInterval 40),(⟨748740463100,748740482429⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159229269632,159229269696⟩ : DyadicInterval 40),(⟨-186258002176,-186258002112⟩ : DyadicInterval 40),(⟨748719213557,748719232887⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨43592714,54529147⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43591808,43591872⟩ : DyadicInterval 40),(⟨-43593600,-43593536⟩ : DyadicInterval 40),(⟨762123382719,762123402048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54527744,54527808⟩ : DyadicInterval 40),(⟨-54530560,-54530496⟩ : DyadicInterval 40),(⟨762123382255,762123401584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2752,-1728⟩ : DyadicInterval 40),(⟨762123384480,762123404256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171254453856,171379091745⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159158514816,159158514880⟩ : DyadicInterval 40),(⟨-186161132864,-186161132800⟩ : DyadicInterval 40),(⟨748732058530,748732077859⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159266350656,159266350720⟩ : DyadicInterval 40),(⟨-186308775168,-186308775104⟩ : DyadicInterval 40),(⟨748712478994,748712498323⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27042424448,-27002617920⟩ : DyadicInterval 40),(⟨775624692576,775644615104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159204836800,159303422592⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186359539648,-186224549824⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1986_ok : ecellOkT e1986 = true := by decide +kernel
theorem e1986_pos {a z : ℝ} (ha1 : ((159543/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1277193/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1986 e1986_ok ha1 ha2 hz1 hz2 hz

-- box ['1277193/8192000', '639021/4096000', '1599/1600', '1999/2000']  interval_lower 171271471/1099511627776
noncomputable def e1987 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270933570453,0,true,159303422528,159303422592⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928089685099,0,false,-186359539648,-186359539584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271047521305,0,true,159401999424,159401999488⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927975734247,0,false,-186494545984,-186494545920⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270826431738,0,true,159210730624,159210730688⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928196823814,0,false,-186232619328,-186232619264⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270961753359,0,true,159327803904,159327803968⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928061502193,0,false,-186392928576,-186392928512⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555250531,0,true,43621888,43621952⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468005021,0,false,-43623680,-43623616⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566194475,0,true,54565312,54565376⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457061077,0,false,-54568064,-54568000⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625067,0,false,-2752,-2688⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626046,0,false,-1792,-1728⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270879996870,0,true,159257073920,159257073984⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928143258682,0,false,-186296072640,-186296072576⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271004641884,0,true,159364906240,159364906304⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928018613668,0,false,-186443741504,-186443741440⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072763521485,0,false,-27078835264,-27078835200⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072802389617,0,false,-27038998720,-27038998656⟩
    { al := (1277193/8192000), au := (639021/4096000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨171421942677,171535893529⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159303422528,159303422592⟩ : DyadicInterval 40),(⟨-186359539648,-186359539584⟩ : DyadicInterval 40),(⟨748705744135,748705763464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159401999424,159401999488⟩ : DyadicInterval 40),(⟨-186494545984,-186494545920⟩ : DyadicInterval 40),(⟨748687826223,748687845553⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159210730624,159210730688⟩ : DyadicInterval 40),(⟨-186232619328,-186232619264⟩ : DyadicInterval 40),(⟨748722579868,748722599198⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159327803904,159327803968⟩ : DyadicInterval 40),(⟨-186392928576,-186392928512⟩ : DyadicInterval 40),(⟨748701313711,748701333041⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨43622755,54566699⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43621888,43621952⟩ : DyadicInterval 40),(⟨-43623680,-43623616⟩ : DyadicInterval 40),(⟨762123382717,762123402046⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54565312,54565376⟩ : DyadicInterval 40),(⟨-54568064,-54568000⟩ : DyadicInterval 40),(⟨762123382219,762123401549⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2752,-1728⟩ : DyadicInterval 40),(⟨762123384480,762123404256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171368369094,171493014108⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159257073920,159257073984⟩ : DyadicInterval 40),(⟨-186296072640,-186296072576⟩ : DyadicInterval 40),(⟨748714163985,748714183314⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159364906240,159364906304⟩ : DyadicInterval 40),(⟨-186443741504,-186443741440⟩ : DyadicInterval 40),(⟨748694570103,748694589433⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27078835264,-27038998656⟩ : DyadicInterval 40),(⟨775642882944,775662820512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159303422528,159401999488⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186494545984,-186359539584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1987_ok : ecellOkT e1987 = true := by decide +kernel
theorem e1987_pos {a z : ℝ} (ha1 : ((1277193/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((639021/4096000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1987 e1987_ok ha1 ha2 hz1 hz2 hz

-- box ['639021/4096000', '1278891/8192000', '3997/4000', '1599/1600']  interval_lower 172509351/1099511627776
noncomputable def e1988 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271047521304,0,true,159401999424,159401999488⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927975734248,0,false,-186494545984,-186494545920⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271161472156,0,true,159500567488,159500567552⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927861783396,0,false,-186629568896,-186629568832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270918869383,0,true,159290704256,159290704320⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928104386169,0,false,-186342123392,-186342123328⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271054191004,0,true,159407768960,159407769024⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927969064548,0,false,-186502448576,-186502448512⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566193713,0,true,54564544,54564608⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457061839,0,false,-54567296,-54567232⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577152682,0,true,65522944,65523008⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446102870,0,false,-65526912,-65526848⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623871,0,false,-3968,-3904⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625069,0,false,-2752,-2688⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270983191249,0,true,159346349696,159346349760⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928040064303,0,false,-186418327168,-186418327104⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271107836240,0,true,159454173248,159454173312⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927915419312,0,false,-186566012416,-186566012352⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072731320942,0,false,-27111839168,-27111839104⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072770212463,0,false,-27071977472,-27071977408⟩
    { al := (639021/4096000), au := (1278891/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨171535893528,171649844380⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159401999424,159401999488⟩ : DyadicInterval 40),(⟨-186494545984,-186494545920⟩ : DyadicInterval 40),(⟨748687826223,748687845553⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159500567488,159500567552⟩ : DyadicInterval 40),(⟨-186629568896,-186629568832⟩ : DyadicInterval 40),(⟨748669896203,748669915533⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159290704256,159290704320⟩ : DyadicInterval 40),(⟨-186342123392,-186342123328⟩ : DyadicInterval 40),(⟨748708054890,748708074219⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159407768960,159407769024⟩ : DyadicInterval 40),(⟨-186502448576,-186502448512⟩ : DyadicInterval 40),(⟨748686777094,748686796424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54565937,65524906⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54564544,54564608⟩ : DyadicInterval 40),(⟨-54567296,-54567232⟩ : DyadicInterval 40),(⟨762123382219,762123401549⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65522944,65523008⟩ : DyadicInterval 40),(⟨-65526912,-65526848⟩ : DyadicInterval 40),(⟨762123381630,762123400960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3968,-2688⟩ : DyadicInterval 40),(⟨762123384960,762123404864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171471563473,171596208464⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159346349696,159346349760⟩ : DyadicInterval 40),(⟨-186418327168,-186418327104⟩ : DyadicInterval 40),(⟨748697943123,748697962452⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159454173248,159454173312⟩ : DyadicInterval 40),(⟨-186566012416,-186566012352⟩ : DyadicInterval 40),(⟨748678337247,748678356576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27111839168,-27071977408⟩ : DyadicInterval 40),(⟨775659372320,775679322464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159401999424,159500567552⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186629568896,-186494545920⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1988_ok : ecellOkT e1988 = true := by decide +kernel
theorem e1988_pos {a z : ℝ} (ha1 : ((639021/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1278891/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1988 e1988_ok ha1 ha2 hz1 hz2 hz

-- box ['1278891/8192000', '63987/409600', '3997/4000', '1599/1600']  interval_lower 173594455/1099511627776
noncomputable def e1989 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271161472155,0,true,159500567488,159500567552⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927861783397,0,false,-186629568896,-186629568832⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271275423007,0,true,159599126656,159599126720⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927747832545,0,false,-186764608384,-186764608320⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271032734771,0,true,159389208320,159389208384⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927990520781,0,false,-186477026304,-186477026240⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271168070636,0,true,159506274880,159506274944⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927855184916,0,false,-186637388096,-186637388032⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566231268,0,true,54602112,54602176⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457024284,0,false,-54604864,-54604800⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577197752,0,true,65568000,65568064⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446057800,0,false,-65571968,-65571904⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623865,0,false,-3968,-3904⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625065,0,false,-2752,-2688⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271097099367,0,true,159444885760,159444885824⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927926156185,0,false,-186553290112,-186553290048⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271221751478,0,true,159552705792,159552705856⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927801504074,0,false,-186701001920,-186701001856⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072695752584,0,false,-27148296064,-27148296000⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072734672156,0,false,-27108404288,-27108404224⟩
    { al := (1278891/8192000), au := (63987/409600), zl := (3997/4000), zu := (1599/1600),
      A := ⟨171649844379,171763795231⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159500567488,159500567552⟩ : DyadicInterval 40),(⟨-186629568896,-186629568832⟩ : DyadicInterval 40),(⟨748669896203,748669915533⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159599126656,159599126720⟩ : DyadicInterval 40),(⟨-186764608384,-186764608320⟩ : DyadicInterval 40),(⟨748651954110,748651973439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159389208320,159389208384⟩ : DyadicInterval 40),(⟨-186477026304,-186477026240⟩ : DyadicInterval 40),(⟨748690151994,748690171324⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159506274880,159506274944⟩ : DyadicInterval 40),(⟨-186637388096,-186637388032⟩ : DyadicInterval 40),(⟨748668857604,748668876934⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54603492,65569976⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54602112,54602176⟩ : DyadicInterval 40),(⟨-54604864,-54604800⟩ : DyadicInterval 40),(⟨762123382216,762123401545⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65568000,65568064⟩ : DyadicInterval 40),(⟨-65571968,-65571904⟩ : DyadicInterval 40),(⟨762123381625,762123400954⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3968,-2688⟩ : DyadicInterval 40),(⟨762123384960,762123404864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171585471591,171710123702⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159444885760,159444885824⟩ : DyadicInterval 40),(⟨-186553290112,-186553290048⟩ : DyadicInterval 40),(⟨748680026685,748680046015⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159552705792,159552705856⟩ : DyadicInterval 40),(⟨-186701001920,-186701001856⟩ : DyadicInterval 40),(⟨748660406458,748660425788⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27148296064,-27108404224⟩ : DyadicInterval 40),(⟨775677585728,775697550912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159500567488,159599126720⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186764608384,-186629568832⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1989_ok : ecellOkT e1989 = true := by decide +kernel
theorem e1989_pos {a z : ℝ} (ha1 : ((1278891/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((63987/409600 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1989 e1989_ok ha1 ha2 hz1 hz2 hz

-- box ['639021/4096000', '1278891/8192000', '1599/1600', '1999/2000']  interval_lower 43088361/274877906944
noncomputable def e1990 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271047521304,0,true,159401999424,159401999488⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927975734248,0,false,-186494545984,-186494545920⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271161472156,0,true,159500567488,159500567552⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927861783396,0,false,-186629568896,-186629568832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270940311370,0,true,159309254208,159309254272⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928082944182,0,false,-186367525696,-186367525632⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271075647234,0,true,159426329280,159426329344⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927947608318,0,false,-186527871488,-186527871424⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555280573,0,true,43651904,43651968⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467974979,0,false,-43653696,-43653632⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566232030,0,true,54602880,54602944⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457023522,0,false,-54605632,-54605568⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625064,0,false,-2752,-2688⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626043,0,false,-1792,-1728⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270993912110,0,true,159355624128,159355624192⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928029343442,0,false,-186431028992,-186431028928⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271118564247,0,true,159463452928,159463452992⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927904691305,0,false,-186578724416,-186578724352⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072727972286,0,false,-27115271424,-27115271360⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072766868469,0,false,-27075404800,-27075404736⟩
    { al := (639021/4096000), au := (1278891/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨171535893528,171649844380⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159401999424,159401999488⟩ : DyadicInterval 40),(⟨-186494545984,-186494545920⟩ : DyadicInterval 40),(⟨748687826223,748687845553⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159500567488,159500567552⟩ : DyadicInterval 40),(⟨-186629568896,-186629568832⟩ : DyadicInterval 40),(⟨748669896203,748669915533⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159309254208,159309254272⟩ : DyadicInterval 40),(⟨-186367525696,-186367525632⟩ : DyadicInterval 40),(⟨748704684534,748704703863⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159426329280,159426329344⟩ : DyadicInterval 40),(⟨-186527871488,-186527871424⟩ : DyadicInterval 40),(⟨748683401791,748683421121⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨43652797,54604254⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43651904,43651968⟩ : DyadicInterval 40),(⟨-43653696,-43653632⟩ : DyadicInterval 40),(⟨762123382714,762123402043⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54602880,54602944⟩ : DyadicInterval 40),(⟨-54605632,-54605568⟩ : DyadicInterval 40),(⟨762123382216,762123401545⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2752,-1728⟩ : DyadicInterval 40),(⟨762123384480,762123404256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171482284334,171606936471⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159355624128,159355624192⟩ : DyadicInterval 40),(⟨-186431028992,-186431028928⟩ : DyadicInterval 40),(⟨748696257385,748696276715⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159463452928,159463452992⟩ : DyadicInterval 40),(⟨-186578724416,-186578724352⟩ : DyadicInterval 40),(⟨748676649153,748676668483⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27115271424,-27075404736⟩ : DyadicInterval 40),(⟨775661085984,775681038592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159401999424,159500567552⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186629568896,-186494545920⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1990_ok : ecellOkT e1990 = true := by decide +kernel
theorem e1990_pos {a z : ℝ} (ha1 : ((639021/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1278891/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1990 e1990_ok ha1 ha2 hz1 hz2 hz

-- box ['1278891/8192000', '63987/409600', '1599/1600', '1999/2000']  interval_lower 21679791/137438953472
noncomputable def e1991 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271161472155,0,true,159500567488,159500567552⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927861783397,0,false,-186629568896,-186629568832⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271275423007,0,true,159599126656,159599126720⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927747832545,0,false,-186764608384,-186764608320⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271054191002,0,true,159407768960,159407769024⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927969064550,0,false,-186502448576,-186502448512⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271189541110,0,true,159524845888,159524845952⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927833714442,0,false,-186662830976,-186662830912⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555310617,0,true,43681920,43681984⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467944935,0,false,-43683712,-43683648⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566269589,0,true,54640448,54640512⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456985963,0,false,-54643200,-54643136⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625060,0,false,-2752,-2688⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626041,0,false,-1792,-1728⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271107827352,0,true,159454165568,159454165632⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927915428200,0,false,-186566001920,-186566001856⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271232486610,0,true,159561990848,159561990912⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927790768942,0,false,-186713723904,-186713723840⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072692399480,0,false,-27151732992,-27151732928⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072731323717,0,false,-27111836288,-27111836224⟩
    { al := (1278891/8192000), au := (63987/409600), zl := (1599/1600), zu := (1999/2000),
      A := ⟨171649844379,171763795231⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159500567488,159500567552⟩ : DyadicInterval 40),(⟨-186629568896,-186629568832⟩ : DyadicInterval 40),(⟨748669896203,748669915533⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159599126656,159599126720⟩ : DyadicInterval 40),(⟨-186764608384,-186764608320⟩ : DyadicInterval 40),(⟨748651954110,748651973439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159407768960,159407769024⟩ : DyadicInterval 40),(⟨-186502448576,-186502448512⟩ : DyadicInterval 40),(⟨748686777095,748686796424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159524845888,159524845952⟩ : DyadicInterval 40),(⟨-186662830976,-186662830912⟩ : DyadicInterval 40),(⟨748665477750,748665497080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨43682841,54641813⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43681920,43681984⟩ : DyadicInterval 40),(⟨-43683712,-43683648⟩ : DyadicInterval 40),(⟨762123382712,762123402041⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54640448,54640512⟩ : DyadicInterval 40),(⟨-54643200,-54643136⟩ : DyadicInterval 40),(⟨762123382212,762123401541⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2752,-1728⟩ : DyadicInterval 40),(⟨762123384480,762123404256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171596199576,171720858834⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159454165568,159454165632⟩ : DyadicInterval 40),(⟨-186566001920,-186566001856⟩ : DyadicInterval 40),(⟨748678338655,748678357985⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159561990848,159561990912⟩ : DyadicInterval 40),(⟨-186713723904,-186713723840⟩ : DyadicInterval 40),(⟨748658716069,748658735399⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27151732992,-27111836224⟩ : DyadicInterval 40),(⟨775679301728,775699269376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159500567488,159599126720⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186764608384,-186629568832⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1991_ok : ecellOkT e1991 = true := by decide +kernel
theorem e1991_pos {a z : ℝ} (ha1 : ((1278891/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((63987/409600 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1991 e1991_ok ha1 ha2 hz1 hz2 hz

-- box ['63987/409600', '1280589/8192000', '999/1000', '7993/8000']  interval_lower 174995255/1099511627776
noncomputable def e1992 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271275423006,0,true,159599126656,159599126720⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927747832546,0,false,-186764608384,-186764608320⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271389373858,0,true,159697677056,159697677120⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927633881694,0,false,-186899664448,-186899664384⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271103659210,0,true,159450560064,159450560128⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927919596342,0,false,-186561062976,-186561062912⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271238980831,0,true,159567607808,159567607872⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927784274721,0,false,-186721420096,-186721420032⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588125003,0,true,76494528,76494592⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435130549,0,false,-76499904,-76499840⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099599114026,0,true,87482752,87482816⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099424141526,0,false,-87489792,-87489728⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620814,0,false,-6976,-6912⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622454,0,false,-5376,-5312⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271189537341,0,true,159524842624,159524842688⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927833718211,0,false,-186662826496,-186662826432⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271314182294,0,true,159632648640,159632648704⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927709073258,0,false,-186810544512,-186810544448⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072666875075,0,false,-27177895872,-27177895808⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072705813369,0,false,-27137983808,-27137983744⟩
    { al := (63987/409600), au := (1280589/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨171763795230,171877746082⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159599126656,159599126720⟩ : DyadicInterval 40),(⟨-186764608384,-186764608320⟩ : DyadicInterval 40),(⟨748651954110,748651973440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159697677056,159697677120⟩ : DyadicInterval 40),(⟨-186899664448,-186899664384⟩ : DyadicInterval 40),(⟨748633999869,748634019199⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159450560064,159450560128⟩ : DyadicInterval 40),(⟨-186561062976,-186561062912⟩ : DyadicInterval 40),(⟨748678994532,748679013861⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159567607808,159567607872⟩ : DyadicInterval 40),(⟨-186721420096,-186721420032⟩ : DyadicInterval 40),(⟨748657693395,748657712725⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨76497227,87486250⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76494528,76494592⟩ : DyadicInterval 40),(⟨-76499904,-76499840⟩ : DyadicInterval 40),(⟨762123380917,762123400246⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨87482752,87482816⟩ : DyadicInterval 40),(⟨-87489792,-87489728⟩ : DyadicInterval 40),(⟨762123380110,762123399440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6976,-5312⟩ : DyadicInterval 40),(⟨762123386272,762123406368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171677909565,171802554518⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159524842624,159524842688⟩ : DyadicInterval 40),(⟨-186662826496,-186662826432⟩ : DyadicInterval 40),(⟨748665478340,748665497670⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159632648640,159632648704⟩ : DyadicInterval 40),(⟨-186810544512,-186810544448⟩ : DyadicInterval 40),(⟨748645848480,748645867809⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27177895872,-27137983744⟩ : DyadicInterval 40),(⟨775692375488,775712350816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159599126656,159697677120⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186899664448,-186764608320⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1992_ok : ecellOkT e1992 = true := by decide +kernel
theorem e1992_pos {a z : ℝ} (ha1 : ((63987/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1280589/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1992 e1992_ok ha1 ha2 hz1 hz2 hz

-- box ['1280589/8192000', '640719/4096000', '999/1000', '7993/8000']  interval_lower 44021677/274877906944
noncomputable def e1993 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271389373857,0,true,159697677056,159697677120⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927633881695,0,false,-186899664448,-186899664384⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271503324709,0,true,159796218560,159796218624⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927519930843,0,false,-187034737088,-187034737024⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271217496110,0,true,159549025216,159549025280⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927805759442,0,false,-186695958976,-186695958912⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271352831975,0,true,159666074752,159666074816⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927670423577,0,false,-186856352704,-186856352640⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588177586,0,true,76547136,76547200⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435077966,0,false,-76552512,-76552448⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099599174126,0,true,87542848,87542912⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099424081426,0,false,-87549888,-87549824⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620805,0,false,-6976,-6912⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622447,0,false,-5376,-5312⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271303431219,0,true,159623350400,159623350464⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927719824333,0,false,-186797802560,-186797802496⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271428083289,0,true,159731152896,159731152960⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927595172263,0,false,-186945547136,-186945547072⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072631268415,0,false,-27214394240,-27214394176⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072670234757,0,false,-27174452096,-27174452032⟩
    { al := (1280589/8192000), au := (640719/4096000), zl := (999/1000), zu := (7993/8000),
      A := ⟨171877746081,171991696933⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159697677056,159697677120⟩ : DyadicInterval 40),(⟨-186899664448,-186899664384⟩ : DyadicInterval 40),(⟨748633999869,748634019199⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159796218560,159796218624⟩ : DyadicInterval 40),(⟨-187034737088,-187034737024⟩ : DyadicInterval 40),(⟨748616033553,748616052883⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159549025216,159549025280⟩ : DyadicInterval 40),(⟨-186695958976,-186695958912⟩ : DyadicInterval 40),(⟨748661076473,748661095802⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159666074752,159666074816⟩ : DyadicInterval 40),(⟨-186856352704,-186856352640⟩ : DyadicInterval 40),(⟨748639758778,748639778107⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨76549810,87546350⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76547136,76547200⟩ : DyadicInterval 40),(⟨-76552512,-76552448⟩ : DyadicInterval 40),(⟨762123380910,762123400239⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨87542848,87542912⟩ : DyadicInterval 40),(⟨-87549888,-87549824⟩ : DyadicInterval 40),(⟨762123380101,762123399430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6976,-5312⟩ : DyadicInterval 40),(⟨762123386272,762123406368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171791803443,171916455513⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159623350400,159623350464⟩ : DyadicInterval 40),(⟨-186797802560,-186797802496⟩ : DyadicInterval 40),(⟨748647542213,748647561543⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159731152896,159731152960⟩ : DyadicInterval 40),(⟨-186945547136,-186945547072⟩ : DyadicInterval 40),(⟨748627898002,748627917331⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27214394240,-27174452032⟩ : DyadicInterval 40),(⟨775710609632,775730600000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159697677056,159796218624⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187034737088,-186899664384⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1993_ok : ecellOkT e1993 = true := by decide +kernel
theorem e1993_pos {a z : ℝ} (ha1 : ((1280589/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((640719/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1993 e1993_ok ha1 ha2 hz1 hz2 hz

-- box ['63987/409600', '1280589/8192000', '7993/8000', '3997/4000']  interval_lower 174838917/1099511627776
noncomputable def e1994 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271275423006,0,true,159599126656,159599126720⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927747832546,0,false,-186764608384,-186764608320⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271389373858,0,true,159697677056,159697677120⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927633881694,0,false,-186899664448,-186899664384⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271125129685,0,true,159469132032,159469132096⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927898125867,0,false,-186586504064,-186586504000⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271260465549,0,true,159586190080,159586190144⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927762790003,0,false,-186746881792,-186746881728⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577196939,0,true,65567168,65567232⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446058613,0,false,-65571136,-65571072⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588178449,0,true,76547968,76548032⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435077103,0,false,-76553344,-76553280⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622446,0,false,-5376,-5312⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623866,0,false,-3968,-3904⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271200272403,0,true,159534127872,159534127936⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927822983149,0,false,-186675547968,-186675547904⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271324924499,0,true,159641939136,159641939200⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927698331053,0,false,-186823276160,-186823276096⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072663517956,0,false,-27181337024,-27181336960⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072702460916,0,false,-27141420096,-27141420032⟩
    { al := (63987/409600), au := (1280589/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨171763795230,171877746082⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159599126656,159599126720⟩ : DyadicInterval 40),(⟨-186764608384,-186764608320⟩ : DyadicInterval 40),(⟨748651954110,748651973440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159697677056,159697677120⟩ : DyadicInterval 40),(⟨-186899664448,-186899664384⟩ : DyadicInterval 40),(⟨748633999869,748634019199⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159469132032,159469132096⟩ : DyadicInterval 40),(⟨-186586504064,-186586504000⟩ : DyadicInterval 40),(⟨748675615945,748675635275⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159586190080,159586190144⟩ : DyadicInterval 40),(⟨-186746881792,-186746881728⟩ : DyadicInterval 40),(⟨748654309886,748654329215⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨65569163,76550673⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65567168,65567232⟩ : DyadicInterval 40),(⟨-65571136,-65571072⟩ : DyadicInterval 40),(⟨762123381625,762123400954⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76547968,76548032⟩ : DyadicInterval 40),(⟨-76553344,-76553280⟩ : DyadicInterval 40),(⟨762123380910,762123400239⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5376,-3904⟩ : DyadicInterval 40),(⟨762123385568,762123405568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171688644627,171813296723⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159534127872,159534127936⟩ : DyadicInterval 40),(⟨-186675547968,-186675547904⟩ : DyadicInterval 40),(⟨748663788280,748663807610⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159641939136,159641939200⟩ : DyadicInterval 40),(⟨-186823276160,-186823276096⟩ : DyadicInterval 40),(⟨748644156058,748644175388⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27181337024,-27141420032⟩ : DyadicInterval 40),(⟨775694093632,775714071392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159599126656,159697677120⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186899664448,-186764608320⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1994_ok : ecellOkT e1994 = true := by decide +kernel
theorem e1994_pos {a z : ℝ} (ha1 : ((63987/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1280589/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1994 e1994_ok ha1 ha2 hz1 hz2 hz

-- box ['1280589/8192000', '640719/4096000', '7993/8000', '3997/4000']  interval_lower 175929957/1099511627776
noncomputable def e1995 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271389373857,0,true,159697677056,159697677120⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927633881695,0,false,-186899664448,-186899664384⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271503324709,0,true,159796218560,159796218624⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927519930843,0,false,-187034737088,-187034737024⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271238980829,0,true,159567607808,159567607872⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927784274723,0,false,-186721420096,-186721420032⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271374330937,0,true,159684667712,159684667776⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927648924615,0,false,-186881834432,-186881834368⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577242010,0,true,65612224,65612288⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446013542,0,false,-65616192,-65616128⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588231038,0,true,76600576,76600640⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435024514,0,false,-76605952,-76605888⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622439,0,false,-5376,-5312⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623861,0,false,-3968,-3904⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271314173401,0,true,159632640960,159632641024⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927709082151,0,false,-186810534016,-186810533952⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271438832617,0,true,159740448704,159740448768⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927584422935,0,false,-186958288768,-186958288704⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072627906842,0,false,-27217840064,-27217840000⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072666877855,0,false,-27177893056,-27177892992⟩
    { al := (1280589/8192000), au := (640719/4096000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨171877746081,171991696933⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159697677056,159697677120⟩ : DyadicInterval 40),(⟨-186899664448,-186899664384⟩ : DyadicInterval 40),(⟨748633999869,748634019199⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159796218560,159796218624⟩ : DyadicInterval 40),(⟨-187034737088,-187034737024⟩ : DyadicInterval 40),(⟨748616033553,748616052883⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159567607808,159567607872⟩ : DyadicInterval 40),(⟨-186721420096,-186721420032⟩ : DyadicInterval 40),(⟨748657693396,748657712725⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159684667712,159684667776⟩ : DyadicInterval 40),(⟨-186881834432,-186881834368⟩ : DyadicInterval 40),(⟨748636370734,748636390064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨65614234,76603262⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65612224,65612288⟩ : DyadicInterval 40),(⟨-65616192,-65616128⟩ : DyadicInterval 40),(⟨762123381620,762123400949⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76600576,76600640⟩ : DyadicInterval 40),(⟨-76605952,-76605888⟩ : DyadicInterval 40),(⟨762123380902,762123400232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5376,-3904⟩ : DyadicInterval 40),(⟨762123385568,762123405568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171802545625,171927204841⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159632640960,159632641024⟩ : DyadicInterval 40),(⟨-186810534016,-186810533952⟩ : DyadicInterval 40),(⟨748645849893,748645869223⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159740448704,159740448768⟩ : DyadicInterval 40),(⟨-186958288768,-186958288704⟩ : DyadicInterval 40),(⟨748626203316,748626222645⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27217840064,-27177892992⟩ : DyadicInterval 40),(⟨775712330112,775732322912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159697677056,159796218624⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187034737088,-186899664384⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1995_ok : ecellOkT e1995 = true := by decide +kernel
theorem e1995_pos {a z : ℝ} (ha1 : ((1280589/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((640719/4096000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1995 e1995_ok ha1 ha2 hz1 hz2 hz

-- box ['640719/4096000', '1282287/8192000', '999/1000', '7993/8000']  interval_lower 88590381/549755813888
noncomputable def e1996 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271503324708,0,true,159796218560,159796218624⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927519930844,0,false,-187034737088,-187034737024⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271617275560,0,true,159894751296,159894751360⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927405979992,0,false,-187169826368,-187169826304⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271331333011,0,true,159647481536,159647481600⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927691922541,0,false,-186830871552,-186830871488⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271466683119,0,true,159764532928,159764532992⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927556572433,0,false,-186991301888,-186991301824⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588230174,0,true,76599680,76599744⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435025378,0,false,-76605120,-76605056⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099599234230,0,true,87602944,87603008⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099424021322,0,false,-87609984,-87609920⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620795,0,false,-7040,-6976⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622440,0,false,-5376,-5312⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271417325094,0,true,159721849344,159721849408⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927605930458,0,false,-186932795136,-186932795072⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271541984289,0,true,159829648320,159829648384⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927481271263,0,false,-187080566336,-187080566272⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072595638154,0,false,-27250918016,-27250917952⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072634632551,0,false,-27210945792,-27210945728⟩
    { al := (640719/4096000), au := (1282287/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨171991696932,172105647784⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159796218560,159796218624⟩ : DyadicInterval 40),(⟨-187034737088,-187034737024⟩ : DyadicInterval 40),(⟨748616033554,748616052883⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159894751296,159894751360⟩ : DyadicInterval 40),(⟨-187169826368,-187169826304⟩ : DyadicInterval 40),(⟨748598055115,748598074444⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159647481536,159647481600⟩ : DyadicInterval 40),(⟨-186830871552,-186830871488⟩ : DyadicInterval 40),(⟨748643146351,748643165681⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159764532928,159764532992⟩ : DyadicInterval 40),(⟨-186991301888,-186991301824⟩ : DyadicInterval 40),(⟨748621812054,748621831384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨76602398,87606454⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76599680,76599744⟩ : DyadicInterval 40),(⟨-76605120,-76605056⟩ : DyadicInterval 40),(⟨762123380934,762123400264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨87602944,87603008⟩ : DyadicInterval 40),(⟨-87609984,-87609920⟩ : DyadicInterval 40),(⟨762123380091,762123399421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7040,-5312⟩ : DyadicInterval 40),(⟨762123386272,762123406400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171905697318,172030356513⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159721849344,159721849408⟩ : DyadicInterval 40),(⟨-186932795136,-186932795072⟩ : DyadicInterval 40),(⟨748629593974,748629613303⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159829648320,159829648384⟩ : DyadicInterval 40),(⟨-187080566336,-187080566272⟩ : DyadicInterval 40),(⟨748609935431,748609954760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27250918016,-27210945728⟩ : DyadicInterval 40),(⟨775728856480,775748861888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159796218560,159894751360⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187169826368,-187034737024⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1996_ok : ecellOkT e1996 = true := by decide +kernel
theorem e1996_pos {a z : ℝ} (ha1 : ((640719/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1282287/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1996 e1996_ok ha1 ha2 hz1 hz2 hz

-- box ['1282287/8192000', '20049/128000', '999/1000', '7993/8000']  interval_lower 178277545/1099511627776
noncomputable def e1997 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271617275559,0,true,159894751296,159894751360⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927405979993,0,false,-187169826368,-187169826304⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271731226412,0,true,159993275200,159993275264⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927292029140,0,false,-187304932224,-187304932160⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271445169911,0,true,159745929024,159745929088⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927578085641,0,false,-186965800704,-186965800640⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271580534264,0,true,159862982272,159862982336⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927442721288,0,false,-187126267584,-187126267520⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588282765,0,true,76652288,76652352⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434972787,0,false,-76657664,-76657600⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099599294339,0,true,87663040,87663104⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099423961213,0,false,-87670080,-87670016⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620786,0,false,-7040,-6976⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622432,0,false,-5376,-5312⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271531218968,0,true,159820339456,159820339520⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927492036584,0,false,-187067804352,-187067804288⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271655885291,0,true,159928134912,159928134976⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927367370261,0,false,-187215602176,-187215602112⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072559984294,0,false,-27287467200,-27287467136⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072599006749,0,false,-27247464896,-27247464832⟩
    { al := (1282287/8192000), au := (20049/128000), zl := (999/1000), zu := (7993/8000),
      A := ⟨172105647783,172219598636⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159894751296,159894751360⟩ : DyadicInterval 40),(⟨-187169826368,-187169826304⟩ : DyadicInterval 40),(⟨748598055115,748598074444⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159993275200,159993275264⟩ : DyadicInterval 40),(⟨-187304932224,-187304932160⟩ : DyadicInterval 40),(⟨748580064561,748580083890⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159745929024,159745929088⟩ : DyadicInterval 40),(⟨-186965800704,-186965800640⟩ : DyadicInterval 40),(⟨748625204167,748625223497⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159862982272,159862982336⟩ : DyadicInterval 40),(⟨-187126267584,-187126267520⟩ : DyadicInterval 40),(⟨748603853233,748603872562⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨76654989,87666563⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76652288,76652352⟩ : DyadicInterval 40),(⟨-76657664,-76657600⟩ : DyadicInterval 40),(⟨762123380895,762123400225⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨87663040,87663104⟩ : DyadicInterval 40),(⟨-87670080,-87670016⟩ : DyadicInterval 40),(⟨762123380081,762123399411⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7040,-5312⟩ : DyadicInterval 40),(⟨762123386272,762123406400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172019591192,172144257515⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159820339456,159820339520⟩ : DyadicInterval 40),(⟨-187067804352,-187067804288⟩ : DyadicInterval 40),(⟨748611633672,748611653002⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159928134912,159928134976⟩ : DyadicInterval 40),(⟨-187215602176,-187215602112⟩ : DyadicInterval 40),(⟨748591960795,748591980124⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27287467200,-27247464832⟩ : DyadicInterval 40),(⟨775747116032,775767136480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159894751296,159993275264⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187304932224,-187169826304⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1997_ok : ecellOkT e1997 = true := by decide +kernel
theorem e1997_pos {a z : ℝ} (ha1 : ((1282287/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((20049/128000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1997 e1997_ok ha1 ha2 hz1 hz2 hz

-- box ['640719/4096000', '1282287/8192000', '7993/8000', '3997/4000']  interval_lower 177023627/1099511627776
noncomputable def e1998 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271503324708,0,true,159796218560,159796218624⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927519930844,0,false,-187034737088,-187034737024⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271617275560,0,true,159894751296,159894751360⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927405979992,0,false,-187169826368,-187169826304⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271352831973,0,true,159666074752,159666074816⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927670423579,0,false,-186856352704,-186856352640⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271488196325,0,true,159783136512,159783136576⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927535059227,0,false,-187016803584,-187016803520⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577287087,0,true,65657344,65657408⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445968465,0,false,-65661312,-65661248⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588283629,0,true,76653120,76653184⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434971923,0,false,-76658560,-76658496⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622431,0,false,-5376,-5312⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623856,0,false,-3968,-3904⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271428074393,0,true,159731145216,159731145280⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927595181159,0,false,-186945536640,-186945536576⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271552740738,0,true,159838949440,159838949504⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927470514814,0,false,-187093318016,-187093317952⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072592272126,0,false,-27254368512,-27254368448⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072631271197,0,false,-27214391360,-27214391296⟩
    { al := (640719/4096000), au := (1282287/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨171991696932,172105647784⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159796218560,159796218624⟩ : DyadicInterval 40),(⟨-187034737088,-187034737024⟩ : DyadicInterval 40),(⟨748616033554,748616052883⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159894751296,159894751360⟩ : DyadicInterval 40),(⟨-187169826368,-187169826304⟩ : DyadicInterval 40),(⟨748598055115,748598074444⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159666074752,159666074816⟩ : DyadicInterval 40),(⟨-186856352704,-186856352640⟩ : DyadicInterval 40),(⟨748639758778,748639778108⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159783136512,159783136576⟩ : DyadicInterval 40),(⟨-187016803584,-187016803520⟩ : DyadicInterval 40),(⟨748618419480,748618438809⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨65659311,76655853⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65657344,65657408⟩ : DyadicInterval 40),(⟨-65661312,-65661248⟩ : DyadicInterval 40),(⟨762123381614,762123400944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76653120,76653184⟩ : DyadicInterval 40),(⟨-76658560,-76658496⟩ : DyadicInterval 40),(⟨762123380927,762123400256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5376,-3904⟩ : DyadicInterval 40),(⟨762123385568,762123405568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171916446617,172041112962⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159731145216,159731145280⟩ : DyadicInterval 40),(⟨-186945536640,-186945536576⟩ : DyadicInterval 40),(⟨748627899417,748627918747⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159838949440,159838949504⟩ : DyadicInterval 40),(⟨-187093318016,-187093317952⟩ : DyadicInterval 40),(⟨748608238505,748608257835⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27254368512,-27214391296⟩ : DyadicInterval 40),(⟨775730579264,775750587136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159796218560,159894751360⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187169826368,-187034737024⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1998_ok : ecellOkT e1998 = true := by decide +kernel
theorem e1998_pos {a z : ℝ} (ha1 : ((640719/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1282287/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1998 e1998_ok ha1 ha2 hz1 hz2 hz

-- box ['1282287/8192000', '20049/128000', '7993/8000', '3997/4000']  interval_lower 89060041/549755813888
noncomputable def e1999 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271617275559,0,true,159894751296,159894751360⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927405979993,0,false,-187169826368,-187169826304⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271731226412,0,true,159993275200,159993275264⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927292029140,0,false,-187304932224,-187304932160⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271466683117,0,true,159764532928,159764532992⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927556572435,0,false,-186991301888,-186991301824⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271602061714,0,true,159881596480,159881596544⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927421193838,0,false,-187151789312,-187151789248⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577332164,0,true,65702400,65702464⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445923388,0,false,-65706368,-65706304⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588336225,0,true,76705728,76705792⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434919327,0,false,-76711168,-76711104⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622424,0,false,-5376,-5312⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623850,0,false,-3968,-3904⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271541975391,0,true,159829640640,159829640704⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927481280161,0,false,-187080555840,-187080555776⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271666648860,0,true,159937441408,159937441472⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927356606692,0,false,-187228363776,-187228363712⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072556613808,0,false,-27290922368,-27290922304⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072595640939,0,false,-27250915136,-27250915072⟩
    { al := (1282287/8192000), au := (20049/128000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨172105647783,172219598636⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159894751296,159894751360⟩ : DyadicInterval 40),(⟨-187169826368,-187169826304⟩ : DyadicInterval 40),(⟨748598055115,748598074444⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159993275200,159993275264⟩ : DyadicInterval 40),(⟨-187304932224,-187304932160⟩ : DyadicInterval 40),(⟨748580064561,748580083890⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159764532928,159764532992⟩ : DyadicInterval 40),(⟨-186991301888,-186991301824⟩ : DyadicInterval 40),(⟨748621812055,748621831384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159881596480,159881596544⟩ : DyadicInterval 40),(⟨-187151789312,-187151789248⟩ : DyadicInterval 40),(⟨748600456149,748600475478⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨65704388,76708449⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65702400,65702464⟩ : DyadicInterval 40),(⟨-65706368,-65706304⟩ : DyadicInterval 40),(⟨762123381609,762123400938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76705728,76705792⟩ : DyadicInterval 40),(⟨-76711168,-76711104⟩ : DyadicInterval 40),(⟨762123380920,762123400249⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5376,-3904⟩ : DyadicInterval 40),(⟨762123385568,762123405568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172030347615,172155021084⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159829640640,159829640704⟩ : DyadicInterval 40),(⟨-187080555840,-187080555776⟩ : DyadicInterval 40),(⟨748609936848,748609956178⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159937441408,159937441472⟩ : DyadicInterval 40),(⟨-187228363776,-187228363712⟩ : DyadicInterval 40),(⟨748590261535,748590280864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27290922368,-27250915072⟩ : DyadicInterval 40),(⟨775748841152,775768864064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159894751296,159993275264⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187304932224,-187169826304⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1999_ok : ecellOkT e1999 = true := by decide +kernel
theorem e1999_pos {a z : ℝ} (ha1 : ((1282287/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((20049/128000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1999 e1999_ok ha1 ha2 hz1 hz2 hz

-- box ['63987/409600', '1280589/8192000', '3997/4000', '1599/1600']  interval_lower 43670575/274877906944
noncomputable def e2000 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271275423006,0,true,159599126656,159599126720⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927747832546,0,false,-186764608384,-186764608320⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271389373858,0,true,159697677056,159697677120⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927633881694,0,false,-186899664448,-186899664384⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271146600159,0,true,159487703616,159487703680⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927876655393,0,false,-186611945792,-186611945728⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271281950267,0,true,159604772032,159604772096⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927741305285,0,false,-186772344128,-186772344064⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566268825,0,true,54639680,54639744⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456986727,0,false,-54642432,-54642368⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577242824,0,true,65613056,65613120⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446012728,0,false,-65617024,-65616960⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623860,0,false,-3968,-3904⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625061,0,false,-2752,-2688⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271211007483,0,true,159543412992,159543413056⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927812248069,0,false,-186688269568,-186688269504⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271335666726,0,true,159651229568,159651229632⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927687588826,0,false,-186836007936,-186836007872⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072660160619,0,false,-27184778368,-27184778304⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072699108248,0,false,-27144856512,-27144856448⟩
    { al := (63987/409600), au := (1280589/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨171763795230,171877746082⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159599126656,159599126720⟩ : DyadicInterval 40),(⟨-186764608384,-186764608320⟩ : DyadicInterval 40),(⟨748651954110,748651973440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159697677056,159697677120⟩ : DyadicInterval 40),(⟨-186899664448,-186899664384⟩ : DyadicInterval 40),(⟨748633999869,748634019199⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159487703616,159487703680⟩ : DyadicInterval 40),(⟨-186611945792,-186611945728⟩ : DyadicInterval 40),(⟨748672236990,748672256320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159604772032,159604772096⟩ : DyadicInterval 40),(⟨-186772344128,-186772344064⟩ : DyadicInterval 40),(⟨748650925971,748650945301⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54641049,65615048⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54639680,54639744⟩ : DyadicInterval 40),(⟨-54642432,-54642368⟩ : DyadicInterval 40),(⟨762123382212,762123401541⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65613056,65613120⟩ : DyadicInterval 40),(⟨-65617024,-65616960⟩ : DyadicInterval 40),(⟨762123381620,762123400949⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3968,-2688⟩ : DyadicInterval 40),(⟨762123384960,762123404864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171699379707,171824038950⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159543412992,159543413056⟩ : DyadicInterval 40),(⟨-186688269568,-186688269504⟩ : DyadicInterval 40),(⟨748662098130,748662117459⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159651229568,159651229632⟩ : DyadicInterval 40),(⟨-186836007936,-186836007872⟩ : DyadicInterval 40),(⟨748642463509,748642482839⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27184778368,-27144856448⟩ : DyadicInterval 40),(⟨775695811840,775715792064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159599126656,159697677120⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186899664448,-186764608320⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2000_ok : ecellOkT e2000 = true := by decide +kernel
theorem e2000_pos {a z : ℝ} (ha1 : ((63987/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1280589/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2000 e2000_ok ha1 ha2 hz1 hz2 hz

-- box ['1280589/8192000', '640719/4096000', '3997/4000', '1599/1600']  interval_lower 175773087/1099511627776
noncomputable def e2001 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271389373857,0,true,159697677056,159697677120⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927633881695,0,false,-186899664448,-186899664384⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271503324709,0,true,159796218560,159796218624⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927519930843,0,false,-187034737088,-187034737024⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271260465547,0,true,159586190080,159586190144⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927762790005,0,false,-186746881792,-186746881728⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271395829899,0,true,159703260288,159703260352⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927627425653,0,false,-186907316736,-186907316672⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566306386,0,true,54677248,54677312⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456949166,0,false,-54680000,-54679936⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577287900,0,true,65658112,65658176⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445967652,0,false,-65662144,-65662080⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623854,0,false,-3968,-3904⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625057,0,false,-2752,-2688⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271324915606,0,true,159641931392,159641931456⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927698339946,0,false,-186823265600,-186823265536⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271449581965,0,true,159749744448,159749744512⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927573673587,0,false,-186971030592,-186971030528⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072624545053,0,false,-27221286144,-27221286080⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072663520736,0,false,-27181334144,-27181334080⟩
    { al := (1280589/8192000), au := (640719/4096000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨171877746081,171991696933⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159697677056,159697677120⟩ : DyadicInterval 40),(⟨-186899664448,-186899664384⟩ : DyadicInterval 40),(⟨748633999869,748634019199⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159796218560,159796218624⟩ : DyadicInterval 40),(⟨-187034737088,-187034737024⟩ : DyadicInterval 40),(⟨748616033553,748616052883⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159586190080,159586190144⟩ : DyadicInterval 40),(⟨-186746881792,-186746881728⟩ : DyadicInterval 40),(⟨748654309886,748654329216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159703260288,159703260352⟩ : DyadicInterval 40),(⟨-186907316736,-186907316672⟩ : DyadicInterval 40),(⟨748632982294,748633001623⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54678610,65660124⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54677248,54677312⟩ : DyadicInterval 40),(⟨-54680000,-54679936⟩ : DyadicInterval 40),(⟨762123382208,762123401537⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65658112,65658176⟩ : DyadicInterval 40),(⟨-65662144,-65662080⟩ : DyadicInterval 40),(⟨762123381646,762123400976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3968,-2688⟩ : DyadicInterval 40),(⟨762123384960,762123404864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171813287830,171937954189⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159641931392,159641931456⟩ : DyadicInterval 40),(⟨-186823265600,-186823265536⟩ : DyadicInterval 40),(⟨748644157482,748644176811⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159749744448,159749744512⟩ : DyadicInterval 40),(⟨-186971030592,-186971030528⟩ : DyadicInterval 40),(⟨748624508529,748624527859⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27221286144,-27181334080⟩ : DyadicInterval 40),(⟨775714050656,775734045952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159697677056,159796218624⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187034737088,-186899664384⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2001_ok : ecellOkT e2001 = true := by decide +kernel
theorem e2001_pos {a z : ℝ} (ha1 : ((1280589/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((640719/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2001 e2001_ok ha1 ha2 hz1 hz2 hz

-- box ['63987/409600', '1280589/8192000', '1599/1600', '1999/2000']  interval_lower 174525997/1099511627776
noncomputable def e2002 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271275423006,0,true,159599126656,159599126720⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927747832546,0,false,-186764608384,-186764608320⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271389373858,0,true,159697677056,159697677120⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927633881694,0,false,-186899664448,-186899664384⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271168070633,0,true,159506274880,159506274944⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927855184919,0,false,-186637388096,-186637388032⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271303434986,0,true,159623353664,159623353728⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927719820566,0,false,-186797806976,-186797806912⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555340663,0,true,43712000,43712064⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467914889,0,false,-43713792,-43713728⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566307149,0,true,54677952,54678016⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456948403,0,false,-54680768,-54680704⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625056,0,false,-2752,-2688⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626039,0,false,-1792,-1728⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271221742586,0,true,159552698112,159552698176⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927801512966,0,false,-186700991360,-186700991296⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271346408979,0,true,159660519936,159660520000⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927676846573,0,false,-186848739968,-186848739904⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072656803065,0,false,-27188220032,-27188219968⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072695755363,0,false,-27148293248,-27148293184⟩
    { al := (63987/409600), au := (1280589/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨171763795230,171877746082⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159599126656,159599126720⟩ : DyadicInterval 40),(⟨-186764608384,-186764608320⟩ : DyadicInterval 40),(⟨748651954110,748651973440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159697677056,159697677120⟩ : DyadicInterval 40),(⟨-186899664448,-186899664384⟩ : DyadicInterval 40),(⟨748633999869,748634019199⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159506274880,159506274944⟩ : DyadicInterval 40),(⟨-186637388096,-186637388032⟩ : DyadicInterval 40),(⟨748668857605,748668876934⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159623353664,159623353728⟩ : DyadicInterval 40),(⟨-186797806976,-186797806912⟩ : DyadicInterval 40),(⟨748647541596,748647560926⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨43712887,54679373⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43712000,43712064⟩ : DyadicInterval 40),(⟨-43713792,-43713728⟩ : DyadicInterval 40),(⟨762123382710,762123402039⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54677952,54678016⟩ : DyadicInterval 40),(⟨-54680768,-54680704⟩ : DyadicInterval 40),(⟨762123382240,762123401569⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2752,-1728⟩ : DyadicInterval 40),(⟨762123384480,762123404256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171710114810,171834781203⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159552698112,159552698176⟩ : DyadicInterval 40),(⟨-186700991360,-186700991296⟩ : DyadicInterval 40),(⟨748660407843,748660427172⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159660519936,159660520000⟩ : DyadicInterval 40),(⟨-186848739968,-186848739904⟩ : DyadicInterval 40),(⟨748640770886,748640790216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27188220032,-27148293184⟩ : DyadicInterval 40),(⟨775697530208,775717512896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159599126656,159697677120⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186899664448,-186764608320⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2002_ok : ecellOkT e2002 = true := by decide +kernel
theorem e2002_pos {a z : ℝ} (ha1 : ((63987/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1280589/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2002 e2002_ok ha1 ha2 hz1 hz2 hz

-- box ['1280589/8192000', '640719/4096000', '1599/1600', '1999/2000']  interval_lower 175616197/1099511627776
noncomputable def e2003 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271389373857,0,true,159697677056,159697677120⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927633881695,0,false,-186899664448,-186899664384⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271503324709,0,true,159796218560,159796218624⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927519930843,0,false,-187034737088,-187034737024⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271281950265,0,true,159604772032,159604772096⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927741305287,0,false,-186772344128,-186772344064⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271417328861,0,true,159721852608,159721852672⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927605926691,0,false,-186932799616,-186932799552⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555370711,0,true,43742016,43742080⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467884841,0,false,-43743808,-43743744⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566344713,0,true,54715520,54715584⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456910839,0,false,-54718336,-54718272⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625053,0,false,-2752,-2688⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626036,0,false,-1792,-1728⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271335657832,0,true,159651221824,159651221888⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927687597720,0,false,-186835997440,-186835997376⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271460331341,0,true,159759040128,159759040192⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927562924211,0,false,-186983772608,-186983772544⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072621183045,0,false,-27224732416,-27224732352⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072660163400,0,false,-27184775552,-27184775488⟩
    { al := (1280589/8192000), au := (640719/4096000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨171877746081,171991696933⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159697677056,159697677120⟩ : DyadicInterval 40),(⟨-186899664448,-186899664384⟩ : DyadicInterval 40),(⟨748633999869,748634019199⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159796218560,159796218624⟩ : DyadicInterval 40),(⟨-187034737088,-187034737024⟩ : DyadicInterval 40),(⟨748616033553,748616052883⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159604772032,159604772096⟩ : DyadicInterval 40),(⟨-186772344128,-186772344064⟩ : DyadicInterval 40),(⟨748650925971,748650945301⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159721852608,159721852672⟩ : DyadicInterval 40),(⟨-186932799616,-186932799552⟩ : DyadicInterval 40),(⟨748629593382,748629612712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨43742935,54716937⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43742016,43742080⟩ : DyadicInterval 40),(⟨-43743808,-43743744⟩ : DyadicInterval 40),(⟨762123382707,762123402036⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54715520,54715584⟩ : DyadicInterval 40),(⟨-54718336,-54718272⟩ : DyadicInterval 40),(⟨762123382236,762123401566⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2752,-1728⟩ : DyadicInterval 40),(⟨762123384480,762123404256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171824030056,171948703565⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159651221824,159651221888⟩ : DyadicInterval 40),(⟨-186835997440,-186835997376⟩ : DyadicInterval 40),(⟨748642464960,748642484289⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159759040128,159759040192⟩ : DyadicInterval 40),(⟨-186983772608,-186983772544⟩ : DyadicInterval 40),(⟨748622813641,748622832971⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27224732416,-27184775488⟩ : DyadicInterval 40),(⟨775715771360,775735769088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159697677056,159796218624⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187034737088,-186899664384⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2003_ok : ecellOkT e2003 = true := by decide +kernel
theorem e2003_pos {a z : ℝ} (ha1 : ((1280589/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((640719/4096000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2003 e2003_ok ha1 ha2 hz1 hz2 hz

-- box ['640719/4096000', '1282287/8192000', '3997/4000', '1599/1600']  interval_lower 88433143/549755813888
noncomputable def e2004 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271503324708,0,true,159796218560,159796218624⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927519930844,0,false,-187034737088,-187034737024⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271617275560,0,true,159894751296,159894751360⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927405979992,0,false,-187169826368,-187169826304⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271374330935,0,true,159684667712,159684667776⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927648924617,0,false,-186881834432,-186881834368⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271509709531,0,true,159801739776,159801739840⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927513546021,0,false,-187042305920,-187042305856⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566343949,0,true,54714752,54714816⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456911603,0,false,-54717568,-54717504⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577332978,0,true,65703232,65703296⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445922574,0,false,-65707200,-65707136⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623849,0,false,-3968,-3904⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625054,0,false,-2752,-2688⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271438823721,0,true,159740441024,159740441088⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927584431831,0,false,-186958278272,-186958278208⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271563497210,0,true,159848250560,159848250624⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927459758342,0,false,-187106069824,-187106069760⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072588905880,0,false,-27257819264,-27257819200⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072627909625,0,false,-27217837184,-27217837120⟩
    { al := (640719/4096000), au := (1282287/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨171991696932,172105647784⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159796218560,159796218624⟩ : DyadicInterval 40),(⟨-187034737088,-187034737024⟩ : DyadicInterval 40),(⟨748616033554,748616052883⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159894751296,159894751360⟩ : DyadicInterval 40),(⟨-187169826368,-187169826304⟩ : DyadicInterval 40),(⟨748598055115,748598074444⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159684667712,159684667776⟩ : DyadicInterval 40),(⟨-186881834432,-186881834368⟩ : DyadicInterval 40),(⟨748636370735,748636390064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159801739776,159801739840⟩ : DyadicInterval 40),(⟨-187042305920,-187042305856⟩ : DyadicInterval 40),(⟨748615026497,748615045827⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54716173,65705202⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54714752,54714816⟩ : DyadicInterval 40),(⟨-54717568,-54717504⟩ : DyadicInterval 40),(⟨762123382237,762123401566⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65703232,65703296⟩ : DyadicInterval 40),(⟨-65707200,-65707136⟩ : DyadicInterval 40),(⟨762123381609,762123400938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3968,-2688⟩ : DyadicInterval 40),(⟨762123384960,762123404864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171927195945,172051869434⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159740441024,159740441088⟩ : DyadicInterval 40),(⟨-186958278272,-186958278208⟩ : DyadicInterval 40),(⟨748626204732,748626224061⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159848250560,159848250624⟩ : DyadicInterval 40),(⟨-187106069824,-187106069760⟩ : DyadicInterval 40),(⟨748606541414,748606560743⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27257819264,-27217837120⟩ : DyadicInterval 40),(⟨775732302176,775752312512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159796218560,159894751360⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187169826368,-187034737024⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2004_ok : ecellOkT e2004 = true := by decide +kernel
theorem e2004_pos {a z : ℝ} (ha1 : ((640719/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1282287/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2004 e2004_ok ha1 ha2 hz1 hz2 hz

-- box ['1282287/8192000', '20049/128000', '3997/4000', '1599/1600']  interval_lower 88981191/549755813888
noncomputable def e2005 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271617275559,0,true,159894751296,159894751360⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927405979993,0,false,-187169826368,-187169826304⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271731226412,0,true,159993275200,159993275264⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927292029140,0,false,-187304932224,-187304932160⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271488196323,0,true,159783136512,159783136576⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927535059229,0,false,-187016803584,-187016803520⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271623589163,0,true,159900210368,159900210432⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927399666389,0,false,-187177311680,-187177311616⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566381514,0,true,54752320,54752384⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456874038,0,false,-54755136,-54755072⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577378061,0,true,65748288,65748352⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445877491,0,false,-65752256,-65752192⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623844,0,false,-3968,-3904⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625050,0,false,-2752,-2688⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271552731840,0,true,159838941760,159838941824⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927470523712,0,false,-187093307456,-187093307392⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271677412451,0,true,159946747776,159946747840⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927345843101,0,false,-187241125632,-187241125568⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072553243104,0,false,-27294377792,-27294377728⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072592274911,0,false,-27254365632,-27254365568⟩
    { al := (1282287/8192000), au := (20049/128000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨172105647783,172219598636⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159894751296,159894751360⟩ : DyadicInterval 40),(⟨-187169826368,-187169826304⟩ : DyadicInterval 40),(⟨748598055115,748598074444⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159993275200,159993275264⟩ : DyadicInterval 40),(⟨-187304932224,-187304932160⟩ : DyadicInterval 40),(⟨748580064561,748580083890⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159783136512,159783136576⟩ : DyadicInterval 40),(⟨-187016803584,-187016803520⟩ : DyadicInterval 40),(⟨748618419481,748618438810⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159900210368,159900210432⟩ : DyadicInterval 40),(⟨-187177311680,-187177311616⟩ : DyadicInterval 40),(⟨748597058655,748597077985⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54753738,65750285⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54752320,54752384⟩ : DyadicInterval 40),(⟨-54755136,-54755072⟩ : DyadicInterval 40),(⟨762123382233,762123401562⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65748288,65748352⟩ : DyadicInterval 40),(⟨-65752256,-65752192⟩ : DyadicInterval 40),(⟨762123381604,762123400933⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3968,-2688⟩ : DyadicInterval 40),(⟨762123384960,762123404864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172041104064,172165784675⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159838941760,159838941824⟩ : DyadicInterval 40),(⟨-187093307456,-187093307392⟩ : DyadicInterval 40),(⟨748608239896,748608259225⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159946747776,159946747840⟩ : DyadicInterval 40),(⟨-187241125632,-187241125568⟩ : DyadicInterval 40),(⟨748588562237,748588581567⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27294377792,-27254365568⟩ : DyadicInterval 40),(⟨775750566400,775770591776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159894751296,159993275264⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187304932224,-187169826304⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2005_ok : ecellOkT e2005 = true := by decide +kernel
theorem e2005_pos {a z : ℝ} (ha1 : ((1282287/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((20049/128000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2005 e2005_ok ha1 ha2 hz1 hz2 hz

-- box ['640719/4096000', '1282287/8192000', '1599/1600', '1999/2000']  interval_lower 176709337/1099511627776
noncomputable def e2006 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271503324708,0,true,159796218560,159796218624⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927519930844,0,false,-187034737088,-187034737024⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271617275560,0,true,159894751296,159894751360⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927405979992,0,false,-187169826368,-187169826304⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271395829897,0,true,159703260288,159703260352⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927627425655,0,false,-186907316736,-186907316672⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271531222737,0,true,159820342656,159820342720⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927492032815,0,false,-187067808832,-187067808768⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555400762,0,true,43772096,43772160⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467854790,0,false,-43773888,-43773824⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566382278,0,true,54753088,54753152⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456873274,0,false,-54755904,-54755840⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625049,0,false,-2752,-2688⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626034,0,false,-1792,-1728⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271449573068,0,true,159749736768,159749736832⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927573682484,0,false,-186971020032,-186971019968⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271574253701,0,true,159857551552,159857551616⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927449001851,0,false,-187118821824,-187118821760⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072585539417,0,false,-27261270208,-27261270144⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072624547836,0,false,-27221283264,-27221283200⟩
    { al := (640719/4096000), au := (1282287/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨171991696932,172105647784⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159796218560,159796218624⟩ : DyadicInterval 40),(⟨-187034737088,-187034737024⟩ : DyadicInterval 40),(⟨748616033554,748616052883⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159894751296,159894751360⟩ : DyadicInterval 40),(⟨-187169826368,-187169826304⟩ : DyadicInterval 40),(⟨748598055115,748598074444⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159703260288,159703260352⟩ : DyadicInterval 40),(⟨-186907316736,-186907316672⟩ : DyadicInterval 40),(⟨748632982294,748633001624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159820342656,159820342720⟩ : DyadicInterval 40),(⟨-187067808832,-187067808768⟩ : DyadicInterval 40),(⟨748611633117,748611652447⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨43772986,54754502⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43772096,43772160⟩ : DyadicInterval 40),(⟨-43773888,-43773824⟩ : DyadicInterval 40),(⟨762123382705,762123402034⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54753088,54753152⟩ : DyadicInterval 40),(⟨-54755904,-54755840⟩ : DyadicInterval 40),(⟨762123382233,762123401562⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2752,-1728⟩ : DyadicInterval 40),(⟨762123384480,762123404256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171937945292,172062625925⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159749736768,159749736832⟩ : DyadicInterval 40),(⟨-186971020032,-186971019968⟩ : DyadicInterval 40),(⟨748624509918,748624529248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159857551552,159857551616⟩ : DyadicInterval 40),(⟨-187118821824,-187118821760⟩ : DyadicInterval 40),(⟨748604844259,748604863588⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27261270208,-27221283200⟩ : DyadicInterval 40),(⟨775734025216,775754037984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159796218560,159894751360⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187169826368,-187034737024⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2006_ok : ecellOkT e2006 = true := by decide +kernel
theorem e2006_pos {a z : ℝ} (ha1 : ((640719/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1282287/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2006 e2006_ok ha1 ha2 hz1 hz2 hz

-- box ['1282287/8192000', '20049/128000', '1599/1600', '1999/2000']  interval_lower 11112803/68719476736
noncomputable def e2007 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271617275559,0,true,159894751296,159894751360⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927405979993,0,false,-187169826368,-187169826304⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271731226412,0,true,159993275200,159993275264⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927292029140,0,false,-187304932224,-187304932160⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271509709529,0,true,159801739776,159801739840⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927513546023,0,false,-187042305920,-187042305856⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271645116613,0,true,159918824000,159918824064⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927378138939,0,false,-187202834624,-187202834560⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555430814,0,true,43802112,43802176⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467824738,0,false,-43803968,-43803904⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566419848,0,true,54790656,54790720⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456835704,0,false,-54793472,-54793408⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625045,0,false,-2752,-2688⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626031,0,false,-1792,-1728⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271563488311,0,true,159848242816,159848242880⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927459767241,0,false,-187106059264,-187106059200⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271688176070,0,true,159956054144,159956054208⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927335079482,0,false,-187253887616,-187253887552⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072549872180,0,false,-27297833472,-27297833408⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072588908666,0,false,-27257816384,-27257816320⟩
    { al := (1282287/8192000), au := (20049/128000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨172105647783,172219598636⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159894751296,159894751360⟩ : DyadicInterval 40),(⟨-187169826368,-187169826304⟩ : DyadicInterval 40),(⟨748598055115,748598074444⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159993275200,159993275264⟩ : DyadicInterval 40),(⟨-187304932224,-187304932160⟩ : DyadicInterval 40),(⟨748580064561,748580083890⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159801739776,159801739840⟩ : DyadicInterval 40),(⟨-187042305920,-187042305856⟩ : DyadicInterval 40),(⟨748615026498,748615045828⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159918824000,159918824064⟩ : DyadicInterval 40),(⟨-187202834624,-187202834560⟩ : DyadicInterval 40),(⟨748593660688,748593680018⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨43803038,54792072⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43802112,43802176⟩ : DyadicInterval 40),(⟨-43803968,-43803904⟩ : DyadicInterval 40),(⟨762123382734,762123402063⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54790656,54790720⟩ : DyadicInterval 40),(⟨-54793472,-54793408⟩ : DyadicInterval 40),(⟨762123382229,762123401558⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2752,-1728⟩ : DyadicInterval 40),(⟨762123384480,762123404256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172051860535,172176548294⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159848242816,159848242880⟩ : DyadicInterval 40),(⟨-187106059264,-187106059200⟩ : DyadicInterval 40),(⟨748606542842,748606562172⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159956054144,159956054208⟩ : DyadicInterval 40),(⟨-187253887616,-187253887552⟩ : DyadicInterval 40),(⟨748586862773,748586882103⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27297833472,-27257816320⟩ : DyadicInterval 40),(⟨775752291776,775772319616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159894751296,159993275264⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187304932224,-187169826304⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2007_ok : ecellOkT e2007 = true := by decide +kernel
theorem e2007_pos {a z : ℝ} (ha1 : ((1282287/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((20049/128000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2007 e2007_ok ha1 ha2 hz1 hz2 hz

-- box ['159543/1024000', '1277193/8192000', '1999/2000', '7997/8000']  interval_lower 170036843/1099511627776
noncomputable def e2008 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270819619602,0,true,159204836800,159204836864⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928203635950,0,false,-186224549888,-186224549824⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270933570454,0,true,159303422528,159303422592⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928089685098,0,false,-186359539648,-186359539584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270733965606,0,true,159130726592,159130726656⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928289289946,0,false,-186123092416,-186123092352⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270869287226,0,true,159247808320,159247808384⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928153968326,0,false,-186283385664,-186283385600⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544322321,0,true,32694016,32694080⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478933231,0,false,-32695040,-32694976⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555251243,0,true,43622592,43622656⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468004309,0,false,-43624384,-43624320⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626045,0,false,-1792,-1728⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626804,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270776788278,0,true,159167778560,159167778624⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928246467274,0,false,-186173814848,-186173814784⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270901433309,0,true,159275619648,159275619712⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928121822243,0,false,-186321467328,-186321467264⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072795707090,0,false,-27045847616,-27045847552⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072834551827,0,false,-27006036224,-27006036160⟩
    { al := (159543/1024000), au := (1277193/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨171307991826,171421942678⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159204836800,159204836864⟩ : DyadicInterval 40),(⟨-186224549888,-186224549824⟩ : DyadicInterval 40),(⟨748723649939,748723669268⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159303422528,159303422592⟩ : DyadicInterval 40),(⟨-186359539648,-186359539584⟩ : DyadicInterval 40),(⟨748705744134,748705763464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159130726592,159130726656⟩ : DyadicInterval 40),(⟨-186123092416,-186123092352⟩ : DyadicInterval 40),(⟨748737101311,748737120641⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159247808320,159247808384⟩ : DyadicInterval 40),(⟨-186283385664,-186283385600⟩ : DyadicInterval 40),(⟨748715846846,748715866175⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32694545,43623467⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32694016,32694080⟩ : DyadicInterval 40),(⟨-32695040,-32694976⟩ : DyadicInterval 40),(⟨762123383091,762123402420⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43622592,43622656⟩ : DyadicInterval 40),(⟨-43624384,-43624320⟩ : DyadicInterval 40),(⟨762123382717,762123402046⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1792,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171265160502,171389805533⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159167778560,159167778624⟩ : DyadicInterval 40),(⟨-186173814848,-186173814784⟩ : DyadicInterval 40),(⟨748730377165,748730396495⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159275619648,159275619712⟩ : DyadicInterval 40),(⟨-186321467328,-186321467264⟩ : DyadicInterval 40),(⟨748710795282,748710814611⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27045847616,-27006036160⟩ : DyadicInterval 40),(⟨775626401696,775646326688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159204836800,159303422592⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186359539648,-186224549824⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2008_ok : ecellOkT e2008 = true := by decide +kernel
theorem e2008_pos {a z : ℝ} (ha1 : ((159543/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1277193/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2008 e2008_ok ha1 ha2 hz1 hz2 hz

-- box ['1277193/8192000', '639021/4096000', '1999/2000', '7997/8000']  interval_lower 42779005/274877906944
noncomputable def e2009 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270933570453,0,true,159303422528,159303422592⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928089685099,0,false,-186359539648,-186359539584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271047521305,0,true,159401999424,159401999488⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927975734247,0,false,-186494545984,-186494545920⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270847859481,0,true,159229269632,159229269696⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928175396071,0,false,-186258002176,-186258002112⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270983195345,0,true,159346353216,159346353280⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928040060207,0,false,-186418332032,-186418331968⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544344852,0,true,32716544,32716608⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478910700,0,false,-32717568,-32717504⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555281285,0,true,43652608,43652672⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467974267,0,false,-43654400,-43654336⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626042,0,false,-1792,-1728⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626803,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270890710638,0,true,159266342976,159266343040⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928132544914,0,false,-186308764608,-186308764544⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271015362793,0,true,159374180544,159374180608⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928007892759,0,false,-186456443648,-186456443584⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072760177057,0,false,-27082263040,-27082262976⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072799049846,0,false,-27042421632,-27042421568⟩
    { al := (1277193/8192000), au := (639021/4096000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨171421942677,171535893529⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159303422528,159303422592⟩ : DyadicInterval 40),(⟨-186359539648,-186359539584⟩ : DyadicInterval 40),(⟨748705744135,748705763464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159401999424,159401999488⟩ : DyadicInterval 40),(⟨-186494545984,-186494545920⟩ : DyadicInterval 40),(⟨748687826223,748687845553⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159229269632,159229269696⟩ : DyadicInterval 40),(⟨-186258002176,-186258002112⟩ : DyadicInterval 40),(⟨748719213557,748719232887⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159346353216,159346353280⟩ : DyadicInterval 40),(⟨-186418332032,-186418331968⟩ : DyadicInterval 40),(⟨748697942497,748697961827⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32717076,43653509⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32716544,32716608⟩ : DyadicInterval 40),(⟨-32717568,-32717504⟩ : DyadicInterval 40),(⟨762123383090,762123402419⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43652608,43652672⟩ : DyadicInterval 40),(⟨-43654400,-43654336⟩ : DyadicInterval 40),(⟨762123382714,762123402043⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1792,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171379082862,171503735017⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159266342976,159266343040⟩ : DyadicInterval 40),(⟨-186308764608,-186308764544⟩ : DyadicInterval 40),(⟨748712480371,748712499701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159374180544,159374180608⟩ : DyadicInterval 40),(⟨-186456443648,-186456443584⟩ : DyadicInterval 40),(⟨748692884138,748692903468⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27082263040,-27042421568⟩ : DyadicInterval 40),(⟨775644594400,775664534400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159303422528,159401999488⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186494545984,-186359539584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2009_ok : ecellOkT e2009 = true := by decide +kernel
theorem e2009_pos {a z : ℝ} (ha1 : ((1277193/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((639021/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2009 e2009_ok ha1 ha2 hz1 hz2 hz

-- box ['159543/1024000', '1277193/8192000', '7997/8000', '3999/4000']  interval_lower 169881599/1099511627776
noncomputable def e2010 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270819619602,0,true,159204836800,159204836864⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928203635950,0,false,-186224549888,-186224549824⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270933570454,0,true,159303422528,159303422592⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928089685098,0,false,-186359539648,-186359539584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270755379104,0,true,159149254592,159149254656⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928267876448,0,false,-186148455872,-186148455808⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270890714969,0,true,159266346688,159266346752⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928132540583,0,false,-186308769728,-186308769664⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533424102,0,true,21796096,21796160⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489831450,0,false,-21796544,-21796480⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544345514,0,true,32717248,32717312⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478910038,0,false,-32718272,-32718208⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626802,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627344,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270787494944,0,true,159177042240,159177042304⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928235760608,0,false,-186186497024,-186186496960⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270912147121,0,true,159284888576,159284888640⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928111108431,0,false,-186334159616,-186334159552⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072792366888,0,false,-27049271040,-27049270976⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072831216280,0,false,-27009454720,-27009454656⟩
    { al := (159543/1024000), au := (1277193/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨171307991826,171421942678⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159204836800,159204836864⟩ : DyadicInterval 40),(⟨-186224549888,-186224549824⟩ : DyadicInterval 40),(⟨748723649939,748723669268⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159303422528,159303422592⟩ : DyadicInterval 40),(⟨-186359539648,-186359539584⟩ : DyadicInterval 40),(⟨748705744134,748705763464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159149254592,159149254656⟩ : DyadicInterval 40),(⟨-186148455872,-186148455808⟩ : DyadicInterval 40),(⟨748733739107,748733758436⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159266346688,159266346752⟩ : DyadicInterval 40),(⟨-186308769728,-186308769664⟩ : DyadicInterval 40),(⟨748712479707,748712499036⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21796326,32717738⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21796096,21796160⟩ : DyadicInterval 40),(⟨-21796544,-21796480⟩ : DyadicInterval 40),(⟨762123383343,762123402672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32717248,32717312⟩ : DyadicInterval 40),(⟨-32718272,-32718208⟩ : DyadicInterval 40),(⟨762123383090,762123402419⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171275867168,171400519345⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159177042240,159177042304⟩ : DyadicInterval 40),(⟨-186186497024,-186186496960⟩ : DyadicInterval 40),(⟨748728695702,748728715032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159284888576,159284888640⟩ : DyadicInterval 40),(⟨-186334159616,-186334159552⟩ : DyadicInterval 40),(⟨748709111442,748709130772⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27049271040,-27009454656⟩ : DyadicInterval 40),(⟨775628110944,775648038400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159204836800,159303422592⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186359539648,-186224549824⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2010_ok : ecellOkT e2010 = true := by decide +kernel
theorem e2010_pos {a z : ℝ} (ha1 : ((159543/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1277193/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2010 e2010_ok ha1 ha2 hz1 hz2 hz

-- box ['1277193/8192000', '639021/4096000', '7997/8000', '3999/4000']  interval_lower 170960401/1099511627776
noncomputable def e2011 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270933570453,0,true,159303422528,159303422592⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928089685099,0,false,-186359539648,-186359539584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271047521305,0,true,159401999424,159401999488⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927975734247,0,false,-186494545984,-186494545920⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270869287224,0,true,159247808320,159247808384⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928153968328,0,false,-186283385664,-186283385600⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271004637332,0,true,159364902272,159364902336⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928018618220,0,false,-186443736128,-186443736064⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533439122,0,true,21811072,21811136⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489816430,0,false,-21811584,-21811520⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544368047,0,true,32739776,32739840⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478887505,0,false,-32740800,-32740736⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626801,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627344,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270901424426,0,true,159275611968,159275612032⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928121831126,0,false,-186321456768,-186321456704⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271026083727,0,true,159383454848,159383454912⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927997171825,0,false,-186469145984,-186469145920⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072756832413,0,false,-27085691136,-27085691072⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072795709860,0,false,-27045844800,-27045844736⟩
    { al := (1277193/8192000), au := (639021/4096000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨171421942677,171535893529⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159303422528,159303422592⟩ : DyadicInterval 40),(⟨-186359539648,-186359539584⟩ : DyadicInterval 40),(⟨748705744135,748705763464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159401999424,159401999488⟩ : DyadicInterval 40),(⟨-186494545984,-186494545920⟩ : DyadicInterval 40),(⟨748687826223,748687845553⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159247808320,159247808384⟩ : DyadicInterval 40),(⟨-186283385664,-186283385600⟩ : DyadicInterval 40),(⟨748715846846,748715866176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159364902272,159364902336⟩ : DyadicInterval 40),(⟨-186443736128,-186443736064⟩ : DyadicInterval 40),(⟨748694570844,748694590173⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21811346,32740271⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21811072,21811136⟩ : DyadicInterval 40),(⟨-21811584,-21811520⟩ : DyadicInterval 40),(⟨762123383375,762123402704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32739776,32739840⟩ : DyadicInterval 40),(⟨-32740800,-32740736⟩ : DyadicInterval 40),(⟨762123383089,762123402418⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171389796650,171514455951⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159275611968,159275612032⟩ : DyadicInterval 40),(⟨-186321456768,-186321456704⟩ : DyadicInterval 40),(⟨748710796659,748710815989⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159383454848,159383454912⟩ : DyadicInterval 40),(⟨-186469145984,-186469145920⟩ : DyadicInterval 40),(⟨748691198036,748691217365⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27085691136,-27045844736⟩ : DyadicInterval 40),(⟨775646305984,775666248448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159303422528,159401999488⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186494545984,-186359539584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2011_ok : ecellOkT e2011 = true := by decide +kernel
theorem e2011_pos {a z : ℝ} (ha1 : ((1277193/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((639021/4096000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2011 e2011_ok ha1 ha2 hz1 hz2 hz

-- box ['639021/4096000', '1278891/8192000', '1999/2000', '7997/8000']  interval_lower 172197839/1099511627776
noncomputable def e2012 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271047521304,0,true,159401999424,159401999488⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927975734248,0,false,-186494545984,-186494545920⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271161472156,0,true,159500567488,159500567552⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927861783396,0,false,-186629568896,-186629568832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270961753357,0,true,159327803904,159327803968⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928061502195,0,false,-186392928576,-186392928512⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271097103465,0,true,159444889344,159444889408⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927926152087,0,false,-186553294976,-186553294912⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544367383,0,true,32739072,32739136⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478888169,0,false,-32740096,-32740032⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555311330,0,true,43682624,43682688⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467944222,0,false,-43684480,-43684416⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626040,0,false,-1792,-1728⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626802,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271004632999,0,true,159364898560,159364898624⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928018622553,0,false,-186443730944,-186443730880⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271129292282,0,true,159472732608,159472732672⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927893963270,0,false,-186591436544,-186591436480⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072724623412,0,false,-27118703936,-27118703872⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072763524257,0,false,-27078832384,-27078832320⟩
    { al := (639021/4096000), au := (1278891/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨171535893528,171649844380⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159401999424,159401999488⟩ : DyadicInterval 40),(⟨-186494545984,-186494545920⟩ : DyadicInterval 40),(⟨748687826223,748687845553⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159500567488,159500567552⟩ : DyadicInterval 40),(⟨-186629568896,-186629568832⟩ : DyadicInterval 40),(⟨748669896203,748669915533⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159327803904,159327803968⟩ : DyadicInterval 40),(⟨-186392928576,-186392928512⟩ : DyadicInterval 40),(⟨748701313711,748701333041⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159444889344,159444889408⟩ : DyadicInterval 40),(⟨-186553294976,-186553294912⟩ : DyadicInterval 40),(⟨748680026021,748680045351⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32739607,43683554⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32739072,32739136⟩ : DyadicInterval 40),(⟨-32740096,-32740032⟩ : DyadicInterval 40),(⟨762123383089,762123402418⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43682624,43682688⟩ : DyadicInterval 40),(⟨-43684480,-43684416⟩ : DyadicInterval 40),(⟨762123382744,762123402073⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1792,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171493005223,171617664506⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159364898560,159364898624⟩ : DyadicInterval 40),(⟨-186443730944,-186443730880⟩ : DyadicInterval 40),(⟨748694571483,748694590812⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159472732608,159472732672⟩ : DyadicInterval 40),(⟨-186591436544,-186591436480⟩ : DyadicInterval 40),(⟨748674960895,748674980225⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27118703936,-27078832320⟩ : DyadicInterval 40),(⟨775662799776,775682754848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159401999424,159500567552⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186629568896,-186494545920⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2012_ok : ecellOkT e2012 = true := by decide +kernel
theorem e2012_pos {a z : ℝ} (ha1 : ((639021/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1278891/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2012 e2012_ok ha1 ha2 hz1 hz2 hz

-- box ['1278891/8192000', '63987/409600', '1999/2000', '7997/8000']  interval_lower 173282161/1099511627776
noncomputable def e2013 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271161472155,0,true,159500567488,159500567552⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927861783397,0,false,-186629568896,-186629568832⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271275423007,0,true,159599126656,159599126720⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927747832545,0,false,-186764608384,-186764608320⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271075647232,0,true,159426329280,159426329344⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927947608320,0,false,-186527871488,-186527871424⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271211011584,0,true,159543416576,159543416640⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927812243968,0,false,-186688274432,-186688274368⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544389916,0,true,32761600,32761664⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478865636,0,false,-32762688,-32762624⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555341376,0,true,43712704,43712768⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467914176,0,false,-43714496,-43714432⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626038,0,false,-1792,-1728⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626800,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271118555359,0,true,159463445248,159463445312⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927904700193,0,false,-186578713856,-186578713792⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271243221766,0,true,159571275840,159571275904⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927780033786,0,false,-186726446016,-186726445952⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072689046159,0,false,-27155170176,-27155170112⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072727975061,0,false,-27115268608,-27115268544⟩
    { al := (1278891/8192000), au := (63987/409600), zl := (1999/2000), zu := (7997/8000),
      A := ⟨171649844379,171763795231⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159500567488,159500567552⟩ : DyadicInterval 40),(⟨-186629568896,-186629568832⟩ : DyadicInterval 40),(⟨748669896203,748669915533⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159599126656,159599126720⟩ : DyadicInterval 40),(⟨-186764608384,-186764608320⟩ : DyadicInterval 40),(⟨748651954110,748651973439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159426329280,159426329344⟩ : DyadicInterval 40),(⟨-186527871488,-186527871424⟩ : DyadicInterval 40),(⟨748683401792,748683421121⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159543416576,159543416640⟩ : DyadicInterval 40),(⟨-186688274432,-186688274368⟩ : DyadicInterval 40),(⟨748662097465,748662116794⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32762140,43713600⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32761600,32761664⟩ : DyadicInterval 40),(⟨-32762688,-32762624⟩ : DyadicInterval 40),(⟨762123383119,762123402448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43712704,43712768⟩ : DyadicInterval 40),(⟨-43714496,-43714432⟩ : DyadicInterval 40),(⟨762123382710,762123402039⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1792,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171606927583,171731593990⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159463445248,159463445312⟩ : DyadicInterval 40),(⟨-186578713856,-186578713792⟩ : DyadicInterval 40),(⟨748676650535,748676669865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159571275840,159571275904⟩ : DyadicInterval 40),(⟨-186726446016,-186726445952⟩ : DyadicInterval 40),(⟨748657025553,748657044882⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27155170176,-27115268544⟩ : DyadicInterval 40),(⟨775681017888,775700987968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159500567488,159599126720⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186764608384,-186629568832⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2013_ok : ecellOkT e2013 = true := by decide +kernel
theorem e2013_pos {a z : ℝ} (ha1 : ((1278891/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((63987/409600 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2013 e2013_ok ha1 ha2 hz1 hz2 hz

-- box ['639021/4096000', '1278891/8192000', '7997/8000', '3999/4000']  interval_lower 86020855/549755813888
noncomputable def e2014 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271047521304,0,true,159401999424,159401999488⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927975734248,0,false,-186494545984,-186494545920⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271161472156,0,true,159500567488,159500567552⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927861783396,0,false,-186629568896,-186629568832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270983195343,0,true,159346353216,159346353280⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928040060209,0,false,-186418332032,-186418331968⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271118559696,0,true,159463449024,159463449088⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927904695856,0,false,-186578718976,-186578718912⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533454144,0,true,21826112,21826176⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489801408,0,false,-21826624,-21826560⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544390579,0,true,32762304,32762368⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478864973,0,false,-32763328,-32763264⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626799,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627343,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271015353907,0,true,159374172864,159374172928⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928007901645,0,false,-186456433088,-186456433024⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271140020340,0,true,159482012224,159482012288⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927883235212,0,false,-186604148864,-186604148800⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072721274322,0,false,-27122136640,-27122136576⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072760179830,0,false,-27082260224,-27082260160⟩
    { al := (639021/4096000), au := (1278891/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨171535893528,171649844380⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159401999424,159401999488⟩ : DyadicInterval 40),(⟨-186494545984,-186494545920⟩ : DyadicInterval 40),(⟨748687826223,748687845553⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159500567488,159500567552⟩ : DyadicInterval 40),(⟨-186629568896,-186629568832⟩ : DyadicInterval 40),(⟨748669896203,748669915533⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159346353216,159346353280⟩ : DyadicInterval 40),(⟨-186418332032,-186418331968⟩ : DyadicInterval 40),(⟨748697942497,748697961827⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159463449024,159463449088⟩ : DyadicInterval 40),(⟨-186578718976,-186578718912⟩ : DyadicInterval 40),(⟨748676649831,748676669160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21826368,32762803⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21826112,21826176⟩ : DyadicInterval 40),(⟨-21826624,-21826560⟩ : DyadicInterval 40),(⟨762123383374,762123402703⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32762304,32762368⟩ : DyadicInterval 40),(⟨-32763328,-32763264⟩ : DyadicInterval 40),(⟨762123383087,762123402416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171503726131,171628392564⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159374172864,159374172928⟩ : DyadicInterval 40),(⟨-186456433088,-186456433024⟩ : DyadicInterval 40),(⟨748692885518,748692904848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159482012224,159482012288⟩ : DyadicInterval 40),(⟨-186604148864,-186604148800⟩ : DyadicInterval 40),(⟨748673272537,748673291867⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27122136640,-27082260160⟩ : DyadicInterval 40),(⟨775664513696,775684471200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159401999424,159500567552⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186629568896,-186494545920⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2014_ok : ecellOkT e2014 = true := by decide +kernel
theorem e2014_pos {a z : ℝ} (ha1 : ((639021/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1278891/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2014 e2014_ok ha1 ha2 hz1 hz2 hz

-- box ['1278891/8192000', '63987/409600', '7997/8000', '3999/4000']  interval_lower 86562925/549755813888
noncomputable def e2015 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271161472155,0,true,159500567488,159500567552⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927861783397,0,false,-186629568896,-186629568832⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271275423007,0,true,159599126656,159599126720⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927747832545,0,false,-186764608384,-186764608320⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271097103463,0,true,159444889280,159444889344⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927926152089,0,false,-186553294976,-186553294912⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271232482059,0,true,159561986880,159561986944⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927790773493,0,false,-186713718464,-186713718400⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533469166,0,true,21841152,21841216⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489786386,0,false,-21841664,-21841600⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544413114,0,true,32784832,32784896⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478842438,0,false,-32785856,-32785792⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626798,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627343,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271129283390,0,true,159472724928,159472724992⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927893972162,0,false,-186591425984,-186591425920⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271253956942,0,true,159580560768,159580560832⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927769298610,0,false,-186739168384,-186739168320⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072685692622,0,false,-27158607552,-27158607488⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072724626189,0,false,-27118701056,-27118700992⟩
    { al := (1278891/8192000), au := (63987/409600), zl := (7997/8000), zu := (3999/4000),
      A := ⟨171649844379,171763795231⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159500567488,159500567552⟩ : DyadicInterval 40),(⟨-186629568896,-186629568832⟩ : DyadicInterval 40),(⟨748669896203,748669915533⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159599126656,159599126720⟩ : DyadicInterval 40),(⟨-186764608384,-186764608320⟩ : DyadicInterval 40),(⟨748651954110,748651973439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159444889280,159444889344⟩ : DyadicInterval 40),(⟨-186553294976,-186553294912⟩ : DyadicInterval 40),(⟨748680026059,748680045388⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159561986880,159561986944⟩ : DyadicInterval 40),(⟨-186713718464,-186713718400⟩ : DyadicInterval 40),(⟨748658716785,748658736114⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21841390,32785338⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21841152,21841216⟩ : DyadicInterval 40),(⟨-21841664,-21841600⟩ : DyadicInterval 40),(⟨762123383374,762123402703⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32784832,32784896⟩ : DyadicInterval 40),(⟨-32785856,-32785792⟩ : DyadicInterval 40),(⟨762123383086,762123402415⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171617655614,171742329166⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159472724928,159472724992⟩ : DyadicInterval 40),(⟨-186591425984,-186591425920⟩ : DyadicInterval 40),(⟨748674962278,748674981608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159580560768,159580560832⟩ : DyadicInterval 40),(⟨-186739168384,-186739168320⟩ : DyadicInterval 40),(⟨748655334963,748655354292⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27158607552,-27118700992⟩ : DyadicInterval 40),(⟨775682734112,775702706656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159500567488,159599126720⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186764608384,-186629568832⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2015_ok : ecellOkT e2015 = true := by decide +kernel
theorem e2015_pos {a z : ℝ} (ha1 : ((1278891/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((63987/409600 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2015 e2015_ok ha1 ha2 hz1 hz2 hz

-- box ['159543/1024000', '1277193/8192000', '3999/4000', '7999/8000']  interval_lower 42431651/274877906944
noncomputable def e2016 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270819619602,0,true,159204836800,159204836864⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928203635950,0,false,-186224549888,-186224549824⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270933570454,0,true,159303422528,159303422592⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928089685098,0,false,-186359539648,-186359539584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270776792604,0,true,159167782336,159167782400⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928246462948,0,false,-186173819968,-186173819904⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270912142712,0,true,159284884800,159284884864⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928111112840,0,false,-186334154432,-186334154368⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522525835,0,true,10897984,10898048⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500729717,0,false,-10898176,-10898112⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533439736,0,true,21811712,21811776⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489815816,0,false,-21812224,-21812160⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627343,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627668,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270798201636,0,true,159186305856,159186305920⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928225053916,0,false,-186199179328,-186199179264⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270922860958,0,true,159294157504,159294157568⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928100394594,0,false,-186346852160,-186346852096⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072789026469,0,false,-27052694656,-27052694592⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072827880517,0,false,-27012873472,-27012873408⟩
    { al := (159543/1024000), au := (1277193/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨171307991826,171421942678⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159204836800,159204836864⟩ : DyadicInterval 40),(⟨-186224549888,-186224549824⟩ : DyadicInterval 40),(⟨748723649939,748723669268⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159303422528,159303422592⟩ : DyadicInterval 40),(⟨-186359539648,-186359539584⟩ : DyadicInterval 40),(⟨748705744134,748705763464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159167782336,159167782400⟩ : DyadicInterval 40),(⟨-186173819968,-186173819904⟩ : DyadicInterval 40),(⟨748730376465,748730395795⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159284884800,159284884864⟩ : DyadicInterval 40),(⟨-186334154432,-186334154368⟩ : DyadicInterval 40),(⟨748709112129,748709131459⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10898059,21811960⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10897984,10898048⟩ : DyadicInterval 40),(⟨-10898176,-10898112⟩ : DyadicInterval 40),(⟨762123383539,762123402868⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21811712,21811776⟩ : DyadicInterval 40),(⟨-21812224,-21812160⟩ : DyadicInterval 40),(⟨762123383375,762123402704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171286573860,171411233182⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159186305856,159186305920⟩ : DyadicInterval 40),(⟨-186199179328,-186199179264⟩ : DyadicInterval 40),(⟨748727014113,748727033442⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159294157504,159294157568⟩ : DyadicInterval 40),(⟨-186346852160,-186346852096⟩ : DyadicInterval 40),(⟨748707427493,748707446822⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27052694656,-27012873408⟩ : DyadicInterval 40),(⟨775629820320,775649750208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159204836800,159303422592⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186359539648,-186224549824⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2016_ok : ecellOkT e2016 = true := by decide +kernel
theorem e2016_pos {a z : ℝ} (ha1 : ((159543/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1277193/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2016 e2016_ok ha1 ha2 hz1 hz2 hz

-- box ['1277193/8192000', '639021/4096000', '3999/4000', '7999/8000']  interval_lower 170804591/1099511627776
noncomputable def e2017 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270933570453,0,true,159303422528,159303422592⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928089685099,0,false,-186359539648,-186359539584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271047521305,0,true,159401999424,159401999488⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927975734247,0,false,-186494545984,-186494545920⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270890714967,0,true,159266346688,159266346752⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928132540585,0,false,-186308769728,-186308769664⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271026079319,0,true,159383451008,159383451072⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927997176233,0,false,-186469140736,-186469140672⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522533345,0,true,10905472,10905536⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500722207,0,false,-10905664,-10905600⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533454758,0,true,21826752,21826816⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489800794,0,false,-21827200,-21827136⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627342,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627668,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270912138238,0,true,159284880896,159284880960⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928111117314,0,false,-186334149120,-186334149056⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271036804687,0,true,159392729024,159392729088⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927986450865,0,false,-186481848448,-186481848384⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072753487551,0,false,-27089119424,-27089119360⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072792369658,0,false,-27049268160,-27049268096⟩
    { al := (1277193/8192000), au := (639021/4096000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨171421942677,171535893529⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159303422528,159303422592⟩ : DyadicInterval 40),(⟨-186359539648,-186359539584⟩ : DyadicInterval 40),(⟨748705744135,748705763464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159401999424,159401999488⟩ : DyadicInterval 40),(⟨-186494545984,-186494545920⟩ : DyadicInterval 40),(⟨748687826223,748687845553⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159266346688,159266346752⟩ : DyadicInterval 40),(⟨-186308769728,-186308769664⟩ : DyadicInterval 40),(⟨748712479707,748712499037⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159383451008,159383451072⟩ : DyadicInterval 40),(⟨-186469140736,-186469140672⟩ : DyadicInterval 40),(⟨748691198734,748691218064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10905569,21826982⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10905472,10905536⟩ : DyadicInterval 40),(⟨-10905664,-10905600⟩ : DyadicInterval 40),(⟨762123383539,762123402868⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21826752,21826816⟩ : DyadicInterval 40),(⟨-21827200,-21827136⟩ : DyadicInterval 40),(⟨762123383342,762123402671⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171400510462,171525176911⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159284880896,159284880960⟩ : DyadicInterval 40),(⟨-186334149120,-186334149056⟩ : DyadicInterval 40),(⟨748709112847,748709132176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159392729024,159392729088⟩ : DyadicInterval 40),(⟨-186481848448,-186481848384⟩ : DyadicInterval 40),(⟨748689511844,748689531173⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27089119424,-27049268096⟩ : DyadicInterval 40),(⟨775648017664,775667962592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159303422528,159401999488⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186494545984,-186359539584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2017_ok : ecellOkT e2017 = true := by decide +kernel
theorem e2017_pos {a z : ℝ} (ha1 : ((1277193/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((639021/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2017 e2017_ok ha1 ha2 hz1 hz2 hz

-- box ['159543/1024000', '1277193/8192000', '7999/8000', '1']  interval_lower 84785649/549755813888
noncomputable def e2018 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270819619602,0,true,159204836800,159204836864⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928203635950,0,false,-186224549888,-186224549824⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270933570454,0,true,159303422528,159303422592⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928089685098,0,false,-186359539648,-186359539584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270798206102,0,true,159186309696,159186309760⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928225049450,0,false,-186199184640,-186199184576⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522533909,0,true,10906048,10906112⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500721643,0,false,-10906240,-10906176⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627667,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1270808908347,0,true,159195569408,159195569472⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨928214347205,0,false,-186211861888,-186211861824⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1270933574817,0,true,159303426304,159303426368⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨928089680735,0,false,-186359544832,-186359544768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1072785685835,0,false,-27056118464,-27056118400⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1072824544539,0,false,-27016292416,-27016292352⟩
    { al := (159543/1024000), au := (1277193/8192000), zl := (7999/8000), zu := 1,
      A := ⟨171307991826,171421942678⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159204836800,159204836864⟩ : DyadicInterval 40),(⟨-186224549888,-186224549824⟩ : DyadicInterval 40),(⟨748723649939,748723669268⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159303422528,159303422592⟩ : DyadicInterval 40),(⟨-186359539648,-186359539584⟩ : DyadicInterval 40),(⟨748705744134,748705763464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159186309696,159186309760⟩ : DyadicInterval 40),(⟨-186199184640,-186199184576⟩ : DyadicInterval 40),(⟨748727013434,748727032764⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159303422528,159303422592⟩ : DyadicInterval 40),(⟨-186359539648,-186359539584⟩ : DyadicInterval 40),(⟨748705744134,748705763464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10906133⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10906048,10906112⟩ : DyadicInterval 40),(⟨-10906240,-10906176⟩ : DyadicInterval 40),(⟨762123383539,762123402868⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨171297280571,171421947041⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159195569408,159195569472⟩ : DyadicInterval 40),(⟨-186211861888,-186211861824⟩ : DyadicInterval 40),(⟨748725332451,748725351780⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159303426304,159303426368⟩ : DyadicInterval 40),(⟨-186359544832,-186359544768⟩ : DyadicInterval 40),(⟨748705743454,748705762784⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27056118464,-27016292352⟩ : DyadicInterval 40),(⟨775631529792,775651462112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨159204836800,159303422592⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186359539648,-186224549824⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2018_ok : ecellOkT e2018 = true := by decide +kernel
theorem e2018_pos {a z : ℝ} (ha1 : ((159543/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1277193/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2018 e2018_ok ha1 ha2 hz1 hz2 hz

-- box ['1277193/8192000', '639021/4096000', '7999/8000', '1']  interval_lower 10665585/68719476736
noncomputable def e2019 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270933570453,0,true,159303422528,159303422592⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928089685099,0,false,-186359539648,-186359539584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271047521305,0,true,159401999424,159401999488⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927975734247,0,false,-186494545984,-186494545920⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270912142710,0,true,159284884800,159284884864⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928111112842,0,false,-186334154432,-186334154368⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522541420,0,true,10913536,10913600⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500714132,0,false,-10913728,-10913664⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627667,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1270922852075,0,true,159294149824,159294149888⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨928100403477,0,false,-186346841600,-186346841536⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1271047525668,0,true,159402003200,159402003264⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨927975729884,0,false,-186494551168,-186494551104⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1072750142474,0,false,-27092547904,-27092547840⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1072789029240,0,false,-27052691776,-27052691712⟩
    { al := (1277193/8192000), au := (639021/4096000), zl := (7999/8000), zu := 1,
      A := ⟨171421942677,171535893529⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159303422528,159303422592⟩ : DyadicInterval 40),(⟨-186359539648,-186359539584⟩ : DyadicInterval 40),(⟨748705744135,748705763464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159401999424,159401999488⟩ : DyadicInterval 40),(⟨-186494545984,-186494545920⟩ : DyadicInterval 40),(⟨748687826223,748687845553⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159284884800,159284884864⟩ : DyadicInterval 40),(⟨-186334154432,-186334154368⟩ : DyadicInterval 40),(⟨748709112130,748709131459⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159401999424,159401999488⟩ : DyadicInterval 40),(⟨-186494545984,-186494545920⟩ : DyadicInterval 40),(⟨748687826223,748687845553⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10913644⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10913536,10913600⟩ : DyadicInterval 40),(⟨-10913728,-10913664⟩ : DyadicInterval 40),(⟨762123383539,762123402868⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨171411224299,171535897892⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159294149824,159294149888⟩ : DyadicInterval 40),(⟨-186346841600,-186346841536⟩ : DyadicInterval 40),(⟨748707428871,748707448200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159402003200,159402003264⟩ : DyadicInterval 40),(⟨-186494551168,-186494551104⟩ : DyadicInterval 40),(⟨748687825542,748687844871⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27092547904,-27052691712⟩ : DyadicInterval 40),(⟨775649729472,775669676832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨159303422528,159401999488⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186494545984,-186359539584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2019_ok : ecellOkT e2019 = true := by decide +kernel
theorem e2019_pos {a z : ℝ} (ha1 : ((1277193/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((639021/4096000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2019 e2019_ok ha1 ha2 hz1 hz2 hz

-- box ['639021/4096000', '1278891/8192000', '3999/4000', '7999/8000']  interval_lower 85942875/549755813888
noncomputable def e2020 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271047521304,0,true,159401999424,159401999488⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927975734248,0,false,-186494545984,-186494545920⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271161472156,0,true,159500567488,159500567552⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927861783396,0,false,-186629568896,-186629568832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271004637330,0,true,159364902272,159364902336⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928018618222,0,false,-186443736064,-186443736000⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271140015926,0,true,159482008384,159482008448⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927883239626,0,false,-186604143680,-186604143616⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522540856,0,true,10913024,10913088⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500714696,0,false,-10913152,-10913088⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533469780,0,true,21841728,21841792⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489785772,0,false,-21842240,-21842176⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627342,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627668,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271026074844,0,true,159383447104,159383447168⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927997180708,0,false,-186469135424,-186469135360⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271150748415,0,true,159491291776,159491291840⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927872507137,0,false,-186616861376,-186616861312⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072717925017,0,false,-27125569600,-27125569536⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072756835185,0,false,-27085688256,-27085688192⟩
    { al := (639021/4096000), au := (1278891/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨171535893528,171649844380⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159401999424,159401999488⟩ : DyadicInterval 40),(⟨-186494545984,-186494545920⟩ : DyadicInterval 40),(⟨748687826223,748687845553⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159500567488,159500567552⟩ : DyadicInterval 40),(⟨-186629568896,-186629568832⟩ : DyadicInterval 40),(⟨748669896203,748669915533⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159364902272,159364902336⟩ : DyadicInterval 40),(⟨-186443736064,-186443736000⟩ : DyadicInterval 40),(⟨748694570817,748694590146⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159482008384,159482008448⟩ : DyadicInterval 40),(⟨-186604143680,-186604143616⟩ : DyadicInterval 40),(⟨748673273264,748673292593⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10913080,21842004⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10913024,10913088⟩ : DyadicInterval 40),(⟨-10913152,-10913088⟩ : DyadicInterval 40),(⟨762123383507,762123402836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21841728,21841792⟩ : DyadicInterval 40),(⟨-21842240,-21842176⟩ : DyadicInterval 40),(⟨762123383374,762123402703⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171514447068,171639120639⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159383447104,159383447168⟩ : DyadicInterval 40),(⟨-186469135424,-186469135360⟩ : DyadicInterval 40),(⟨748691199453,748691218782⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159491291776,159491291840⟩ : DyadicInterval 40),(⟨-186616861376,-186616861312⟩ : DyadicInterval 40),(⟨748671584079,748671603409⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27125569600,-27085688192⟩ : DyadicInterval 40),(⟨775666227712,775686187680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159401999424,159500567552⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186629568896,-186494545920⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2020_ok : ecellOkT e2020 = true := by decide +kernel
theorem e2020_pos {a z : ℝ} (ha1 : ((639021/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1278891/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2020 e2020_ok ha1 ha2 hz1 hz2 hz

-- box ['1278891/8192000', '63987/409600', '3999/4000', '7999/8000']  interval_lower 172969685/1099511627776
noncomputable def e2021 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271161472155,0,true,159500567488,159500567552⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927861783397,0,false,-186629568896,-186629568832⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271275423007,0,true,159599126656,159599126720⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927747832545,0,false,-186764608384,-186764608320⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271118559693,0,true,159463449024,159463449088⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927904695859,0,false,-186578718976,-186578718912⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271253952533,0,true,159580556928,159580556992⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927769303019,0,false,-186739163136,-186739163072⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522548367,0,true,10920512,10920576⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500707185,0,false,-10920704,-10920640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533484803,0,true,21856768,21856832⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489770749,0,false,-21857280,-21857216⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627341,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627668,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271140011451,0,true,159482004544,159482004608⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927883244101,0,false,-186604138368,-186604138304⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271264692143,0,true,159589845632,159589845696⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927758563409,0,false,-186751890880,-186751890816⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072682338867,0,false,-27162045184,-27162045120⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072721277098,0,false,-27122133824,-27122133760⟩
    { al := (1278891/8192000), au := (63987/409600), zl := (3999/4000), zu := (7999/8000),
      A := ⟨171649844379,171763795231⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159500567488,159500567552⟩ : DyadicInterval 40),(⟨-186629568896,-186629568832⟩ : DyadicInterval 40),(⟨748669896203,748669915533⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159599126656,159599126720⟩ : DyadicInterval 40),(⟨-186764608384,-186764608320⟩ : DyadicInterval 40),(⟨748651954110,748651973439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159463449024,159463449088⟩ : DyadicInterval 40),(⟨-186578718976,-186578718912⟩ : DyadicInterval 40),(⟨748676649831,748676669161⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159580556928,159580556992⟩ : DyadicInterval 40),(⟨-186739163136,-186739163072⟩ : DyadicInterval 40),(⟨748655335663,748655354993⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10920591,21857027⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10920512,10920576⟩ : DyadicInterval 40),(⟨-10920704,-10920640⟩ : DyadicInterval 40),(⟨762123383539,762123402868⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21856768,21856832⟩ : DyadicInterval 40),(⟨-21857280,-21857216⟩ : DyadicInterval 40),(⟨762123383373,762123402702⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171628383675,171753064367⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159482004544,159482004608⟩ : DyadicInterval 40),(⟨-186604138368,-186604138304⟩ : DyadicInterval 40),(⟨748673273947,748673293276⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159589845632,159589845696⟩ : DyadicInterval 40),(⟨-186751890880,-186751890816⟩ : DyadicInterval 40),(⟨748653644245,748653663575⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27162045184,-27122133760⟩ : DyadicInterval 40),(⟨775684450496,775704425472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159500567488,159599126720⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186764608384,-186629568832⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2021_ok : ecellOkT e2021 = true := by decide +kernel
theorem e2021_pos {a z : ℝ} (ha1 : ((1278891/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((63987/409600 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2021 e2021_ok ha1 ha2 hz1 hz2 hz

-- box ['639021/4096000', '1278891/8192000', '7999/8000', '1']  interval_lower 171729649/1099511627776
noncomputable def e2022 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271047521304,0,true,159401999424,159401999488⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927975734248,0,false,-186494545984,-186494545920⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271161472156,0,true,159500567488,159500567552⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927861783396,0,false,-186629568896,-186629568832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271026079317,0,true,159383451008,159383451072⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927997176235,0,false,-186469140736,-186469140672⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522548932,0,true,10921088,10921152⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500706620,0,false,-10921216,-10921152⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627667,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1271036795801,0,true,159392721344,159392721408⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨927986459751,0,false,-186481837952,-186481837888⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1271161476521,0,true,159500571264,159500571328⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨927861779031,0,false,-186629574080,-186629574016⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1072714575493,0,false,-27129002816,-27129002752⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1072753490325,0,false,-27089116544,-27089116480⟩
    { al := (639021/4096000), au := (1278891/8192000), zl := (7999/8000), zu := 1,
      A := ⟨171535893528,171649844380⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159401999424,159401999488⟩ : DyadicInterval 40),(⟨-186494545984,-186494545920⟩ : DyadicInterval 40),(⟨748687826223,748687845553⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159500567488,159500567552⟩ : DyadicInterval 40),(⟨-186629568896,-186629568832⟩ : DyadicInterval 40),(⟨748669896203,748669915533⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159383451008,159383451072⟩ : DyadicInterval 40),(⟨-186469140736,-186469140672⟩ : DyadicInterval 40),(⟨748691198735,748691218064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159500567488,159500567552⟩ : DyadicInterval 40),(⟨-186629568896,-186629568832⟩ : DyadicInterval 40),(⟨748669896203,748669915533⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10921156⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10921088,10921152⟩ : DyadicInterval 40),(⟨-10921216,-10921152⟩ : DyadicInterval 40),(⟨762123383507,762123402836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨171525168025,171649848745⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159392721344,159392721408⟩ : DyadicInterval 40),(⟨-186481837952,-186481837888⟩ : DyadicInterval 40),(⟨748689513251,748689532580⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159500571264,159500571328⟩ : DyadicInterval 40),(⟨-186629574080,-186629574016⟩ : DyadicInterval 40),(⟨748669895520,748669914850⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27129002816,-27089116480⟩ : DyadicInterval 40),(⟨775667941856,775687904288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨159401999424,159500567552⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186629568896,-186494545920⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2022_ok : ecellOkT e2022 = true := by decide +kernel
theorem e2022_pos {a z : ℝ} (ha1 : ((639021/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1278891/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2022 e2022_ok ha1 ha2 hz1 hz2 hz

-- box ['1278891/8192000', '63987/409600', '7999/8000', '1']  interval_lower 172813189/1099511627776
noncomputable def e2023 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271161472155,0,true,159500567488,159500567552⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927861783397,0,false,-186629568896,-186629568832⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271275423007,0,true,159599126656,159599126720⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927747832545,0,false,-186764608384,-186764608320⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271140015924,0,true,159482008384,159482008448⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927883239628,0,false,-186604143616,-186604143552⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522556443,0,true,10928576,10928640⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500699109,0,false,-10928768,-10928704⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627667,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1271150739529,0,true,159491284032,159491284096⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨927872516023,0,false,-186616850816,-186616850752⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1271275427367,0,true,159599130432,159599130496⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨927747828185,0,false,-186764613568,-186764613504⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1072678984896,0,false,-27165483072,-27165483008⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1072717927793,0,false,-27125566720,-27125566656⟩
    { al := (1278891/8192000), au := (63987/409600), zl := (7999/8000), zu := 1,
      A := ⟨171649844379,171763795231⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159500567488,159500567552⟩ : DyadicInterval 40),(⟨-186629568896,-186629568832⟩ : DyadicInterval 40),(⟨748669896203,748669915533⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159599126656,159599126720⟩ : DyadicInterval 40),(⟨-186764608384,-186764608320⟩ : DyadicInterval 40),(⟨748651954110,748651973439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159482008384,159482008448⟩ : DyadicInterval 40),(⟨-186604143616,-186604143552⟩ : DyadicInterval 40),(⟨748673273237,748673292567⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159599126656,159599126720⟩ : DyadicInterval 40),(⟨-186764608384,-186764608320⟩ : DyadicInterval 40),(⟨748651954110,748651973439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10928667⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10928576,10928640⟩ : DyadicInterval 40),(⟨-10928768,-10928704⟩ : DyadicInterval 40),(⟨762123383539,762123402868⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨171639111753,171763799591⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159491284032,159491284096⟩ : DyadicInterval 40),(⟨-186616850816,-186616850752⟩ : DyadicInterval 40),(⟨748671585499,748671604828⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159599130432,159599130496⟩ : DyadicInterval 40),(⟨-186764613568,-186764613504⟩ : DyadicInterval 40),(⟨748651953428,748651972757⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27165483072,-27125566656⟩ : DyadicInterval 40),(⟨775686166944,775706144416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨159500567488,159599126720⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186764608384,-186629568832⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2023_ok : ecellOkT e2023 = true := by decide +kernel
theorem e2023_pos {a z : ℝ} (ha1 : ((1278891/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((63987/409600 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2023 e2023_ok ha1 ha2 hz1 hz2 hz

-- box ['63987/409600', '1280589/8192000', '1999/2000', '7997/8000']  interval_lower 87184729/549755813888
noncomputable def e2024 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271275423006,0,true,159599126656,159599126720⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927747832546,0,false,-186764608384,-186764608320⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271389373858,0,true,159697677056,159697677120⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927633881694,0,false,-186899664448,-186899664384⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271189541108,0,true,159524845888,159524845952⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927833714444,0,false,-186662830976,-186662830912⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271324919704,0,true,159641934976,159641935040⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927698335848,0,false,-186823270464,-186823270400⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544412451,0,true,32784128,32784192⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478843101,0,false,-32785216,-32785152⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555371425,0,true,43742720,43742784⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467884127,0,false,-43744576,-43744512⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626035,0,false,-1792,-1728⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626799,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271232477719,0,true,159561983168,159561983232⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927790777833,0,false,-186713713344,-186713713280⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271357151254,0,true,159669810240,159669810304⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927666104298,0,false,-186861472128,-186861472064⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072653445294,0,false,-27191661824,-27191661760⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072692402258,0,false,-27151730176,-27151730112⟩
    { al := (63987/409600), au := (1280589/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨171763795230,171877746082⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159599126656,159599126720⟩ : DyadicInterval 40),(⟨-186764608384,-186764608320⟩ : DyadicInterval 40),(⟨748651954110,748651973440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159697677056,159697677120⟩ : DyadicInterval 40),(⟨-186899664448,-186899664384⟩ : DyadicInterval 40),(⟨748633999869,748634019199⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159524845888,159524845952⟩ : DyadicInterval 40),(⟨-186662830976,-186662830912⟩ : DyadicInterval 40),(⟨748665477751,748665497080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159641934976,159641935040⟩ : DyadicInterval 40),(⟨-186823270464,-186823270400⟩ : DyadicInterval 40),(⟨748644156816,748644176146⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32784675,43743649⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32784128,32784192⟩ : DyadicInterval 40),(⟨-32785216,-32785152⟩ : DyadicInterval 40),(⟨762123383118,762123402447⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43742720,43742784⟩ : DyadicInterval 40),(⟨-43744576,-43744512⟩ : DyadicInterval 40),(⟨762123382739,762123402068⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1792,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171720849943,171845523478⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159561983168,159561983232⟩ : DyadicInterval 40),(⟨-186713713344,-186713713280⟩ : DyadicInterval 40),(⟨748658717454,748658736783⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159669810240,159669810304⟩ : DyadicInterval 40),(⟨-186861472128,-186861472064⟩ : DyadicInterval 40),(⟨748639078135,748639097464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27191661824,-27151730112⟩ : DyadicInterval 40),(⟨775699248672,775719233792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159599126656,159697677120⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186899664448,-186764608320⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2024_ok : ecellOkT e2024 = true := by decide +kernel
theorem e2024_pos {a z : ℝ} (ha1 : ((63987/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1280589/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2024 e2024_ok ha1 ha2 hz1 hz2 hz

-- box ['1280589/8192000', '640719/4096000', '1999/2000', '7997/8000']  interval_lower 21932389/137438953472
noncomputable def e2025 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271389373857,0,true,159697677056,159697677120⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927633881695,0,false,-186899664448,-186899664384⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271503324709,0,true,159796218560,159796218624⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927519930843,0,false,-187034737088,-187034737024⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271303434983,0,true,159623353664,159623353728⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927719820569,0,false,-186797806976,-186797806912⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271438827823,0,true,159740444544,159740444608⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927584427729,0,false,-186958283136,-186958283072⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544434987,0,true,32806720,32806784⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478820565,0,false,-32807744,-32807680⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555401476,0,true,43772800,43772864⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467854076,0,false,-43774592,-43774528⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626033,0,false,-1792,-1728⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626798,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271346400085,0,true,159660512192,159660512256⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927676855467,0,false,-186848729408,-186848729344⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271471080735,0,true,159768335808,159768335872⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927552174817,0,false,-186996514752,-186996514688⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072617820821,0,false,-27228178944,-27228178880⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072656805846,0,false,-27188217152,-27188217088⟩
    { al := (1280589/8192000), au := (640719/4096000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨171877746081,171991696933⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159697677056,159697677120⟩ : DyadicInterval 40),(⟨-186899664448,-186899664384⟩ : DyadicInterval 40),(⟨748633999869,748634019199⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159796218560,159796218624⟩ : DyadicInterval 40),(⟨-187034737088,-187034737024⟩ : DyadicInterval 40),(⟨748616033553,748616052883⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159623353664,159623353728⟩ : DyadicInterval 40),(⟨-186797806976,-186797806912⟩ : DyadicInterval 40),(⟨748647541597,748647560926⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159740444544,159740444608⟩ : DyadicInterval 40),(⟨-186958283136,-186958283072⟩ : DyadicInterval 40),(⟨748626204101,748626223431⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32807211,43773700⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32806720,32806784⟩ : DyadicInterval 40),(⟨-32807744,-32807680⟩ : DyadicInterval 40),(⟨762123383085,762123402414⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43772800,43772864⟩ : DyadicInterval 40),(⟨-43774592,-43774528⟩ : DyadicInterval 40),(⟨762123382705,762123402034⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1792,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171834772309,171959452959⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159660512192,159660512256⟩ : DyadicInterval 40),(⟨-186848729408,-186848729344⟩ : DyadicInterval 40),(⟨748640772310,748640791639⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159768335808,159768335872⟩ : DyadicInterval 40),(⟨-186996514752,-186996514688⟩ : DyadicInterval 40),(⟨748621118589,748621137918⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27228178944,-27188217088⟩ : DyadicInterval 40),(⟨775717492160,775737492352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159697677056,159796218624⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187034737088,-186899664384⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2025_ok : ecellOkT e2025 = true := by decide +kernel
theorem e2025_pos {a z : ℝ} (ha1 : ((1280589/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((640719/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2025 e2025_ok ha1 ha2 hz1 hz2 hz

-- box ['63987/409600', '1280589/8192000', '7997/8000', '3999/4000']  interval_lower 87106239/549755813888
noncomputable def e2026 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271275423006,0,true,159599126656,159599126720⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927747832546,0,false,-186764608384,-186764608320⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271389373858,0,true,159697677056,159697677120⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927633881694,0,false,-186899664448,-186899664384⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271211011582,0,true,159543416576,159543416640⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927812243970,0,false,-186688274432,-186688274368⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271346404422,0,true,159660515968,159660516032⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927676851130,0,false,-186848734528,-186848734464⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533484190,0,true,21856192,21856256⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489771362,0,false,-21856640,-21856576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544435651,0,true,32807360,32807424⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478819901,0,false,-32808384,-32808320⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626797,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627342,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271243212874,0,true,159571268160,159571268224⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927780042678,0,false,-186726435520,-186726435456⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271367893552,0,true,159679100480,159679100544⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927655362000,0,false,-186874204416,-186874204352⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072650087306,0,false,-27195103936,-27195103872⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072689048938,0,false,-27155167296,-27155167232⟩
    { al := (63987/409600), au := (1280589/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨171763795230,171877746082⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159599126656,159599126720⟩ : DyadicInterval 40),(⟨-186764608384,-186764608320⟩ : DyadicInterval 40),(⟨748651954110,748651973440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159697677056,159697677120⟩ : DyadicInterval 40),(⟨-186899664448,-186899664384⟩ : DyadicInterval 40),(⟨748633999869,748634019199⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159543416576,159543416640⟩ : DyadicInterval 40),(⟨-186688274432,-186688274368⟩ : DyadicInterval 40),(⟨748662097465,748662116795⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159660515968,159660516032⟩ : DyadicInterval 40),(⟨-186848734528,-186848734464⟩ : DyadicInterval 40),(⟨748640771603,748640790933⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21856414,32807875⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21856192,21856256⟩ : DyadicInterval 40),(⟨-21856640,-21856576⟩ : DyadicInterval 40),(⟨762123383341,762123402670⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32807360,32807424⟩ : DyadicInterval 40),(⟨-32808384,-32808320⟩ : DyadicInterval 40),(⟨762123383085,762123402414⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171731585098,171856265776⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159571268160,159571268224⟩ : DyadicInterval 40),(⟨-186726435520,-186726435456⟩ : DyadicInterval 40),(⟨748657026964,748657046294⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159679100480,159679100544⟩ : DyadicInterval 40),(⟨-186874204416,-186874204352⟩ : DyadicInterval 40),(⟨748637385256,748637404585⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27195103936,-27155167232⟩ : DyadicInterval 40),(⟨775700967232,775720954848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159599126656,159697677120⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186899664448,-186764608320⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2026_ok : ecellOkT e2026 = true := by decide +kernel
theorem e2026_pos {a z : ℝ} (ha1 : ((63987/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1280589/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2026 e2026_ok ha1 ha2 hz1 hz2 hz

-- box ['1280589/8192000', '640719/4096000', '7997/8000', '3999/4000']  interval_lower 175302195/1099511627776
noncomputable def e2027 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271389373857,0,true,159697677056,159697677120⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927633881695,0,false,-186899664448,-186899664384⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271503324709,0,true,159796218560,159796218624⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927519930843,0,false,-187034737088,-187034737024⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271324919702,0,true,159641934976,159641935040⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927698335850,0,false,-186823270464,-186823270400⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271460326785,0,true,159759036224,159759036288⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927562928767,0,false,-186983767168,-186983767104⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533499214,0,true,21871168,21871232⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489756338,0,false,-21871680,-21871616⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544458190,0,true,32829888,32829952⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478797362,0,false,-32830912,-32830848⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626795,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627341,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271357142360,0,true,159669802560,159669802624⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927666113192,0,false,-186861461568,-186861461504⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271481830159,0,true,159777631360,159777631424⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927541425393,0,false,-187009257088,-187009257024⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072614458377,0,false,-27231625664,-27231625600⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072653448075,0,false,-27191659008,-27191658944⟩
    { al := (1280589/8192000), au := (640719/4096000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨171877746081,171991696933⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159697677056,159697677120⟩ : DyadicInterval 40),(⟨-186899664448,-186899664384⟩ : DyadicInterval 40),(⟨748633999869,748634019199⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159796218560,159796218624⟩ : DyadicInterval 40),(⟨-187034737088,-187034737024⟩ : DyadicInterval 40),(⟨748616033553,748616052883⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159641934976,159641935040⟩ : DyadicInterval 40),(⟨-186823270464,-186823270400⟩ : DyadicInterval 40),(⟨748644156816,748644176146⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159759036224,159759036288⟩ : DyadicInterval 40),(⟨-186983767168,-186983767104⟩ : DyadicInterval 40),(⟨748622814322,748622833652⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21871438,32830414⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21871168,21871232⟩ : DyadicInterval 40),(⟨-21871680,-21871616⟩ : DyadicInterval 40),(⟨762123383372,762123402701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32829888,32829952⟩ : DyadicInterval 40),(⟨-32830912,-32830848⟩ : DyadicInterval 40),(⟨762123383083,762123402412⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171845514584,171970202383⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159669802560,159669802624⟩ : DyadicInterval 40),(⟨-186861461568,-186861461504⟩ : DyadicInterval 40),(⟨748639079522,748639098851⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159777631360,159777631424⟩ : DyadicInterval 40),(⟨-187009257088,-187009257024⟩ : DyadicInterval 40),(⟨748619423471,748619442800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27231625664,-27191658944⟩ : DyadicInterval 40),(⟨775719213088,775739215712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159697677056,159796218624⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187034737088,-186899664384⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2027_ok : ecellOkT e2027 = true := by decide +kernel
theorem e2027_pos {a z : ℝ} (ha1 : ((1280589/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((640719/4096000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2027 e2027_ok ha1 ha2 hz1 hz2 hz

-- box ['640719/4096000', '1282287/8192000', '1999/2000', '7997/8000']  interval_lower 176551665/1099511627776
noncomputable def e2028 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271503324708,0,true,159796218560,159796218624⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927519930844,0,false,-187034737088,-187034737024⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271617275560,0,true,159894751296,159894751360⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927405979992,0,false,-187169826368,-187169826304⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271417328859,0,true,159721852544,159721852608⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927605926693,0,false,-186932799616,-186932799552⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271552735943,0,true,159838945344,159838945408⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927470519609,0,false,-187093312320,-187093312256⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544457526,0,true,32829248,32829312⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478798026,0,false,-32830272,-32830208⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555431529,0,true,43802880,43802944⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467824023,0,false,-43804672,-43804608⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626030,0,false,-1792,-1728⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626796,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271460322441,0,true,159759032448,159759032512⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927562933111,0,false,-186983762048,-186983761984⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271585010225,0,true,159866852544,159866852608⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927438245327,0,false,-187131574016,-187131573952⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072582172734,0,false,-27264721408,-27264721344⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072621185829,0,false,-27224729536,-27224729472⟩
    { al := (640719/4096000), au := (1282287/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨171991696932,172105647784⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159796218560,159796218624⟩ : DyadicInterval 40),(⟨-187034737088,-187034737024⟩ : DyadicInterval 40),(⟨748616033554,748616052883⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159894751296,159894751360⟩ : DyadicInterval 40),(⟨-187169826368,-187169826304⟩ : DyadicInterval 40),(⟨748598055115,748598074444⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159721852544,159721852608⟩ : DyadicInterval 40),(⟨-186932799616,-186932799552⟩ : DyadicInterval 40),(⟨748629593420,748629612749⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159838945344,159838945408⟩ : DyadicInterval 40),(⟨-187093312320,-187093312256⟩ : DyadicInterval 40),(⟨748608239228,748608258557⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32829750,43803753⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32829248,32829312⟩ : DyadicInterval 40),(⟨-32830272,-32830208⟩ : DyadicInterval 40),(⟨762123383083,762123402412⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43802880,43802944⟩ : DyadicInterval 40),(⟨-43804672,-43804608⟩ : DyadicInterval 40),(⟨762123382702,762123402031⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1792,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171948694665,172073382449⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159759032448,159759032512⟩ : DyadicInterval 40),(⟨-186983762048,-186983761984⟩ : DyadicInterval 40),(⟨748622815031,748622834360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159866852544,159866852608⟩ : DyadicInterval 40),(⟨-187131574016,-187131573952⟩ : DyadicInterval 40),(⟨748603146964,748603166293⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27264721408,-27224729472⟩ : DyadicInterval 40),(⟨775735748352,775755763584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159796218560,159894751360⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187169826368,-187034737024⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2028_ok : ecellOkT e2028 = true := by decide +kernel
theorem e2028_pos {a z : ℝ} (ha1 : ((640719/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1282287/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2028 e2028_ok ha1 ha2 hz1 hz2 hz

-- box ['1282287/8192000', '20049/128000', '1999/2000', '7997/8000']  interval_lower 177647143/1099511627776
noncomputable def e2029 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271617275559,0,true,159894751296,159894751360⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927405979993,0,false,-187169826368,-187169826304⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271731226412,0,true,159993275200,159993275264⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927292029140,0,false,-187304932224,-187304932160⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271531222735,0,true,159820342656,159820342720⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927492032817,0,false,-187067808832,-187067808768⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271666644063,0,true,159937437248,159937437312⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927356611489,0,false,-187228358144,-187228358080⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544480065,0,true,32851776,32851840⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478775487,0,false,-32852800,-32852736⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555461584,0,true,43832896,43832960⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467793968,0,false,-43834688,-43834624⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626028,0,false,-1792,-1728⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626795,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271574244802,0,true,159857543872,159857543936⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927449010750,0,false,-187118811264,-187118811200⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271698939709,0,true,159965360448,159965360512⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927324315843,0,false,-187266649792,-187266649728⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072546501039,0,false,-27301289344,-27301289280⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072585542204,0,false,-27261267392,-27261267328⟩
    { al := (1282287/8192000), au := (20049/128000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨172105647783,172219598636⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159894751296,159894751360⟩ : DyadicInterval 40),(⟨-187169826368,-187169826304⟩ : DyadicInterval 40),(⟨748598055115,748598074444⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159993275200,159993275264⟩ : DyadicInterval 40),(⟨-187304932224,-187304932160⟩ : DyadicInterval 40),(⟨748580064561,748580083890⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159820342656,159820342720⟩ : DyadicInterval 40),(⟨-187067808832,-187067808768⟩ : DyadicInterval 40),(⟨748611633118,748611652447⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159937437248,159937437312⟩ : DyadicInterval 40),(⟨-187228358144,-187228358080⟩ : DyadicInterval 40),(⟨748590262323,748590281652⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32852289,43833808⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32851776,32851840⟩ : DyadicInterval 40),(⟨-32852800,-32852736⟩ : DyadicInterval 40),(⟨762123383082,762123402411⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43832896,43832960⟩ : DyadicInterval 40),(⟨-43834688,-43834624⟩ : DyadicInterval 40),(⟨762123382700,762123402029⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1792,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172062617026,172187311933⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159857543872,159857543936⟩ : DyadicInterval 40),(⟨-187118811264,-187118811200⟩ : DyadicInterval 40),(⟨748604845650,748604864980⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159965360448,159965360512⟩ : DyadicInterval 40),(⟨-187266649792,-187266649728⟩ : DyadicInterval 40),(⟨748585163208,748585182537⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27301289344,-27261267328⟩ : DyadicInterval 40),(⟨775754017280,775774047552⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159894751296,159993275264⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187304932224,-187169826304⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2029_ok : ecellOkT e2029 = true := by decide +kernel
theorem e2029_pos {a z : ℝ} (ha1 : ((1282287/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((20049/128000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2029 e2029_ok ha1 ha2 hz1 hz2 hz

-- box ['640719/4096000', '1282287/8192000', '7997/8000', '3999/4000']  interval_lower 22049291/137438953472
noncomputable def e2030 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271503324708,0,true,159796218560,159796218624⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927519930844,0,false,-187034737088,-187034737024⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271617275560,0,true,159894751296,159894751360⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927405979992,0,false,-187169826368,-187169826304⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271438827821,0,true,159740444544,159740444608⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927584427731,0,false,-186958283136,-186958283072⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271574249149,0,true,159857547648,159857547712⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927449006403,0,false,-187118816384,-187118816320⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533514240,0,true,21886208,21886272⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489741312,0,false,-21886720,-21886656⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544480730,0,true,32852416,32852480⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478774822,0,false,-32853504,-32853440⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626794,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627341,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271471071838,0,true,159768328064,159768328128⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927552183714,0,false,-186996504192,-186996504128⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271595766769,0,true,159876153408,159876153472⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927427488783,0,false,-187144326336,-187144326272⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072578805834,0,false,-27268172864,-27268172800⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072617823605,0,false,-27228176064,-27228176000⟩
    { al := (640719/4096000), au := (1282287/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨171991696932,172105647784⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159796218560,159796218624⟩ : DyadicInterval 40),(⟨-187034737088,-187034737024⟩ : DyadicInterval 40),(⟨748616033554,748616052883⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159894751296,159894751360⟩ : DyadicInterval 40),(⟨-187169826368,-187169826304⟩ : DyadicInterval 40),(⟨748598055115,748598074444⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159740444544,159740444608⟩ : DyadicInterval 40),(⟨-186958283136,-186958283072⟩ : DyadicInterval 40),(⟨748626204102,748626223431⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159857547648,159857547712⟩ : DyadicInterval 40),(⟨-187118816384,-187118816320⟩ : DyadicInterval 40),(⟨748604844940,748604864270⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21886464,32852954⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21886208,21886272⟩ : DyadicInterval 40),(⟨-21886720,-21886656⟩ : DyadicInterval 40),(⟨762123383372,762123402701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32852416,32852480⟩ : DyadicInterval 40),(⟨-32853504,-32853440⟩ : DyadicInterval 40),(⟨762123383114,762123402443⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171959444062,172084138993⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159768328064,159768328128⟩ : DyadicInterval 40),(⟨-186996504192,-186996504128⟩ : DyadicInterval 40),(⟨748621120015,748621139345⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159876153408,159876153472⟩ : DyadicInterval 40),(⟨-187144326336,-187144326272⟩ : DyadicInterval 40),(⟨748601449578,748601468908⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27268172864,-27228176000⟩ : DyadicInterval 40),(⟨775737471616,775757489312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159796218560,159894751360⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187169826368,-187034737024⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2030_ok : ecellOkT e2030 = true := by decide +kernel
theorem e2030_pos {a z : ℝ} (ha1 : ((640719/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1282287/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2030 e2030_ok ha1 ha2 hz1 hz2 hz

-- box ['1282287/8192000', '20049/128000', '7997/8000', '3999/4000']  interval_lower 88744651/549755813888
noncomputable def e2031 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271617275559,0,true,159894751296,159894751360⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927405979993,0,false,-187169826368,-187169826304⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271731226412,0,true,159993275200,159993275264⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927292029140,0,false,-187304932224,-187304932160⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271552735940,0,true,159838945280,159838945344⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927470519612,0,false,-187093312320,-187093312256⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271688171513,0,true,159956050240,159956050304⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927335084039,0,false,-187253882240,-187253882176⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533529265,0,true,21901248,21901312⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489726287,0,false,-21901760,-21901696⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544503271,0,true,32874944,32875008⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478752281,0,false,-32876032,-32875968⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626793,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627340,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271585001320,0,true,159866844800,159866844864⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927438254232,0,false,-187131563456,-187131563392⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271709703377,0,true,159974666688,159974666752⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927313552175,0,false,-187279412160,-187279412096⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072543129679,0,false,-27304745472,-27304745408⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072582175523,0,false,-27264718592,-27264718528⟩
    { al := (1282287/8192000), au := (20049/128000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨172105647783,172219598636⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159894751296,159894751360⟩ : DyadicInterval 40),(⟨-187169826368,-187169826304⟩ : DyadicInterval 40),(⟨748598055115,748598074444⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159993275200,159993275264⟩ : DyadicInterval 40),(⟨-187304932224,-187304932160⟩ : DyadicInterval 40),(⟨748580064561,748580083890⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159838945280,159838945344⟩ : DyadicInterval 40),(⟨-187093312320,-187093312256⟩ : DyadicInterval 40),(⟨748608239265,748608258595⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159956050240,159956050304⟩ : DyadicInterval 40),(⟨-187253882240,-187253882176⟩ : DyadicInterval 40),(⟨748586863483,748586882813⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21901489,32875495⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21901248,21901312⟩ : DyadicInterval 40),(⟨-21901760,-21901696⟩ : DyadicInterval 40),(⟨762123383371,762123402700⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32874944,32875008⟩ : DyadicInterval 40),(⟨-32876032,-32875968⟩ : DyadicInterval 40),(⟨762123383113,762123402442⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172073373544,172198075601⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159866844800,159866844864⟩ : DyadicInterval 40),(⟨-187131563456,-187131563392⟩ : DyadicInterval 40),(⟨748603148393,748603167723⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159974666688,159974666752⟩ : DyadicInterval 40),(⟨-187279412160,-187279412096⟩ : DyadicInterval 40),(⟨748583463540,748583482870⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27304745472,-27264718528⟩ : DyadicInterval 40),(⟨775755742880,775775775616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159894751296,159993275264⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187304932224,-187169826304⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2031_ok : ecellOkT e2031 = true := by decide +kernel
theorem e2031_pos {a z : ℝ} (ha1 : ((1282287/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((20049/128000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2031 e2031_ok ha1 ha2 hz1 hz2 hz

-- box ['63987/409600', '1280589/8192000', '3999/4000', '7999/8000']  interval_lower 43514007/274877906944
noncomputable def e2032 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271275423006,0,true,159599126656,159599126720⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927747832546,0,false,-186764608384,-186764608320⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271389373858,0,true,159697677056,159697677120⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927633881694,0,false,-186899664448,-186899664384⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271232482057,0,true,159561986880,159561986944⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927790773495,0,false,-186713718464,-186713718400⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271367889140,0,true,159679096640,159679096704⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927655366412,0,false,-186874199232,-186874199168⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522555879,0,true,10928000,10928064⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500699673,0,false,-10928192,-10928128⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533499828,0,true,21871808,21871872⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489755724,0,false,-21872320,-21872256⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627340,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627668,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271253948050,0,true,159580553088,159580553152⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927769307502,0,false,-186739157824,-186739157760⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271378635871,0,true,159688390656,159688390720⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927644619681,0,false,-186886936960,-186886936896⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072646729101,0,false,-27198546240,-27198546176⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072685695401,0,false,-27158604736,-27158604672⟩
    { al := (63987/409600), au := (1280589/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨171763795230,171877746082⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159599126656,159599126720⟩ : DyadicInterval 40),(⟨-186764608384,-186764608320⟩ : DyadicInterval 40),(⟨748651954110,748651973440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159697677056,159697677120⟩ : DyadicInterval 40),(⟨-186899664448,-186899664384⟩ : DyadicInterval 40),(⟨748633999869,748634019199⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159561986880,159561986944⟩ : DyadicInterval 40),(⟨-186713718464,-186713718400⟩ : DyadicInterval 40),(⟨748658716785,748658736114⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159679096640,159679096704⟩ : DyadicInterval 40),(⟨-186874199232,-186874199168⟩ : DyadicInterval 40),(⟨748637385984,748637405314⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10928103,21872052⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10928000,10928064⟩ : DyadicInterval 40),(⟨-10928192,-10928128⟩ : DyadicInterval 40),(⟨762123383539,762123402868⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21871808,21871872⟩ : DyadicInterval 40),(⟨-21872320,-21872256⟩ : DyadicInterval 40),(⟨762123383372,762123402701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171742320274,171867008095⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159580553088,159580553152⟩ : DyadicInterval 40),(⟨-186739157824,-186739157760⟩ : DyadicInterval 40),(⟨748655336348,748655355677⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159688390656,159688390720⟩ : DyadicInterval 40),(⟨-186886936960,-186886936896⟩ : DyadicInterval 40),(⟨748635692304,748635711633⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27198546240,-27158604672⟩ : DyadicInterval 40),(⟨775702685952,775722676000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159599126656,159697677120⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186899664448,-186764608320⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2032_ok : ecellOkT e2032 = true := by decide +kernel
theorem e2032_pos {a z : ℝ} (ha1 : ((63987/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1280589/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2032 e2032_ok ha1 ha2 hz1 hz2 hz

-- box ['1280589/8192000', '640719/4096000', '3999/4000', '7999/8000']  interval_lower 87572469/549755813888
noncomputable def e2033 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271389373857,0,true,159697677056,159697677120⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927633881695,0,false,-186899664448,-186899664384⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271503324709,0,true,159796218560,159796218624⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927519930843,0,false,-187034737088,-187034737024⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271346404420,0,true,159660515968,159660516032⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927676851132,0,false,-186848734528,-186848734464⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271481825747,0,true,159777627584,159777627648⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927541429805,0,false,-187009251840,-187009251776⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522563391,0,true,10935552,10935616⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500692161,0,false,-10935680,-10935616⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533514854,0,true,21886848,21886912⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489740698,0,false,-21887296,-21887232⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627340,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627668,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271367884658,0,true,159679092800,159679092864⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927655370894,0,false,-186874193920,-186874193856⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271492579605,0,true,159786926912,159786926976⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927530675947,0,false,-187021999616,-187021999552⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072611095717,0,false,-27235072640,-27235072576⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072650090087,0,false,-27195101056,-27195100992⟩
    { al := (1280589/8192000), au := (640719/4096000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨171877746081,171991696933⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159697677056,159697677120⟩ : DyadicInterval 40),(⟨-186899664448,-186899664384⟩ : DyadicInterval 40),(⟨748633999869,748634019199⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159796218560,159796218624⟩ : DyadicInterval 40),(⟨-187034737088,-187034737024⟩ : DyadicInterval 40),(⟨748616033553,748616052883⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159660515968,159660516032⟩ : DyadicInterval 40),(⟨-186848734528,-186848734464⟩ : DyadicInterval 40),(⟨748640771603,748640790933⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159777627584,159777627648⟩ : DyadicInterval 40),(⟨-187009251840,-187009251776⟩ : DyadicInterval 40),(⟨748619424136,748619443466⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10935615,21887078⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10935552,10935616⟩ : DyadicInterval 40),(⟨-10935680,-10935616⟩ : DyadicInterval 40),(⟨762123383507,762123402836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21886848,21886912⟩ : DyadicInterval 40),(⟨-21887296,-21887232⟩ : DyadicInterval 40),(⟨762123383340,762123402669⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171856256882,171980951829⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159679092800,159679092864⟩ : DyadicInterval 40),(⟨-186874193920,-186874193856⟩ : DyadicInterval 40),(⟨748637386670,748637406000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159786926912,159786926976⟩ : DyadicInterval 40),(⟨-187021999616,-187021999552⟩ : DyadicInterval 40),(⟨748617728215,748617747544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27235072640,-27195100992⟩ : DyadicInterval 40),(⟨775720934112,775740939200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159697677056,159796218624⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187034737088,-186899664384⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2033_ok : ecellOkT e2033 = true := by decide +kernel
theorem e2033_pos {a z : ℝ} (ha1 : ((1280589/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((640719/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2033 e2033_ok ha1 ha2 hz1 hz2 hz

-- box ['63987/409600', '1280589/8192000', '7999/8000', '1']  interval_lower 173899357/1099511627776
noncomputable def e2034 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271275423006,0,true,159599126656,159599126720⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927747832546,0,false,-186764608384,-186764608320⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271389373858,0,true,159697677056,159697677120⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927633881694,0,false,-186899664448,-186899664384⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271253952531,0,true,159580556928,159580556992⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927769303021,0,false,-186739163136,-186739163072⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522563956,0,true,10936064,10936128⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500691596,0,false,-10936256,-10936192⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627667,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1271264683250,0,true,159589837952,159589838016⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨927758572302,0,false,-186751880320,-186751880256⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1271389378222,0,true,159697680832,159697680896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨927633877330,0,false,-186899669632,-186899669568⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1072643370677,0,false,-27201988736,-27201988672⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1072682341647,0,false,-27162042368,-27162042304⟩
    { al := (63987/409600), au := (1280589/8192000), zl := (7999/8000), zu := 1,
      A := ⟨171763795230,171877746082⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159599126656,159599126720⟩ : DyadicInterval 40),(⟨-186764608384,-186764608320⟩ : DyadicInterval 40),(⟨748651954110,748651973440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159697677056,159697677120⟩ : DyadicInterval 40),(⟨-186899664448,-186899664384⟩ : DyadicInterval 40),(⟨748633999869,748634019199⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159580556928,159580556992⟩ : DyadicInterval 40),(⟨-186739163136,-186739163072⟩ : DyadicInterval 40),(⟨748655335663,748655354993⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159697677056,159697677120⟩ : DyadicInterval 40),(⟨-186899664448,-186899664384⟩ : DyadicInterval 40),(⟨748633999869,748634019199⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10936180⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10936064,10936128⟩ : DyadicInterval 40),(⟨-10936256,-10936192⟩ : DyadicInterval 40),(⟨762123383539,762123402868⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨171753055474,171877750446⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159589837952,159589838016⟩ : DyadicInterval 40),(⟨-186751880320,-186751880256⟩ : DyadicInterval 40),(⟨748653645631,748653664960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159697680832,159697680896⟩ : DyadicInterval 40),(⟨-186899669632,-186899669568⟩ : DyadicInterval 40),(⟨748633999185,748634018515⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27201988736,-27162042304⟩ : DyadicInterval 40),(⟨775704404768,775724397248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨159599126656,159697677120⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186899664448,-186764608320⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2034_ok : ecellOkT e2034 = true := by decide +kernel
theorem e2034_pos {a z : ℝ} (ha1 : ((63987/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1280589/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2034 e2034_ok ha1 ha2 hz1 hz2 hz

-- box ['1280589/8192000', '640719/4096000', '7999/8000', '1']  interval_lower 174988033/1099511627776
noncomputable def e2035 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271389373857,0,true,159697677056,159697677120⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927633881695,0,false,-186899664448,-186899664384⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271503324709,0,true,159796218560,159796218624⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927519930843,0,false,-187034737088,-187034737024⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271367889138,0,true,159679096640,159679096704⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927655366414,0,false,-186874199168,-186874199104⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522571469,0,true,10943616,10943680⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500684083,0,false,-10943808,-10943744⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627667,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1271378626980,0,true,159688382976,159688383040⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨927644628572,0,false,-186886926400,-186886926336⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1271503329071,0,true,159796222336,159796222400⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨927519926481,0,false,-187034742272,-187034742208⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1072607732840,0,false,-27238519872,-27238519808⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1072646731882,0,false,-27198543360,-27198543296⟩
    { al := (1280589/8192000), au := (640719/4096000), zl := (7999/8000), zu := 1,
      A := ⟨171877746081,171991696933⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159697677056,159697677120⟩ : DyadicInterval 40),(⟨-186899664448,-186899664384⟩ : DyadicInterval 40),(⟨748633999869,748634019199⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159796218560,159796218624⟩ : DyadicInterval 40),(⟨-187034737088,-187034737024⟩ : DyadicInterval 40),(⟨748616033553,748616052883⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159679096640,159679096704⟩ : DyadicInterval 40),(⟨-186874199168,-186874199104⟩ : DyadicInterval 40),(⟨748637385958,748637405288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159796218560,159796218624⟩ : DyadicInterval 40),(⟨-187034737088,-187034737024⟩ : DyadicInterval 40),(⟨748616033553,748616052883⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10943693⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10943616,10943680⟩ : DyadicInterval 40),(⟨-10943808,-10943744⟩ : DyadicInterval 40),(⟨762123383539,762123402868⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨171866999204,171991701295⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159688382976,159688383040⟩ : DyadicInterval 40),(⟨-186886926400,-186886926336⟩ : DyadicInterval 40),(⟨748635693691,748635713020⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159796222336,159796222400⟩ : DyadicInterval 40),(⟨-187034742272,-187034742208⟩ : DyadicInterval 40),(⟨748616032869,748616052198⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27238519872,-27198543296⟩ : DyadicInterval 40),(⟨775722655264,775742662816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨159697677056,159796218624⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187034737088,-186899664384⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2035_ok : ecellOkT e2035 = true := by decide +kernel
theorem e2035_pos {a z : ℝ} (ha1 : ((1280589/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((640719/4096000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2035 e2035_ok ha1 ha2 hz1 hz2 hz

-- box ['640719/4096000', '1282287/8192000', '3999/4000', '7999/8000']  interval_lower 176237053/1099511627776
noncomputable def e2036 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271503324708,0,true,159796218560,159796218624⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927519930844,0,false,-187034737088,-187034737024⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271617275560,0,true,159894751296,159894751360⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927405979992,0,false,-187169826368,-187169826304⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271460326783,0,true,159759036224,159759036288⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927562928769,0,false,-186983767168,-186983767104⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271595762355,0,true,159876149632,159876149696⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927427493197,0,false,-187144321088,-187144321024⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522570904,0,true,10943040,10943104⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500684648,0,false,-10943232,-10943168⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533529880,0,true,21901824,21901888⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489725672,0,false,-21902336,-21902272⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627339,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627668,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271481821262,0,true,159777623680,159777623744⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927541434290,0,false,-187009246528,-187009246464⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271606523334,0,true,159885454272,159885454336⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927416732218,0,false,-187157078848,-187157078784⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072575438718,0,false,-27271624512,-27271624448⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072614461161,0,false,-27231622848,-27231622784⟩
    { al := (640719/4096000), au := (1282287/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨171991696932,172105647784⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159796218560,159796218624⟩ : DyadicInterval 40),(⟨-187034737088,-187034737024⟩ : DyadicInterval 40),(⟨748616033554,748616052883⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159894751296,159894751360⟩ : DyadicInterval 40),(⟨-187169826368,-187169826304⟩ : DyadicInterval 40),(⟨748598055115,748598074444⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159759036224,159759036288⟩ : DyadicInterval 40),(⟨-186983767168,-186983767104⟩ : DyadicInterval 40),(⟨748622814323,748622833652⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159876149632,159876149696⟩ : DyadicInterval 40),(⟨-187144321088,-187144321024⟩ : DyadicInterval 40),(⟨748601450245,748601469574⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10943128,21902104⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10943040,10943104⟩ : DyadicInterval 40),(⟨-10943232,-10943168⟩ : DyadicInterval 40),(⟨762123383539,762123402868⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21901824,21901888⟩ : DyadicInterval 40),(⟨-21902336,-21902272⟩ : DyadicInterval 40),(⟨762123383371,762123402700⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171970193486,172094895558⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159777623680,159777623744⟩ : DyadicInterval 40),(⟨-187009246528,-187009246464⟩ : DyadicInterval 40),(⟨748619424860,748619444190⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159885454272,159885454336⟩ : DyadicInterval 40),(⟨-187157078848,-187157078784⟩ : DyadicInterval 40),(⟨748599752054,748599771384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27271624512,-27231622784⟩ : DyadicInterval 40),(⟨775739195008,775759215136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159796218560,159894751360⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187169826368,-187034737024⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2036_ok : ecellOkT e2036 = true := by decide +kernel
theorem e2036_pos {a z : ℝ} (ha1 : ((640719/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1282287/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2036 e2036_ok ha1 ha2 hz1 hz2 hz

-- box ['1282287/8192000', '20049/128000', '3999/4000', '7999/8000']  interval_lower 177331465/1099511627776
noncomputable def e2037 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271617275559,0,true,159894751296,159894751360⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927405979993,0,false,-187169826368,-187169826304⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271731226412,0,true,159993275200,159993275264⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927292029140,0,false,-187304932224,-187304932160⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271574249147,0,true,159857547648,159857547712⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927449006405,0,false,-187118816384,-187118816320⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1271709698963,0,true,159974662848,159974662912⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨927313556589,0,false,-187279406912,-187279406848⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522578417,0,true,10950528,10950592⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500677135,0,false,-10950720,-10950656⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533544908,0,true,21916864,21916928⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489710644,0,false,-21917376,-21917312⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627339,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627667,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1271595757870,0,true,159876145728,159876145792⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨927427497682,0,false,-187144315776,-187144315712⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1271720467066,0,true,159983972864,159983972928⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨927302788486,0,false,-187292174720,-187292174656⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072539758101,0,false,-27308201856,-27308201792⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072578808621,0,false,-27268169984,-27268169920⟩
    { al := (1282287/8192000), au := (20049/128000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨172105647783,172219598636⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159894751296,159894751360⟩ : DyadicInterval 40),(⟨-187169826368,-187169826304⟩ : DyadicInterval 40),(⟨748598055115,748598074444⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159993275200,159993275264⟩ : DyadicInterval 40),(⟨-187304932224,-187304932160⟩ : DyadicInterval 40),(⟨748580064561,748580083890⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159857547648,159857547712⟩ : DyadicInterval 40),(⟨-187118816384,-187118816320⟩ : DyadicInterval 40),(⟨748604844940,748604864270⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159974662848,159974662912⟩ : DyadicInterval 40),(⟨-187279406912,-187279406848⟩ : DyadicInterval 40),(⟨748583464245,748583483575⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10950641,21917132⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10950528,10950592⟩ : DyadicInterval 40),(⟨-10950720,-10950656⟩ : DyadicInterval 40),(⟨762123383538,762123402867⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21916864,21916928⟩ : DyadicInterval 40),(⟨-21917376,-21917312⟩ : DyadicInterval 40),(⟨762123383371,762123402700⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172084130094,172208839290⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159876145728,159876145792⟩ : DyadicInterval 40),(⟨-187144315776,-187144315712⟩ : DyadicInterval 40),(⟨748601450970,748601470299⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159983972864,159983972928⟩ : DyadicInterval 40),(⟨-187292174720,-187292174656⟩ : DyadicInterval 40),(⟨748581763771,748581783101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27308201856,-27268169920⟩ : DyadicInterval 40),(⟨775757468576,775777503808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159894751296,159993275264⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187304932224,-187169826304⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2037_ok : ecellOkT e2037 = true := by decide +kernel
theorem e2037_pos {a z : ℝ} (ha1 : ((1282287/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((20049/128000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2037 e2037_ok ha1 ha2 hz1 hz2 hz

-- box ['640719/4096000', '1282287/8192000', '7999/8000', '1']  interval_lower 176079673/1099511627776
noncomputable def e2038 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271503324708,0,true,159796218560,159796218624⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927519930844,0,false,-187034737088,-187034737024⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271617275560,0,true,159894751296,159894751360⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927405979992,0,false,-187169826368,-187169826304⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271481825745,0,true,159777627584,159777627648⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927541429807,0,false,-187009251840,-187009251776⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522578982,0,true,10951104,10951168⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500676570,0,false,-10951296,-10951232⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627666,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1271492570708,0,true,159786919232,159786919296⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨927530684844,0,false,-187021989056,-187021988992⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1271617279923,0,true,159894755072,159894755136⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨927405975629,0,false,-187169831552,-187169831488⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1072572071383,0,false,-27275076416,-27275076352⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1072611098501,0,false,-27235069824,-27235069760⟩
    { al := (640719/4096000), au := (1282287/8192000), zl := (7999/8000), zu := 1,
      A := ⟨171991696932,172105647784⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159796218560,159796218624⟩ : DyadicInterval 40),(⟨-187034737088,-187034737024⟩ : DyadicInterval 40),(⟨748616033554,748616052883⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159894751296,159894751360⟩ : DyadicInterval 40),(⟨-187169826368,-187169826304⟩ : DyadicInterval 40),(⟨748598055115,748598074444⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159777627584,159777627648⟩ : DyadicInterval 40),(⟨-187009251840,-187009251776⟩ : DyadicInterval 40),(⟨748619424137,748619443466⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159894751296,159894751360⟩ : DyadicInterval 40),(⟨-187169826368,-187169826304⟩ : DyadicInterval 40),(⟨748598055115,748598074444⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10951206⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10951104,10951168⟩ : DyadicInterval 40),(⟨-10951296,-10951232⟩ : DyadicInterval 40),(⟨762123383538,762123402867⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨171980942932,172105652147⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159786919232,159786919296⟩ : DyadicInterval 40),(⟨-187021989056,-187021988992⟩ : DyadicInterval 40),(⟨748617729605,748617748934⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159894755072,159894755136⟩ : DyadicInterval 40),(⟨-187169831552,-187169831488⟩ : DyadicInterval 40),(⟨748598054429,748598073758⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27275076416,-27235069760⟩ : DyadicInterval 40),(⟨775740918496,775760941088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨159796218560,159894751360⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187169826368,-187034737024⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2038_ok : ecellOkT e2038 = true := by decide +kernel
theorem e2038_pos {a z : ℝ} (ha1 : ((640719/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1282287/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2038 e2038_ok ha1 ha2 hz1 hz2 hz

-- box ['1282287/8192000', '20049/128000', '7999/8000', '1']  interval_lower 177173673/1099511627776
noncomputable def e2039 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1271617275559,0,true,159894751296,159894751360⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨927405979993,0,false,-187169826368,-187169826304⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271731226412,0,true,159993275200,159993275264⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927292029140,0,false,-187304932224,-187304932160⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1271595762352,0,true,159876149632,159876149696⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨927427493200,0,false,-187144321088,-187144321024⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522586495,0,true,10958656,10958720⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500669057,0,false,-10958784,-10958720⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627666,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1271606514434,0,true,159885446592,159885446656⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨927416741118,0,false,-187157068288,-187157068224⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1271731230778,0,true,159993278976,159993279040⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨927292024774,0,false,-187304937408,-187304937344⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1072536386306,0,false,-27311658432,-27311658368⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1072575441505,0,false,-27271621696,-27271621632⟩
    { al := (1282287/8192000), au := (20049/128000), zl := (7999/8000), zu := 1,
      A := ⟨172105647783,172219598636⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159894751296,159894751360⟩ : DyadicInterval 40),(⟨-187169826368,-187169826304⟩ : DyadicInterval 40),(⟨748598055115,748598074444⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159993275200,159993275264⟩ : DyadicInterval 40),(⟨-187304932224,-187304932160⟩ : DyadicInterval 40),(⟨748580064561,748580083890⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159876149632,159876149696⟩ : DyadicInterval 40),(⟨-187144321088,-187144321024⟩ : DyadicInterval 40),(⟨748601450245,748601469575⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159993275200,159993275264⟩ : DyadicInterval 40),(⟨-187304932224,-187304932160⟩ : DyadicInterval 40),(⟨748580064561,748580083890⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10958719⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10958656,10958720⟩ : DyadicInterval 40),(⟨-10958784,-10958720⟩ : DyadicInterval 40),(⟨762123383506,762123402835⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨172094886658,172219603002⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159885446592,159885446656⟩ : DyadicInterval 40),(⟨-187157068288,-187157068224⟩ : DyadicInterval 40),(⟨748599753446,748599772776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159993278976,159993279040⟩ : DyadicInterval 40),(⟨-187304937408,-187304937344⟩ : DyadicInterval 40),(⟨748580063873,748580083203⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27311658432,-27271621632⟩ : DyadicInterval 40),(⟨775759194432,775779232096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨159894751296,159993275264⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-187304932224,-187169826304⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2039_ok : ecellOkT e2039 = true := by decide +kernel
theorem e2039_pos {a z : ℝ} (ha1 : ((1282287/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((20049/128000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2039 e2039_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B033

end


