-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B032__2_q00
-- name    : CK_CKLaneC2R_EpCells_B032__2_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:16:54.653192+00:00
-- url     : https://prove2.me/theorems/5260a645-001d-40e3-b354-320ffd8918ea
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B032 (+1 modules: CKLaneC2R.EpCells.B033) (piece 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B032 (+1 modules: CKLaneC2R.EpCells.B033) (piece 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B032 (+1 modules: CKLaneC2R.EpCells.B033) (piece 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B032 (+1 modules: CKLaneC2R.EpCells.B033) (piece 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B032 (+1 modules: CKLaneC2R/EpCells/B033) (piece 1 of 2).lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheckT

-- ===== source module CKLaneC2R.EpCells.B032 =====
section

namespace CKLaneC2R.EpCells.B032

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['79347/512000', '1270401/8192000', '3997/4000', '1599/1600']  interval_lower 161806203/1099511627776
noncomputable def e1920 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269908012793,0,true,158415832640,158415832704⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929115242759,0,false,-185145228096,-185145228032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270021963645,0,true,158514489152,158514489216⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929001291907,0,false,-185280085440,-185280085376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269780215504,0,true,158305177664,158305177728⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929243040048,0,false,-184994003648,-184994003584⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269915394686,0,true,158422224000,158422224064⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929107860866,0,false,-185153963840,-185153963776⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565818312,0,true,54189184,54189248⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457437240,0,false,-54191872,-54191808⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576702165,0,true,65072448,65072512⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446553387,0,false,-65076352,-65076288⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623924,0,false,-3904,-3840⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625106,0,false,-2688,-2624⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269844110073,0,true,158360503040,158360503104⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929179145479,0,false,-185069608448,-185069608384⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269968683816,0,true,158468361600,158468361664⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929054571736,0,false,-185217028352,-185217028288⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073085706285,0,false,-26748666688,-26748666624⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073124317454,0,false,-26709105408,-26709105344⟩
    { al := (79347/512000), au := (1270401/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨170396385017,170510335869⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158415832640,158415832704⟩ : DyadicInterval 40),(⟨-185145228096,-185145228032⟩ : DyadicInterval 40),(⟨748866460688,748866480017⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158514489152,158514489216⟩ : DyadicInterval 40),(⟨-185280085440,-185280085376⟩ : DyadicInterval 40),(⟨748848651705,748848671035⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158305177664,158305177728⟩ : DyadicInterval 40),(⟨-184994003648,-184994003584⟩ : DyadicInterval 40),(⟨748886419279,748886438608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158422224000,158422224064⟩ : DyadicInterval 40),(⟨-185153963840,-185153963776⟩ : DyadicInterval 40),(⟨748865307371,748865326701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54190536,65074389⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54189184,54189248⟩ : DyadicInterval 40),(⟨-54191872,-54191808⟩ : DyadicInterval 40),(⟨762123382225,762123401554⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65072448,65072512⟩ : DyadicInterval 40),(⟨-65076352,-65076288⟩ : DyadicInterval 40),(⟨762123381652,762123400981⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3904,-2624⟩ : DyadicInterval 40),(⟨762123384928,762123404832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170332482297,170457056040⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158360503040,158360503104⟩ : DyadicInterval 40),(⟨-185069608448,-185069608384⟩ : DyadicInterval 40),(⟨748876442507,748876461836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158468361600,158468361664⟩ : DyadicInterval 40),(⟨-185217028352,-185217028288⟩ : DyadicInterval 40),(⟨748856980124,748856999453⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26748666688,-26709105344⟩ : DyadicInterval 40),(⟨775477936288,775497736224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158415832640,158514489216⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185280085440,-185145228032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1920_ok : ecellOkT e1920 = true := by decide +kernel
theorem e1920_pos {a z : ℝ} (ha1 : ((79347/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1270401/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1920 e1920_ok ha1 ha2 hz1 hz2 hz

-- box ['1270401/8192000', '5085/32768', '3997/4000', '1599/1600']  interval_lower 20358065/137438953472
noncomputable def e1921 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270021963644,0,true,158514489152,158514489216⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929001291908,0,false,-185280085440,-185280085376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270135914496,0,true,158613136768,158613136832⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928887341056,0,false,-185414959232,-185414959168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269894080892,0,true,158403770048,158403770112⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929129174660,0,false,-185128741248,-185128741184⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270029274317,0,true,158520818304,158520818368⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928993981235,0,false,-185288737920,-185288737856⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565855839,0,true,54226688,54226752⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457399713,0,false,-54229440,-54229376⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576747203,0,true,65117440,65117504⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446508349,0,false,-65121408,-65121344⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623919,0,false,-3904,-3840⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625102,0,false,-2688,-2624⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269958018189,0,true,158459127488,158459127552⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929065237363,0,false,-185204405888,-185204405824⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270082599061,0,true,158566982528,158566982592⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928940656491,0,false,-185351852288,-185351852224⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073050373970,0,false,-26784869696,-26784869632⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073089013162,0,false,-26745278400,-26745278336⟩
    { al := (1270401/8192000), au := (5085/32768), zl := (3997/4000), zu := (1599/1600),
      A := ⟨170510335868,170624286720⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158514489152,158514489216⟩ : DyadicInterval 40),(⟨-185280085440,-185280085376⟩ : DyadicInterval 40),(⟨748848651706,748848671035⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158613136768,158613136832⟩ : DyadicInterval 40),(⟨-185414959232,-185414959168⟩ : DyadicInterval 40),(⟨748830830608,748830849938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158403770048,158403770112⟩ : DyadicInterval 40),(⟨-185128741248,-185128741184⟩ : DyadicInterval 40),(⟨748868637227,748868656557⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158520818304,158520818368⟩ : DyadicInterval 40),(⟨-185288737920,-185288737856⟩ : DyadicInterval 40),(⟨748847508709,748847528038⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54228063,65119427⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54226688,54226752⟩ : DyadicInterval 40),(⟨-54229440,-54229376⟩ : DyadicInterval 40),(⟨762123382253,762123401582⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65117440,65117504⟩ : DyadicInterval 40),(⟨-65121408,-65121344⟩ : DyadicInterval 40),(⟨762123381679,762123401008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3904,-2624⟩ : DyadicInterval 40),(⟨762123384928,762123404832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170446390413,170570971285⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158459127488,158459127552⟩ : DyadicInterval 40),(⟨-185204405888,-185204405824⟩ : DyadicInterval 40),(⟨748858646983,748858666313⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158566982528,158566982592⟩ : DyadicInterval 40),(⟨-185351852288,-185351852224⟩ : DyadicInterval 40),(⟨748839170265,748839189595⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26784869696,-26745278336⟩ : DyadicInterval 40),(⟨775496022784,775515837728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158514489152,158613136832⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185414959232,-185280085376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1921_ok : ecellOkT e1921 = true := by decide +kernel
theorem e1921_pos {a z : ℝ} (ha1 : ((1270401/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((5085/32768 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1921 e1921_ok ha1 ha2 hz1 hz2 hz

-- box ['79347/512000', '1270401/8192000', '1599/1600', '1999/2000']  interval_lower 80827011/549755813888
noncomputable def e1922 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269908012793,0,true,158415832640,158415832704⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929115242759,0,false,-185145228096,-185145228032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270021963645,0,true,158514489152,158514489216⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929001291907,0,false,-185280085440,-185280085376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269801515052,0,true,158323620928,158323620992⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929221740500,0,false,-185019206272,-185019206208⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269936708478,0,true,158440677696,158440677760⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929086547074,0,false,-185179187008,-185179186944⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554980250,0,true,43351616,43351680⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468275302,0,false,-43353344,-43353280⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565856598,0,true,54227456,54227520⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457398954,0,false,-54230208,-54230144⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625101,0,false,-2688,-2624⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626067,0,false,-1728,-1664⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269854759718,0,true,158369724096,158369724160⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929168495834,0,false,-185082210432,-185082210368⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269979340610,0,true,158477587968,158477588032⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929043914942,0,false,-185229640448,-185229640384⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073082401940,0,false,-26752052416,-26752052352⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073121017739,0,false,-26712486272,-26712486208⟩
    { al := (79347/512000), au := (1270401/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨170396385017,170510335869⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158415832640,158415832704⟩ : DyadicInterval 40),(⟨-185145228096,-185145228032⟩ : DyadicInterval 40),(⟨748866460688,748866480017⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158514489152,158514489216⟩ : DyadicInterval 40),(⟨-185280085440,-185280085376⟩ : DyadicInterval 40),(⟨748848651705,748848671035⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158323620928,158323620992⟩ : DyadicInterval 40),(⟨-185019206272,-185019206208⟩ : DyadicInterval 40),(⟨748883093904,748883113233⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158440677696,158440677760⟩ : DyadicInterval 40),(⟨-185179187008,-185179186944⟩ : DyadicInterval 40),(⟨748861977060,748861996390⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨43352474,54228822⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43351616,43351680⟩ : DyadicInterval 40),(⟨-43353344,-43353280⟩ : DyadicInterval 40),(⟨762123382706,762123402035⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54227456,54227520⟩ : DyadicInterval 40),(⟨-54230208,-54230144⟩ : DyadicInterval 40),(⟨762123382253,762123401582⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2688,-1664⟩ : DyadicInterval 40),(⟨762123384448,762123404224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170343131942,170467712834⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158369724096,158369724160⟩ : DyadicInterval 40),(⟨-185082210432,-185082210368⟩ : DyadicInterval 40),(⟨748874779294,748874798623⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158477587968,158477588032⟩ : DyadicInterval 40),(⟨-185229640448,-185229640384⟩ : DyadicInterval 40),(⟨748855314526,748855333855⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26752052416,-26712486208⟩ : DyadicInterval 40),(⟨775479626720,775499429088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158415832640,158514489216⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185280085440,-185145228032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1922_ok : ecellOkT e1922 = true := by decide +kernel
theorem e1922_pos {a z : ℝ} (ha1 : ((79347/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1270401/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1922 e1922_ok ha1 ha2 hz1 hz2 hz

-- box ['1270401/8192000', '5085/32768', '1599/1600', '1999/2000']  interval_lower 162711863/1099511627776
noncomputable def e1923 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270021963644,0,true,158514489152,158514489216⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929001291908,0,false,-185280085440,-185280085376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270135914496,0,true,158613136768,158613136832⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928887341056,0,false,-185414959232,-185414959168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269915394683,0,true,158422224000,158422224064⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929107860869,0,false,-185153963840,-185153963776⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270050602353,0,true,158539282624,158539282688⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928972653199,0,false,-185313981056,-185313980992⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555010271,0,true,43381632,43381696⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468245281,0,false,-43383360,-43383296⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565894128,0,true,54264960,54265024⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457361424,0,false,-54267712,-54267648⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625097,0,false,-2688,-2624⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626065,0,false,-1728,-1664⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269968674954,0,true,158468353920,158468353984⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929054580598,0,false,-185217017856,-185217017792⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270093262973,0,true,158576214272,158576214336⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928929992579,0,false,-185364474368,-185364474304⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073047065208,0,false,-26788260096,-26788260032⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073085709033,0,false,-26748663872,-26748663808⟩
    { al := (1270401/8192000), au := (5085/32768), zl := (1599/1600), zu := (1999/2000),
      A := ⟨170510335868,170624286720⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158514489152,158514489216⟩ : DyadicInterval 40),(⟨-185280085440,-185280085376⟩ : DyadicInterval 40),(⟨748848651706,748848671035⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158613136768,158613136832⟩ : DyadicInterval 40),(⟨-185414959232,-185414959168⟩ : DyadicInterval 40),(⟨748830830608,748830849938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158422224000,158422224064⟩ : DyadicInterval 40),(⟨-185153963840,-185153963776⟩ : DyadicInterval 40),(⟨748865307371,748865326701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158539282624,158539282688⟩ : DyadicInterval 40),(⟨-185313981056,-185313980992⟩ : DyadicInterval 40),(⟨748844173946,748844193276⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨43382495,54266352⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43381632,43381696⟩ : DyadicInterval 40),(⟨-43383360,-43383296⟩ : DyadicInterval 40),(⟨762123382704,762123402033⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54264960,54265024⟩ : DyadicInterval 40),(⟨-54267712,-54267648⟩ : DyadicInterval 40),(⟨762123382249,762123401578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2688,-1664⟩ : DyadicInterval 40),(⟨762123384448,762123404224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170457047178,170581635197⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158468353920,158468353984⟩ : DyadicInterval 40),(⟨-185217017856,-185217017792⟩ : DyadicInterval 40),(⟨748856981510,748857000839⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158576214272,158576214336⟩ : DyadicInterval 40),(⟨-185364474368,-185364474304⟩ : DyadicInterval 40),(⟨748837502403,748837521733⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26788260096,-26748663808⟩ : DyadicInterval 40),(⟨775497715520,775517532928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158514489152,158613136832⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185414959232,-185280085376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1923_ok : ecellOkT e1923 = true := by decide +kernel
theorem e1923_pos {a z : ℝ} (ha1 : ((1270401/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((5085/32768 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1923 e1923_ok ha1 ha2 hz1 hz2 hz

-- box ['5085/32768', '1272099/8192000', '3997/4000', '1599/1600']  interval_lower 81962645/549755813888
noncomputable def e1924 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270135914496,0,true,158613136768,158613136832⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928887341056,0,false,-185414959232,-185414959168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270249865348,0,true,158711775552,158711775616⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928773390204,0,false,-185549849664,-185549849600⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270007946280,0,true,158502353664,158502353728⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929015309272,0,false,-185263495424,-185263495360⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270143153950,0,true,158619403712,158619403776⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928880101602,0,false,-185423528512,-185423528448⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565893370,0,true,54264192,54264256⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457362182,0,false,-54266944,-54266880⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576792243,0,true,65162496,65162560⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446463309,0,false,-65166400,-65166336⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623913,0,false,-3904,-3840⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625098,0,false,-2688,-2624⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270071926308,0,true,158557743104,158557743168⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928951329244,0,false,-185339219904,-185339219840⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270196514301,0,true,158665594624,158665594688⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928826741251,0,false,-185486692800,-185486692736⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073015018052,0,false,-26821098112,-26821098048⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073053685268,0,false,-26781476800,-26781476736⟩
    { al := (5085/32768), au := (1272099/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨170624286720,170738237572⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158613136768,158613136832⟩ : DyadicInterval 40),(⟨-185414959232,-185414959168⟩ : DyadicInterval 40),(⟨748830830608,748830849938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158711775552,158711775616⟩ : DyadicInterval 40),(⟨-185549849664,-185549849600⟩ : DyadicInterval 40),(⟨748812997440,748813016769⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158502353664,158502353728⟩ : DyadicInterval 40),(⟨-185263495424,-185263495360⟩ : DyadicInterval 40),(⟨748850843079,748850862408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158619403712,158619403776⟩ : DyadicInterval 40),(⟨-185423528512,-185423528448⟩ : DyadicInterval 40),(⟨748829697988,748829717318⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54265594,65164467⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54264192,54264256⟩ : DyadicInterval 40),(⟨-54266944,-54266880⟩ : DyadicInterval 40),(⟨762123382249,762123401578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65162496,65162560⟩ : DyadicInterval 40),(⟨-65166400,-65166336⟩ : DyadicInterval 40),(⟨762123381641,762123400971⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3904,-2624⟩ : DyadicInterval 40),(⟨762123384928,762123404832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170560298532,170684886525⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158557743104,158557743168⟩ : DyadicInterval 40),(⟨-185339219904,-185339219840⟩ : DyadicInterval 40),(⟨748840839380,748840858710⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158665594624,158665594688⟩ : DyadicInterval 40),(⟨-185486692800,-185486692736⟩ : DyadicInterval 40),(⟨748821348323,748821367653⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26821098112,-26781476736⟩ : DyadicInterval 40),(⟨775514121984,775533951936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158613136768,158711775616⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185549849664,-185414959168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1924_ok : ecellOkT e1924 = true := by decide +kernel
theorem e1924_pos {a z : ℝ} (ha1 : ((5085/32768 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1272099/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1924 e1924_ok ha1 ha2 hz1 hz2 hz

-- box ['1272099/8192000', '318237/2048000', '3997/4000', '1599/1600']  interval_lower 164988819/1099511627776
noncomputable def e1925 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270249865347,0,true,158711775552,158711775616⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928773390205,0,false,-185549849664,-185549849600⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270363816199,0,true,158810405504,158810405568⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928659439353,0,false,-185684756544,-185684756480⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270121811668,0,true,158600928384,158600928448⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928901443884,0,false,-185398266048,-185398265984⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270257033582,0,true,158717980288,158717980352⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928766221970,0,false,-185558335680,-185558335616⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565930904,0,true,54301760,54301824⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457324648,0,false,-54304512,-54304448⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576837286,0,true,65207552,65207616⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446418266,0,false,-65211456,-65211392⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623908,0,false,-3904,-3840⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625095,0,false,-2688,-2624⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270185834422,0,true,158656349824,158656349888⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928837421130,0,false,-185474050368,-185474050304⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270310429545,0,true,158764197888,158764197952⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928712826007,0,false,-185621549824,-185621549760⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072979638528,0,false,-26857351872,-26857351808⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073018333774,0,false,-26817700544,-26817700480⟩
    { al := (1272099/8192000), au := (318237/2048000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨170738237571,170852188423⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158711775552,158711775616⟩ : DyadicInterval 40),(⟨-185549849664,-185549849600⟩ : DyadicInterval 40),(⟨748812997440,748813016769⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158810405504,158810405568⟩ : DyadicInterval 40),(⟨-185684756544,-185684756480⟩ : DyadicInterval 40),(⟨748795152117,748795171446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158600928384,158600928448⟩ : DyadicInterval 40),(⟨-185398266048,-185398265984⟩ : DyadicInterval 40),(⟨748833036852,748833056182⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158717980288,158717980352⟩ : DyadicInterval 40),(⟨-185558335680,-185558335616⟩ : DyadicInterval 40),(⟨748811875199,748811894529⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54303128,65209510⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54301760,54301824⟩ : DyadicInterval 40),(⟨-54304512,-54304448⟩ : DyadicInterval 40),(⟨762123382245,762123401575⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65207552,65207616⟩ : DyadicInterval 40),(⟨-65211456,-65211392⟩ : DyadicInterval 40),(⟨762123381636,762123400965⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3904,-2624⟩ : DyadicInterval 40),(⟨762123384928,762123404832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170674206646,170798801769⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158656349824,158656349888⟩ : DyadicInterval 40),(⟨-185474050368,-185474050304⟩ : DyadicInterval 40),(⟨748823019681,748823039011⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158764197888,158764197952⟩ : DyadicInterval 40),(⟨-185621549824,-185621549760⟩ : DyadicInterval 40),(⟨748803514270,748803533599⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26857351872,-26817700480⟩ : DyadicInterval 40),(⟨775532233856,775552078816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158711775552,158810405568⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185684756544,-185549849600⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1925_ok : ecellOkT e1925 = true := by decide +kernel
theorem e1925_pos {a z : ℝ} (ha1 : ((1272099/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((318237/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1925 e1925_ok ha1 ha2 hz1 hz2 hz

-- box ['5085/32768', '1272099/8192000', '1599/1600', '1999/2000']  interval_lower 40943107/274877906944
noncomputable def e1926 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270135914496,0,true,158613136768,158613136832⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928887341056,0,false,-185414959232,-185414959168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270249865348,0,true,158711775552,158711775616⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928773390204,0,false,-185549849664,-185549849600⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270029274316,0,true,158520818304,158520818368⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928993981236,0,false,-185288737920,-185288737856⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270164496230,0,true,158637878720,158637878784⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928858759322,0,false,-185448791616,-185448791552⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555040297,0,true,43411648,43411712⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468215255,0,false,-43413440,-43413376⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565931663,0,true,54302528,54302592⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457323889,0,false,-54305280,-54305216⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625093,0,false,-2688,-2624⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626062,0,false,-1728,-1664⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270082590199,0,true,158566974848,158566974912⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928940665353,0,false,-185351841792,-185351841728⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270207185335,0,true,158674831680,158674831744⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928816070217,0,false,-185499324864,-185499324800⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073011704869,0,false,-26824493120,-26824493056⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073050376720,0,false,-26784866880,-26784866816⟩
    { al := (5085/32768), au := (1272099/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨170624286720,170738237572⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158613136768,158613136832⟩ : DyadicInterval 40),(⟨-185414959232,-185414959168⟩ : DyadicInterval 40),(⟨748830830608,748830849938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158711775552,158711775616⟩ : DyadicInterval 40),(⟨-185549849664,-185549849600⟩ : DyadicInterval 40),(⟨748812997440,748813016769⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158520818304,158520818368⟩ : DyadicInterval 40),(⟨-185288737920,-185288737856⟩ : DyadicInterval 40),(⟨748847508709,748847528038⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158637878720,158637878784⟩ : DyadicInterval 40),(⟨-185448791616,-185448791552⟩ : DyadicInterval 40),(⟨748826358731,748826378061⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨43412521,54303887⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43411648,43411712⟩ : DyadicInterval 40),(⟨-43413440,-43413376⟩ : DyadicInterval 40),(⟨762123382733,762123402062⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54302528,54302592⟩ : DyadicInterval 40),(⟨-54305280,-54305216⟩ : DyadicInterval 40),(⟨762123382245,762123401575⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2688,-1664⟩ : DyadicInterval 40),(⟨762123384448,762123404224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170570962423,170695557559⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158566974848,158566974912⟩ : DyadicInterval 40),(⟨-185351841792,-185351841728⟩ : DyadicInterval 40),(⟨748839171653,748839190982⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158674831680,158674831744⟩ : DyadicInterval 40),(⟨-185499324864,-185499324800⟩ : DyadicInterval 40),(⟨748819678231,748819697561⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26824493120,-26784866816⟩ : DyadicInterval 40),(⟨775515817024,775535649440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158613136768,158711775616⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185549849664,-185414959168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1926_ok : ecellOkT e1926 = true := by decide +kernel
theorem e1926_pos {a z : ℝ} (ha1 : ((5085/32768 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1272099/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1926 e1926_ok ha1 ha2 hz1 hz2 hz

-- box ['1272099/8192000', '318237/2048000', '1599/1600', '1999/2000']  interval_lower 164835631/1099511627776
noncomputable def e1927 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270249865347,0,true,158711775552,158711775616⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928773390205,0,false,-185549849664,-185549849600⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270363816199,0,true,158810405504,158810405568⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928659439353,0,false,-185684756544,-185684756480⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270143153948,0,true,158619403712,158619403776⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928880101604,0,false,-185423528512,-185423528448⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270278390105,0,true,158736465920,158736465984⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928744865447,0,false,-185583618688,-185583618624⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555070324,0,true,43441664,43441728⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468185228,0,false,-43443456,-43443392⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565969199,0,true,54340032,54340096⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457286353,0,false,-54342784,-54342720⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625090,0,false,-2688,-2624⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626060,0,false,-1728,-1664⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270196505436,0,true,158665586944,158665587008⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928826750116,0,false,-185486682304,-185486682240⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270321107699,0,true,158773440256,158773440320⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928702147853,0,false,-185634191872,-185634191808⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072976320922,0,false,-26860751552,-26860751488⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073015020805,0,false,-26821095296,-26821095232⟩
    { al := (1272099/8192000), au := (318237/2048000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨170738237571,170852188423⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158711775552,158711775616⟩ : DyadicInterval 40),(⟨-185549849664,-185549849600⟩ : DyadicInterval 40),(⟨748812997440,748813016769⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158810405504,158810405568⟩ : DyadicInterval 40),(⟨-185684756544,-185684756480⟩ : DyadicInterval 40),(⟨748795152117,748795171446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158619403712,158619403776⟩ : DyadicInterval 40),(⟨-185423528512,-185423528448⟩ : DyadicInterval 40),(⟨748829697988,748829717318⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158736465920,158736465984⟩ : DyadicInterval 40),(⟨-185583618688,-185583618624⟩ : DyadicInterval 40),(⟨748808531451,748808550781⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨43442548,54341423⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43441664,43441728⟩ : DyadicInterval 40),(⟨-43443456,-43443392⟩ : DyadicInterval 40),(⟨762123382731,762123402060⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54340032,54340096⟩ : DyadicInterval 40),(⟨-54342784,-54342720⟩ : DyadicInterval 40),(⟨762123382242,762123401571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2688,-1664⟩ : DyadicInterval 40),(⟨762123384448,762123404224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170684877660,170809479923⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158665586944,158665587008⟩ : DyadicInterval 40),(⟨-185486682304,-185486682240⟩ : DyadicInterval 40),(⟨748821349714,748821369043⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158773440256,158773440320⟩ : DyadicInterval 40),(⟨-185634191872,-185634191808⟩ : DyadicInterval 40),(⟨748801841945,748801861274⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26860751552,-26821095232⟩ : DyadicInterval 40),(⟨775533931232,775553778656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158711775552,158810405568⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185684756544,-185549849600⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1927_ok : ecellOkT e1927 = true := by decide +kernel
theorem e1927_pos {a z : ℝ} (ha1 : ((1272099/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((318237/2048000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1927 e1927_ok ha1 ha2 hz1 hz2 hz

-- box ['318237/2048000', '1273797/8192000', '999/1000', '7993/8000']  interval_lower 166362265/1099511627776
noncomputable def e1928 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270363816198,0,true,158810405504,158810405568⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928659439354,0,false,-185684756544,-185684756480⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270477767050,0,true,158909026624,158909026688⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928545488502,0,false,-185819680064,-185819680000⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270192964009,0,true,158662521408,158662521472⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928830291543,0,false,-185482490048,-185482489984⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270328171679,0,true,158779554432,158779554496⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928695083873,0,false,-185642555072,-185642555008⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587704470,0,true,76074048,76074112⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435551082,0,false,-76079360,-76079296⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099598633377,0,true,87002112,87002176⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099424622175,0,false,-87009088,-87009024⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620891,0,false,-6912,-6848⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622513,0,false,-5312,-5248⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270278386349,0,true,158736462720,158736462784⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928744869203,0,false,-185583614208,-185583614144⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270402974304,0,true,158844296704,158844296768⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928620281248,0,false,-185731119872,-185731119808⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072950878821,0,false,-26886823104,-26886823040⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072989592814,0,false,-26847151488,-26847151424⟩
    { al := (318237/2048000), au := (1273797/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨170852188422,170966139274⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158810405504,158810405568⟩ : DyadicInterval 40),(⟨-185684756544,-185684756480⟩ : DyadicInterval 40),(⟨748795152117,748795171446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158909026624,158909026688⟩ : DyadicInterval 40),(⟨-185819680064,-185819680000⟩ : DyadicInterval 40),(⟨748777294720,748777314049⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158662521408,158662521472⟩ : DyadicInterval 40),(⟨-185482490048,-185482489984⟩ : DyadicInterval 40),(⟨748821903923,748821923252⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158779554432,158779554496⟩ : DyadicInterval 40),(⟨-185642555072,-185642555008⟩ : DyadicInterval 40),(⟨748800735528,748800754858⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨76076694,87005601⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76074048,76074112⟩ : DyadicInterval 40),(⟨-76079360,-76079296⟩ : DyadicInterval 40),(⟨762123380943,762123400273⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨87002112,87002176⟩ : DyadicInterval 40),(⟨-87009088,-87009024⟩ : DyadicInterval 40),(⟨762123380154,762123399484⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6912,-5248⟩ : DyadicInterval 40),(⟨762123386240,762123406336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170766758573,170891346528⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158736462720,158736462784⟩ : DyadicInterval 40),(⟨-185583614208,-185583614144⟩ : DyadicInterval 40),(⟨748808531996,748808551325⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158844296704,158844296768⟩ : DyadicInterval 40),(⟨-185731119872,-185731119808⟩ : DyadicInterval 40),(⟨748789016969,748789036299⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26886823104,-26847151424⟩ : DyadicInterval 40),(⟨775546959328,775566814432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158810405504,158909026688⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185819680064,-185684756480⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1928_ok : ecellOkT e1928 = true := by decide +kernel
theorem e1928_pos {a z : ℝ} (ha1 : ((318237/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1273797/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1928 e1928_ok ha1 ha2 hz1 hz2 hz

-- box ['1273797/8192000', '637323/4096000', '999/1000', '7993/8000']  interval_lower 167431657/1099511627776
noncomputable def e1929 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270477767049,0,true,158909026624,158909026688⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928545488503,0,false,-185819680064,-185819680000⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270591717901,0,true,159007638848,159007638912⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928431537651,0,false,-185954620096,-185954620032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270306800909,0,true,158761057152,158761057216⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928716454643,0,false,-185617253824,-185617253760⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270442022823,0,true,158878091968,158878092032⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928581232729,0,false,-185777355328,-185777355264⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587757023,0,true,76126592,76126656⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435498529,0,false,-76131904,-76131840⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099598693444,0,true,87062208,87062272⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099424562108,0,false,-87069120,-87069056⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620881,0,false,-6912,-6848⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622505,0,false,-5312,-5248⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270392280225,0,true,158835041088,158835041152⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928630975327,0,false,-185718457856,-185718457792⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270516875300,0,true,158942871616,158942871680⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928506380252,0,false,-185865990016,-185865989952⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072915460948,0,false,-26923118400,-26923118336⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072954202967,0,false,-26883416704,-26883416640⟩
    { al := (1273797/8192000), au := (637323/4096000), zl := (999/1000), zu := (7993/8000),
      A := ⟨170966139273,171080090125⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158909026624,158909026688⟩ : DyadicInterval 40),(⟨-185819680064,-185819680000⟩ : DyadicInterval 40),(⟨748777294720,748777314050⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159007638848,159007638912⟩ : DyadicInterval 40),(⟨-185954620096,-185954620032⟩ : DyadicInterval 40),(⟨748759425230,748759444560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158761057152,158761057216⟩ : DyadicInterval 40),(⟨-185617253824,-185617253760⟩ : DyadicInterval 40),(⟨748804082514,748804101844⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158878091968,158878092032⟩ : DyadicInterval 40),(⟨-185777355328,-185777355264⟩ : DyadicInterval 40),(⟨748782897567,748782916897⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨76129247,87065668⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76126592,76126656⟩ : DyadicInterval 40),(⟨-76131904,-76131840⟩ : DyadicInterval 40),(⟨762123380936,762123400266⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨87062208,87062272⟩ : DyadicInterval 40),(⟨-87069120,-87069056⟩ : DyadicInterval 40),(⟨762123380113,762123399442⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6912,-5248⟩ : DyadicInterval 40),(⟨762123386240,762123406336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170880652449,171005247524⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158835041088,158835041152⟩ : DyadicInterval 40),(⟨-185718457856,-185718457792⟩ : DyadicInterval 40),(⟨748790692640,748790711970⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158942871616,158942871680⟩ : DyadicInterval 40),(⟨-185865990016,-185865989952⟩ : DyadicInterval 40),(⟨748771163232,748771182562⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26923118400,-26883416640⟩ : DyadicInterval 40),(⟨775565091936,775584962080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158909026624,159007638912⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185954620096,-185819680000⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1929_ok : ecellOkT e1929 = true := by decide +kernel
theorem e1929_pos {a z : ℝ} (ha1 : ((1273797/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((637323/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1929 e1929_ok ha1 ha2 hz1 hz2 hz

-- box ['318237/2048000', '1273797/8192000', '7993/8000', '3997/4000']  interval_lower 83104407/549755813888
noncomputable def e1930 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270363816198,0,true,158810405504,158810405568⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928659439354,0,false,-185684756544,-185684756480⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270477767050,0,true,158909026624,158909026688⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928545488502,0,false,-185819680064,-185819680000⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270214320533,0,true,158681008000,158681008064⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928808935019,0,false,-185507771328,-185507771264⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270349542446,0,true,158798051392,158798051456⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928673713106,0,false,-185667856896,-185667856832⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576836479,0,true,65206720,65206784⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446419073,0,false,-65210688,-65210624⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587757879,0,true,76127424,76127488⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435497673,0,false,-76132800,-76132736⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622504,0,false,-5312,-5248⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623909,0,false,-3904,-3840⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270289064435,0,true,158745705280,158745705344⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928734191117,0,false,-185596255744,-185596255680⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270413659535,0,true,158853544512,158853544576⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928609596017,0,false,-185743771520,-185743771456⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072947557218,0,false,-26890226944,-26890226880⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072986275852,0,false,-26850550464,-26850550400⟩
    { al := (318237/2048000), au := (1273797/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨170852188422,170966139274⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158810405504,158810405568⟩ : DyadicInterval 40),(⟨-185684756544,-185684756480⟩ : DyadicInterval 40),(⟨748795152117,748795171446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158909026624,158909026688⟩ : DyadicInterval 40),(⟨-185819680064,-185819680000⟩ : DyadicInterval 40),(⟨748777294720,748777314049⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158681008000,158681008064⟩ : DyadicInterval 40),(⟨-185507771328,-185507771264⟩ : DyadicInterval 40),(⟨748818561440,748818580770⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158798051392,158798051456⟩ : DyadicInterval 40),(⟨-185667856896,-185667856832⟩ : DyadicInterval 40),(⟨748797388119,748797407448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨65208703,76130103⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65206720,65206784⟩ : DyadicInterval 40),(⟨-65210688,-65210624⟩ : DyadicInterval 40),(⟨762123381668,762123400997⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76127424,76127488⟩ : DyadicInterval 40),(⟨-76132800,-76132736⟩ : DyadicInterval 40),(⟨762123380968,762123400297⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5312,-3840⟩ : DyadicInterval 40),(⟨762123385536,762123405536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170777436659,170902031759⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158745705280,158745705344⟩ : DyadicInterval 40),(⟨-185596255744,-185596255680⟩ : DyadicInterval 40),(⟨748806859992,748806879321⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158853544512,158853544576⟩ : DyadicInterval 40),(⟨-185743771520,-185743771456⟩ : DyadicInterval 40),(⟨748787342604,748787361934⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26890226944,-26850550400⟩ : DyadicInterval 40),(⟨775548658816,775568516352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158810405504,158909026688⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185819680064,-185684756480⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1930_ok : ecellOkT e1930 = true := by decide +kernel
theorem e1930_pos {a z : ℝ} (ha1 : ((318237/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1273797/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1930 e1930_ok ha1 ha2 hz1 hz2 hz

-- box ['1273797/8192000', '637323/4096000', '7993/8000', '3997/4000']  interval_lower 167278021/1099511627776
noncomputable def e1931 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270477767049,0,true,158909026624,158909026688⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928545488503,0,false,-185819680064,-185819680000⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270591717901,0,true,159007638848,159007638912⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928431537651,0,false,-185954620096,-185954620032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270328171677,0,true,158779554432,158779554496⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928695083875,0,false,-185642555072,-185642555008⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270463407834,0,true,158896599616,158896599680⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928559847718,0,false,-185802677120,-185802677056⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576881525,0,true,65251776,65251840⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446374027,0,false,-65255744,-65255680⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587810438,0,true,76179968,76180032⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435445114,0,false,-76185344,-76185280⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622497,0,false,-5312,-5248⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623904,0,false,-3904,-3840⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270402965433,0,true,158844289024,158844289088⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928620290119,0,false,-185731109376,-185731109312⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270527567654,0,true,158952124800,158952124864⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928495687898,0,false,-185878651648,-185878651584⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072912134916,0,false,-26926526848,-26926526784⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072950881579,0,false,-26886820288,-26886820224⟩
    { al := (1273797/8192000), au := (637323/4096000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨170966139273,171080090125⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158909026624,158909026688⟩ : DyadicInterval 40),(⟨-185819680064,-185819680000⟩ : DyadicInterval 40),(⟨748777294720,748777314050⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159007638848,159007638912⟩ : DyadicInterval 40),(⟨-185954620096,-185954620032⟩ : DyadicInterval 40),(⟨748759425230,748759444560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158779554432,158779554496⟩ : DyadicInterval 40),(⟨-185642555072,-185642555008⟩ : DyadicInterval 40),(⟨748800735528,748800754858⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158896599616,158896599680⟩ : DyadicInterval 40),(⟨-185802677120,-185802677056⟩ : DyadicInterval 40),(⟨748779545647,748779564977⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨65253749,76182662⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65251776,65251840⟩ : DyadicInterval 40),(⟨-65255744,-65255680⟩ : DyadicInterval 40),(⟨762123381663,762123400992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76179968,76180032⟩ : DyadicInterval 40),(⟨-76185344,-76185280⟩ : DyadicInterval 40),(⟨762123380961,762123400290⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5312,-3840⟩ : DyadicInterval 40),(⟨762123385536,762123405536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170891337657,171015939878⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158844289024,158844289088⟩ : DyadicInterval 40),(⟨-185731109376,-185731109312⟩ : DyadicInterval 40),(⟨748789018364,748789037693⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158952124800,158952124864⟩ : DyadicInterval 40),(⟨-185878651648,-185878651584⟩ : DyadicInterval 40),(⟨748769486591,748769505920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26926526848,-26886820224⟩ : DyadicInterval 40),(⟨775566793728,775586666304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158909026624,159007638912⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185954620096,-185819680000⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1931_ok : ecellOkT e1931 = true := by decide +kernel
theorem e1931_pos {a z : ℝ} (ha1 : ((1273797/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((637323/4096000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1931 e1931_ok ha1 ha2 hz1 hz2 hz

-- box ['637323/4096000', '255099/1638400', '999/1000', '7993/8000']  interval_lower 84252103/549755813888
noncomputable def e1932 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270591717900,0,true,159007638848,159007638912⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928431537652,0,false,-185954620096,-185954620032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270705668752,0,true,159106242240,159106242304⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928317586800,0,false,-186089576704,-186089576640⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270420637809,0,true,158859584064,158859584128⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928602617743,0,false,-185752034112,-185752034048⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270555873967,0,true,158976620736,158976620800⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928467381585,0,false,-185912172096,-185912172032⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587809581,0,true,76179136,76179200⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435445971,0,false,-76184448,-76184384⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099598753514,0,true,87122240,87122304⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099424502038,0,false,-87129216,-87129152⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620872,0,false,-6912,-6848⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622498,0,false,-5312,-5248⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270506174099,0,true,158933610688,158933610752⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928517081453,0,false,-185853318016,-185853317952⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270630776301,0,true,159041437696,159041437760⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928392479251,0,false,-186000876672,-186000876608⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072880019476,0,false,-26959438976,-26959438912⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072918789526,0,false,-26919707264,-26919707200⟩
    { al := (637323/4096000), au := (255099/1638400), zl := (999/1000), zu := (7993/8000),
      A := ⟨171080090124,171194040976⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159007638848,159007638912⟩ : DyadicInterval 40),(⟨-185954620096,-185954620032⟩ : DyadicInterval 40),(⟨748759425230,748759444560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159106242240,159106242304⟩ : DyadicInterval 40),(⟨-186089576704,-186089576640⟩ : DyadicInterval 40),(⟨748741543637,748741562966⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158859584064,158859584128⟩ : DyadicInterval 40),(⟨-185752034112,-185752034048⟩ : DyadicInterval 40),(⟨748786249027,748786268357⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158976620736,158976620800⟩ : DyadicInterval 40),(⟨-185912172096,-185912172032⟩ : DyadicInterval 40),(⟨748765047483,748765066813⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨76181805,87125738⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76179136,76179200⟩ : DyadicInterval 40),(⟨-76184448,-76184384⟩ : DyadicInterval 40),(⟨762123380929,762123400258⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨87122240,87122304⟩ : DyadicInterval 40),(⟨-87129216,-87129152⟩ : DyadicInterval 40),(⟨762123380135,762123399465⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6912,-5248⟩ : DyadicInterval 40),(⟨762123386240,762123406336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170994546323,171119148525⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158933610688,158933610752⟩ : DyadicInterval 40),(⟨-185853318016,-185853317952⟩ : DyadicInterval 40),(⟨748772841144,748772860473⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159041437696,159041437760⟩ : DyadicInterval 40),(⟨-186000876672,-186000876608⟩ : DyadicInterval 40),(⟨748753297386,748753316715⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26959438976,-26919707200⟩ : DyadicInterval 40),(⟨775583237216,775603122368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159007638848,159106242304⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186089576704,-185954620032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1932_ok : ecellOkT e1932 = true := by decide +kernel
theorem e1932_pos {a z : ℝ} (ha1 : ((637323/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((255099/1638400 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1932 e1932_ok ha1 ha2 hz1 hz2 hz

-- box ['255099/1638400', '159543/1024000', '999/1000', '7993/8000']  interval_lower 10598693/68719476736
noncomputable def e1933 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270705668751,0,true,159106242240,159106242304⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928317586801,0,false,-186089576704,-186089576640⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270819619603,0,true,159204836800,159204836864⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928203635949,0,false,-186224549888,-186224549824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270534474709,0,true,158958102080,158958102144⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928488780843,0,false,-185886830912,-185886830848⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270669725111,0,true,159075140608,159075140672⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928353530441,0,false,-186047005440,-186047005376⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587862141,0,true,76231680,76231744⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435393411,0,false,-76237056,-76236992⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099598813588,0,true,87182336,87182400⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099424441964,0,false,-87189312,-87189248⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620862,0,false,-6976,-6912⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622491,0,false,-5312,-5248⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270620067971,0,true,159032171392,159032171456⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928403187581,0,false,-185988194688,-185988194624⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270744677296,0,true,159139994880,159139994944⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928278578256,0,false,-186135779904,-186135779840⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072844554407,0,false,-26995785024,-26995784960⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072883352489,0,false,-26956023232,-26956023168⟩
    { al := (255099/1638400), au := (159543/1024000), zl := (999/1000), zu := (7993/8000),
      A := ⟨171194040975,171307991827⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159106242240,159106242304⟩ : DyadicInterval 40),(⟨-186089576704,-186089576640⟩ : DyadicInterval 40),(⟨748741543637,748741562966⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159204836800,159204836864⟩ : DyadicInterval 40),(⟨-186224549888,-186224549824⟩ : DyadicInterval 40),(⟨748723649939,748723669268⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158958102080,158958102144⟩ : DyadicInterval 40),(⟨-185886830912,-185886830848⟩ : DyadicInterval 40),(⟨748768403496,748768422826⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159075140608,159075140672⟩ : DyadicInterval 40),(⟨-186047005440,-186047005376⟩ : DyadicInterval 40),(⟨748747185375,748747204705⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨76234365,87185812⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76231680,76231744⟩ : DyadicInterval 40),(⟨-76237056,-76236992⟩ : DyadicInterval 40),(⟨762123380954,762123400283⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨87182336,87182400⟩ : DyadicInterval 40),(⟨-87189312,-87189248⟩ : DyadicInterval 40),(⟨762123380126,762123399455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6976,-5248⟩ : DyadicInterval 40),(⟨762123386240,762123406368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171108440195,171233049520⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159032171392,159032171456⟩ : DyadicInterval 40),(⟨-185988194688,-185988194624⟩ : DyadicInterval 40),(⟨748754977579,748754996908⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159139994880,159139994944⟩ : DyadicInterval 40),(⟨-186135779904,-186135779840⟩ : DyadicInterval 40),(⟨748735419494,748735438823⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26995785024,-26956023168⟩ : DyadicInterval 40),(⟨775601395200,775621295392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159106242240,159204836864⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186224549888,-186089576640⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1933_ok : ecellOkT e1933 = true := by decide +kernel
theorem e1933_pos {a z : ℝ} (ha1 : ((255099/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((159543/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1933 e1933_ok ha1 ha2 hz1 hz2 hz

-- box ['637323/4096000', '255099/1638400', '7993/8000', '3997/4000']  interval_lower 168349851/1099511627776
noncomputable def e1934 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270591717900,0,true,159007638848,159007638912⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928431537652,0,false,-185954620096,-185954620032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270705668752,0,true,159106242240,159106242304⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928317586800,0,false,-186089576704,-186089576640⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270442022821,0,true,158878091968,158878092032⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928581232731,0,false,-185777355328,-185777355264⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270577273222,0,true,158995139008,158995139072⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928445982330,0,false,-185937513856,-185937513792⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576926574,0,true,65296832,65296896⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446328978,0,false,-65300800,-65300736⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587862999,0,true,76232576,76232640⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435392553,0,false,-76237888,-76237824⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622490,0,false,-5312,-5248⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623898,0,false,-3904,-3840⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270516866426,0,true,158942863936,158942864000⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928506389126,0,false,-185865979520,-185865979456⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270641475774,0,true,159050696192,159050696256⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928381779778,0,false,-186013548352,-186013548288⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072876689012,0,false,-26962852160,-26962852096⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072915463710,0,false,-26923115520,-26923115456⟩
    { al := (637323/4096000), au := (255099/1638400), zl := (7993/8000), zu := (3997/4000),
      A := ⟨171080090124,171194040976⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159007638848,159007638912⟩ : DyadicInterval 40),(⟨-185954620096,-185954620032⟩ : DyadicInterval 40),(⟨748759425230,748759444560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159106242240,159106242304⟩ : DyadicInterval 40),(⟨-186089576704,-186089576640⟩ : DyadicInterval 40),(⟨748741543637,748741562966⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158878091968,158878092032⟩ : DyadicInterval 40),(⟨-185777355328,-185777355264⟩ : DyadicInterval 40),(⟨748782897568,748782916898⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158995139008,158995139072⟩ : DyadicInterval 40),(⟨-185937513856,-185937513792⟩ : DyadicInterval 40),(⟨748761691083,748761710412⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨65298798,76235223⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65296832,65296896⟩ : DyadicInterval 40),(⟨-65300800,-65300736⟩ : DyadicInterval 40),(⟨762123381657,762123400987⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76232576,76232640⟩ : DyadicInterval 40),(⟨-76237888,-76237824⟩ : DyadicInterval 40),(⟨762123380922,762123400251⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5312,-3840⟩ : DyadicInterval 40),(⟨762123385536,762123405536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171005238650,171129847998⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158942863936,158942864000⟩ : DyadicInterval 40),(⟨-185865979520,-185865979456⟩ : DyadicInterval 40),(⟨748771164629,748771183959⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159050696192,159050696256⟩ : DyadicInterval 40),(⟨-186013548352,-186013548288⟩ : DyadicInterval 40),(⟨748751618530,748751637859⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26962852160,-26923115456⟩ : DyadicInterval 40),(⟨775584941344,775604828960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159007638848,159106242304⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186089576704,-185954620032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1934_ok : ecellOkT e1934 = true := by decide +kernel
theorem e1934_pos {a z : ℝ} (ha1 : ((637323/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((255099/1638400 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1934 e1934_ok ha1 ha2 hz1 hz2 hz

-- box ['255099/1638400', '159543/1024000', '7993/8000', '3997/4000']  interval_lower 84712437/549755813888
noncomputable def e1935 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270705668751,0,true,159106242240,159106242304⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928317586801,0,false,-186089576704,-186089576640⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270819619603,0,true,159204836800,159204836864⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928203635949,0,false,-186224549888,-186224549824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270555873965,0,true,158976620736,158976620800⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928467381587,0,false,-185912172096,-185912172032⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270691138610,0,true,159093669568,159093669632⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928332116942,0,false,-186072367168,-186072367104⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576971628,0,true,65341888,65341952⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446283924,0,false,-65345856,-65345792⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587915566,0,true,76285120,76285184⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435339986,0,false,-76290496,-76290432⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622482,0,false,-5312,-5248⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623893,0,false,-3904,-3840⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270630767425,0,true,159041430016,159041430080⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928392488127,0,false,-186000866176,-186000866112⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270755383892,0,true,159149258752,159149258816⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928267871660,0,false,-186148461568,-186148461504⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072841219507,0,false,-26999202816,-26999202752⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072880022240,0,false,-26959436160,-26959436096⟩
    { al := (255099/1638400), au := (159543/1024000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨171194040975,171307991827⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159106242240,159106242304⟩ : DyadicInterval 40),(⟨-186089576704,-186089576640⟩ : DyadicInterval 40),(⟨748741543637,748741562966⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159204836800,159204836864⟩ : DyadicInterval 40),(⟨-186224549888,-186224549824⟩ : DyadicInterval 40),(⟨748723649939,748723669268⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158976620736,158976620800⟩ : DyadicInterval 40),(⟨-185912172096,-185912172032⟩ : DyadicInterval 40),(⟨748765047484,748765066813⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159093669568,159093669632⟩ : DyadicInterval 40),(⟨-186072367168,-186072367104⟩ : DyadicInterval 40),(⟨748743824451,748743843780⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨65343852,76287790⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65341888,65341952⟩ : DyadicInterval 40),(⟨-65345856,-65345792⟩ : DyadicInterval 40),(⟨762123381652,762123400981⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76285120,76285184⟩ : DyadicInterval 40),(⟨-76290496,-76290432⟩ : DyadicInterval 40),(⟨762123380946,762123400276⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5312,-3840⟩ : DyadicInterval 40),(⟨762123385536,762123405536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171119139649,171243756116⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159041430016,159041430080⟩ : DyadicInterval 40),(⟨-186000866176,-186000866112⟩ : DyadicInterval 40),(⟨748753298785,748753318114⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159149258752,159149258816⟩ : DyadicInterval 40),(⟨-186148461568,-186148461504⟩ : DyadicInterval 40),(⟨748733738355,748733757685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26999202816,-26959436096⟩ : DyadicInterval 40),(⟨775603101664,775623004288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159106242240,159204836864⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186224549888,-186089576640⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1935_ok : ecellOkT e1935 = true := by decide +kernel
theorem e1935_pos {a z : ℝ} (ha1 : ((255099/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((159543/1024000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1935 e1935_ok ha1 ha2 hz1 hz2 hz

-- box ['318237/2048000', '1273797/8192000', '3997/4000', '1599/1600']  interval_lower 83027477/549755813888
noncomputable def e1936 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270363816198,0,true,158810405504,158810405568⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928659439354,0,false,-185684756544,-185684756480⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270477767050,0,true,158909026624,158909026688⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928545488502,0,false,-185819680064,-185819680000⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270235677056,0,true,158699494272,158699494336⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928787578496,0,false,-185533053184,-185533053120⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270370913214,0,true,158816548032,158816548096⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928652342338,0,false,-185693159296,-185693159232⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565968440,0,true,54339264,54339328⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457287112,0,false,-54342016,-54341952⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576882334,0,true,65252608,65252672⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446373218,0,false,-65256512,-65256448⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623903,0,false,-3904,-3840⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625091,0,false,-2688,-2624⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270299742544,0,true,158754947776,158754947840⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928723513008,0,false,-185608897472,-185608897408⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270424344790,0,true,158862792320,158862792384⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928598910762,0,false,-185756423360,-185756423296⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072944235399,0,false,-26893631040,-26893630976⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072982958675,0,false,-26853949632,-26853949568⟩
    { al := (318237/2048000), au := (1273797/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨170852188422,170966139274⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158810405504,158810405568⟩ : DyadicInterval 40),(⟨-185684756544,-185684756480⟩ : DyadicInterval 40),(⟨748795152117,748795171446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158909026624,158909026688⟩ : DyadicInterval 40),(⟨-185819680064,-185819680000⟩ : DyadicInterval 40),(⟨748777294720,748777314049⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158699494272,158699494336⟩ : DyadicInterval 40),(⟨-185533053184,-185533053120⟩ : DyadicInterval 40),(⟨748815218536,748815237865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158816548032,158816548096⟩ : DyadicInterval 40),(⟨-185693159296,-185693159232⟩ : DyadicInterval 40),(⟨748794040286,748794059616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54340664,65254558⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54339264,54339328⟩ : DyadicInterval 40),(⟨-54342016,-54341952⟩ : DyadicInterval 40),(⟨762123382242,762123401571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65252608,65252672⟩ : DyadicInterval 40),(⟨-65256512,-65256448⟩ : DyadicInterval 40),(⟨762123381631,762123400960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3904,-2624⟩ : DyadicInterval 40),(⟨762123384928,762123404832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170788114768,170912717014⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158754947776,158754947840⟩ : DyadicInterval 40),(⟨-185608897472,-185608897408⟩ : DyadicInterval 40),(⟨748805187890,748805207219⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158862792320,158862792384⟩ : DyadicInterval 40),(⟨-185756423360,-185756423296⟩ : DyadicInterval 40),(⟨748785668103,748785687433⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26893631040,-26853949568⟩ : DyadicInterval 40),(⟨775550358400,775570218400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158810405504,158909026688⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185819680064,-185684756480⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1936_ok : ecellOkT e1936 = true := by decide +kernel
theorem e1936_pos {a z : ℝ} (ha1 : ((318237/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1273797/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1936 e1936_ok ha1 ha2 hz1 hz2 hz

-- box ['1273797/8192000', '637323/4096000', '3997/4000', '1599/1600']  interval_lower 167123991/1099511627776
noncomputable def e1937 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270477767049,0,true,158909026624,158909026688⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928545488503,0,false,-185819680064,-185819680000⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270591717901,0,true,159007638848,159007638912⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928431537651,0,false,-185954620096,-185954620032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270349542444,0,true,158798051392,158798051456⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928673713108,0,false,-185667856896,-185667856832⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270484792845,0,true,158915106944,158915107008⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928538462707,0,false,-185827999488,-185827999424⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566005979,0,true,54376832,54376896⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457249573,0,false,-54379584,-54379520⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576927383,0,true,65297664,65297728⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446328169,0,false,-65301568,-65301504⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623897,0,false,-3904,-3840⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625087,0,false,-2752,-2688⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270413650664,0,true,158853536832,158853536896⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928609604888,0,false,-185743761024,-185743760960⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270538260031,0,true,158961377920,158961377984⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928484995521,0,false,-185891313472,-185891313408⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072908808668,0,false,-26929935552,-26929935488⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072947559976,0,false,-26890224128,-26890224064⟩
    { al := (1273797/8192000), au := (637323/4096000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨170966139273,171080090125⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158909026624,158909026688⟩ : DyadicInterval 40),(⟨-185819680064,-185819680000⟩ : DyadicInterval 40),(⟨748777294720,748777314050⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159007638848,159007638912⟩ : DyadicInterval 40),(⟨-185954620096,-185954620032⟩ : DyadicInterval 40),(⟨748759425230,748759444560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158798051392,158798051456⟩ : DyadicInterval 40),(⟨-185667856896,-185667856832⟩ : DyadicInterval 40),(⟨748797388119,748797407449⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158915106944,158915107008⟩ : DyadicInterval 40),(⟨-185827999488,-185827999424⟩ : DyadicInterval 40),(⟨748776193302,748776212632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54378203,65299607⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54376832,54376896⟩ : DyadicInterval 40),(⟨-54379584,-54379520⟩ : DyadicInterval 40),(⟨762123382238,762123401567⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65297664,65297728⟩ : DyadicInterval 40),(⟨-65301568,-65301504⟩ : DyadicInterval 40),(⟨762123381625,762123400954⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3904,-2688⟩ : DyadicInterval 40),(⟨762123384960,762123404832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170902022888,171026632255⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158853536832,158853536896⟩ : DyadicInterval 40),(⟨-185743761024,-185743760960⟩ : DyadicInterval 40),(⟨748787343999,748787363329⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158961377920,158961377984⟩ : DyadicInterval 40),(⟨-185891313472,-185891313408⟩ : DyadicInterval 40),(⟨748767809851,748767829181⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26929935552,-26890224064⟩ : DyadicInterval 40),(⟨775568495648,775588370656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158909026624,159007638912⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185954620096,-185819680000⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1937_ok : ecellOkT e1937 = true := by decide +kernel
theorem e1937_pos {a z : ℝ} (ha1 : ((1273797/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((637323/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1937 e1937_ok ha1 ha2 hz1 hz2 hz

-- box ['318237/2048000', '1273797/8192000', '1599/1600', '1999/2000']  interval_lower 82950683/549755813888
noncomputable def e1938 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270363816198,0,true,158810405504,158810405568⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928659439354,0,false,-185684756544,-185684756480⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270477767050,0,true,158909026624,158909026688⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928545488502,0,false,-185819680064,-185819680000⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270257033580,0,true,158717980288,158717980352⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928766221972,0,false,-185558335680,-185558335616⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270392283981,0,true,158835044352,158835044416⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928630971571,0,false,-185718462272,-185718462208⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555100353,0,true,43471680,43471744⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468155199,0,false,-43473472,-43473408⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566006738,0,true,54377600,54377664⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457248814,0,false,-54380352,-54380288⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625086,0,false,-2752,-2688⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626058,0,false,-1728,-1664⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270310420677,0,true,158764190208,158764190272⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928712834875,0,false,-185621539328,-185621539264⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270435030068,0,true,158872040064,158872040128⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928588225484,0,false,-185769075392,-185769075328⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072940913366,0,false,-26897035328,-26897035264⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072979641284,0,false,-26857349056,-26857348992⟩
    { al := (318237/2048000), au := (1273797/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨170852188422,170966139274⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158810405504,158810405568⟩ : DyadicInterval 40),(⟨-185684756544,-185684756480⟩ : DyadicInterval 40),(⟨748795152117,748795171446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158909026624,158909026688⟩ : DyadicInterval 40),(⟨-185819680064,-185819680000⟩ : DyadicInterval 40),(⟨748777294720,748777314049⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158717980288,158717980352⟩ : DyadicInterval 40),(⟨-185558335680,-185558335616⟩ : DyadicInterval 40),(⟨748811875200,748811894529⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158835044352,158835044416⟩ : DyadicInterval 40),(⟨-185718462272,-185718462208⟩ : DyadicInterval 40),(⟨748790692031,748790711361⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨43472577,54378962⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43471680,43471744⟩ : DyadicInterval 40),(⟨-43473472,-43473408⟩ : DyadicInterval 40),(⟨762123382729,762123402058⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54377600,54377664⟩ : DyadicInterval 40),(⟨-54380352,-54380288⟩ : DyadicInterval 40),(⟨762123382238,762123401567⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2752,-1664⟩ : DyadicInterval 40),(⟨762123384448,762123404256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170798792901,170923402292⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158764190208,158764190272⟩ : DyadicInterval 40),(⟨-185621539328,-185621539264⟩ : DyadicInterval 40),(⟨748803515663,748803534992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158872040064,158872040128⟩ : DyadicInterval 40),(⟨-185769075392,-185769075328⟩ : DyadicInterval 40),(⟨748783993504,748784012834⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26897035328,-26857348992⟩ : DyadicInterval 40),(⟨775552058112,775571920544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158810405504,158909026688⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185819680064,-185684756480⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1938_ok : ecellOkT e1938 = true := by decide +kernel
theorem e1938_pos {a z : ℝ} (ha1 : ((318237/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1273797/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1938 e1938_ok ha1 ha2 hz1 hz2 hz

-- box ['1273797/8192000', '637323/4096000', '1599/1600', '1999/2000']  interval_lower 83485063/549755813888
noncomputable def e1939 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270477767049,0,true,158909026624,158909026688⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928545488503,0,false,-185819680064,-185819680000⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270591717901,0,true,159007638848,159007638912⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928431537651,0,false,-185954620096,-185954620032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270370913211,0,true,158816548032,158816548096⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928652342341,0,false,-185693159296,-185693159232⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270506177857,0,true,158933613952,158933614016⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928517077695,0,false,-185853322432,-185853322368⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555130384,0,true,43501696,43501760⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468125168,0,false,-43503488,-43503424⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566044281,0,true,54415104,54415168⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457211271,0,false,-54417856,-54417792⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625082,0,false,-2752,-2688⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626055,0,false,-1728,-1664⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270424335918,0,true,158862784640,158862784704⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928598919634,0,false,-185756412864,-185756412800⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270548952432,0,true,158970630976,158970631040⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928474303120,0,false,-185903975488,-185903975424⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072905482205,0,false,-26933344512,-26933344448⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072944238159,0,false,-26893628224,-26893628160⟩
    { al := (1273797/8192000), au := (637323/4096000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨170966139273,171080090125⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158909026624,158909026688⟩ : DyadicInterval 40),(⟨-185819680064,-185819680000⟩ : DyadicInterval 40),(⟨748777294720,748777314050⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159007638848,159007638912⟩ : DyadicInterval 40),(⟨-185954620096,-185954620032⟩ : DyadicInterval 40),(⟨748759425230,748759444560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158816548032,158816548096⟩ : DyadicInterval 40),(⟨-185693159296,-185693159232⟩ : DyadicInterval 40),(⟨748794040287,748794059616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158933613952,158933614016⟩ : DyadicInterval 40),(⟨-185853322432,-185853322368⟩ : DyadicInterval 40),(⟨748772840533,748772859863⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨43502608,54416505⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43501696,43501760⟩ : DyadicInterval 40),(⟨-43503488,-43503424⟩ : DyadicInterval 40),(⟨762123382726,762123402055⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54415104,54415168⟩ : DyadicInterval 40),(⟨-54417856,-54417792⟩ : DyadicInterval 40),(⟨762123382234,762123401563⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2752,-1664⟩ : DyadicInterval 40),(⟨762123384448,762123404256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170912708142,171037324656⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158862784640,158862784704⟩ : DyadicInterval 40),(⟨-185756412864,-185756412800⟩ : DyadicInterval 40),(⟨748785669499,748785688828⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158970630976,158970631040⟩ : DyadicInterval 40),(⟨-185903975488,-185903975424⟩ : DyadicInterval 40),(⟨748766133012,748766152342⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26933344512,-26893628160⟩ : DyadicInterval 40),(⟨775570197696,775590075136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158909026624,159007638912⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185954620096,-185819680000⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1939_ok : ecellOkT e1939 = true := by decide +kernel
theorem e1939_pos {a z : ℝ} (ha1 : ((1273797/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((637323/4096000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1939 e1939_ok ha1 ha2 hz1 hz2 hz

-- box ['637323/4096000', '255099/1638400', '3997/4000', '1599/1600']  interval_lower 5256123/34359738368
noncomputable def e1940 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270591717900,0,true,159007638848,159007638912⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928431537652,0,false,-185954620096,-185954620032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270705668752,0,true,159106242240,159106242304⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928317586800,0,false,-186089576704,-186089576640⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270463407832,0,true,158896599616,158896599680⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928559847720,0,false,-185802677120,-185802677056⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270598672477,0,true,159013657024,159013657088⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928424583075,0,false,-185962856192,-185962856128⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566043521,0,true,54414336,54414400⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457212031,0,false,-54417152,-54417088⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099576972437,0,true,65342656,65342720⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446283115,0,false,-65346624,-65346560⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623892,0,false,-3904,-3840⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625083,0,false,-2752,-2688⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270527558780,0,true,158952117120,158952117184⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928495696772,0,false,-185878641152,-185878641088⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270652175275,0,true,159059954624,159059954688⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928371080277,0,false,-186026220160,-186026220096⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072873358331,0,false,-26966265472,-26966265408⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072912137677,0,false,-26926524032,-26926523968⟩
    { al := (637323/4096000), au := (255099/1638400), zl := (3997/4000), zu := (1599/1600),
      A := ⟨171080090124,171194040976⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159007638848,159007638912⟩ : DyadicInterval 40),(⟨-185954620096,-185954620032⟩ : DyadicInterval 40),(⟨748759425230,748759444560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159106242240,159106242304⟩ : DyadicInterval 40),(⟨-186089576704,-186089576640⟩ : DyadicInterval 40),(⟨748741543637,748741562966⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158896599616,158896599680⟩ : DyadicInterval 40),(⟨-185802677120,-185802677056⟩ : DyadicInterval 40),(⟨748779545647,748779564977⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159013657024,159013657088⟩ : DyadicInterval 40),(⟨-185962856192,-185962856128⟩ : DyadicInterval 40),(⟨748758334219,748758353549⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54415745,65344661⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54414336,54414400⟩ : DyadicInterval 40),(⟨-54417152,-54417088⟩ : DyadicInterval 40),(⟨762123382266,762123401595⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65342656,65342720⟩ : DyadicInterval 40),(⟨-65346624,-65346560⟩ : DyadicInterval 40),(⟨762123381652,762123400981⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3904,-2688⟩ : DyadicInterval 40),(⟨762123384960,762123404832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171015931004,171140547499⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158952117120,158952117184⟩ : DyadicInterval 40),(⟨-185878641152,-185878641088⟩ : DyadicInterval 40),(⟨748769487988,748769507317⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159059954624,159059954688⟩ : DyadicInterval 40),(⟨-186026220160,-186026220096⟩ : DyadicInterval 40),(⟨748749939547,748749958876⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26966265472,-26926523968⟩ : DyadicInterval 40),(⟨775586645600,775606535616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159007638848,159106242304⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186089576704,-185954620032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1940_ok : ecellOkT e1940 = true := by decide +kernel
theorem e1940_pos {a z : ℝ} (ha1 : ((637323/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((255099/1638400 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1940 e1940_ok ha1 ha2 hz1 hz2 hz

-- box ['255099/1638400', '159543/1024000', '3997/4000', '1599/1600']  interval_lower 42317533/274877906944
noncomputable def e1941 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270705668751,0,true,159106242240,159106242304⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928317586801,0,false,-186089576704,-186089576640⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270819619603,0,true,159204836800,159204836864⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928203635949,0,false,-186224549888,-186224549824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270577273220,0,true,158995139008,158995139072⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928445982332,0,false,-185937513856,-185937513792⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270712552109,0,true,159112198272,159112198336⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928310703443,0,false,-186097729472,-186097729408⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566081064,0,true,54451904,54451968⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457174488,0,false,-54454656,-54454592⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577017493,0,true,65387712,65387776⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446238059,0,false,-65391680,-65391616⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623887,0,false,-3904,-3840⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625080,0,false,-2752,-2688⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270641466897,0,true,159050688512,159050688576⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928381788655,0,false,-186013537856,-186013537792⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270766090516,0,true,159158522560,159158522624⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928257165036,0,false,-186161143360,-186161143296⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072837884390,0,false,-27002620800,-27002620736⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072876691776,0,false,-26962849280,-26962849216⟩
    { al := (255099/1638400), au := (159543/1024000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨171194040975,171307991827⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159106242240,159106242304⟩ : DyadicInterval 40),(⟨-186089576704,-186089576640⟩ : DyadicInterval 40),(⟨748741543637,748741562966⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159204836800,159204836864⟩ : DyadicInterval 40),(⟨-186224549888,-186224549824⟩ : DyadicInterval 40),(⟨748723649939,748723669268⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158995139008,158995139072⟩ : DyadicInterval 40),(⟨-185937513856,-185937513792⟩ : DyadicInterval 40),(⟨748761691083,748761710412⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159112198272,159112198336⟩ : DyadicInterval 40),(⟨-186097729472,-186097729408⟩ : DyadicInterval 40),(⟨748740463062,748740482392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54453288,65389717⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54451904,54451968⟩ : DyadicInterval 40),(⟨-54454656,-54454592⟩ : DyadicInterval 40),(⟨762123382231,762123401560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65387712,65387776⟩ : DyadicInterval 40),(⟨-65391680,-65391616⟩ : DyadicInterval 40),(⟨762123381647,762123400976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3904,-2688⟩ : DyadicInterval 40),(⟨762123384960,762123404832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171129839121,171254462740⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159050688512,159050688576⟩ : DyadicInterval 40),(⟨-186013537856,-186013537792⟩ : DyadicInterval 40),(⟨748751619929,748751639259⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159158522560,159158522624⟩ : DyadicInterval 40),(⟨-186161143360,-186161143296⟩ : DyadicInterval 40),(⟨748732057090,748732076420⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27002620800,-26962849216⟩ : DyadicInterval 40),(⟨775604808224,775624713280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159106242240,159204836864⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186224549888,-186089576640⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1941_ok : ecellOkT e1941 = true := by decide +kernel
theorem e1941_pos {a z : ℝ} (ha1 : ((255099/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((159543/1024000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1941 e1941_ok ha1 ha2 hz1 hz2 hz

-- box ['637323/4096000', '255099/1638400', '1599/1600', '1999/2000']  interval_lower 168041455/1099511627776
noncomputable def e1942 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270591717900,0,true,159007638848,159007638912⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928431537652,0,false,-185954620096,-185954620032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270705668752,0,true,159106242240,159106242304⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928317586800,0,false,-186089576704,-186089576640⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270484792843,0,true,158915106944,158915107008⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928538462709,0,false,-185827999488,-185827999424⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270620071732,0,true,159032174656,159032174720⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928403183820,0,false,-185988199168,-185988199104⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555160417,0,true,43531776,43531840⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468095135,0,false,-43533504,-43533440⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566081825,0,true,54452672,54452736⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457173727,0,false,-54455424,-54455360⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625079,0,false,-2752,-2688⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626053,0,false,-1728,-1664⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270538251157,0,true,158961370240,158961370304⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928485004395,0,false,-185891302976,-185891302912⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270662874791,0,true,159069212992,159069213056⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928360380761,0,false,-186038892160,-186038892096⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072870027437,0,false,-26969679104,-26969679040⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072908811430,0,false,-26929932736,-26929932672⟩
    { al := (637323/4096000), au := (255099/1638400), zl := (1599/1600), zu := (1999/2000),
      A := ⟨171080090124,171194040976⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159007638848,159007638912⟩ : DyadicInterval 40),(⟨-185954620096,-185954620032⟩ : DyadicInterval 40),(⟨748759425230,748759444560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159106242240,159106242304⟩ : DyadicInterval 40),(⟨-186089576704,-186089576640⟩ : DyadicInterval 40),(⟨748741543637,748741562966⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158915106944,158915107008⟩ : DyadicInterval 40),(⟨-185827999488,-185827999424⟩ : DyadicInterval 40),(⟨748776193303,748776212632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159032174656,159032174720⟩ : DyadicInterval 40),(⟨-185988199168,-185988199104⟩ : DyadicInterval 40),(⟨748754976994,748754996324⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨43532641,54454049⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43531776,43531840⟩ : DyadicInterval 40),(⟨-43533504,-43533440⟩ : DyadicInterval 40),(⟨762123382692,762123402021⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54452672,54452736⟩ : DyadicInterval 40),(⟨-54455424,-54455360⟩ : DyadicInterval 40),(⟨762123382231,762123401560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2752,-1664⟩ : DyadicInterval 40),(⟨762123384448,762123404256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171026623381,171151247015⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158961370240,158961370304⟩ : DyadicInterval 40),(⟨-185891302976,-185891302912⟩ : DyadicInterval 40),(⟨748767811248,748767830577⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159069212992,159069213056⟩ : DyadicInterval 40),(⟨-186038892160,-186038892096⟩ : DyadicInterval 40),(⟨748748260467,748748279796⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26969679104,-26929932672⟩ : DyadicInterval 40),(⟨775588349952,775608242432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159007638848,159106242304⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186089576704,-185954620032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1942_ok : ecellOkT e1942 = true := by decide +kernel
theorem e1942_pos {a z : ℝ} (ha1 : ((637323/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((255099/1638400 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1942 e1942_ok ha1 ha2 hz1 hz2 hz

-- box ['255099/1638400', '159543/1024000', '1599/1600', '1999/2000']  interval_lower 169115261/1099511627776
noncomputable def e1943 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270705668751,0,true,159106242240,159106242304⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928317586801,0,false,-186089576704,-186089576640⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270819619603,0,true,159204836800,159204836864⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928203635949,0,false,-186224549888,-186224549824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270598672475,0,true,159013657024,159013657088⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928424583077,0,false,-185962856192,-185962856128⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270733965608,0,true,159130726592,159130726656⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928289289944,0,false,-186123092416,-186123092352⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555190454,0,true,43561792,43561856⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468065098,0,false,-43563584,-43563520⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566119372,0,true,54490240,54490304⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457136180,0,false,-54492992,-54492928⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625075,0,false,-2752,-2688⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626051,0,false,-1728,-1664⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270652166398,0,true,159059946944,159059947008⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928371089154,0,false,-186026209664,-186026209600⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270776797158,0,true,159167786240,159167786304⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928246458394,0,false,-186173825408,-186173825344⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072834549059,0,false,-27006039104,-27006039040⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072873361095,0,false,-26966262656,-26966262592⟩
    { al := (255099/1638400), au := (159543/1024000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨171194040975,171307991827⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159106242240,159106242304⟩ : DyadicInterval 40),(⟨-186089576704,-186089576640⟩ : DyadicInterval 40),(⟨748741543637,748741562966⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159204836800,159204836864⟩ : DyadicInterval 40),(⟨-186224549888,-186224549824⟩ : DyadicInterval 40),(⟨748723649939,748723669268⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159013657024,159013657088⟩ : DyadicInterval 40),(⟨-185962856192,-185962856128⟩ : DyadicInterval 40),(⟨748758334219,748758353549⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159130726592,159130726656⟩ : DyadicInterval 40),(⟨-186123092416,-186123092352⟩ : DyadicInterval 40),(⟨748737101311,748737120641⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨43562678,54491596⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43561792,43561856⟩ : DyadicInterval 40),(⟨-43563584,-43563520⟩ : DyadicInterval 40),(⟨762123382722,762123402051⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54490240,54490304⟩ : DyadicInterval 40),(⟨-54492992,-54492928⟩ : DyadicInterval 40),(⟨762123382227,762123401556⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2752,-1664⟩ : DyadicInterval 40),(⟨762123384448,762123404256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171140538622,171265169382⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159059946944,159059947008⟩ : DyadicInterval 40),(⟨-186026209664,-186026209600⟩ : DyadicInterval 40),(⟨748749940946,748749960276⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159167786240,159167786304⟩ : DyadicInterval 40),(⟨-186173825408,-186173825344⟩ : DyadicInterval 40),(⟨748730375790,748730395120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27006039104,-26966262592⟩ : DyadicInterval 40),(⟨775606514912,775626422432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159106242240,159204836864⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186224549888,-186089576640⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1943_ok : ecellOkT e1943 = true := by decide +kernel
theorem e1943_pos {a z : ℝ} (ha1 : ((255099/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((159543/1024000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1943 e1943_ok ha1 ha2 hz1 hz2 hz

-- box ['79347/512000', '1270401/8192000', '1999/2000', '7997/8000']  interval_lower 80750841/549755813888
noncomputable def e1944 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269908012793,0,true,158415832640,158415832704⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929115242759,0,false,-185145228096,-185145228032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270021963645,0,true,158514489152,158514489216⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929001291907,0,false,-185280085440,-185280085376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269822814600,0,true,158342063872,158342063936⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929200440952,0,false,-185044409472,-185044409408⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269958022270,0,true,158459131008,158459131072⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929065233282,0,false,-185204410752,-185204410688⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544142139,0,true,32513856,32513920⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479113413,0,false,-32514880,-32514816⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555010980,0,true,43382336,43382400⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468244572,0,false,-43384064,-43384000⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626064,0,false,-1728,-1664⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626815,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269865409387,0,true,158378945152,158378945216⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929157846165,0,false,-185094812544,-185094812480⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1269989997423,0,true,158486814272,158486814336⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929033258129,0,false,-185242252736,-185242252672⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073079097384,0,false,-26755438400,-26755438336⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073117717811,0,false,-26715867328,-26715867264⟩
    { al := (79347/512000), au := (1270401/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨170396385017,170510335869⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158415832640,158415832704⟩ : DyadicInterval 40),(⟨-185145228096,-185145228032⟩ : DyadicInterval 40),(⟨748866460688,748866480017⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158514489152,158514489216⟩ : DyadicInterval 40),(⟨-185280085440,-185280085376⟩ : DyadicInterval 40),(⟨748848651705,748848671035⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158342063872,158342063936⟩ : DyadicInterval 40),(⟨-185044409472,-185044409408⟩ : DyadicInterval 40),(⟨748879768112,748879787441⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158459131008,158459131072⟩ : DyadicInterval 40),(⟨-185204410752,-185204410688⟩ : DyadicInterval 40),(⟨748858646368,748858665697⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32514363,43383204⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32513856,32513920⟩ : DyadicInterval 40),(⟨-32514880,-32514816⟩ : DyadicInterval 40),(⟨762123383102,762123402431⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43382336,43382400⟩ : DyadicInterval 40),(⟨-43384064,-43384000⟩ : DyadicInterval 40),(⟨762123382704,762123402033⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1728,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170353781611,170478369647⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158378945152,158378945216⟩ : DyadicInterval 40),(⟨-185094812544,-185094812480⟩ : DyadicInterval 40),(⟨748873115920,748873135249⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158486814272,158486814336⟩ : DyadicInterval 40),(⟨-185242252736,-185242252672⟩ : DyadicInterval 40),(⟨748853648830,748853668160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26755438400,-26715867264⟩ : DyadicInterval 40),(⟨775481317248,775501122080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158415832640,158514489216⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185280085440,-185145228032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1944_ok : ecellOkT e1944 = true := by decide +kernel
theorem e1944_pos {a z : ℝ} (ha1 : ((79347/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1270401/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1944 e1944_ok ha1 ha2 hz1 hz2 hz

-- box ['1270401/8192000', '5085/32768', '1999/2000', '7997/8000']  interval_lower 162559317/1099511627776
noncomputable def e1945 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270021963644,0,true,158514489152,158514489216⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929001291908,0,false,-185280085440,-185280085376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270135914496,0,true,158613136768,158613136832⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928887341056,0,false,-185414959232,-185414959168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269936708476,0,true,158440677696,158440677760⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929086547076,0,false,-185179187008,-185179186944⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270071930389,0,true,158557746624,158557746688⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928951325163,0,false,-185339224704,-185339224640⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544164656,0,true,32536384,32536448⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479090896,0,false,-32537408,-32537344⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555041006,0,true,43412352,43412416⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468214546,0,false,-43414144,-43414080⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626061,0,false,-1728,-1664⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626814,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269979331749,0,true,158477580288,158477580352⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929043923803,0,false,-185229629952,-185229629888⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270103926911,0,true,158585445888,158585445952⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928919328641,0,false,-185377096640,-185377096576⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073043756232,0,false,-26791650688,-26791650624⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073082404689,0,false,-26752049600,-26752049536⟩
    { al := (1270401/8192000), au := (5085/32768), zl := (1999/2000), zu := (7997/8000),
      A := ⟨170510335868,170624286720⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158514489152,158514489216⟩ : DyadicInterval 40),(⟨-185280085440,-185280085376⟩ : DyadicInterval 40),(⟨748848651706,748848671035⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158613136768,158613136832⟩ : DyadicInterval 40),(⟨-185414959232,-185414959168⟩ : DyadicInterval 40),(⟨748830830608,748830849938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158440677696,158440677760⟩ : DyadicInterval 40),(⟨-185179187008,-185179186944⟩ : DyadicInterval 40),(⟨748861977060,748861996390⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158557746624,158557746688⟩ : DyadicInterval 40),(⟨-185339224704,-185339224640⟩ : DyadicInterval 40),(⟨748840838737,748840858067⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32536880,43413230⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32536384,32536448⟩ : DyadicInterval 40),(⟨-32537408,-32537344⟩ : DyadicInterval 40),(⟨762123383101,762123402430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43412352,43412416⟩ : DyadicInterval 40),(⟨-43414144,-43414080⟩ : DyadicInterval 40),(⟨762123382733,762123402062⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1728,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170467703973,170592299135⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158477580288,158477580352⟩ : DyadicInterval 40),(⟨-185229629952,-185229629888⟩ : DyadicInterval 40),(⟨748855315911,748855335241⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158585445888,158585445952⟩ : DyadicInterval 40),(⟨-185377096640,-185377096576⟩ : DyadicInterval 40),(⟨748835834480,748835853809⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26791650688,-26752049536⟩ : DyadicInterval 40),(⟨775499408384,775519228224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158514489152,158613136832⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185414959232,-185280085376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1945_ok : ecellOkT e1945 = true := by decide +kernel
theorem e1945_pos {a z : ℝ} (ha1 : ((1270401/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((5085/32768 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1945 e1945_ok ha1 ha2 hz1 hz2 hz

-- box ['79347/512000', '1270401/8192000', '7997/8000', '3999/4000']  interval_lower 80674759/549755813888
noncomputable def e1946 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269908012793,0,true,158415832640,158415832704⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929115242759,0,false,-185145228096,-185145228032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270021963645,0,true,158514489152,158514489216⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929001291907,0,false,-185280085440,-185280085376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269844114148,0,true,158360506560,158360506624⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929179141404,0,false,-185069613312,-185069613248⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1269979336062,0,true,158477584000,158477584064⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929043919490,0,false,-185229635072,-185229635008⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533303981,0,true,21675968,21676032⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489951571,0,false,-21676480,-21676416⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544165317,0,true,32537024,32537088⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479090235,0,false,-32538048,-32537984⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626813,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627349,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269876059079,0,true,158388166144,158388166208⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929147196473,0,false,-185107414848,-185107414784⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270000654258,0,true,158496040576,158496040640⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929022601294,0,false,-185254865152,-185254865088⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073075792613,0,false,-26758824576,-26758824512⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073114417670,0,false,-26719248704,-26719248640⟩
    { al := (79347/512000), au := (1270401/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨170396385017,170510335869⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158415832640,158415832704⟩ : DyadicInterval 40),(⟨-185145228096,-185145228032⟩ : DyadicInterval 40),(⟨748866460688,748866480017⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158514489152,158514489216⟩ : DyadicInterval 40),(⟨-185280085440,-185280085376⟩ : DyadicInterval 40),(⟨748848651705,748848671035⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158360506560,158360506624⟩ : DyadicInterval 40),(⟨-185069613312,-185069613248⟩ : DyadicInterval 40),(⟨748876441893,748876461223⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158477584000,158477584064⟩ : DyadicInterval 40),(⟨-185229635072,-185229635008⟩ : DyadicInterval 40),(⟨748855315257,748855334586⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21676205,32537541⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21675968,21676032⟩ : DyadicInterval 40),(⟨-21676480,-21676416⟩ : DyadicInterval 40),(⟨762123383380,762123402709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32537024,32537088⟩ : DyadicInterval 40),(⟨-32538048,-32537984⟩ : DyadicInterval 40),(⟨762123383101,762123402430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170364431303,170489026482⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158388166144,158388166208⟩ : DyadicInterval 40),(⟨-185107414848,-185107414784⟩ : DyadicInterval 40),(⟨748871452449,748871471779⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158496040576,158496040640⟩ : DyadicInterval 40),(⟨-185254865152,-185254865088⟩ : DyadicInterval 40),(⟨748851982974,748852002303⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26758824576,-26719248640⟩ : DyadicInterval 40),(⟨775483007936,775502815168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158415832640,158514489216⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185280085440,-185145228032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1946_ok : ecellOkT e1946 = true := by decide +kernel
theorem e1946_pos {a z : ℝ} (ha1 : ((79347/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1270401/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1946 e1946_ok ha1 ha2 hz1 hz2 hz

-- box ['1270401/8192000', '5085/32768', '7997/8000', '3999/4000']  interval_lower 20300815/137438953472
noncomputable def e1947 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270021963644,0,true,158514489152,158514489216⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929001291908,0,false,-185280085440,-185280085376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270135914496,0,true,158613136768,158613136832⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928887341056,0,false,-185414959232,-185414959168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269958022267,0,true,158459131008,158459131072⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929065233285,0,false,-185204410752,-185204410688⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270093258425,0,true,158576210304,158576210368⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928929997127,0,false,-185364468992,-185364468928⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533318991,0,true,21690944,21691008⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489936561,0,false,-21691456,-21691392⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544187835,0,true,32559552,32559616⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479067717,0,false,-32560576,-32560512⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626811,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627349,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269989988561,0,true,158486806592,158486806656⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929033266991,0,false,-185242242240,-185242242176⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270114590868,0,true,158594677504,158594677568⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928908664684,0,false,-185389719040,-185389718976⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073040447044,0,false,-26795041472,-26795041408⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073079100133,0,false,-26755435584,-26755435520⟩
    { al := (1270401/8192000), au := (5085/32768), zl := (7997/8000), zu := (3999/4000),
      A := ⟨170510335868,170624286720⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158514489152,158514489216⟩ : DyadicInterval 40),(⟨-185280085440,-185280085376⟩ : DyadicInterval 40),(⟨748848651706,748848671035⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158613136768,158613136832⟩ : DyadicInterval 40),(⟨-185414959232,-185414959168⟩ : DyadicInterval 40),(⟨748830830608,748830849938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158459131008,158459131072⟩ : DyadicInterval 40),(⟨-185204410752,-185204410688⟩ : DyadicInterval 40),(⟨748858646368,748858665697⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158576210304,158576210368⟩ : DyadicInterval 40),(⟨-185364468992,-185364468928⟩ : DyadicInterval 40),(⟨748837503135,748837522465⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21691215,32560059⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21690944,21691008⟩ : DyadicInterval 40),(⟨-21691456,-21691392⟩ : DyadicInterval 40),(⟨762123383380,762123402709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32559552,32559616⟩ : DyadicInterval 40),(⟨-32560576,-32560512⟩ : DyadicInterval 40),(⟨762123383099,762123402428⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170478360785,170602963092⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158486806592,158486806656⟩ : DyadicInterval 40),(⟨-185242242240,-185242242176⟩ : DyadicInterval 40),(⟨748853650217,748853669546⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158594677504,158594677568⟩ : DyadicInterval 40),(⟨-185389719040,-185389718976⟩ : DyadicInterval 40),(⟨748834166396,748834185725⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26795041472,-26755435520⟩ : DyadicInterval 40),(⟨775501101376,775520923616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158514489152,158613136832⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185414959232,-185280085376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1947_ok : ecellOkT e1947 = true := by decide +kernel
theorem e1947_pos {a z : ℝ} (ha1 : ((1270401/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((5085/32768 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1947 e1947_ok ha1 ha2 hz1 hz2 hz

-- box ['5085/32768', '1272099/8192000', '1999/2000', '7997/8000']  interval_lower 163619679/1099511627776
noncomputable def e1948 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270135914496,0,true,158613136768,158613136832⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928887341056,0,false,-185414959232,-185414959168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270249865348,0,true,158711775552,158711775616⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928773390204,0,false,-185549849664,-185549849600⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270050602352,0,true,158539282624,158539282688⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928972653200,0,false,-185313981056,-185313980992⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270185838509,0,true,158656353408,158656353472⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928837417043,0,false,-185474055232,-185474055168⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544187175,0,true,32558912,32558976⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479068377,0,false,-32559936,-32559872⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555071033,0,true,43442368,43442432⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468184519,0,false,-43444160,-43444096⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626059,0,false,-1728,-1664⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626812,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270093254110,0,true,158576206592,158576206656⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928930001442,0,false,-185364463872,-185364463808⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270217856395,0,true,158684068672,158684068736⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928805399157,0,false,-185511957056,-185511956992⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073008391472,0,false,-26827888320,-26827888256⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073047067960,0,false,-26788257280,-26788257216⟩
    { al := (5085/32768), au := (1272099/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨170624286720,170738237572⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158613136768,158613136832⟩ : DyadicInterval 40),(⟨-185414959232,-185414959168⟩ : DyadicInterval 40),(⟨748830830608,748830849938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158711775552,158711775616⟩ : DyadicInterval 40),(⟨-185549849664,-185549849600⟩ : DyadicInterval 40),(⟨748812997440,748813016769⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158539282624,158539282688⟩ : DyadicInterval 40),(⟨-185313981056,-185313980992⟩ : DyadicInterval 40),(⟨748844173946,748844193276⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158656353408,158656353472⟩ : DyadicInterval 40),(⟨-185474055232,-185474055168⟩ : DyadicInterval 40),(⟨748823019026,748823038356⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32559399,43443257⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32558912,32558976⟩ : DyadicInterval 40),(⟨-32559936,-32559872⟩ : DyadicInterval 40),(⟨762123383099,762123402428⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43442368,43442432⟩ : DyadicInterval 40),(⟨-43444160,-43444096⟩ : DyadicInterval 40),(⟨762123382731,762123402060⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1728,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170581626334,170706228619⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158576206592,158576206656⟩ : DyadicInterval 40),(⟨-185364463872,-185364463808⟩ : DyadicInterval 40),(⟨748837503791,748837523120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158684068672,158684068736⟩ : DyadicInterval 40),(⟨-185511957056,-185511956992⟩ : DyadicInterval 40),(⟨748818008014,748818027343⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26827888320,-26788257216⟩ : DyadicInterval 40),(⟨775517512224,775537347040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158613136768,158711775616⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185549849664,-185414959168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1948_ok : ecellOkT e1948 = true := by decide +kernel
theorem e1948_pos {a z : ℝ} (ha1 : ((5085/32768 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1272099/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1948 e1948_ok ha1 ha2 hz1 hz2 hz

-- box ['1272099/8192000', '318237/2048000', '1999/2000', '7997/8000']  interval_lower 164682331/1099511627776
noncomputable def e1949 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270249865347,0,true,158711775552,158711775616⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928773390205,0,false,-185549849664,-185549849600⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270363816199,0,true,158810405504,158810405568⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928659439353,0,false,-185684756544,-185684756480⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270164496228,0,true,158637878720,158637878784⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928858759324,0,false,-185448791616,-185448791552⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270299746629,0,true,158754951296,158754951360⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928723508923,0,false,-185608902272,-185608902208⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544209695,0,true,32581376,32581440⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479045857,0,false,-32582464,-32582400⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555101063,0,true,43472384,43472448⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468154489,0,false,-43474176,-43474112⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626057,0,false,-1728,-1664⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626811,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270207176469,0,true,158674824000,158674824064⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928816079083,0,false,-185499314368,-185499314304⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270331785882,0,true,158782682624,158782682688⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928691469670,0,false,-185646834048,-185646833984⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072973003100,0,false,-26864151424,-26864151360⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073011707623,0,false,-26824490304,-26824490240⟩
    { al := (1272099/8192000), au := (318237/2048000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨170738237571,170852188423⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158711775552,158711775616⟩ : DyadicInterval 40),(⟨-185549849664,-185549849600⟩ : DyadicInterval 40),(⟨748812997440,748813016769⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158810405504,158810405568⟩ : DyadicInterval 40),(⟨-185684756544,-185684756480⟩ : DyadicInterval 40),(⟨748795152117,748795171446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158637878720,158637878784⟩ : DyadicInterval 40),(⟨-185448791616,-185448791552⟩ : DyadicInterval 40),(⟨748826358731,748826378061⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158754951296,158754951360⟩ : DyadicInterval 40),(⟨-185608902272,-185608902208⟩ : DyadicInterval 40),(⟨748805187244,748805206573⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32581919,43473287⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32581376,32581440⟩ : DyadicInterval 40),(⟨-32582464,-32582400⟩ : DyadicInterval 40),(⟨762123383130,762123402459⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43472384,43472448⟩ : DyadicInterval 40),(⟨-43474176,-43474112⟩ : DyadicInterval 40),(⟨762123382729,762123402058⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1728,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170695548693,170820158106⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158674824000,158674824064⟩ : DyadicInterval 40),(⟨-185499314368,-185499314304⟩ : DyadicInterval 40),(⟨748819679622,748819698951⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158782682624,158782682688⟩ : DyadicInterval 40),(⟨-185646834048,-185646833984⟩ : DyadicInterval 40),(⟨748800169457,748800188786⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26864151424,-26824490240⟩ : DyadicInterval 40),(⟨775535628736,775555478592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158711775552,158810405568⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185684756544,-185549849600⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1949_ok : ecellOkT e1949 = true := by decide +kernel
theorem e1949_pos {a z : ℝ} (ha1 : ((1272099/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((318237/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1949 e1949_ok ha1 ha2 hz1 hz2 hz

-- box ['5085/32768', '1272099/8192000', '7997/8000', '3999/4000']  interval_lower 163466505/1099511627776
noncomputable def e1950 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270135914496,0,true,158613136768,158613136832⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928887341056,0,false,-185414959232,-185414959168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270249865348,0,true,158711775552,158711775616⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928773390204,0,false,-185549849664,-185549849600⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270071930388,0,true,158557746624,158557746688⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928951325164,0,false,-185339224704,-185339224640⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270207180789,0,true,158674827776,158674827840⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928816074763,0,false,-185499319424,-185499319360⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533334004,0,true,21705984,21706048⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489921548,0,false,-21706496,-21706432⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544210356,0,true,32582080,32582144⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479045196,0,false,-32583104,-32583040⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626810,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627348,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270103918048,0,true,158585438272,158585438336⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928919337504,0,false,-185377086144,-185377086080⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270228527477,0,true,158693305664,158693305728⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928794728075,0,false,-185524589504,-185524589440⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073005077861,0,false,-26831283776,-26831283712⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073043758984,0,false,-26791647872,-26791647808⟩
    { al := (5085/32768), au := (1272099/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨170624286720,170738237572⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158613136768,158613136832⟩ : DyadicInterval 40),(⟨-185414959232,-185414959168⟩ : DyadicInterval 40),(⟨748830830608,748830849938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158711775552,158711775616⟩ : DyadicInterval 40),(⟨-185549849664,-185549849600⟩ : DyadicInterval 40),(⟨748812997440,748813016769⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158557746624,158557746688⟩ : DyadicInterval 40),(⟨-185339224704,-185339224640⟩ : DyadicInterval 40),(⟨748840838737,748840858067⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158674827776,158674827840⟩ : DyadicInterval 40),(⟨-185499319424,-185499319360⟩ : DyadicInterval 40),(⟨748819678900,748819698230⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21706228,32582580⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21705984,21706048⟩ : DyadicInterval 40),(⟨-21706496,-21706432⟩ : DyadicInterval 40),(⟨762123383379,762123402708⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32582080,32582144⟩ : DyadicInterval 40),(⟨-32583104,-32583040⟩ : DyadicInterval 40),(⟨762123383098,762123402427⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170592290272,170716899701⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158585438272,158585438336⟩ : DyadicInterval 40),(⟨-185377086144,-185377086080⟩ : DyadicInterval 40),(⟨748835835832,748835855161⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158693305664,158693305728⟩ : DyadicInterval 40),(⟨-185524589504,-185524589440⟩ : DyadicInterval 40),(⟨748816337689,748816357018⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26831283776,-26791647808⟩ : DyadicInterval 40),(⟨775519207520,775539044768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158613136768,158711775616⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185549849664,-185414959168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1950_ok : ecellOkT e1950 = true := by decide +kernel
theorem e1950_pos {a z : ℝ} (ha1 : ((5085/32768 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1272099/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1950 e1950_ok ha1 ha2 hz1 hz2 hz

-- box ['1272099/8192000', '318237/2048000', '7997/8000', '3999/4000']  interval_lower 164528801/1099511627776
noncomputable def e1951 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270249865347,0,true,158711775552,158711775616⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928773390205,0,false,-185549849664,-185549849600⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270363816199,0,true,158810405504,158810405568⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928659439353,0,false,-185684756544,-185684756480⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270185838507,0,true,158656353408,158656353472⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928837417045,0,false,-185474055232,-185474055168⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270321103153,0,true,158773436352,158773436416⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928702152399,0,false,-185634186432,-185634186368⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533349018,0,true,21721024,21721088⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489906534,0,false,-21721472,-21721408⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544232879,0,true,32604608,32604672⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479022673,0,false,-32605632,-32605568⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626809,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627347,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270217847528,0,true,158684060992,158684061056⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928805408024,0,false,-185511946560,-185511946496⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270342464087,0,true,158791924928,158791924992⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928680791465,0,false,-185659476416,-185659476352⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072969685064,0,false,-26867551488,-26867551424⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073008394226,0,false,-26827885504,-26827885440⟩
    { al := (1272099/8192000), au := (318237/2048000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨170738237571,170852188423⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158711775552,158711775616⟩ : DyadicInterval 40),(⟨-185549849664,-185549849600⟩ : DyadicInterval 40),(⟨748812997440,748813016769⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158810405504,158810405568⟩ : DyadicInterval 40),(⟨-185684756544,-185684756480⟩ : DyadicInterval 40),(⟨748795152117,748795171446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158656353408,158656353472⟩ : DyadicInterval 40),(⟨-185474055232,-185474055168⟩ : DyadicInterval 40),(⟨748823019026,748823038356⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158773436352,158773436416⟩ : DyadicInterval 40),(⟨-185634186432,-185634186368⟩ : DyadicInterval 40),(⟨748801842614,748801861944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21721242,32605103⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21721024,21721088⟩ : DyadicInterval 40),(⟨-21721472,-21721408⟩ : DyadicInterval 40),(⟨762123383346,762123402675⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32604608,32604672⟩ : DyadicInterval 40),(⟨-32605632,-32605568⟩ : DyadicInterval 40),(⟨762123383097,762123402426⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170706219752,170830836311⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158684060992,158684061056⟩ : DyadicInterval 40),(⟨-185511946560,-185511946496⟩ : DyadicInterval 40),(⟨748818009405,748818028734⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158791924928,158791924992⟩ : DyadicInterval 40),(⟨-185659476416,-185659476352⟩ : DyadicInterval 40),(⟨748798496870,748798516200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26867551488,-26827885440⟩ : DyadicInterval 40),(⟨775537326336,775557178624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158711775552,158810405568⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185684756544,-185549849600⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1951_ok : ecellOkT e1951 = true := by decide +kernel
theorem e1951_pos {a z : ℝ} (ha1 : ((1272099/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((318237/2048000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1951 e1951_ok ha1 ha2 hz1 hz2 hz

-- box ['79347/512000', '1270401/8192000', '3999/4000', '7999/8000']  interval_lower 161197121/1099511627776
noncomputable def e1952 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269908012793,0,true,158415832640,158415832704⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929115242759,0,false,-185145228096,-185145228032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270021963645,0,true,158514489152,158514489216⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929001291907,0,false,-185280085440,-185280085376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269865413696,0,true,158378948864,158378948928⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929157841856,0,false,-185094817664,-185094817600⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270000649854,0,true,158496036736,158496036800⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨929022605698,0,false,-185254859968,-185254859904⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522465774,0,true,10837888,10837952⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500789778,0,false,-10838080,-10838016⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533319603,0,true,21691584,21691648⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489935949,0,false,-21692096,-21692032⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627348,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627670,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1269886708793,0,true,158397387072,158397387136⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929136546759,0,false,-185120017344,-185120017280⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270011311120,0,true,158505266752,158505266816⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨929011944432,0,false,-185267477760,-185267477696⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073072487628,0,false,-26762211008,-26762210944⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073111117315,0,false,-26722630208,-26722630144⟩
    { al := (79347/512000), au := (1270401/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨170396385017,170510335869⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158415832640,158415832704⟩ : DyadicInterval 40),(⟨-185145228096,-185145228032⟩ : DyadicInterval 40),(⟨748866460688,748866480017⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158514489152,158514489216⟩ : DyadicInterval 40),(⟨-185280085440,-185280085376⟩ : DyadicInterval 40),(⟨748848651705,748848671035⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158378948864,158378948928⟩ : DyadicInterval 40),(⟨-185094817664,-185094817600⟩ : DyadicInterval 40),(⟨748873115266,748873134596⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158496036736,158496036800⟩ : DyadicInterval 40),(⟨-185254859968,-185254859904⟩ : DyadicInterval 40),(⟨748851983690,748852003020⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10837998,21691827⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10837888,10837952⟩ : DyadicInterval 40),(⟨-10838080,-10838016⟩ : DyadicInterval 40),(⟨762123383541,762123402870⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21691584,21691648⟩ : DyadicInterval 40),(⟨-21692096,-21692032⟩ : DyadicInterval 40),(⟨762123383380,762123402709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170375081017,170499683344⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158397387072,158397387136⟩ : DyadicInterval 40),(⟨-185120017344,-185120017280⟩ : DyadicInterval 40),(⟨748869788881,748869808211⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158505266752,158505266816⟩ : DyadicInterval 40),(⟨-185267477760,-185267477696⟩ : DyadicInterval 40),(⟨748850317057,748850336387⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26762211008,-26722630144⟩ : DyadicInterval 40),(⟨775484698688,775504508384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158415832640,158514489216⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185280085440,-185145228032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1952_ok : ecellOkT e1952 = true := by decide +kernel
theorem e1952_pos {a z : ℝ} (ha1 : ((79347/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1270401/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1952 e1952_ok ha1 ha2 hz1 hz2 hz

-- box ['1270401/8192000', '5085/32768', '3999/4000', '7999/8000']  interval_lower 10140867/68719476736
noncomputable def e1953 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270021963644,0,true,158514489152,158514489216⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929001291908,0,false,-185280085440,-185280085376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270135914496,0,true,158613136768,158613136832⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928887341056,0,false,-185414959232,-185414959168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269979336060,0,true,158477584000,158477584064⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929043919492,0,false,-185229635072,-185229635008⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270114586461,0,true,158594673728,158594673792⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928908669091,0,false,-185389713856,-185389713792⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522473279,0,true,10845440,10845504⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500782273,0,false,-10845568,-10845504⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533334616,0,true,21706624,21706688⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489920936,0,false,-21707072,-21707008⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627347,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627670,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270000645397,0,true,158496032896,158496032960⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨929022610155,0,false,-185254854656,-185254854592⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270125254852,0,true,158603909056,158603909120⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928898000700,0,false,-185402341632,-185402341568⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073037137639,0,false,-26798432576,-26798432512⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073075795362,0,false,-26758821760,-26758821696⟩
    { al := (1270401/8192000), au := (5085/32768), zl := (3999/4000), zu := (7999/8000),
      A := ⟨170510335868,170624286720⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158514489152,158514489216⟩ : DyadicInterval 40),(⟨-185280085440,-185280085376⟩ : DyadicInterval 40),(⟨748848651706,748848671035⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158613136768,158613136832⟩ : DyadicInterval 40),(⟨-185414959232,-185414959168⟩ : DyadicInterval 40),(⟨748830830608,748830849938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158477584000,158477584064⟩ : DyadicInterval 40),(⟨-185229635072,-185229635008⟩ : DyadicInterval 40),(⟨748855315257,748855334586⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158594673728,158594673792⟩ : DyadicInterval 40),(⟨-185389713856,-185389713792⟩ : DyadicInterval 40),(⟨748834167077,748834186406⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10845503,21706840⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10845440,10845504⟩ : DyadicInterval 40),(⟨-10845568,-10845504⟩ : DyadicInterval 40),(⟨762123383509,762123402838⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21706624,21706688⟩ : DyadicInterval 40),(⟨-21707072,-21707008⟩ : DyadicInterval 40),(⟨762123383347,762123402676⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170489017621,170613627076⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158496032896,158496032960⟩ : DyadicInterval 40),(⟨-185254854656,-185254854592⟩ : DyadicInterval 40),(⟨748851984361,748852003690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158603909056,158603909120⟩ : DyadicInterval 40),(⟨-185402341632,-185402341568⟩ : DyadicInterval 40),(⟨748832498214,748832517543⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26798432576,-26758821696⟩ : DyadicInterval 40),(⟨775502794464,775522619168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158514489152,158613136832⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185414959232,-185280085376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1953_ok : ecellOkT e1953 = true := by decide +kernel
theorem e1953_pos {a z : ℝ} (ha1 : ((1270401/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((5085/32768 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1953 e1953_ok ha1 ha2 hz1 hz2 hz

-- box ['79347/512000', '1270401/8192000', '7999/8000', '1']  interval_lower 161044853/1099511627776
noncomputable def e1954 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1269908012793,0,true,158415832640,158415832704⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929115242759,0,false,-185145228096,-185145228032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270021963645,0,true,158514489152,158514489216⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨929001291907,0,false,-185280085440,-185280085376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1269886713244,0,true,158397390912,158397390976⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929136542308,0,false,-185120022592,-185120022528⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522473843,0,true,10845952,10846016⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500781709,0,false,-10846144,-10846080⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627669,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1269897358533,0,true,158406607936,158406608000⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨929125897019,0,false,-185132619968,-185132619904⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1270021968005,0,true,158514492928,158514492992⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨929001287547,0,false,-185280090560,-185280090496⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1073069182429,0,false,-26765597632,-26765597568⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1073107816746,0,false,-26726011968,-26726011904⟩
    { al := (79347/512000), au := (1270401/8192000), zl := (7999/8000), zu := 1,
      A := ⟨170396385017,170510335869⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158415832640,158415832704⟩ : DyadicInterval 40),(⟨-185145228096,-185145228032⟩ : DyadicInterval 40),(⟨748866460688,748866480017⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158514489152,158514489216⟩ : DyadicInterval 40),(⟨-185280085440,-185280085376⟩ : DyadicInterval 40),(⟨748848651705,748848671035⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158397390912,158397390976⟩ : DyadicInterval 40),(⟨-185120022592,-185120022528⟩ : DyadicInterval 40),(⟨748869788186,748869807515⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158514489152,158514489216⟩ : DyadicInterval 40),(⟨-185280085440,-185280085376⟩ : DyadicInterval 40),(⟨748848651705,748848671035⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10846067⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10845952,10846016⟩ : DyadicInterval 40),(⟨-10846144,-10846080⟩ : DyadicInterval 40),(⟨762123383541,762123402870⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨170385730757,170510340229⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158406607936,158406608000⟩ : DyadicInterval 40),(⟨-185132619968,-185132619904⟩ : DyadicInterval 40),(⟨748868125189,748868144518⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158514492928,158514492992⟩ : DyadicInterval 40),(⟨-185280090560,-185280090496⟩ : DyadicInterval 40),(⟨748848651006,748848670335⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26765597632,-26726011904⟩ : DyadicInterval 40),(⟨775486389568,775506201696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨158415832640,158514489216⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185280085440,-185145228032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1954_ok : ecellOkT e1954 = true := by decide +kernel
theorem e1954_pos {a z : ℝ} (ha1 : ((79347/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1270401/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1954 e1954_ok ha1 ha2 hz1 hz2 hz

-- box ['1270401/8192000', '5085/32768', '7999/8000', '1']  interval_lower 10131329/68719476736
noncomputable def e1955 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270021963644,0,true,158514489152,158514489216⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨929001291908,0,false,-185280085440,-185280085376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270135914496,0,true,158613136768,158613136832⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928887341056,0,false,-185414959232,-185414959168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270000649851,0,true,158496036736,158496036800⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨929022605701,0,false,-185254859968,-185254859904⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522481348,0,true,10853504,10853568⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500774204,0,false,-10853632,-10853568⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627668,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1270011302258,0,true,158505259072,158505259136⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨929011953294,0,false,-185267467264,-185267467200⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1270135918857,0,true,158613140544,158613140608⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨928887336695,0,false,-185414964416,-185414964352⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1073033828022,0,false,-26801823808,-26801823744⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1073072490378,0,false,-26762208192,-26762208128⟩
    { al := (1270401/8192000), au := (5085/32768), zl := (7999/8000), zu := 1,
      A := ⟨170510335868,170624286720⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158514489152,158514489216⟩ : DyadicInterval 40),(⟨-185280085440,-185280085376⟩ : DyadicInterval 40),(⟨748848651706,748848671035⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158613136768,158613136832⟩ : DyadicInterval 40),(⟨-185414959232,-185414959168⟩ : DyadicInterval 40),(⟨748830830608,748830849938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158496036736,158496036800⟩ : DyadicInterval 40),(⟨-185254859968,-185254859904⟩ : DyadicInterval 40),(⟨748851983691,748852003020⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158613136768,158613136832⟩ : DyadicInterval 40),(⟨-185414959232,-185414959168⟩ : DyadicInterval 40),(⟨748830830608,748830849938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10853572⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10853504,10853568⟩ : DyadicInterval 40),(⟨-10853632,-10853568⟩ : DyadicInterval 40),(⟨762123383508,762123402837⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨170499674482,170624291081⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158505259072,158505259136⟩ : DyadicInterval 40),(⟨-185267467264,-185267467200⟩ : DyadicInterval 40),(⟨748850318444,748850337773⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158613140544,158613140608⟩ : DyadicInterval 40),(⟨-185414964416,-185414964352⟩ : DyadicInterval 40),(⟨748830829935,748830849264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26801823808,-26762208128⟩ : DyadicInterval 40),(⟨775504487680,775524314784⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨158514489152,158613136832⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185414959232,-185280085376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1955_ok : ecellOkT e1955 = true := by decide +kernel
theorem e1955_pos {a z : ℝ} (ha1 : ((1270401/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((5085/32768 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1955 e1955_ok ha1 ha2 hz1 hz2 hz

-- box ['5085/32768', '1272099/8192000', '3999/4000', '7999/8000']  interval_lower 81656689/549755813888
noncomputable def e1956 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270135914496,0,true,158613136768,158613136832⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928887341056,0,false,-185414959232,-185414959168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270249865348,0,true,158711775552,158711775616⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928773390204,0,false,-185549849664,-185549849600⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270093258424,0,true,158576210304,158576210368⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928929997128,0,false,-185364468992,-185364468928⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270228523069,0,true,158693301824,158693301888⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928794732483,0,false,-185524584256,-185524584192⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522480785,0,true,10852928,10852992⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500774767,0,false,-10853120,-10853056⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533349630,0,true,21721600,21721664⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489905922,0,false,-21722112,-21722048⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627346,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627669,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270114582005,0,true,158594669824,158594669888⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928908673547,0,false,-185389708544,-185389708480⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270239198580,0,true,158702542528,158702542592⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928784056972,0,false,-185537222016,-185537221952⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073001764036,0,false,-26834679488,-26834679424⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073040449795,0,false,-26795038656,-26795038592⟩
    { al := (5085/32768), au := (1272099/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨170624286720,170738237572⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158613136768,158613136832⟩ : DyadicInterval 40),(⟨-185414959232,-185414959168⟩ : DyadicInterval 40),(⟨748830830608,748830849938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158711775552,158711775616⟩ : DyadicInterval 40),(⟨-185549849664,-185549849600⟩ : DyadicInterval 40),(⟨748812997440,748813016769⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158576210304,158576210368⟩ : DyadicInterval 40),(⟨-185364468992,-185364468928⟩ : DyadicInterval 40),(⟨748837503135,748837522465⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158693301824,158693301888⟩ : DyadicInterval 40),(⟨-185524584256,-185524584192⟩ : DyadicInterval 40),(⟨748816338380,748816357710⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10853009,21721854⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10852928,10852992⟩ : DyadicInterval 40),(⟨-10853120,-10853056⟩ : DyadicInterval 40),(⟨762123383540,762123402869⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21721600,21721664⟩ : DyadicInterval 40),(⟨-21722112,-21722048⟩ : DyadicInterval 40),(⟨762123383378,762123402707⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170602954229,170727570804⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158594669824,158594669888⟩ : DyadicInterval 40),(⟨-185389708544,-185389708480⟩ : DyadicInterval 40),(⟨748834167785,748834187114⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158702542528,158702542592⟩ : DyadicInterval 40),(⟨-185537222016,-185537221952⟩ : DyadicInterval 40),(⟨748814667249,748814686579⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26834679488,-26795038592⟩ : DyadicInterval 40),(⟨775520902912,775540742624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158613136768,158711775616⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185549849664,-185414959168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1956_ok : ecellOkT e1956 = true := by decide +kernel
theorem e1956_pos {a z : ℝ} (ha1 : ((5085/32768 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1272099/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1956 e1956_ok ha1 ha2 hz1 hz2 hz

-- box ['1272099/8192000', '318237/2048000', '3999/4000', '7999/8000']  interval_lower 82187687/549755813888
noncomputable def e1957 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270249865347,0,true,158711775552,158711775616⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928773390205,0,false,-185549849664,-185549849600⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270363816199,0,true,158810405504,158810405568⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928659439353,0,false,-185684756544,-185684756480⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270207180787,0,true,158674827776,158674827840⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928816074765,0,false,-185499319424,-185499319360⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270342459676,0,true,158791921088,158791921152⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928680795876,0,false,-185659471232,-185659471168⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522488292,0,true,10860416,10860480⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500767260,0,false,-10860608,-10860544⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533364645,0,true,21736640,21736704⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489890907,0,false,-21737088,-21737024⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627346,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627669,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270228518611,0,true,158693297984,158693298048⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928794736941,0,false,-185524579008,-185524578944⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270353142312,0,true,158801167104,158801167168⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928670113240,0,false,-185672118976,-185672118912⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072966366815,0,false,-26870951872,-26870951808⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1073005080615,0,false,-26831280960,-26831280896⟩
    { al := (1272099/8192000), au := (318237/2048000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨170738237571,170852188423⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158711775552,158711775616⟩ : DyadicInterval 40),(⟨-185549849664,-185549849600⟩ : DyadicInterval 40),(⟨748812997440,748813016769⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158810405504,158810405568⟩ : DyadicInterval 40),(⟨-185684756544,-185684756480⟩ : DyadicInterval 40),(⟨748795152117,748795171446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158674827776,158674827840⟩ : DyadicInterval 40),(⟨-185499319424,-185499319360⟩ : DyadicInterval 40),(⟨748819678900,748819698230⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158791921088,158791921152⟩ : DyadicInterval 40),(⟨-185659471232,-185659471168⟩ : DyadicInterval 40),(⟨748798497590,748798516920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10860516,21736869⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10860416,10860480⟩ : DyadicInterval 40),(⟨-10860608,-10860544⟩ : DyadicInterval 40),(⟨762123383540,762123402869⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21736640,21736704⟩ : DyadicInterval 40),(⟨-21737088,-21737024⟩ : DyadicInterval 40),(⟨762123383346,762123402675⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170716890835,170841514536⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158693297984,158693298048⟩ : DyadicInterval 40),(⟨-185524579008,-185524578944⟩ : DyadicInterval 40),(⟨748816339080,748816358409⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158801167104,158801167168⟩ : DyadicInterval 40),(⟨-185672118976,-185672118912⟩ : DyadicInterval 40),(⟨748796824223,748796843553⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26870951872,-26831280896⟩ : DyadicInterval 40),(⟨775539024064,775558878816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158711775552,158810405568⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185684756544,-185549849600⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1957_ok : ecellOkT e1957 = true := by decide +kernel
theorem e1957_pos {a z : ℝ} (ha1 : ((1272099/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((318237/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1957 e1957_ok ha1 ha2 hz1 hz2 hz

-- box ['5085/32768', '1272099/8192000', '7999/8000', '1']  interval_lower 163160421/1099511627776
noncomputable def e1958 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270135914496,0,true,158613136768,158613136832⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928887341056,0,false,-185414959232,-185414959168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270249865348,0,true,158711775552,158711775616⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928773390204,0,false,-185549849664,-185549849600⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270114586460,0,true,158594673728,158594673792⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928908669092,0,false,-185389713856,-185389713792⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522488856,0,true,10860992,10861056⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500766696,0,false,-10861184,-10861120⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627668,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1270125245989,0,true,158603901376,158603901440⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨928898009563,0,false,-185402331136,-185402331072⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1270249869705,0,true,158711779328,158711779392⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨928773385847,0,false,-185549854784,-185549854720⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1072998449997,0,false,-26838075392,-26838075328⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1073037140391,0,false,-26798429696,-26798429632⟩
    { al := (5085/32768), au := (1272099/8192000), zl := (7999/8000), zu := 1,
      A := ⟨170624286720,170738237572⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158613136768,158613136832⟩ : DyadicInterval 40),(⟨-185414959232,-185414959168⟩ : DyadicInterval 40),(⟨748830830608,748830849938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158711775552,158711775616⟩ : DyadicInterval 40),(⟨-185549849664,-185549849600⟩ : DyadicInterval 40),(⟨748812997440,748813016769⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158594673728,158594673792⟩ : DyadicInterval 40),(⟨-185389713856,-185389713792⟩ : DyadicInterval 40),(⟨748834167077,748834186406⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158711775552,158711775616⟩ : DyadicInterval 40),(⟨-185549849664,-185549849600⟩ : DyadicInterval 40),(⟨748812997440,748813016769⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10861080⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10860992,10861056⟩ : DyadicInterval 40),(⟨-10861184,-10861120⟩ : DyadicInterval 40),(⟨762123383540,762123402869⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨170613618213,170738241929⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158603901376,158603901440⟩ : DyadicInterval 40),(⟨-185402331136,-185402331072⟩ : DyadicInterval 40),(⟨748832499603,748832518933⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158711779328,158711779392⟩ : DyadicInterval 40),(⟨-185549854784,-185549854720⟩ : DyadicInterval 40),(⟨748812996739,748813016068⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26838075392,-26798429632⟩ : DyadicInterval 40),(⟨775522598432,775542440576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨158613136768,158711775616⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185549849664,-185414959168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1958_ok : ecellOkT e1958 = true := by decide +kernel
theorem e1958_pos {a z : ℝ} (ha1 : ((5085/32768 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1272099/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1958 e1958_ok ha1 ha2 hz1 hz2 hz

-- box ['1272099/8192000', '318237/2048000', '7999/8000', '1']  interval_lower 41055555/274877906944
noncomputable def e1959 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270249865347,0,true,158711775552,158711775616⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928773390205,0,false,-185549849664,-185549849600⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270363816199,0,true,158810405504,158810405568⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928659439353,0,false,-185684756544,-185684756480⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270228523067,0,true,158693301824,158693301888⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928794732485,0,false,-185524584256,-185524584192⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522496363,0,true,10868480,10868544⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500759189,0,false,-10868672,-10868608⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627668,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1270239189713,0,true,158702534848,158702534912⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨928784065839,0,false,-185537211520,-185537211456⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1270363820563,0,true,158810409280,158810409344⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨928659434989,0,false,-185684761728,-185684761664⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1072963048349,0,false,-26874352448,-26874352384⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1073001766790,0,false,-26834676672,-26834676608⟩
    { al := (1272099/8192000), au := (318237/2048000), zl := (7999/8000), zu := 1,
      A := ⟨170738237571,170852188423⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158711775552,158711775616⟩ : DyadicInterval 40),(⟨-185549849664,-185549849600⟩ : DyadicInterval 40),(⟨748812997440,748813016769⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158810405504,158810405568⟩ : DyadicInterval 40),(⟨-185684756544,-185684756480⟩ : DyadicInterval 40),(⟨748795152117,748795171446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158693301824,158693301888⟩ : DyadicInterval 40),(⟨-185524584256,-185524584192⟩ : DyadicInterval 40),(⟨748816338380,748816357710⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158810405504,158810405568⟩ : DyadicInterval 40),(⟨-185684756544,-185684756480⟩ : DyadicInterval 40),(⟨748795152117,748795171446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10868587⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10868480,10868544⟩ : DyadicInterval 40),(⟨-10868672,-10868608⟩ : DyadicInterval 40),(⟨762123383540,762123402869⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨170727561937,170852192787⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158702534848,158702534912⟩ : DyadicInterval 40),(⟨-185537211520,-185537211456⟩ : DyadicInterval 40),(⟨748814668640,748814687970⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158810409280,158810409344⟩ : DyadicInterval 40),(⟨-185684761728,-185684761664⟩ : DyadicInterval 40),(⟨748795151441,748795170771⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26874352448,-26834676608⟩ : DyadicInterval 40),(⟨775540721920,775560579104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨158711775552,158810405568⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185684756544,-185549849600⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1959_ok : ecellOkT e1959 = true := by decide +kernel
theorem e1959_pos {a z : ℝ} (ha1 : ((1272099/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((318237/2048000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1959 e1959_ok ha1 ha2 hz1 hz2 hz

-- box ['318237/2048000', '1273797/8192000', '1999/2000', '7997/8000']  interval_lower 165747991/1099511627776
noncomputable def e1960 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270363816198,0,true,158810405504,158810405568⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928659439354,0,false,-185684756544,-185684756480⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270477767050,0,true,158909026624,158909026688⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928545488502,0,false,-185819680064,-185819680000⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270278390103,0,true,158736465920,158736465984⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928744865449,0,false,-185583618688,-185583618624⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270413654748,0,true,158853540416,158853540480⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928609600804,0,false,-185743765888,-185743765824⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544232217,0,true,32603904,32603968⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479023335,0,false,-32604928,-32604864⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555131095,0,true,43502400,43502464⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468124457,0,false,-43504192,-43504128⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626054,0,false,-1728,-1664⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626810,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270321098831,0,true,158773432640,158773432704⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928702156721,0,false,-185634181312,-185634181248⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270445715369,0,true,158881287680,158881287744⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928577540183,0,false,-185781727616,-185781727552⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072937591119,0,false,-26900439872,-26900439808⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072976323679,0,false,-26860748672,-26860748608⟩
    { al := (318237/2048000), au := (1273797/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨170852188422,170966139274⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158810405504,158810405568⟩ : DyadicInterval 40),(⟨-185684756544,-185684756480⟩ : DyadicInterval 40),(⟨748795152117,748795171446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158909026624,158909026688⟩ : DyadicInterval 40),(⟨-185819680064,-185819680000⟩ : DyadicInterval 40),(⟨748777294720,748777314049⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158736465920,158736465984⟩ : DyadicInterval 40),(⟨-185583618688,-185583618624⟩ : DyadicInterval 40),(⟨748808531451,748808550781⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158853540416,158853540480⟩ : DyadicInterval 40),(⟨-185743765888,-185743765824⟩ : DyadicInterval 40),(⟨748787343343,748787362672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32604441,43503319⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32603904,32603968⟩ : DyadicInterval 40),(⟨-32604928,-32604864⟩ : DyadicInterval 40),(⟨762123383097,762123402426⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43502400,43502464⟩ : DyadicInterval 40),(⟨-43504192,-43504128⟩ : DyadicInterval 40),(⟨762123382726,762123402055⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1728,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170809471055,170934087593⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158773432640,158773432704⟩ : DyadicInterval 40),(⟨-185634181312,-185634181248⟩ : DyadicInterval 40),(⟨748801843273,748801862603⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158881287680,158881287744⟩ : DyadicInterval 40),(⟨-185781727616,-185781727552⟩ : DyadicInterval 40),(⟨748782318844,748782338174⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26900439872,-26860748608⟩ : DyadicInterval 40),(⟨775553757920,775573622816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158810405504,158909026688⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185819680064,-185684756480⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1960_ok : ecellOkT e1960 = true := by decide +kernel
theorem e1960_pos {a z : ℝ} (ha1 : ((318237/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1273797/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1960 e1960_ok ha1 ha2 hz1 hz2 hz

-- box ['1273797/8192000', '637323/4096000', '1999/2000', '7997/8000']  interval_lower 166816267/1099511627776
noncomputable def e1961 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270477767049,0,true,158909026624,158909026688⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928545488503,0,false,-185819680064,-185819680000⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270591717901,0,true,159007638848,159007638912⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928431537651,0,false,-185954620096,-185954620032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270392283979,0,true,158835044352,158835044416⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928630971573,0,false,-185718462272,-185718462208⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270527562868,0,true,158952120640,158952120704⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928495692684,0,false,-185878646016,-185878645952⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544254741,0,true,32626432,32626496⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479000811,0,false,-32627456,-32627392⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555161129,0,true,43532480,43532544⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468094423,0,false,-43534272,-43534208⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626052,0,false,-1728,-1664⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626808,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270435021195,0,true,158872032384,158872032448⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928588234357,0,false,-185769064896,-185769064832⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270559644853,0,true,158979883968,158979884032⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928463610699,0,false,-185916637696,-185916637632⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072902155527,0,false,-26936753728,-26936753664⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072940916126,0,false,-26897032512,-26897032448⟩
    { al := (1273797/8192000), au := (637323/4096000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨170966139273,171080090125⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158909026624,158909026688⟩ : DyadicInterval 40),(⟨-185819680064,-185819680000⟩ : DyadicInterval 40),(⟨748777294720,748777314050⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159007638848,159007638912⟩ : DyadicInterval 40),(⟨-185954620096,-185954620032⟩ : DyadicInterval 40),(⟨748759425230,748759444560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158835044352,158835044416⟩ : DyadicInterval 40),(⟨-185718462272,-185718462208⟩ : DyadicInterval 40),(⟨748790692031,748790711361⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158952120640,158952120704⟩ : DyadicInterval 40),(⟨-185878646016,-185878645952⟩ : DyadicInterval 40),(⟨748769487367,748769506696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32626965,43533353⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32626432,32626496⟩ : DyadicInterval 40),(⟨-32627456,-32627392⟩ : DyadicInterval 40),(⟨762123383095,762123402424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43532480,43532544⟩ : DyadicInterval 40),(⟨-43534272,-43534208⟩ : DyadicInterval 40),(⟨762123382724,762123402053⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1728,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170923393419,171048017077⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158872032384,158872032448⟩ : DyadicInterval 40),(⟨-185769064896,-185769064832⟩ : DyadicInterval 40),(⟨748783994900,748784014229⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158979883968,158979884032⟩ : DyadicInterval 40),(⟨-185916637696,-185916637632⟩ : DyadicInterval 40),(⟨748764456075,748764475405⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26936753728,-26897032448⟩ : DyadicInterval 40),(⟨775571899840,775591779744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158909026624,159007638912⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185954620096,-185819680000⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1961_ok : ecellOkT e1961 = true := by decide +kernel
theorem e1961_pos {a z : ℝ} (ha1 : ((1273797/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((637323/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1961 e1961_ok ha1 ha2 hz1 hz2 hz

-- box ['318237/2048000', '1273797/8192000', '7997/8000', '3999/4000']  interval_lower 82797061/549755813888
noncomputable def e1962 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270363816198,0,true,158810405504,158810405568⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928659439354,0,false,-185684756544,-185684756480⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270477767050,0,true,158909026624,158909026688⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928545488502,0,false,-185819680064,-185819680000⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270299746627,0,true,158754951296,158754951360⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928723508925,0,false,-185608902272,-185608902208⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270435025516,0,true,158872036096,158872036160⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928588230036,0,false,-185769070016,-185769069952⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533364033,0,true,21736000,21736064⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489891519,0,false,-21736512,-21736448⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544255403,0,true,32627136,32627200⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479000149,0,false,-32628160,-32628096⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626807,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627347,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270331777013,0,true,158782674944,158782675008⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928691478539,0,false,-185646823552,-185646823488⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270456400693,0,true,158890535296,158890535360⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928566854859,0,false,-185794379968,-185794379904⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072934268656,0,false,-26903844608,-26903844544⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072973005857,0,false,-26864148608,-26864148544⟩
    { al := (318237/2048000), au := (1273797/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨170852188422,170966139274⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158810405504,158810405568⟩ : DyadicInterval 40),(⟨-185684756544,-185684756480⟩ : DyadicInterval 40),(⟨748795152117,748795171446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158909026624,158909026688⟩ : DyadicInterval 40),(⟨-185819680064,-185819680000⟩ : DyadicInterval 40),(⟨748777294720,748777314049⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158754951296,158754951360⟩ : DyadicInterval 40),(⟨-185608902272,-185608902208⟩ : DyadicInterval 40),(⟨748805187244,748805206573⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158872036096,158872036160⟩ : DyadicInterval 40),(⟨-185769070016,-185769069952⟩ : DyadicInterval 40),(⟨748783994240,748784013570⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21736257,32627627⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21736000,21736064⟩ : DyadicInterval 40),(⟨-21736512,-21736448⟩ : DyadicInterval 40),(⟨762123383378,762123402707⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32627136,32627200⟩ : DyadicInterval 40),(⟨-32628160,-32628096⟩ : DyadicInterval 40),(⟨762123383095,762123402424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170820149237,170944772917⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158782674944,158782675008⟩ : DyadicInterval 40),(⟨-185646823552,-185646823488⟩ : DyadicInterval 40),(⟨748800170850,748800190179⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158890535296,158890535360⟩ : DyadicInterval 40),(⟨-185794379968,-185794379904⟩ : DyadicInterval 40),(⟨748780644022,748780663351⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26903844608,-26864148544⟩ : DyadicInterval 40),(⟨775555457888,775575325184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158810405504,158909026688⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185819680064,-185684756480⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1962_ok : ecellOkT e1962 = true := by decide +kernel
theorem e1962_pos {a z : ℝ} (ha1 : ((318237/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1273797/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1962 e1962_ok ha1 ha2 hz1 hz2 hz

-- box ['1273797/8192000', '637323/4096000', '7997/8000', '3999/4000']  interval_lower 83331005/549755813888
noncomputable def e1963 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270477767049,0,true,158909026624,158909026688⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928545488503,0,false,-185819680064,-185819680000⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270591717901,0,true,159007638848,159007638912⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928431537651,0,false,-185954620096,-185954620032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270413654746,0,true,158853540416,158853540480⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928609600806,0,false,-185743765888,-185743765824⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270548947879,0,true,158970627008,158970627072⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928474307673,0,false,-185903970112,-185903970048⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533379049,0,true,21751040,21751104⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489876503,0,false,-21751552,-21751488⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544277928,0,true,32649664,32649728⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478977624,0,false,-32650688,-32650624⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626806,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627346,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270445706497,0,true,158881280064,158881280128⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928577549055,0,false,-185781717120,-185781717056⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270570337300,0,true,158989136896,158989136960⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928452918252,0,false,-185929300032,-185929299968⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072898828634,0,false,-26940163136,-26940163072⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072937593878,0,false,-26900437056,-26900436992⟩
    { al := (1273797/8192000), au := (637323/4096000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨170966139273,171080090125⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158909026624,158909026688⟩ : DyadicInterval 40),(⟨-185819680064,-185819680000⟩ : DyadicInterval 40),(⟨748777294720,748777314050⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159007638848,159007638912⟩ : DyadicInterval 40),(⟨-185954620096,-185954620032⟩ : DyadicInterval 40),(⟨748759425230,748759444560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158853540416,158853540480⟩ : DyadicInterval 40),(⟨-185743765888,-185743765824⟩ : DyadicInterval 40),(⟨748787343343,748787362672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158970627008,158970627072⟩ : DyadicInterval 40),(⟨-185903970112,-185903970048⟩ : DyadicInterval 40),(⟨748766133749,748766153079⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21751273,32650152⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21751040,21751104⟩ : DyadicInterval 40),(⟨-21751552,-21751488⟩ : DyadicInterval 40),(⟨762123383377,762123402706⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32649664,32649728⟩ : DyadicInterval 40),(⟨-32650688,-32650624⟩ : DyadicInterval 40),(⟨762123383094,762123402423⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170934078721,171058709524⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158881280064,158881280128⟩ : DyadicInterval 40),(⟨-185781717120,-185781717056⟩ : DyadicInterval 40),(⟨748782320203,748782339532⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158989136896,158989136960⟩ : DyadicInterval 40),(⟨-185929300032,-185929299968⟩ : DyadicInterval 40),(⟨748762779012,748762798342⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26940163136,-26900436992⟩ : DyadicInterval 40),(⟨775573602112,775593484448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158909026624,159007638912⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185954620096,-185819680000⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1963_ok : ecellOkT e1963 = true := by decide +kernel
theorem e1963_pos {a z : ℝ} (ha1 : ((1273797/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((637323/4096000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1963 e1963_ok ha1 ha2 hz1 hz2 hz

-- box ['637323/4096000', '255099/1638400', '1999/2000', '7997/8000']  interval_lower 41971807/274877906944
noncomputable def e1964 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270591717900,0,true,159007638848,159007638912⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928431537652,0,false,-185954620096,-185954620032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270705668752,0,true,159106242240,159106242304⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928317586800,0,false,-186089576704,-186089576640⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270506177854,0,true,158933613952,158933614016⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928517077698,0,false,-185853322432,-185853322368⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270641470987,0,true,159050692032,159050692096⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928381784565,0,false,-186013542656,-186013542592⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544277266,0,true,32648960,32649024⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478978286,0,false,-32649984,-32649920⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555191165,0,true,43562496,43562560⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468064387,0,false,-43564288,-43564224⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626049,0,false,-1728,-1664⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626807,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270548943558,0,true,158970623296,158970623360⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928474311994,0,false,-185903964992,-185903964928⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270673574339,0,true,159078471360,159078471424⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928349681213,0,false,-186051564352,-186051564288⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072866696325,0,false,-26973092928,-26973092864⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072905484966,0,false,-26933341696,-26933341632⟩
    { al := (637323/4096000), au := (255099/1638400), zl := (1999/2000), zu := (7997/8000),
      A := ⟨171080090124,171194040976⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159007638848,159007638912⟩ : DyadicInterval 40),(⟨-185954620096,-185954620032⟩ : DyadicInterval 40),(⟨748759425230,748759444560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159106242240,159106242304⟩ : DyadicInterval 40),(⟨-186089576704,-186089576640⟩ : DyadicInterval 40),(⟨748741543637,748741562966⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158933613952,158933614016⟩ : DyadicInterval 40),(⟨-185853322432,-185853322368⟩ : DyadicInterval 40),(⟨748772840534,748772859863⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159050692032,159050692096⟩ : DyadicInterval 40),(⟨-186013542656,-186013542592⟩ : DyadicInterval 40),(⟨748751619280,748751638609⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32649490,43563389⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32648960,32649024⟩ : DyadicInterval 40),(⟨-32649984,-32649920⟩ : DyadicInterval 40),(⟨762123383094,762123402423⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43562496,43562560⟩ : DyadicInterval 40),(⟨-43564288,-43564224⟩ : DyadicInterval 40),(⟨762123382721,762123402051⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1728,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171037315782,171161946563⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158970623296,158970623360⟩ : DyadicInterval 40),(⟨-185903964992,-185903964928⟩ : DyadicInterval 40),(⟨748766134410,748766153739⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159078471360,159078471424⟩ : DyadicInterval 40),(⟨-186051564352,-186051564288⟩ : DyadicInterval 40),(⟨748746581249,748746600578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26973092928,-26933341632⟩ : DyadicInterval 40),(⟨775590054432,775609949344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159007638848,159106242304⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186089576704,-185954620032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1964_ok : ecellOkT e1964 = true := by decide +kernel
theorem e1964_pos {a z : ℝ} (ha1 : ((637323/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((255099/1638400 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1964 e1964_ok ha1 ha2 hz1 hz2 hz

-- box ['255099/1638400', '159543/1024000', '1999/2000', '7997/8000']  interval_lower 168960493/1099511627776
noncomputable def e1965 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270705668751,0,true,159106242240,159106242304⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928317586801,0,false,-186089576704,-186089576640⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270819619603,0,true,159204836800,159204836864⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928203635949,0,false,-186224549888,-186224549824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270620071730,0,true,159032174656,159032174720⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928403183822,0,false,-185988199168,-185988199104⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270755379107,0,true,159149254592,159149254656⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928267876445,0,false,-186148455872,-186148455808⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544299792,0,true,32671488,32671552⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478955760,0,false,-32672512,-32672448⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555221202,0,true,43592512,43592576⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099468034350,0,false,-43594304,-43594240⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626047,0,false,-1792,-1728⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626806,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270662865914,0,true,159069205312,159069205376⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928360389638,0,false,-186038881664,-186038881600⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270787503824,0,true,159177049920,159177049984⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928235751728,0,false,-186186507520,-186186507456⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072831213513,0,false,-27009457600,-27009457536⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072870030202,0,false,-26969676288,-26969676224⟩
    { al := (255099/1638400), au := (159543/1024000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨171194040975,171307991827⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159106242240,159106242304⟩ : DyadicInterval 40),(⟨-186089576704,-186089576640⟩ : DyadicInterval 40),(⟨748741543637,748741562966⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159204836800,159204836864⟩ : DyadicInterval 40),(⟨-186224549888,-186224549824⟩ : DyadicInterval 40),(⟨748723649939,748723669268⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159032174656,159032174720⟩ : DyadicInterval 40),(⟨-185988199168,-185988199104⟩ : DyadicInterval 40),(⟨748754976994,748754996324⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159149254592,159149254656⟩ : DyadicInterval 40),(⟨-186148455872,-186148455808⟩ : DyadicInterval 40),(⟨748733739107,748733758436⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨32672016,43593426⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32671488,32671552⟩ : DyadicInterval 40),(⟨-32672512,-32672448⟩ : DyadicInterval 40),(⟨762123383093,762123402422⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨43592512,43592576⟩ : DyadicInterval 40),(⟨-43594304,-43594240⟩ : DyadicInterval 40),(⟨762123382719,762123402048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1792,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171151238138,171275876048⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159069205312,159069205376⟩ : DyadicInterval 40),(⟨-186038881664,-186038881600⟩ : DyadicInterval 40),(⟨748748261867,748748281196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159177049920,159177049984⟩ : DyadicInterval 40),(⟨-186186507520,-186186507456⟩ : DyadicInterval 40),(⟨748728694300,748728713629⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27009457600,-26969676224⟩ : DyadicInterval 40),(⟨775608221728,775628131680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159106242240,159204836864⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186224549888,-186089576640⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1965_ok : ecellOkT e1965 = true := by decide +kernel
theorem e1965_pos {a z : ℝ} (ha1 : ((255099/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((159543/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1965 e1965_ok ha1 ha2 hz1 hz2 hz

-- box ['637323/4096000', '255099/1638400', '7997/8000', '3999/4000']  interval_lower 10483277/68719476736
noncomputable def e1966 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270591717900,0,true,159007638848,159007638912⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928431537652,0,false,-185954620096,-185954620032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270705668752,0,true,159106242240,159106242304⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928317586800,0,false,-186089576704,-186089576640⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270527562866,0,true,158952120640,158952120704⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928495692686,0,false,-185878646016,-185878645952⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270662870242,0,true,159069209088,159069209152⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928360385310,0,false,-186038886784,-186038886720⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533394066,0,true,21766016,21766080⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489861486,0,false,-21766528,-21766464⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544300455,0,true,32672192,32672256⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478955097,0,false,-32673216,-32673152⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626805,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627346,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270559635979,0,true,158979876288,158979876352⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928463619573,0,false,-185916627200,-185916627136⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270684273906,0,true,159087729664,159087729728⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928338981646,0,false,-186064236672,-186064236608⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072863364999,0,false,-26976507008,-26976506944⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072902158289,0,false,-26936750848,-26936750784⟩
    { al := (637323/4096000), au := (255099/1638400), zl := (7997/8000), zu := (3999/4000),
      A := ⟨171080090124,171194040976⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159007638848,159007638912⟩ : DyadicInterval 40),(⟨-185954620096,-185954620032⟩ : DyadicInterval 40),(⟨748759425230,748759444560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159106242240,159106242304⟩ : DyadicInterval 40),(⟨-186089576704,-186089576640⟩ : DyadicInterval 40),(⟨748741543637,748741562966⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158952120640,158952120704⟩ : DyadicInterval 40),(⟨-185878646016,-185878645952⟩ : DyadicInterval 40),(⟨748769487367,748769506697⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159069209088,159069209152⟩ : DyadicInterval 40),(⟨-186038886784,-186038886720⟩ : DyadicInterval 40),(⟨748748261167,748748280496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21766290,32672679⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21766016,21766080⟩ : DyadicInterval 40),(⟨-21766528,-21766464⟩ : DyadicInterval 40),(⟨762123383377,762123402706⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32672192,32672256⟩ : DyadicInterval 40),(⟨-32673216,-32673152⟩ : DyadicInterval 40),(⟨762123383093,762123402422⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171048008203,171172646130⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158979876288,158979876352⟩ : DyadicInterval 40),(⟨-185916627200,-185916627136⟩ : DyadicInterval 40),(⟨748764457473,748764476802⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159087729664,159087729728⟩ : DyadicInterval 40),(⟨-186064236672,-186064236608⟩ : DyadicInterval 40),(⟨748744901906,748744921235⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26976507008,-26936750784⟩ : DyadicInterval 40),(⟨775591759008,775611656384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159007638848,159106242304⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186089576704,-185954620032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1966_ok : ecellOkT e1966 = true := by decide +kernel
theorem e1966_pos {a z : ℝ} (ha1 : ((637323/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((255099/1638400 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1966 e1966_ok ha1 ha2 hz1 hz2 hz

-- box ['255099/1638400', '159543/1024000', '7997/8000', '3999/4000']  interval_lower 168805805/1099511627776
noncomputable def e1967 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270705668751,0,true,159106242240,159106242304⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928317586801,0,false,-186089576704,-186089576640⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270819619603,0,true,159204836800,159204836864⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928203635949,0,false,-186224549888,-186224549824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270641470985,0,true,159050692032,159050692096⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928381784567,0,false,-186013542656,-186013542592⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270776792606,0,true,159167782336,159167782400⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928246462946,0,false,-186173819968,-186173819904⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533409084,0,true,21781056,21781120⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489846468,0,false,-21781568,-21781504⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544322984,0,true,32694720,32694784⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478932568,0,false,-32695744,-32695680⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626803,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627345,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270673565462,0,true,159078463680,159078463744⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928349690090,0,false,-186051553792,-186051553728⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270798210517,0,true,159186313536,159186313600⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928225045035,0,false,-186199189888,-186199189824⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072827877749,0,false,-27012876288,-27012876224⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072866699090,0,false,-26973090112,-26973090048⟩
    { al := (255099/1638400), au := (159543/1024000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨171194040975,171307991827⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159106242240,159106242304⟩ : DyadicInterval 40),(⟨-186089576704,-186089576640⟩ : DyadicInterval 40),(⟨748741543637,748741562966⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159204836800,159204836864⟩ : DyadicInterval 40),(⟨-186224549888,-186224549824⟩ : DyadicInterval 40),(⟨748723649939,748723669268⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159050692032,159050692096⟩ : DyadicInterval 40),(⟨-186013542656,-186013542592⟩ : DyadicInterval 40),(⟨748751619280,748751638610⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159167782336,159167782400⟩ : DyadicInterval 40),(⟨-186173819968,-186173819904⟩ : DyadicInterval 40),(⟨748730376465,748730395794⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21781308,32695208⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21781056,21781120⟩ : DyadicInterval 40),(⟨-21781568,-21781504⟩ : DyadicInterval 40),(⟨762123383376,762123402705⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨32694720,32694784⟩ : DyadicInterval 40),(⟨-32695744,-32695680⟩ : DyadicInterval 40),(⟨762123383091,762123402420⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171161937686,171286582741⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159078463680,159078463744⟩ : DyadicInterval 40),(⟨-186051553792,-186051553728⟩ : DyadicInterval 40),(⟨748746582622,748746601951⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159186313536,159186313600⟩ : DyadicInterval 40),(⟨-186199189888,-186199189824⟩ : DyadicInterval 40),(⟨748727012737,748727032066⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27012876288,-26973090048⟩ : DyadicInterval 40),(⟨775609928640,775629841024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159106242240,159204836864⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186224549888,-186089576640⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1967_ok : ecellOkT e1967 = true := by decide +kernel
theorem e1967_pos {a z : ℝ} (ha1 : ((255099/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((159543/1024000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1967 e1967_ok ha1 ha2 hz1 hz2 hz

-- box ['318237/2048000', '1273797/8192000', '3999/4000', '7999/8000']  interval_lower 20680055/137438953472
noncomputable def e1968 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270363816198,0,true,158810405504,158810405568⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928659439354,0,false,-185684756544,-185684756480⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270477767050,0,true,158909026624,158909026688⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928545488502,0,false,-185819680064,-185819680000⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270321103150,0,true,158773436352,158773436416⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928702152402,0,false,-185634186432,-185634186368⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270456396283,0,true,158890531520,158890531584⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928566859269,0,false,-185794374720,-185794374656⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522495800,0,true,10867968,10868032⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500759752,0,false,-10868096,-10868032⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533379661,0,true,21751616,21751680⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489875891,0,false,-21752128,-21752064⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627345,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627669,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270342455218,0,true,158791917248,158791917312⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928680800334,0,false,-185659465920,-185659465856⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270467086044,0,true,158899782912,158899782976⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928556169508,0,false,-185807032512,-185807032448⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072930945977,0,false,-26907249600,-26907249536⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072969687821,0,false,-26867548672,-26867548608⟩
    { al := (318237/2048000), au := (1273797/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨170852188422,170966139274⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158810405504,158810405568⟩ : DyadicInterval 40),(⟨-185684756544,-185684756480⟩ : DyadicInterval 40),(⟨748795152117,748795171446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158909026624,158909026688⟩ : DyadicInterval 40),(⟨-185819680064,-185819680000⟩ : DyadicInterval 40),(⟨748777294720,748777314049⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158773436352,158773436416⟩ : DyadicInterval 40),(⟨-185634186432,-185634186368⟩ : DyadicInterval 40),(⟨748801842615,748801861945⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158890531520,158890531584⟩ : DyadicInterval 40),(⟨-185794374720,-185794374656⟩ : DyadicInterval 40),(⟨748780644678,748780664008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10868024,21751885⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10867968,10868032⟩ : DyadicInterval 40),(⟨-10868096,-10868032⟩ : DyadicInterval 40),(⟨762123383508,762123402837⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21751616,21751680⟩ : DyadicInterval 40),(⟨-21752128,-21752064⟩ : DyadicInterval 40),(⟨762123383377,762123402706⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170830827442,170955458268⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158791917248,158791917312⟩ : DyadicInterval 40),(⟨-185659465920,-185659465856⟩ : DyadicInterval 40),(⟨748798498263,748798517593⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158899782912,158899782976⟩ : DyadicInterval 40),(⟨-185807032512,-185807032448⟩ : DyadicInterval 40),(⟨748778969063,748778988392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26907249600,-26867548608⟩ : DyadicInterval 40),(⟨775557157920,775577027680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158810405504,158909026688⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185819680064,-185684756480⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1968_ok : ecellOkT e1968 = true := by decide +kernel
theorem e1968_pos {a z : ℝ} (ha1 : ((318237/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1273797/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1968 e1968_ok ha1 ha2 hz1 hz2 hz

-- box ['1273797/8192000', '637323/4096000', '3999/4000', '7999/8000']  interval_lower 166507847/1099511627776
noncomputable def e1969 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270477767049,0,true,158909026624,158909026688⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928545488503,0,false,-185819680064,-185819680000⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270591717901,0,true,159007638848,159007638912⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928431537651,0,false,-185954620096,-185954620032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270435025514,0,true,158872036096,158872036160⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928588230038,0,false,-185769070016,-185769069952⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270570332890,0,true,158989133056,158989133120⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928452922662,0,false,-185929294848,-185929294784⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522503308,0,true,10875456,10875520⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500752244,0,false,-10875648,-10875584⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533394678,0,true,21766656,21766720⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489860874,0,false,-21767168,-21767104⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627345,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627669,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270456391821,0,true,158890527616,158890527680⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928566863731,0,false,-185794369472,-185794369408⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270581029768,0,true,158998389760,158998389824⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928442225784,0,false,-185941962560,-185941962496⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072895501526,0,false,-26943572736,-26943572672⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072934271416,0,false,-26903841792,-26903841728⟩
    { al := (1273797/8192000), au := (637323/4096000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨170966139273,171080090125⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158909026624,158909026688⟩ : DyadicInterval 40),(⟨-185819680064,-185819680000⟩ : DyadicInterval 40),(⟨748777294720,748777314050⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159007638848,159007638912⟩ : DyadicInterval 40),(⟨-185954620096,-185954620032⟩ : DyadicInterval 40),(⟨748759425230,748759444560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158872036096,158872036160⟩ : DyadicInterval 40),(⟨-185769070016,-185769069952⟩ : DyadicInterval 40),(⟨748783994241,748784013570⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158989133056,158989133120⟩ : DyadicInterval 40),(⟨-185929294848,-185929294784⟩ : DyadicInterval 40),(⟨748762779734,748762799063⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10875532,21766902⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10875456,10875520⟩ : DyadicInterval 40),(⟨-10875648,-10875584⟩ : DyadicInterval 40),(⟨762123383540,762123402869⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21766656,21766720⟩ : DyadicInterval 40),(⟨-21767168,-21767104⟩ : DyadicInterval 40),(⟨762123383377,762123402706⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨170944764045,171069401992⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158890527616,158890527680⟩ : DyadicInterval 40),(⟨-185794369472,-185794369408⟩ : DyadicInterval 40),(⟨748780645417,748780664747⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158998389760,158998389824⟩ : DyadicInterval 40),(⟨-185941962560,-185941962496⟩ : DyadicInterval 40),(⟨748761101851,748761121180⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26943572736,-26903841728⟩ : DyadicInterval 40),(⟨775575304480,775595189248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨158909026624,159007638912⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185954620096,-185819680000⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1969_ok : ecellOkT e1969 = true := by decide +kernel
theorem e1969_pos {a z : ℝ} (ha1 : ((1273797/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((637323/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1969 e1969_ok ha1 ha2 hz1 hz2 hz

-- box ['318237/2048000', '1273797/8192000', '7999/8000', '1']  interval_lower 82643263/549755813888
noncomputable def e1970 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270363816198,0,true,158810405504,158810405568⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928659439354,0,false,-185684756544,-185684756480⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270477767050,0,true,158909026624,158909026688⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928545488502,0,false,-185819680064,-185819680000⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270342459674,0,true,158791921088,158791921152⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928680795878,0,false,-185659471232,-185659471168⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522503872,0,true,10876032,10876096⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500751680,0,false,-10876160,-10876096⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627668,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1270353133443,0,true,158801159424,158801159488⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨928670122109,0,false,-185672108480,-185672108416⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1270477771415,0,true,158909030400,158909030464⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨928545484137,0,false,-185819685248,-185819685184⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1072927623084,0,false,-26910654848,-26910654784⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1072966369572,0,false,-26870949056,-26870948992⟩
    { al := (318237/2048000), au := (1273797/8192000), zl := (7999/8000), zu := 1,
      A := ⟨170852188422,170966139274⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158810405504,158810405568⟩ : DyadicInterval 40),(⟨-185684756544,-185684756480⟩ : DyadicInterval 40),(⟨748795152117,748795171446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158909026624,158909026688⟩ : DyadicInterval 40),(⟨-185819680064,-185819680000⟩ : DyadicInterval 40),(⟨748777294720,748777314049⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158791921088,158791921152⟩ : DyadicInterval 40),(⟨-185659471232,-185659471168⟩ : DyadicInterval 40),(⟨748798497590,748798516920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158909026624,158909026688⟩ : DyadicInterval 40),(⟨-185819680064,-185819680000⟩ : DyadicInterval 40),(⟨748777294720,748777314049⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10876096⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10876032,10876096⟩ : DyadicInterval 40),(⟨-10876160,-10876096⟩ : DyadicInterval 40),(⟨762123383508,762123402837⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨170841505667,170966143639⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158801159424,158801159488⟩ : DyadicInterval 40),(⟨-185672108480,-185672108416⟩ : DyadicInterval 40),(⟨748796825617,748796844946⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158909030400,158909030464⟩ : DyadicInterval 40),(⟨-185819685248,-185819685184⟩ : DyadicInterval 40),(⟨748777294043,748777313373⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26910654848,-26870948992⟩ : DyadicInterval 40),(⟨775558858112,775578730304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨158810405504,158909026688⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185819680064,-185684756480⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1970_ok : ecellOkT e1970 = true := by decide +kernel
theorem e1970_pos {a z : ℝ} (ha1 : ((318237/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1273797/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1970 e1970_ok ha1 ha2 hz1 hz2 hz

-- box ['1273797/8192000', '637323/4096000', '7999/8000', '1']  interval_lower 166353873/1099511627776
noncomputable def e1971 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270477767049,0,true,158909026624,158909026688⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928545488503,0,false,-185819680064,-185819680000⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270591717901,0,true,159007638848,159007638912⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928431537651,0,false,-185954620096,-185954620032⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270456396281,0,true,158890531520,158890531584⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928566859271,0,false,-185794374720,-185794374656⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522511380,0,true,10883520,10883584⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500744172,0,false,-10883712,-10883648⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627668,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1270467077171,0,true,158899775232,158899775296⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨928556178381,0,false,-185807022016,-185807021952⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1270591722265,0,true,159007642624,159007642688⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨928431533287,0,false,-185954625280,-185954625216⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1072892174201,0,false,-26946982656,-26946982592⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1072930948737,0,false,-26907246784,-26907246720⟩
    { al := (1273797/8192000), au := (637323/4096000), zl := (7999/8000), zu := 1,
      A := ⟨170966139273,171080090125⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158909026624,158909026688⟩ : DyadicInterval 40),(⟨-185819680064,-185819680000⟩ : DyadicInterval 40),(⟨748777294720,748777314050⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159007638848,159007638912⟩ : DyadicInterval 40),(⟨-185954620096,-185954620032⟩ : DyadicInterval 40),(⟨748759425230,748759444560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158890531520,158890531584⟩ : DyadicInterval 40),(⟨-185794374720,-185794374656⟩ : DyadicInterval 40),(⟨748780644678,748780664008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159007638848,159007638912⟩ : DyadicInterval 40),(⟨-185954620096,-185954620032⟩ : DyadicInterval 40),(⟨748759425230,748759444560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10883604⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10883520,10883584⟩ : DyadicInterval 40),(⟨-10883712,-10883648⟩ : DyadicInterval 40),(⟨762123383540,762123402869⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨170955449395,171080094489⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158899775232,158899775296⟩ : DyadicInterval 40),(⟨-185807022016,-185807021952⟩ : DyadicInterval 40),(⟨748778970459,748778989788⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159007642624,159007642688⟩ : DyadicInterval 40),(⟨-185954625280,-185954625216⟩ : DyadicInterval 40),(⟨748759424552,748759443882⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26946982656,-26907246720⟩ : DyadicInterval 40),(⟨775577006976,775596894208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨158909026624,159007638912⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-185954620096,-185819680000⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1971_ok : ecellOkT e1971 = true := by decide +kernel
theorem e1971_pos {a z : ℝ} (ha1 : ((1273797/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((637323/4096000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1971 e1971_ok ha1 ha2 hz1 hz2 hz

-- box ['637323/4096000', '255099/1638400', '3999/4000', '7999/8000']  interval_lower 167577873/1099511627776
noncomputable def e1972 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270591717900,0,true,159007638848,159007638912⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928431537652,0,false,-185954620096,-185954620032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270705668752,0,true,159106242240,159106242304⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928317586800,0,false,-186089576704,-186089576640⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270548947877,0,true,158970627008,158970627072⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928474307675,0,false,-185903970112,-185903970048⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270684269497,0,true,159087725824,159087725888⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928338986055,0,false,-186064231424,-186064231360⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522510816,0,true,10882944,10883008⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500744736,0,false,-10883136,-10883072⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533409697,0,true,21781696,21781760⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489845855,0,false,-21782144,-21782080⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627344,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627669,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270570328425,0,true,158989129216,158989129280⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928452927127,0,false,-185929289536,-185929289472⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270694973501,0,true,159096987840,159096987904⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928328282051,0,false,-186076909184,-186076909120⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072860033456,0,false,-26979921280,-26979921216⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072898831396,0,false,-26940160256,-26940160192⟩
    { al := (637323/4096000), au := (255099/1638400), zl := (3999/4000), zu := (7999/8000),
      A := ⟨171080090124,171194040976⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159007638848,159007638912⟩ : DyadicInterval 40),(⟨-185954620096,-185954620032⟩ : DyadicInterval 40),(⟨748759425230,748759444560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159106242240,159106242304⟩ : DyadicInterval 40),(⟨-186089576704,-186089576640⟩ : DyadicInterval 40),(⟨748741543637,748741562966⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158970627008,158970627072⟩ : DyadicInterval 40),(⟨-185903970112,-185903970048⟩ : DyadicInterval 40),(⟨748766133749,748766153079⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159087725824,159087725888⟩ : DyadicInterval 40),(⟨-186064231424,-186064231360⟩ : DyadicInterval 40),(⟨748744902601,748744921931⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10883040,21781921⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10882944,10883008⟩ : DyadicInterval 40),(⟨-10883136,-10883072⟩ : DyadicInterval 40),(⟨762123383540,762123402869⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21781696,21781760⟩ : DyadicInterval 40),(⟨-21782144,-21782080⟩ : DyadicInterval 40),(⟨762123383344,762123402673⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171058700649,171183345725⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158989129216,158989129280⟩ : DyadicInterval 40),(⟨-185929289536,-185929289472⟩ : DyadicInterval 40),(⟨748762780410,748762799740⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159096987840,159096987904⟩ : DyadicInterval 40),(⟨-186076909184,-186076909120⟩ : DyadicInterval 40),(⟨748743222500,748743241829⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26979921280,-26940160192⟩ : DyadicInterval 40),(⟨775593463712,775613363520⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159007638848,159106242304⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186089576704,-185954620032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1972_ok : ecellOkT e1972 = true := by decide +kernel
theorem e1972_pos {a z : ℝ} (ha1 : ((637323/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((255099/1638400 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1972 e1972_ok ha1 ha2 hz1 hz2 hz

-- box ['255099/1638400', '159543/1024000', '3999/4000', '7999/8000']  interval_lower 168651077/1099511627776
noncomputable def e1973 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270705668751,0,true,159106242240,159106242304⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928317586801,0,false,-186089576704,-186089576640⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270819619603,0,true,159204836800,159204836864⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928203635949,0,false,-186224549888,-186224549824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270662870240,0,true,159069209088,159069209152⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928360385312,0,false,-186038886784,-186038886720⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270798206105,0,true,159186309696,159186309760⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928225049447,0,false,-186199184640,-186199184576⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522518326,0,true,10890496,10890560⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500737226,0,false,-10890624,-10890560⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533424715,0,true,21796672,21796736⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489830837,0,false,-21797184,-21797120⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627343,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627669,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270684265029,0,true,159087721984,159087722048⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928338990523,0,false,-186064226176,-186064226112⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270808917227,0,true,159195577088,159195577152⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928214338325,0,false,-186211872384,-186211872320⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072824541771,0,false,-27016295232,-27016295168⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072863367764,0,false,-26976504192,-26976504128⟩
    { al := (255099/1638400), au := (159543/1024000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨171194040975,171307991827⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159106242240,159106242304⟩ : DyadicInterval 40),(⟨-186089576704,-186089576640⟩ : DyadicInterval 40),(⟨748741543637,748741562966⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159204836800,159204836864⟩ : DyadicInterval 40),(⟨-186224549888,-186224549824⟩ : DyadicInterval 40),(⟨748723649939,748723669268⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159069209088,159069209152⟩ : DyadicInterval 40),(⟨-186038886784,-186038886720⟩ : DyadicInterval 40),(⟨748748261167,748748280497⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159186309696,159186309760⟩ : DyadicInterval 40),(⟨-186199184640,-186199184576⟩ : DyadicInterval 40),(⟨748727013433,748727032763⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10890550,21796939⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10890496,10890560⟩ : DyadicInterval 40),(⟨-10890624,-10890560⟩ : DyadicInterval 40),(⟨762123383508,762123402837⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21796672,21796736⟩ : DyadicInterval 40),(⟨-21797184,-21797120⟩ : DyadicInterval 40),(⟨762123383375,762123402704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171172637253,171297289451⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159087721984,159087722048⟩ : DyadicInterval 40),(⟨-186064226176,-186064226112⟩ : DyadicInterval 40),(⟨748744903306,748744922635⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159195577088,159195577152⟩ : DyadicInterval 40),(⟨-186211872384,-186211872320⟩ : DyadicInterval 40),(⟨748725331048,748725350378⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27016295232,-26976504128⟩ : DyadicInterval 40),(⟨775611635680,775631550496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159106242240,159204836864⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186224549888,-186089576640⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1973_ok : ecellOkT e1973 = true := by decide +kernel
theorem e1973_pos {a z : ℝ} (ha1 : ((255099/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((159543/1024000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1973 e1973_ok ha1 ha2 hz1 hz2 hz

-- box ['637323/4096000', '255099/1638400', '7999/8000', '1']  interval_lower 41855885/274877906944
noncomputable def e1974 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270591717900,0,true,159007638848,159007638912⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928431537652,0,false,-185954620096,-185954620032⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270705668752,0,true,159106242240,159106242304⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928317586800,0,false,-186089576704,-186089576640⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270570332888,0,true,158989133056,158989133120⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928452922664,0,false,-185929294848,-185929294784⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522518889,0,true,10891008,10891072⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500736663,0,false,-10891200,-10891136⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627668,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1270581020892,0,true,158998382080,158998382144⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨928442234660,0,false,-185941952064,-185941952000⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1270705673115,0,true,159106246016,159106246080⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨928317582437,0,false,-186089581888,-186089581824⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1072856701698,0,false,-26983335808,-26983335744⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1072895504289,0,false,-26943569920,-26943569856⟩
    { al := (637323/4096000), au := (255099/1638400), zl := (7999/8000), zu := 1,
      A := ⟨171080090124,171194040976⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159007638848,159007638912⟩ : DyadicInterval 40),(⟨-185954620096,-185954620032⟩ : DyadicInterval 40),(⟨748759425230,748759444560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159106242240,159106242304⟩ : DyadicInterval 40),(⟨-186089576704,-186089576640⟩ : DyadicInterval 40),(⟨748741543637,748741562966⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158989133056,158989133120⟩ : DyadicInterval 40),(⟨-185929294848,-185929294784⟩ : DyadicInterval 40),(⟨748762779734,748762799064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159106242240,159106242304⟩ : DyadicInterval 40),(⟨-186089576704,-186089576640⟩ : DyadicInterval 40),(⟨748741543637,748741562966⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10891113⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10891008,10891072⟩ : DyadicInterval 40),(⟨-10891200,-10891136⟩ : DyadicInterval 40),(⟨762123383540,762123402869⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨171069393116,171194045339⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨158998382080,158998382144⟩ : DyadicInterval 40),(⟨-185941952064,-185941952000⟩ : DyadicInterval 40),(⟨748761103249,748761122578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159106246016,159106246080⟩ : DyadicInterval 40),(⟨-186089581888,-186089581824⟩ : DyadicInterval 40),(⟨748741542958,748741562288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-26983335808,-26943569856⟩ : DyadicInterval 40),(⟨775595168544,775615070784⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨159007638848,159106242304⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186089576704,-185954620032⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1974_ok : ecellOkT e1974 = true := by decide +kernel
theorem e1974_pos {a z : ℝ} (ha1 : ((637323/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((255099/1638400 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1974 e1974_ok ha1 ha2 hz1 hz2 hz

-- box ['255099/1638400', '159543/1024000', '7999/8000', '1']  interval_lower 168495959/1099511627776
noncomputable def e1975 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270705668751,0,true,159106242240,159106242304⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928317586801,0,false,-186089576704,-186089576640⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270819619603,0,true,159204836800,159204836864⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928203635949,0,false,-186224549888,-186224549824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270684269495,0,true,159087725824,159087725888⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928338986057,0,false,-186064231424,-186064231360⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522526399,0,true,10898560,10898624⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500729153,0,false,-10898688,-10898624⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627667,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1270694964623,0,true,159096980160,159096980224⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨928328290929,0,false,-186076898688,-186076898624⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1270819623966,0,true,159204840576,159204840640⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨928203631586,0,false,-186224555072,-186224555008⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1072821205576,0,false,-27019714432,-27019714368⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1072860036221,0,false,-26979918464,-26979918400⟩
    { al := (255099/1638400), au := (159543/1024000), zl := (7999/8000), zu := 1,
      A := ⟨171194040975,171307991827⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159106242240,159106242304⟩ : DyadicInterval 40),(⟨-186089576704,-186089576640⟩ : DyadicInterval 40),(⟨748741543637,748741562966⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159204836800,159204836864⟩ : DyadicInterval 40),(⟨-186224549888,-186224549824⟩ : DyadicInterval 40),(⟨748723649939,748723669268⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159087725824,159087725888⟩ : DyadicInterval 40),(⟨-186064231424,-186064231360⟩ : DyadicInterval 40),(⟨748744902601,748744921931⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159204836800,159204836864⟩ : DyadicInterval 40),(⟨-186224549888,-186224549824⟩ : DyadicInterval 40),(⟨748723649939,748723669268⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10898623⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10898560,10898624⟩ : DyadicInterval 40),(⟨-10898688,-10898624⟩ : DyadicInterval 40),(⟨762123383507,762123402836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨171183336847,171307996190⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159096980160,159096980224⟩ : DyadicInterval 40),(⟨-186076898688,-186076898624⟩ : DyadicInterval 40),(⟨748743223900,748743243229⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159204840576,159204840640⟩ : DyadicInterval 40),(⟨-186224555072,-186224555008⟩ : DyadicInterval 40),(⟨748723649260,748723668589⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27019714432,-26979918400⟩ : DyadicInterval 40),(⟨775613342816,775633260096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨159106242240,159204836864⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186224549888,-186089576640⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1975_ok : ecellOkT e1975 = true := by decide +kernel
theorem e1975_pos {a z : ℝ} (ha1 : ((255099/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((159543/1024000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1975 e1975_ok ha1 ha2 hz1 hz2 hz

-- box ['159543/1024000', '1277193/8192000', '999/1000', '7993/8000']  interval_lower 170657127/1099511627776
noncomputable def e1976 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270819619602,0,true,159204836800,159204836864⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928203635950,0,false,-186224549888,-186224549824⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270933570454,0,true,159303422528,159303422592⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928089685098,0,false,-186359539648,-186359539584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270648311610,0,true,159056611328,159056611392⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928374943942,0,false,-186021644288,-186021644224⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270783576255,0,true,159173651712,159173651776⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928239679297,0,false,-186181855296,-186181855232⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587914706,0,true,76284224,76284288⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435340846,0,false,-76289600,-76289536⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099598873667,0,true,87242368,87242432⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099424381885,0,false,-87249408,-87249344⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620853,0,false,-6976,-6912⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622484,0,false,-5312,-5248⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270733961844,0,true,159130723328,159130723392⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928289293708,0,false,-186123087936,-186123087872⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270858578296,0,true,159238543296,159238543360⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928164677256,0,false,-186270699712,-186270699648⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072809065737,0,false,-27032156416,-27032156352⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072847891857,0,false,-26992364608,-26992364544⟩
    { al := (159543/1024000), au := (1277193/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨171307991826,171421942678⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159204836800,159204836864⟩ : DyadicInterval 40),(⟨-186224549888,-186224549824⟩ : DyadicInterval 40),(⟨748723649939,748723669268⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159303422528,159303422592⟩ : DyadicInterval 40),(⟨-186359539648,-186359539584⟩ : DyadicInterval 40),(⟨748705744134,748705763464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159056611328,159056611392⟩ : DyadicInterval 40),(⟨-186021644288,-186021644224⟩ : DyadicInterval 40),(⟨748750545873,748750565203⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159173651712,159173651776⟩ : DyadicInterval 40),(⟨-186181855296,-186181855232⟩ : DyadicInterval 40),(⟨748729311141,748729330470⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨76286930,87245891⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76284224,76284288⟩ : DyadicInterval 40),(⟨-76289600,-76289536⟩ : DyadicInterval 40),(⟨762123380946,762123400276⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨87242368,87242432⟩ : DyadicInterval 40),(⟨-87249408,-87249344⟩ : DyadicInterval 40),(⟨762123380148,762123399478⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6976,-5248⟩ : DyadicInterval 40),(⟨762123386240,762123406368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171222334068,171346950520⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159130723328,159130723392⟩ : DyadicInterval 40),(⟨-186123087936,-186123087872⟩ : DyadicInterval 40),(⟨748737101897,748737121227⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159238543296,159238543360⟩ : DyadicInterval 40),(⟨-186270699712,-186270699648⟩ : DyadicInterval 40),(⟨748717529480,748717548810⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27032156416,-26992364544⟩ : DyadicInterval 40),(⟨775619565888,775639481088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159204836800,159303422592⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186359539648,-186224549824⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1976_ok : ecellOkT e1976 = true := by decide +kernel
theorem e1976_pos {a z : ℝ} (ha1 : ((159543/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1277193/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1976 e1976_ok ha1 ha2 hz1 hz2 hz

-- box ['1277193/8192000', '639021/4096000', '999/1000', '7993/8000']  interval_lower 171737495/1099511627776
noncomputable def e1977 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270933570453,0,true,159303422528,159303422592⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928089685099,0,false,-186359539648,-186359539584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271047521305,0,true,159401999424,159401999488⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927975734247,0,false,-186494545984,-186494545920⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270762148510,0,true,159155111744,159155111808⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928261107042,0,false,-186156474112,-186156474048⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270897427399,0,true,159272153984,159272154048⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928125828153,0,false,-186316721664,-186316721600⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587967274,0,true,76336832,76336896⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435288278,0,false,-76342208,-76342144⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099598933750,0,true,87302464,87302528⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099424321802,0,false,-87309504,-87309440⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620843,0,false,-6976,-6912⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622476,0,false,-5312,-5248⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270847855720,0,true,159229266368,159229266432⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928175399832,0,false,-186257997760,-186257997696⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270972479297,0,true,159337082880,159337082944⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928050776255,0,false,-186405636096,-186405636032⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072773553469,0,false,-27068553152,-27068553088⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072812407628,0,false,-27028731328,-27028731264⟩
    { al := (1277193/8192000), au := (639021/4096000), zl := (999/1000), zu := (7993/8000),
      A := ⟨171421942677,171535893529⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159303422528,159303422592⟩ : DyadicInterval 40),(⟨-186359539648,-186359539584⟩ : DyadicInterval 40),(⟨748705744135,748705763464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159401999424,159401999488⟩ : DyadicInterval 40),(⟨-186494545984,-186494545920⟩ : DyadicInterval 40),(⟨748687826223,748687845553⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159155111744,159155111808⟩ : DyadicInterval 40),(⟨-186156474112,-186156474048⟩ : DyadicInterval 40),(⟨748732676141,748732695470⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159272153984,159272154048⟩ : DyadicInterval 40),(⟨-186316721664,-186316721600⟩ : DyadicInterval 40),(⟨748711424816,748711444146⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨76339498,87305974⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76336832,76336896⟩ : DyadicInterval 40),(⟨-76342208,-76342144⟩ : DyadicInterval 40),(⟨762123380939,762123400268⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨87302464,87302528⟩ : DyadicInterval 40),(⟨-87309504,-87309440⟩ : DyadicInterval 40),(⟨762123380139,762123399468⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6976,-5248⟩ : DyadicInterval 40),(⟨762123386240,762123406368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171336227944,171460851521⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159229266368,159229266432⟩ : DyadicInterval 40),(⟨-186257997760,-186257997696⟩ : DyadicInterval 40),(⟨748719214171,748719233501⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159337082880,159337082944⟩ : DyadicInterval 40),(⟨-186405636096,-186405636032⟩ : DyadicInterval 40),(⟨748699627381,748699646711⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27068553152,-27028731264⟩ : DyadicInterval 40),(⟨775637749248,775657679456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159303422528,159401999488⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186494545984,-186359539584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1977_ok : ecellOkT e1977 = true := by decide +kernel
theorem e1977_pos {a z : ℝ} (ha1 : ((1277193/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((639021/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1977 e1977_ok ha1 ha2 hz1 hz2 hz

-- box ['159543/1024000', '1277193/8192000', '7993/8000', '3997/4000']  interval_lower 170502097/1099511627776
noncomputable def e1978 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270819619602,0,true,159204836800,159204836864⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928203635950,0,false,-186224549888,-186224549824⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1270933570454,0,true,159303422528,159303422592⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨928089685098,0,false,-186359539648,-186359539584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270669725109,0,true,159075140608,159075140672⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928353530443,0,false,-186047005440,-186047005376⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270805003998,0,true,159192191360,159192191424⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928218251554,0,false,-186207236992,-186207236928⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577016683,0,true,65386944,65387008⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446238869,0,false,-65390912,-65390848⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587968135,0,true,76337664,76337728⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435287417,0,false,-76343040,-76342976⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622475,0,false,-5312,-5248⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623888,0,false,-3904,-3840⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270744668416,0,true,159139987200,159139987264⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928278587136,0,false,-186135769408,-186135769344⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270869292016,0,true,159247812480,159247812544⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928153963536,0,false,-186283391360,-186283391296⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072805726399,0,false,-27035578816,-27035578752⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072844557173,0,false,-26995782144,-26995782080⟩
    { al := (159543/1024000), au := (1277193/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨171307991826,171421942678⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159204836800,159204836864⟩ : DyadicInterval 40),(⟨-186224549888,-186224549824⟩ : DyadicInterval 40),(⟨748723649939,748723669268⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159303422528,159303422592⟩ : DyadicInterval 40),(⟨-186359539648,-186359539584⟩ : DyadicInterval 40),(⟨748705744134,748705763464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159075140608,159075140672⟩ : DyadicInterval 40),(⟨-186047005440,-186047005376⟩ : DyadicInterval 40),(⟨748747185375,748747204705⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159192191360,159192191424⟩ : DyadicInterval 40),(⟨-186207236992,-186207236928⟩ : DyadicInterval 40),(⟨748725945686,748725965016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨65388907,76340359⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65386944,65387008⟩ : DyadicInterval 40),(⟨-65390912,-65390848⟩ : DyadicInterval 40),(⟨762123381647,762123400976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76337664,76337728⟩ : DyadicInterval 40),(⟨-76343040,-76342976⟩ : DyadicInterval 40),(⟨762123380939,762123400268⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5312,-3840⟩ : DyadicInterval 40),(⟨762123385536,762123405536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171233040640,171357664240⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159139987200,159139987264⟩ : DyadicInterval 40),(⟨-186135769408,-186135769344⟩ : DyadicInterval 40),(⟨748735420895,748735440225⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159247812480,159247812544⟩ : DyadicInterval 40),(⟨-186283391360,-186283391296⟩ : DyadicInterval 40),(⟨748715846093,748715865423⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27035578816,-26995782080⟩ : DyadicInterval 40),(⟨775621274656,775641192288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159204836800,159303422592⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186359539648,-186224549824⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1978_ok : ecellOkT e1978 = true := by decide +kernel
theorem e1978_pos {a z : ℝ} (ha1 : ((159543/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1277193/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1978 e1978_ok ha1 ha2 hz1 hz2 hz

-- box ['1277193/8192000', '639021/4096000', '7993/8000', '3997/4000']  interval_lower 171582237/1099511627776
noncomputable def e1979 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1270933570453,0,true,159303422528,159303422592⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨928089685099,0,false,-186359539648,-186359539584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1271047521305,0,true,159401999424,159401999488⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨927975734247,0,false,-186494545984,-186494545920⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1270783576253,0,true,159173651712,159173651776⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨928239679299,0,false,-186181855296,-186181855232⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1270918869385,0,true,159290704256,159290704320⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨928104386167,0,false,-186342123392,-186342123328⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577061742,0,true,65432000,65432064⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099446193810,0,false,-65435968,-65435904⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588020708,0,true,76390272,76390336⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435234844,0,false,-76395648,-76395584⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622468,0,false,-5312,-5248⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623882,0,false,-3904,-3840⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1270858569414,0,true,159238535616,159238535680⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨928164686138,0,false,-186270689216,-186270689152⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1270983200134,0,true,159346357376,159346357440⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨928040055418,0,false,-186418337728,-186418337664⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072770209691,0,false,-27071980288,-27071980224⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072809068507,0,false,-27032153536,-27032153472⟩
    { al := (1277193/8192000), au := (639021/4096000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨171421942677,171535893529⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159303422528,159303422592⟩ : DyadicInterval 40),(⟨-186359539648,-186359539584⟩ : DyadicInterval 40),(⟨748705744135,748705763464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159401999424,159401999488⟩ : DyadicInterval 40),(⟨-186494545984,-186494545920⟩ : DyadicInterval 40),(⟨748687826223,748687845553⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159173651712,159173651776⟩ : DyadicInterval 40),(⟨-186181855296,-186181855232⟩ : DyadicInterval 40),(⟨748729311141,748729330470⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159290704256,159290704320⟩ : DyadicInterval 40),(⟨-186342123392,-186342123328⟩ : DyadicInterval 40),(⟨748708054889,748708074218⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨65433966,76392932⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨65432000,65432064⟩ : DyadicInterval 40),(⟨-65435968,-65435904⟩ : DyadicInterval 40),(⟨762123381641,762123400971⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76390272,76390336⟩ : DyadicInterval 40),(⟨-76395648,-76395584⟩ : DyadicInterval 40),(⟨762123380932,762123400261⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5312,-3840⟩ : DyadicInterval 40),(⟨762123385536,762123405536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨171346941638,171471572358⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159238535616,159238535680⟩ : DyadicInterval 40),(⟨-186270689216,-186270689152⟩ : DyadicInterval 40),(⟨748717530884,748717550213⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨159346357376,159346357440⟩ : DyadicInterval 40),(⟨-186418337728,-186418337664⟩ : DyadicInterval 40),(⟨748697941744,748697961073⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27071980288,-27032153472⟩ : DyadicInterval 40),(⟨775639460352,775659393024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨159303422528,159401999488⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-186494545984,-186359539584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1979_ok : ecellOkT e1979 = true := by decide +kernel
theorem e1979_pos {a z : ℝ} (ha1 : ((1277193/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((639021/4096000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1979 e1979_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B032

end


