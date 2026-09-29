-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B047_part00
-- name    : CK_CKLaneC2R_EpCells_B047_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:14:20.066263+00:00
-- url     : https://prove2.me/theorems/a6d923d7-531f-4a69-8cf2-d3d4369bfad4
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B047 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B047 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B047 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B047 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B047 (part 1 of 2).lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheckT

namespace CKLaneC2R.EpCells.B047

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['683169/4096000', '1367187/8192000', '3997/4000', '1599/1600']  interval_lower 300685603/1099511627776
noncomputable def e2820 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282898409816,0,true,169606039424,169606039488⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916124845736,0,false,-200626496512,-200626496448⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283012360668,0,true,169703696960,169703697024⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916010894884,0,false,-200763266176,-200763266112⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282760869729,0,true,169488153984,169488154048⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916262385823,0,false,-200461436544,-200461436480⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282897672711,0,true,169605407680,169605407744⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916125582841,0,false,-200625611840,-200625611776⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570114149,0,true,58484800,58484864⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453141403,0,false,-58487936,-58487872⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581857585,0,true,70227520,70227584⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441397967,0,false,-70232064,-70232000⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623290,0,false,-4544,-4480⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624665,0,false,-3136,-3072⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282829635505,0,true,169547094656,169547094720⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916193620047,0,false,-200543958272,-200543958208⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282955025528,0,true,169654561024,169654561088⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916068230024,0,false,-200694447488,-200694447424⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068905784846,0,false,-31039886400,-31039886336⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068947610890,0,false,-30996863616,-30996863552⟩
    { al := (683169/4096000), au := (1367187/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨183386782040,183500732892⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169606039424,169606039488⟩ : DyadicInterval 40),(⟨-200626496512,-200626496448⟩ : DyadicInterval 40),(⟨746758198113,746758217443⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169703696960,169703697024⟩ : DyadicInterval 40),(⟨-200763266176,-200763266112⟩ : DyadicInterval 40),(⟨746739007030,746739026360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169488153984,169488154048⟩ : DyadicInterval 40),(⟨-200461436544,-200461436480⟩ : DyadicInterval 40),(⟨746781345847,746781365176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169605407680,169605407744⟩ : DyadicInterval 40),(⟨-200625611840,-200625611776⟩ : DyadicInterval 40),(⟨746758322210,746758341539⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨58486373,70229809⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58484800,58484864⟩ : DyadicInterval 40),(⟨-58487936,-58487872⟩ : DyadicInterval 40),(⟨762123382008,762123401338⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70227520,70227584⟩ : DyadicInterval 40),(⟨-70232064,-70232000⟩ : DyadicInterval 40),(⟨762123381338,762123400667⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4544,-3072⟩ : DyadicInterval 40),(⟨762123385152,762123405152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183318007729,183443397752⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169547094656,169547094720⟩ : DyadicInterval 40),(⟨-200543958272,-200543958208⟩ : DyadicInterval 40),(⟨746769774877,746769794207⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169654561024,169654561088⟩ : DyadicInterval 40),(⟨-200694447488,-200694447424⟩ : DyadicInterval 40),(⟨746748664663,746748683992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31039886400,-30996863552⟩ : DyadicInterval 40),(⟨777621815392,777643346080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169606039424,169703697024⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200763266176,-200626496448⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2820_ok : ecellOkT e2820 = true := by decide +kernel
theorem e2820_pos {a z : ℝ} (ha1 : ((683169/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1367187/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2820 e2820_ok ha1 ha2 hz1 hz2 hz

-- box ['1367187/8192000', '342009/2048000', '3997/4000', '1599/1600']  interval_lower 302076075/1099511627776
noncomputable def e2821 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283012360667,0,true,169703696960,169703697024⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916010894885,0,false,-200763266176,-200763266112⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283126311519,0,true,169801345856,169801345920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915896944033,0,false,-200900052864,-200900052800⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282874735117,0,true,169585748800,169585748864⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916148520435,0,false,-200598083072,-200598083008⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283011552342,0,true,169703004288,169703004352⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916011703210,0,false,-200762295936,-200762295872⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570151992,0,true,58522624,58522688⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453103560,0,false,-58525824,-58525760⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581903004,0,true,70272960,70273024⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441352548,0,false,-70277504,-70277440⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623284,0,false,-4544,-4480⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624661,0,false,-3136,-3072⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282943543626,0,true,169644720832,169644720896⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916079711926,0,false,-200680666432,-200680666368⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283068940770,0,true,169752183744,169752183808⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915954314782,0,false,-200831182848,-200831182784⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068867761624,0,false,-31078999040,-31078998976⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068909616027,0,false,-31035945536,-31035945472⟩
    { al := (1367187/8192000), au := (342009/2048000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨183500732891,183614683743⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169703696960,169703697024⟩ : DyadicInterval 40),(⟨-200763266176,-200763266112⟩ : DyadicInterval 40),(⟨746739007031,746739026360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169801345856,169801345920⟩ : DyadicInterval 40),(⟨-200900052864,-200900052800⟩ : DyadicInterval 40),(⟨746719803785,746719823114⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169585748800,169585748864⟩ : DyadicInterval 40),(⟨-200598083072,-200598083008⟩ : DyadicInterval 40),(⟨746762183765,746762203095⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169703004288,169703004352⟩ : DyadicInterval 40),(⟨-200762295936,-200762295872⟩ : DyadicInterval 40),(⟨746739143188,746739162517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨58524216,70275228⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58522624,58522688⟩ : DyadicInterval 40),(⟨-58525824,-58525760⟩ : DyadicInterval 40),(⟨762123382036,762123401365⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70272960,70273024⟩ : DyadicInterval 40),(⟨-70277504,-70277440⟩ : DyadicInterval 40),(⟨762123381332,762123400661⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4544,-3072⟩ : DyadicInterval 40),(⟨762123385152,762123405152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183431915850,183557312994⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169644720832,169644720896⟩ : DyadicInterval 40),(⟨-200680666432,-200680666368⟩ : DyadicInterval 40),(⟨746750598328,746750617658⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169752183744,169752183808⟩ : DyadicInterval 40),(⟨-200831182848,-200831182784⟩ : DyadicInterval 40),(⟨746729473536,746729492866⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31078999040,-31035945472⟩ : DyadicInterval 40),(⟨777641356352,777662902400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169703696960,169801345920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200900052864,-200763266112⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2821_ok : ecellOkT e2821 = true := by decide +kernel
theorem e2821_pos {a z : ℝ} (ha1 : ((1367187/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((342009/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2821 e2821_ok ha1 ha2 hz1 hz2 hz

-- box ['683169/4096000', '1367187/8192000', '1599/1600', '1999/2000']  interval_lower 75121869/274877906944
noncomputable def e2822 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282898409816,0,true,169606039424,169606039488⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916124845736,0,false,-200626496512,-200626496448⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283012360668,0,true,169703696960,169703697024⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916010894884,0,false,-200763266176,-200763266112⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282783793077,0,true,169507802432,169507802496⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916239462475,0,false,-200488944768,-200488944704⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282920610302,0,true,169625066240,169625066304⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916102645250,0,false,-200653141376,-200653141312⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558416943,0,true,46788160,46788224⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464838609,0,false,-46790208,-46790144⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570152812,0,true,58523456,58523520⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453102740,0,false,-58526656,-58526592⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624660,0,false,-3136,-3072⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625785,0,false,-2048,-1984⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282841097022,0,true,169556918272,169556918336⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916182158530,0,false,-200557713216,-200557713152⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282966494190,0,true,169664389760,169664389824⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916056761362,0,false,-200708212864,-200708212800⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068901957845,0,false,-31043823040,-31043822976⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068943788888,0,false,-31000794944,-31000794880⟩
    { al := (683169/4096000), au := (1367187/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨183386782040,183500732892⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169606039424,169606039488⟩ : DyadicInterval 40),(⟨-200626496512,-200626496448⟩ : DyadicInterval 40),(⟨746758198113,746758217443⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169703696960,169703697024⟩ : DyadicInterval 40),(⟨-200763266176,-200763266112⟩ : DyadicInterval 40),(⟨746739007030,746739026360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169507802432,169507802496⟩ : DyadicInterval 40),(⟨-200488944768,-200488944704⟩ : DyadicInterval 40),(⟨746777489101,746777508430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169625066240,169625066304⟩ : DyadicInterval 40),(⟨-200653141376,-200653141312⟩ : DyadicInterval 40),(⟨746754460178,746754479508⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨46789167,58525036⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46788160,46788224⟩ : DyadicInterval 40),(⟨-46790208,-46790144⟩ : DyadicInterval 40),(⟨762123382584,762123401913⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58523456,58523520⟩ : DyadicInterval 40),(⟨-58526656,-58526592⟩ : DyadicInterval 40),(⟨762123382036,762123401365⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3136,-1984⟩ : DyadicInterval 40),(⟨762123384608,762123404448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183329469246,183454866414⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169556918272,169556918336⟩ : DyadicInterval 40),(⟨-200557713216,-200557713152⟩ : DyadicInterval 40),(⟨746767845880,746767865210⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169664389760,169664389824⟩ : DyadicInterval 40),(⟨-200708212864,-200708212800⟩ : DyadicInterval 40),(⟨746746733132,746746752461⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31043823040,-31000794880⟩ : DyadicInterval 40),(⟨777623781056,777645314400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169606039424,169703697024⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200763266176,-200626496448⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2822_ok : ecellOkT e2822 = true := by decide +kernel
theorem e2822_pos {a z : ℝ} (ha1 : ((683169/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1367187/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2822 e2822_ok ha1 ha2 hz1 hz2 hz

-- box ['1367187/8192000', '342009/2048000', '1599/1600', '1999/2000']  interval_lower 301877451/1099511627776
noncomputable def e2823 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283012360667,0,true,169703696960,169703697024⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916010894885,0,false,-200763266176,-200763266112⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283126311519,0,true,169801345856,169801345920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915896944033,0,false,-200900052864,-200900052800⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282897672708,0,true,169605407680,169605407744⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916125582844,0,false,-200625611840,-200625611776⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283034504178,0,true,169722673280,169722673344⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915988751374,0,false,-200789845952,-200789845888⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558447219,0,true,46818432,46818496⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464808333,0,false,-46820480,-46820416⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570190660,0,true,58561280,58561344⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453064892,0,false,-58564480,-58564416⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624656,0,false,-3136,-3072⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625783,0,false,-2048,-1984⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282955012260,0,true,169654549632,169654549696⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916068243292,0,false,-200694431552,-200694431488⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283080416555,0,true,169762017728,169762017792⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915942838997,0,false,-200844958464,-200844958400⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068863929868,0,false,-31082940672,-31082940608⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068905789274,0,false,-31039881856,-31039881792⟩
    { al := (1367187/8192000), au := (342009/2048000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨183500732891,183614683743⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169703696960,169703697024⟩ : DyadicInterval 40),(⟨-200763266176,-200763266112⟩ : DyadicInterval 40),(⟨746739007031,746739026360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169801345856,169801345920⟩ : DyadicInterval 40),(⟨-200900052864,-200900052800⟩ : DyadicInterval 40),(⟨746719803785,746719823114⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169605407680,169605407744⟩ : DyadicInterval 40),(⟨-200625611840,-200625611776⟩ : DyadicInterval 40),(⟨746758322211,746758341540⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169722673280,169722673344⟩ : DyadicInterval 40),(⟨-200789845952,-200789845888⟩ : DyadicInterval 40),(⟨746735276312,746735295642⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨46819443,58562884⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46818432,46818496⟩ : DyadicInterval 40),(⟨-46820480,-46820416⟩ : DyadicInterval 40),(⟨762123382582,762123401911⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58561280,58561344⟩ : DyadicInterval 40),(⟨-58564480,-58564416⟩ : DyadicInterval 40),(⟨762123382032,762123401361⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3136,-1984⟩ : DyadicInterval 40),(⟨762123384608,762123404448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183443384484,183568788779⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169654549632,169654549696⟩ : DyadicInterval 40),(⟨-200694431552,-200694431488⟩ : DyadicInterval 40),(⟨746748666905,746748686235⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169762017728,169762017792⟩ : DyadicInterval 40),(⟨-200844958464,-200844958400⟩ : DyadicInterval 40),(⟨746727539563,746727558893⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31082940672,-31039881792⟩ : DyadicInterval 40),(⟨777643324512,777664873216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169703696960,169801345920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200900052864,-200763266112⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2823_ok : ecellOkT e2823 = true := by decide +kernel
theorem e2823_pos {a z : ℝ} (ha1 : ((1367187/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((342009/2048000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2823 e2823_ok ha1 ha2 hz1 hz2 hz

-- box ['342009/2048000', '273777/1638400', '999/1000', '7993/8000']  interval_lower 303868055/1099511627776
noncomputable def e2824 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283126311518,0,true,169801345856,169801345920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915896944034,0,false,-200900052864,-200900052800⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283240262370,0,true,169898986048,169898986112⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915782993182,0,false,-201036856512,-201036856448⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282942696834,0,true,169643995072,169643995136⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916080558718,0,false,-200679650048,-200679649984⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283079499815,0,true,169761232192,169761232256⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915943755737,0,false,-200843857984,-200843857920⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593614345,0,true,81983488,81983552⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429641207,0,false,-81989632,-81989568⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099605388069,0,true,93756288,93756352⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099417867483,0,false,-93764352,-93764288⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619780,0,false,-8000,-7936⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621663,0,false,-6144,-6080⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283034500313,0,true,169722669952,169722670016⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915988755239,0,false,-200789841280,-200789841216⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283159890285,0,true,169830119168,169830119232⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915863365267,0,false,-200940364032,-200940363968⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068837387076,0,false,-31110244864,-31110244800⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068879259829,0,false,-31067171264,-31067171200⟩
    { al := (342009/2048000), au := (273777/1638400), zl := (999/1000), zu := (7993/8000),
      A := ⟨183614683742,183728634594⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169801345856,169801345920⟩ : DyadicInterval 40),(⟨-200900052864,-200900052800⟩ : DyadicInterval 40),(⟨746719803785,746719823114⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169898986048,169898986112⟩ : DyadicInterval 40),(⟨-201036856512,-201036856448⟩ : DyadicInterval 40),(⟨746700588385,746700607714⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169643995072,169643995136⟩ : DyadicInterval 40),(⟨-200679650048,-200679649984⟩ : DyadicInterval 40),(⟨746750740941,746750760270⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169761232192,169761232256⟩ : DyadicInterval 40),(⟨-200843857984,-200843857920⟩ : DyadicInterval 40),(⟨746727694031,746727713361⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨81986569,93760293⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81983488,81983552⟩ : DyadicInterval 40),(⟨-81989632,-81989568⟩ : DyadicInterval 40),(⟨762123380510,762123399839⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨93756288,93756352⟩ : DyadicInterval 40),(⟨-93764352,-93764288⟩ : DyadicInterval 40),(⟨762123379588,762123398917⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8000,-6080⟩ : DyadicInterval 40),(⟨762123386656,762123406880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183522872537,183648262509⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169722669952,169722670016⟩ : DyadicInterval 40),(⟨-200789841280,-200789841216⟩ : DyadicInterval 40),(⟨746735276959,746735296289⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169830119168,169830119232⟩ : DyadicInterval 40),(⟨-200940364032,-200940363968⟩ : DyadicInterval 40),(⟨746714142665,746714161995⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31110244864,-31067171200⟩ : DyadicInterval 40),(⟨777656969216,777678525312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169801345856,169898986112⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201036856512,-200900052800⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2824_ok : ecellOkT e2824 = true := by decide +kernel
theorem e2824_pos {a z : ℝ} (ha1 : ((342009/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((273777/1638400 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2824 e2824_ok ha1 ha2 hz1 hz2 hz

-- box ['273777/1638400', '684867/4096000', '999/1000', '7993/8000']  interval_lower 305265753/1099511627776
noncomputable def e2825 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283240262369,0,true,169898986048,169898986112⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915782993183,0,false,-201036856512,-201036856448⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283354213221,0,true,169996617600,169996617664⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915669042331,0,false,-201173677248,-201173677184⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283056533734,0,true,169741551616,169741551680⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915966721818,0,false,-200816289536,-200816289472⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283193350959,0,true,169858790528,169858790592⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915829904593,0,false,-200980534976,-200980534912⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593667335,0,true,82036480,82036544⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429588217,0,false,-82042624,-82042560⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099605448633,0,true,93816832,93816896⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099417806919,0,false,-93824896,-93824832⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619770,0,false,-8064,-8000⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621655,0,false,-6144,-6080⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283148394188,0,true,169820268352,169820268416⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915874861364,0,false,-200926562880,-200926562816⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283273791283,0,true,169927714112,169927714176⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915749464269,0,false,-201077112896,-201077112832⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068799326165,0,false,-31149398784,-31149398720⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068841227277,0,false,-31106294464,-31106294400⟩
    { al := (273777/1638400), au := (684867/4096000), zl := (999/1000), zu := (7993/8000),
      A := ⟨183728634593,183842585445⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169898986048,169898986112⟩ : DyadicInterval 40),(⟨-201036856512,-201036856448⟩ : DyadicInterval 40),(⟨746700588385,746700607715⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169996617600,169996617664⟩ : DyadicInterval 40),(⟨-201173677248,-201173677184⟩ : DyadicInterval 40),(⟨746681360845,746681380175⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169741551616,169741551680⟩ : DyadicInterval 40),(⟨-200816289536,-200816289472⟩ : DyadicInterval 40),(⟨746731564321,746731583650⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169858790528,169858790592⟩ : DyadicInterval 40),(⟨-200980534976,-200980534912⟩ : DyadicInterval 40),(⟨746708500444,746708519773⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨82039559,93820857⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82036480,82036544⟩ : DyadicInterval 40),(⟨-82042624,-82042560⟩ : DyadicInterval 40),(⟨762123380502,762123399831⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨93816832,93816896⟩ : DyadicInterval 40),(⟨-93824896,-93824832⟩ : DyadicInterval 40),(⟨762123379577,762123398907⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8064,-6080⟩ : DyadicInterval 40),(⟨762123386656,762123406912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183636766412,183762163507⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169820268352,169820268416⟩ : DyadicInterval 40),(⟨-200926562880,-200926562816⟩ : DyadicInterval 40),(⟨746716080955,746716100285⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169927714112,169927714176⟩ : DyadicInterval 40),(⟨-201077112896,-201077112832⟩ : DyadicInterval 40),(⟨746694932108,746694951437⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31149398784,-31106294400⟩ : DyadicInterval 40),(⟨777676530816,777698102272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169898986048,169996617664⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201173677248,-201036856448⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2825_ok : ecellOkT e2825 = true := by decide +kernel
theorem e2825_pos {a z : ℝ} (ha1 : ((273777/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((684867/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2825 e2825_ok ha1 ha2 hz1 hz2 hz

-- box ['342009/2048000', '273777/1638400', '7993/8000', '3997/4000']  interval_lower 151834551/549755813888
noncomputable def e2826 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283126311518,0,true,169801345856,169801345920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915896944034,0,false,-200900052864,-200900052800⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283240262370,0,true,169898986048,169898986112⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915782993182,0,false,-201036856512,-201036856448⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282965648669,0,true,169663665152,169663665216⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916057606883,0,false,-200707197952,-200707197888⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283102465895,0,true,169780912320,169780912384⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915920789657,0,false,-200871427136,-200871427072⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581902124,0,true,70272064,70272128⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441353428,0,false,-70276608,-70276544⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593668277,0,true,82037440,82037504⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429587275,0,false,-82043584,-82043520⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621654,0,false,-6144,-6080⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623285,0,false,-4544,-4480⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283045976013,0,true,169732504192,169732504256⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915977279539,0,false,-200803616256,-200803616192⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283171373131,0,true,169839958528,169839958592⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915851882421,0,false,-200954149504,-200954149440⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068833551062,0,false,-31114190976,-31114190912⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068875428821,0,false,-31071112064,-31071112000⟩
    { al := (342009/2048000), au := (273777/1638400), zl := (7993/8000), zu := (3997/4000),
      A := ⟨183614683742,183728634594⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169801345856,169801345920⟩ : DyadicInterval 40),(⟨-200900052864,-200900052800⟩ : DyadicInterval 40),(⟨746719803785,746719823114⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169898986048,169898986112⟩ : DyadicInterval 40),(⟨-201036856512,-201036856448⟩ : DyadicInterval 40),(⟨746700588385,746700607714⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169663665152,169663665216⟩ : DyadicInterval 40),(⟨-200707197952,-200707197888⟩ : DyadicInterval 40),(⟨746746875507,746746894837⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169780912320,169780912384⟩ : DyadicInterval 40),(⟨-200871427136,-200871427072⟩ : DyadicInterval 40),(⟨746723823309,746723842639⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨70274348,82040501⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70272064,70272128⟩ : DyadicInterval 40),(⟨-70276608,-70276544⟩ : DyadicInterval 40),(⟨762123381332,762123400661⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82037440,82037504⟩ : DyadicInterval 40),(⟨-82043584,-82043520⟩ : DyadicInterval 40),(⟨762123380502,762123399831⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6144,-4480⟩ : DyadicInterval 40),(⟨762123385856,762123405952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183534348237,183659745355⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169732504192,169732504256⟩ : DyadicInterval 40),(⟨-200803616256,-200803616192⟩ : DyadicInterval 40),(⟨746733343324,746733362654⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169839958528,169839958592⟩ : DyadicInterval 40),(⟨-200954149504,-200954149440⟩ : DyadicInterval 40),(⟨746712206517,746712225847⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31114190976,-31071112000⟩ : DyadicInterval 40),(⟨777658939616,777680498368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169801345856,169898986112⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201036856512,-200900052800⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2826_ok : ecellOkT e2826 = true := by decide +kernel
theorem e2826_pos {a z : ℝ} (ha1 : ((342009/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((273777/1638400 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2826 e2826_ok ha1 ha2 hz1 hz2 hz

-- box ['273777/1638400', '684867/4096000', '7993/8000', '3997/4000']  interval_lower 76266619/274877906944
noncomputable def e2827 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283240262369,0,true,169898986048,169898986112⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915782993183,0,false,-201036856512,-201036856448⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283354213221,0,true,169996617600,169996617664⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915669042331,0,false,-201173677248,-201173677184⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283079499813,0,true,169761232192,169761232256⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915943755739,0,false,-200843857984,-200843857920⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283216331283,0,true,169878481152,169878481216⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915806924269,0,false,-201008124672,-201008124608⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581947543,0,true,70317504,70317568⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441308009,0,false,-70322048,-70321984⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593721272,0,true,82090368,82090432⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429534280,0,false,-82096576,-82096512⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621646,0,false,-6144,-6080⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623279,0,false,-4544,-4480⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283159877013,0,true,169830107776,169830107840⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915863378539,0,false,-200940348160,-200940348096⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283285281253,0,true,169937558656,169937558720⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915737974299,0,false,-201090908672,-201090908608⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068795485391,0,false,-31153349952,-31153349888⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068837391510,0,false,-31110240320,-31110240256⟩
    { al := (273777/1638400), au := (684867/4096000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨183728634593,183842585445⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169898986048,169898986112⟩ : DyadicInterval 40),(⟨-201036856512,-201036856448⟩ : DyadicInterval 40),(⟨746700588385,746700607715⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169996617600,169996617664⟩ : DyadicInterval 40),(⟨-201173677248,-201173677184⟩ : DyadicInterval 40),(⟨746681360845,746681380175⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169761232192,169761232256⟩ : DyadicInterval 40),(⟨-200843857984,-200843857920⟩ : DyadicInterval 40),(⟨746727694031,746727713361⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169878481152,169878481216⟩ : DyadicInterval 40),(⟨-201008124672,-201008124608⟩ : DyadicInterval 40),(⟨746704624858,746704644187⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨70319767,82093496⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70317504,70317568⟩ : DyadicInterval 40),(⟨-70322048,-70321984⟩ : DyadicInterval 40),(⟨762123381326,762123400655⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82090368,82090432⟩ : DyadicInterval 40),(⟨-82096576,-82096512⟩ : DyadicInterval 40),(⟨762123380526,762123399855⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6144,-4480⟩ : DyadicInterval 40),(⟨762123385856,762123405952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183648249237,183773653477⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169830107776,169830107840⟩ : DyadicInterval 40),(⟨-200940348160,-200940348096⟩ : DyadicInterval 40),(⟨746714144940,746714164270⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169937558656,169937558720⟩ : DyadicInterval 40),(⟨-201090908672,-201090908608⟩ : DyadicInterval 40),(⟨746692993576,746693012906⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31153349952,-31110240256⟩ : DyadicInterval 40),(⟨777678503744,777700077856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169898986048,169996617664⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201173677248,-201036856448⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2827_ok : ecellOkT e2827 = true := by decide +kernel
theorem e2827_pos {a z : ℝ} (ha1 : ((273777/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((684867/4096000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2827 e2827_ok ha1 ha2 hz1 hz2 hz

-- box ['684867/4096000', '1370583/8192000', '999/1000', '7993/8000']  interval_lower 306666777/1099511627776
noncomputable def e2828 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283354213220,0,true,169996617600,169996617664⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915669042332,0,false,-201173677248,-201173677184⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283468164072,0,true,170094240512,170094240576⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915555091480,0,false,-201310515008,-201310514944⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283170370634,0,true,169839099520,169839099584⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915852884918,0,false,-200952945984,-200952945920⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283307202103,0,true,169956340160,169956340224⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915716053449,0,false,-201117228992,-201117228928⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593720329,0,true,82089472,82089536⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429535223,0,false,-82095680,-82095616⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099605509203,0,true,93877376,93877440⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099417746349,0,false,-93885440,-93885376⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619759,0,false,-8064,-8000⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621647,0,false,-6144,-6080⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283262288065,0,true,169917858048,169917858112⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915760967487,0,false,-201063301440,-201063301376⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283387692279,0,true,170025300352,170025300416⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915635563273,0,false,-201213878784,-201213878720⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068761241656,0,false,-31188578368,-31188578304⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068803171127,0,false,-31145443328,-31145443264⟩
    { al := (684867/4096000), au := (1370583/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨183842585444,183956536296⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169996617600,169996617664⟩ : DyadicInterval 40),(⟨-201173677248,-201173677184⟩ : DyadicInterval 40),(⟨746681360846,746681380175⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170094240512,170094240576⟩ : DyadicInterval 40),(⟨-201310515008,-201310514944⟩ : DyadicInterval 40),(⟨746662121139,746662140468⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169839099520,169839099584⟩ : DyadicInterval 40),(⟨-200952945984,-200952945920⟩ : DyadicInterval 40),(⟨746712375559,746712394888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169956340160,169956340224⟩ : DyadicInterval 40),(⟨-201117228992,-201117228928⟩ : DyadicInterval 40),(⟨746689294771,746689314100⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨82092553,93881427⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82089472,82089536⟩ : DyadicInterval 40),(⟨-82095680,-82095616⟩ : DyadicInterval 40),(⟨762123380526,762123399855⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨93877376,93877440⟩ : DyadicInterval 40),(⟨-93885440,-93885376⟩ : DyadicInterval 40),(⟨762123379567,762123398897⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8064,-6080⟩ : DyadicInterval 40),(⟨762123386656,762123406912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183750660289,183876064503⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169917858048,169917858112⟩ : DyadicInterval 40),(⟨-201063301440,-201063301376⟩ : DyadicInterval 40),(⟨746696872821,746696892150⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170025300352,170025300416⟩ : DyadicInterval 40),(⟨-201213878784,-201213878720⟩ : DyadicInterval 40),(⟨746675709443,746675728772⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31188578368,-31145443264⟩ : DyadicInterval 40),(⟨777696105248,777717692064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169996617600,170094240576⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201310515008,-201173677184⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2828_ok : ecellOkT e2828 = true := by decide +kernel
theorem e2828_pos {a z : ℝ} (ha1 : ((684867/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1370583/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2828 e2828_ok ha1 ha2 hz1 hz2 hz

-- box ['1370583/8192000', '171429/1024000', '999/1000', '7993/8000']  interval_lower 77017733/274877906944
noncomputable def e2829 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283468164071,0,true,170094240512,170094240576⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915555091481,0,false,-201310515008,-201310514944⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283582114923,0,true,170191854720,170191854784⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915441140629,0,false,-201447369728,-201447369664⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283284207534,0,true,169936638720,169936638784⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915739048018,0,false,-201089619456,-201089619392⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283421053247,0,true,170053881216,170053881280⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915602202305,0,false,-201253939968,-201253939904⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593773327,0,true,82142464,82142528⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429482225,0,false,-82148672,-82148608⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099605569777,0,true,93937984,93938048⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099417685775,0,false,-93946048,-93945984⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619749,0,false,-8064,-8000⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621639,0,false,-6144,-6080⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283376181939,0,true,170015439104,170015439168⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915647073613,0,false,-201200057024,-201200056960⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283501593283,0,true,170122878016,170122878080⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915521662269,0,false,-201350661632,-201350661568⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068723133546,0,false,-31227783616,-31227783552⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068765091384,0,false,-31184617856,-31184617792⟩
    { al := (1370583/8192000), au := (171429/1024000), zl := (999/1000), zu := (7993/8000),
      A := ⟨183956536295,184070487147⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170094240512,170094240576⟩ : DyadicInterval 40),(⟨-201310515008,-201310514944⟩ : DyadicInterval 40),(⟨746662121139,746662140469⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170191854720,170191854784⟩ : DyadicInterval 40),(⟨-201447369728,-201447369664⟩ : DyadicInterval 40),(⟨746642869274,746642888603⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169936638720,169936638784⟩ : DyadicInterval 40),(⟨-201089619456,-201089619392⟩ : DyadicInterval 40),(⟨746693174717,746693194047⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170053881216,170053881280⟩ : DyadicInterval 40),(⟨-201253939968,-201253939904⟩ : DyadicInterval 40),(⟨746670076909,746670096239⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨82145551,93942001⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82142464,82142528⟩ : DyadicInterval 40),(⟨-82148672,-82148608⟩ : DyadicInterval 40),(⟨762123380518,762123399848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨93937984,93938048⟩ : DyadicInterval 40),(⟨-93946048,-93945984⟩ : DyadicInterval 40),(⟨762123379557,762123398886⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8064,-6080⟩ : DyadicInterval 40),(⟨762123386656,762123406912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183864554163,183989965507⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170015439104,170015439168⟩ : DyadicInterval 40),(⟨-201200057024,-201200056960⟩ : DyadicInterval 40),(⟨746677652544,746677671874⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170122878016,170122878080⟩ : DyadicInterval 40),(⟨-201350661632,-201350661568⟩ : DyadicInterval 40),(⟨746656474565,746656493895⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31227783616,-31184617792⟩ : DyadicInterval 40),(⟨777715692512,777737294688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170094240512,170191854784⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201447369728,-201310514944⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2829_ok : ecellOkT e2829 = true := by decide +kernel
theorem e2829_pos {a z : ℝ} (ha1 : ((1370583/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((171429/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2829 e2829_ok ha1 ha2 hz1 hz2 hz

-- box ['684867/4096000', '1370583/8192000', '7993/8000', '3997/4000']  interval_lower 306467013/1099511627776
noncomputable def e2830 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283354213220,0,true,169996617600,169996617664⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915669042332,0,false,-201173677248,-201173677184⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283468164072,0,true,170094240512,170094240576⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915555091480,0,false,-201310515008,-201310514944⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283193350957,0,true,169858790528,169858790592⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915829904595,0,false,-200980534976,-200980534912⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283330196670,0,true,169976041280,169976041344⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915693058882,0,false,-201144839168,-201144839104⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581992967,0,true,70362880,70362944⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441262585,0,false,-70367488,-70367424⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593774270,0,true,82143424,82143488⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429481282,0,false,-82149568,-82149504⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621638,0,false,-6144,-6080⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623273,0,false,-4544,-4480⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283273778008,0,true,169927702720,169927702784⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915749477544,0,false,-201077096960,-201077096896⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283399189375,0,true,170035150208,170035150272⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915624066177,0,false,-201227684800,-201227684736⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068757396118,0,false,-31192534528,-31192534464⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068799330603,0,false,-31149394240,-31149394176⟩
    { al := (684867/4096000), au := (1370583/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨183842585444,183956536296⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169996617600,169996617664⟩ : DyadicInterval 40),(⟨-201173677248,-201173677184⟩ : DyadicInterval 40),(⟨746681360846,746681380175⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170094240512,170094240576⟩ : DyadicInterval 40),(⟨-201310515008,-201310514944⟩ : DyadicInterval 40),(⟨746662121139,746662140468⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169858790528,169858790592⟩ : DyadicInterval 40),(⟨-200980534976,-200980534912⟩ : DyadicInterval 40),(⟨746708500444,746708519774⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169976041280,169976041344⟩ : DyadicInterval 40),(⟨-201144839168,-201144839104⟩ : DyadicInterval 40),(⟨746685414288,746685433617⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨70365191,82146494⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70362880,70362944⟩ : DyadicInterval 40),(⟨-70367488,-70367424⟩ : DyadicInterval 40),(⟨762123381352,762123400682⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82143424,82143488⟩ : DyadicInterval 40),(⟨-82149568,-82149504⟩ : DyadicInterval 40),(⟨762123380486,762123399815⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6144,-4480⟩ : DyadicInterval 40),(⟨762123385856,762123405952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183762150232,183887561599⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169927702720,169927702784⟩ : DyadicInterval 40),(⟨-201077096960,-201077096896⟩ : DyadicInterval 40),(⟨746694934359,746694953689⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170035150208,170035150272⟩ : DyadicInterval 40),(⟨-201227684800,-201227684736⟩ : DyadicInterval 40),(⟨746673768422,746673787752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31192534528,-31149394176⟩ : DyadicInterval 40),(⟨777698080704,777719670144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169996617600,170094240576⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201310515008,-201173677184⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2830_ok : ecellOkT e2830 = true := by decide +kernel
theorem e2830_pos {a z : ℝ} (ha1 : ((684867/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1370583/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2830 e2830_ok ha1 ha2 hz1 hz2 hz

-- box ['1370583/8192000', '171429/1024000', '7993/8000', '3997/4000']  interval_lower 307870727/1099511627776
noncomputable def e2831 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283468164071,0,true,170094240512,170094240576⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915555091481,0,false,-201310515008,-201310514944⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283582114923,0,true,170191854720,170191854784⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915441140629,0,false,-201447369728,-201447369664⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283307202101,0,true,169956340160,169956340224⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915716053451,0,false,-201117228992,-201117228928⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283444062058,0,true,170073592768,170073592832⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915579193494,0,false,-201281570688,-201281570624⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582038394,0,true,70408320,70408384⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441217158,0,false,-70412928,-70412864⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593827274,0,true,82196416,82196480⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429428278,0,false,-82202624,-82202560⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621630,0,false,-6208,-6144⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623268,0,false,-4544,-4480⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283387679001,0,true,170025289024,170025289088⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915635576551,0,false,-201213862848,-201213862784⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283513097500,0,true,170132733056,170132733120⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915510158052,0,false,-201364477952,-201364477888⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068719283242,0,false,-31231744832,-31231744768⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068761246098,0,false,-31188573824,-31188573760⟩
    { al := (1370583/8192000), au := (171429/1024000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨183956536295,184070487147⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170094240512,170094240576⟩ : DyadicInterval 40),(⟨-201310515008,-201310514944⟩ : DyadicInterval 40),(⟨746662121139,746662140469⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170191854720,170191854784⟩ : DyadicInterval 40),(⟨-201447369728,-201447369664⟩ : DyadicInterval 40),(⟨746642869274,746642888603⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169956340160,169956340224⟩ : DyadicInterval 40),(⟨-201117228992,-201117228928⟩ : DyadicInterval 40),(⟨746689294771,746689314100⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170073592768,170073592832⟩ : DyadicInterval 40),(⟨-201281570688,-201281570624⟩ : DyadicInterval 40),(⟨746666191587,746666210916⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨70410618,82199498⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70408320,70408384⟩ : DyadicInterval 40),(⟨-70412928,-70412864⟩ : DyadicInterval 40),(⟨762123381346,762123400676⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82196416,82196480⟩ : DyadicInterval 40),(⟨-82202624,-82202560⟩ : DyadicInterval 40),(⟨762123380510,762123399839⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6208,-4480⟩ : DyadicInterval 40),(⟨762123385856,762123405984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183876051225,184001469724⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170025289024,170025289088⟩ : DyadicInterval 40),(⟨-201213862848,-201213862784⟩ : DyadicInterval 40),(⟨746675711660,746675730989⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170132733056,170132733120⟩ : DyadicInterval 40),(⟨-201364477952,-201364477888⟩ : DyadicInterval 40),(⟨746654531156,746654550485⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31231744832,-31188573760⟩ : DyadicInterval 40),(⟨777717670496,777739275296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170094240512,170191854784⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201447369728,-201310514944⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2831_ok : ecellOkT e2831 = true := by decide +kernel
theorem e2831_pos {a z : ℝ} (ha1 : ((1370583/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((171429/1024000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2831 e2831_ok ha1 ha2 hz1 hz2 hz

-- box ['342009/2048000', '273777/1638400', '3997/4000', '1599/1600']  interval_lower 75867525/274877906944
noncomputable def e2832 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283126311518,0,true,169801345856,169801345920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915896944034,0,false,-200900052864,-200900052800⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283240262370,0,true,169898986048,169898986112⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915782993182,0,false,-201036856512,-201036856448⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282988600505,0,true,169683334912,169683334976⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916034655047,0,false,-200734746624,-200734746560⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283125431974,0,true,169800592192,169800592256⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915897823578,0,false,-200898996992,-200898996928⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570189840,0,true,58560448,58560512⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453065712,0,false,-58563648,-58563584⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581948424,0,true,70318336,70318400⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441307128,0,false,-70322944,-70322880⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623278,0,false,-4544,-4480⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624657,0,false,-3136,-3072⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283057451742,0,true,169742338304,169742338368⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915965803810,0,false,-200817391488,-200817391424⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283182856012,0,true,169849797824,169849797888⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915840399540,0,false,-200967935232,-200967935168⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068829714798,0,false,-31118137344,-31118137280⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068871597563,0,false,-31075053184,-31075053120⟩
    { al := (342009/2048000), au := (273777/1638400), zl := (3997/4000), zu := (1599/1600),
      A := ⟨183614683742,183728634594⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169801345856,169801345920⟩ : DyadicInterval 40),(⟨-200900052864,-200900052800⟩ : DyadicInterval 40),(⟨746719803785,746719823114⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169898986048,169898986112⟩ : DyadicInterval 40),(⟨-201036856512,-201036856448⟩ : DyadicInterval 40),(⟨746700588385,746700607714⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169683334912,169683334976⟩ : DyadicInterval 40),(⟨-200734746624,-200734746560⟩ : DyadicInterval 40),(⟨746743009596,746743028925⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169800592192,169800592256⟩ : DyadicInterval 40),(⟨-200898996992,-200898996928⟩ : DyadicInterval 40),(⟨746719952043,746719971373⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨58562064,70320648⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58560448,58560512⟩ : DyadicInterval 40),(⟨-58563648,-58563584⟩ : DyadicInterval 40),(⟨762123382032,762123401361⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70318336,70318400⟩ : DyadicInterval 40),(⟨-70322944,-70322880⟩ : DyadicInterval 40),(⟨762123381358,762123400687⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4544,-3072⟩ : DyadicInterval 40),(⟨762123385152,762123405152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183545823966,183671228236⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169742338304,169742338368⟩ : DyadicInterval 40),(⟨-200817391488,-200817391424⟩ : DyadicInterval 40),(⟨746731409620,746731428949⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169849797824,169849797888⟩ : DyadicInterval 40),(⟨-200967935232,-200967935168⟩ : DyadicInterval 40),(⟨746710270260,746710289590⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31118137344,-31075053120⟩ : DyadicInterval 40),(⟨777660910176,777682471552⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169801345856,169898986112⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201036856512,-200900052800⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2832_ok : ecellOkT e2832 = true := by decide +kernel
theorem e2832_pos {a z : ℝ} (ha1 : ((342009/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((273777/1638400 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2832 e2832_ok ha1 ha2 hz1 hz2 hz

-- box ['273777/1638400', '684867/4096000', '3997/4000', '1599/1600']  interval_lower 304866943/1099511627776
noncomputable def e2833 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283240262369,0,true,169898986048,169898986112⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915782993183,0,false,-201036856512,-201036856448⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283354213221,0,true,169996617600,169996617664⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915669042331,0,false,-201173677248,-201173677184⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283102465893,0,true,169780912320,169780912384⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915920789659,0,false,-200871427136,-200871427072⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283239311606,0,true,169898171456,169898171520⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915783943946,0,false,-201035715008,-201035714944⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570227691,0,true,58598336,58598400⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453027861,0,false,-58601536,-58601472⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581993848,0,true,70363776,70363840⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441261704,0,false,-70368384,-70368320⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623272,0,false,-4544,-4480⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624653,0,false,-3136,-3072⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283171359859,0,true,169839947136,169839947200⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915851895693,0,false,-200954133568,-200954133504⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283296771257,0,true,169947403200,169947403264⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915726484295,0,false,-201104704576,-201104704512⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068791644366,0,false,-31157301376,-31157301312⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068833555497,0,false,-31114186432,-31114186368⟩
    { al := (273777/1638400), au := (684867/4096000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨183728634593,183842585445⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169898986048,169898986112⟩ : DyadicInterval 40),(⟨-201036856512,-201036856448⟩ : DyadicInterval 40),(⟨746700588385,746700607715⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169996617600,169996617664⟩ : DyadicInterval 40),(⟨-201173677248,-201173677184⟩ : DyadicInterval 40),(⟨746681360845,746681380175⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169780912320,169780912384⟩ : DyadicInterval 40),(⟨-200871427136,-200871427072⟩ : DyadicInterval 40),(⟨746723823310,746723842639⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169898171456,169898171520⟩ : DyadicInterval 40),(⟨-201035715008,-201035714944⟩ : DyadicInterval 40),(⟨746700748737,746700768066⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨58599915,70366072⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58598336,58598400⟩ : DyadicInterval 40),(⟨-58601536,-58601472⟩ : DyadicInterval 40),(⟨762123382028,762123401357⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70363776,70363840⟩ : DyadicInterval 40),(⟨-70368384,-70368320⟩ : DyadicInterval 40),(⟨762123381352,762123400681⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4544,-3072⟩ : DyadicInterval 40),(⟨762123385152,762123405152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183659732083,183785143481⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169839947136,169839947200⟩ : DyadicInterval 40),(⟨-200954133568,-200954133504⟩ : DyadicInterval 40),(⟨746712208766,746712228095⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169947403200,169947403264⟩ : DyadicInterval 40),(⟨-201104704576,-201104704512⟩ : DyadicInterval 40),(⟨746691054845,746691074174⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31157301376,-31114186368⟩ : DyadicInterval 40),(⟨777680476800,777702053568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169898986048,169996617664⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201173677248,-201036856448⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2833_ok : ecellOkT e2833 = true := by decide +kernel
theorem e2833_pos {a z : ℝ} (ha1 : ((273777/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((684867/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2833 e2833_ok ha1 ha2 hz1 hz2 hz

-- box ['342009/2048000', '273777/1638400', '1599/1600', '1999/2000']  interval_lower 151635289/549755813888
noncomputable def e2834 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283126311518,0,true,169801345856,169801345920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915896944034,0,false,-200900052864,-200900052800⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283240262370,0,true,169898986048,169898986112⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915782993182,0,false,-201036856512,-201036856448⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283011552340,0,true,169703004288,169703004352⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916011703212,0,false,-200762295936,-200762295872⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283148398053,0,true,169820271680,169820271744⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915874857499,0,false,-200926567488,-200926567424⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558477497,0,true,46848704,46848768⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464778055,0,false,-46850752,-46850688⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570228511,0,true,58599168,58599232⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453027041,0,false,-58602304,-58602240⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624652,0,false,-3136,-3072⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625780,0,false,-2048,-1984⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283068927500,0,true,169752172352,169752172416⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915954328052,0,false,-200831166912,-200831166848⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283194338923,0,true,169859637056,169859637120⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915828916629,0,false,-200981721088,-200981721024⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068825878283,0,false,-31122084032,-31122083968⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068867766056,0,false,-31078994496,-31078994432⟩
    { al := (342009/2048000), au := (273777/1638400), zl := (1599/1600), zu := (1999/2000),
      A := ⟨183614683742,183728634594⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169801345856,169801345920⟩ : DyadicInterval 40),(⟨-200900052864,-200900052800⟩ : DyadicInterval 40),(⟨746719803785,746719823114⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169898986048,169898986112⟩ : DyadicInterval 40),(⟨-201036856512,-201036856448⟩ : DyadicInterval 40),(⟨746700588385,746700607714⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169703004288,169703004352⟩ : DyadicInterval 40),(⟨-200762295936,-200762295872⟩ : DyadicInterval 40),(⟨746739143188,746739162518⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169820271680,169820271744⟩ : DyadicInterval 40),(⟨-200926567488,-200926567424⟩ : DyadicInterval 40),(⟨746716080281,746716099610⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨46849721,58600735⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46848704,46848768⟩ : DyadicInterval 40),(⟨-46850752,-46850688⟩ : DyadicInterval 40),(⟨762123382579,762123401908⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58599168,58599232⟩ : DyadicInterval 40),(⟨-58602304,-58602240⟩ : DyadicInterval 40),(⟨762123381996,762123401325⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3136,-1984⟩ : DyadicInterval 40),(⟨762123384608,762123404448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183557299724,183682711147⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169752172352,169752172416⟩ : DyadicInterval 40),(⟨-200831166912,-200831166848⟩ : DyadicInterval 40),(⟨746729475782,746729495111⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169859637056,169859637120⟩ : DyadicInterval 40),(⟨-200981721088,-200981721024⟩ : DyadicInterval 40),(⟨746708333842,746708353172⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31122084032,-31078994432⟩ : DyadicInterval 40),(⟨777662880832,777684444896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169801345856,169898986112⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201036856512,-200900052800⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2834_ok : ecellOkT e2834 = true := by decide +kernel
theorem e2834_pos {a z : ℝ} (ha1 : ((342009/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((273777/1638400 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2834 e2834_ok ha1 ha2 hz1 hz2 hz

-- box ['273777/1638400', '684867/4096000', '1599/1600', '1999/2000']  interval_lower 152333609/549755813888
noncomputable def e2835 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283240262369,0,true,169898986048,169898986112⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915782993183,0,false,-201036856512,-201036856448⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283354213221,0,true,169996617600,169996617664⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915669042331,0,false,-201173677248,-201173677184⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283125431972,0,true,169800592192,169800592256⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915897823580,0,false,-200898996992,-200898996928⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283262291929,0,true,169917861376,169917861440⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915760963623,0,false,-201063306112,-201063306048⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558507778,0,true,46878976,46879040⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464747774,0,false,-46881024,-46880960⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570266366,0,true,58636992,58637056⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452989186,0,false,-58640192,-58640128⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624648,0,false,-3136,-3072⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625778,0,false,-2048,-1984⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283182842739,0,true,169849786432,169849786496⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915840412813,0,false,-200967919296,-200967919232⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283308261283,0,true,169957247680,169957247744⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915714994269,0,false,-201118500736,-201118500672⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068787803093,0,false,-31161253056,-31161252992⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068829719233,0,false,-31118132800,-31118132736⟩
    { al := (273777/1638400), au := (684867/4096000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨183728634593,183842585445⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169898986048,169898986112⟩ : DyadicInterval 40),(⟨-201036856512,-201036856448⟩ : DyadicInterval 40),(⟨746700588385,746700607715⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169996617600,169996617664⟩ : DyadicInterval 40),(⟨-201173677248,-201173677184⟩ : DyadicInterval 40),(⟨746681360845,746681380175⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169800592192,169800592256⟩ : DyadicInterval 40),(⟨-200898996992,-200898996928⟩ : DyadicInterval 40),(⟨746719952044,746719971373⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169917861376,169917861440⟩ : DyadicInterval 40),(⟨-201063306112,-201063306048⟩ : DyadicInterval 40),(⟨746696872172,746696891502⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨46880002,58638590⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46878976,46879040⟩ : DyadicInterval 40),(⟨-46881024,-46880960⟩ : DyadicInterval 40),(⟨762123382577,762123401906⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58636992,58637056⟩ : DyadicInterval 40),(⟨-58640192,-58640128⟩ : DyadicInterval 40),(⟨762123382024,762123401353⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3136,-1984⟩ : DyadicInterval 40),(⟨762123384608,762123404448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183671214963,183796633507⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169849786432,169849786496⟩ : DyadicInterval 40),(⟨-200967919296,-200967919232⟩ : DyadicInterval 40),(⟨746710272509,746710291839⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169957247680,169957247744⟩ : DyadicInterval 40),(⟨-201118500736,-201118500672⟩ : DyadicInterval 40),(⟨746689116006,746689135336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31161253056,-31118132736⟩ : DyadicInterval 40),(⟨777682449984,777704029408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169898986048,169996617664⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201173677248,-201036856448⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2835_ok : ecellOkT e2835 = true := by decide +kernel
theorem e2835_pos {a z : ℝ} (ha1 : ((273777/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((684867/4096000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2835 e2835_ok ha1 ha2 hz1 hz2 hz

-- box ['684867/4096000', '1370583/8192000', '3997/4000', '1599/1600']  interval_lower 306266925/1099511627776
noncomputable def e2836 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283354213220,0,true,169996617600,169996617664⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915669042332,0,false,-201173677248,-201173677184⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283468164072,0,true,170094240512,170094240576⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915555091480,0,false,-201310515008,-201310514944⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283216331280,0,true,169878481152,169878481216⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915806924272,0,false,-201008124672,-201008124608⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283353191237,0,true,169995742016,169995742080⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915670064315,0,false,-201172450048,-201172449984⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570265544,0,true,58636160,58636224⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452990008,0,false,-58639360,-58639296⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582039277,0,true,70409216,70409280⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441216275,0,false,-70413760,-70413696⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623266,0,false,-4544,-4480⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624649,0,false,-3136,-3072⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283285267977,0,true,169937547328,169937547392⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915737987575,0,false,-201090892672,-201090892608⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283410686498,0,true,170044999936,170045000000⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915612569054,0,false,-201241491008,-201241490944⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068753550330,0,false,-31196491008,-31196490944⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068795489830,0,false,-31153345344,-31153345280⟩
    { al := (684867/4096000), au := (1370583/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨183842585444,183956536296⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169996617600,169996617664⟩ : DyadicInterval 40),(⟨-201173677248,-201173677184⟩ : DyadicInterval 40),(⟨746681360846,746681380175⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170094240512,170094240576⟩ : DyadicInterval 40),(⟨-201310515008,-201310514944⟩ : DyadicInterval 40),(⟨746662121139,746662140468⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169878481152,169878481216⟩ : DyadicInterval 40),(⟨-201008124672,-201008124608⟩ : DyadicInterval 40),(⟨746704624858,746704644188⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169995742016,169995742080⟩ : DyadicInterval 40),(⟨-201172450048,-201172449984⟩ : DyadicInterval 40),(⟨746681533333,746681552662⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨58637768,70411501⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58636160,58636224⟩ : DyadicInterval 40),(⟨-58639360,-58639296⟩ : DyadicInterval 40),(⟨762123382024,762123401353⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70409216,70409280⟩ : DyadicInterval 40),(⟨-70413760,-70413696⟩ : DyadicInterval 40),(⟨762123381314,762123400644⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4544,-3072⟩ : DyadicInterval 40),(⟨762123385152,762123405152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183773640201,183899058722⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169937547328,169937547392⟩ : DyadicInterval 40),(⟨-201090892672,-201090892608⟩ : DyadicInterval 40),(⟨746692995764,746693015093⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170044999936,170045000000⟩ : DyadicInterval 40),(⟨-201241491008,-201241490944⟩ : DyadicInterval 40),(⟨746671827304,746671846634⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31196491008,-31153345280⟩ : DyadicInterval 40),(⟨777700056256,777721648384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169996617600,170094240576⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201310515008,-201173677184⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2836_ok : ecellOkT e2836 = true := by decide +kernel
theorem e2836_pos {a z : ℝ} (ha1 : ((684867/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1370583/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2836 e2836_ok ha1 ha2 hz1 hz2 hz

-- box ['1370583/8192000', '171429/1024000', '3997/4000', '1599/1600']  interval_lower 307670171/1099511627776
noncomputable def e2837 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283468164071,0,true,170094240512,170094240576⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915555091481,0,false,-201310515008,-201310514944⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283582114923,0,true,170191854720,170191854784⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915441140629,0,false,-201447369728,-201447369664⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283330196668,0,true,169976041280,169976041344⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915693058884,0,false,-201144839168,-201144839104⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283467070869,0,true,170093304000,170093304064⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915556184683,0,false,-201309202112,-201309202048⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570303401,0,true,58674048,58674112⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452952151,0,false,-58677248,-58677184⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582084708,0,true,70454656,70454720⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441170844,0,false,-70459200,-70459136⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623261,0,false,-4544,-4480⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624645,0,false,-3136,-3072⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283399176097,0,true,170035138816,170035138880⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915624079455,0,false,-201227668800,-201227668736⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283524601746,0,true,170142588032,170142588096⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915498653806,0,false,-201378294400,-201378294336⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068715432689,0,false,-31235706368,-31235706304⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068757400560,0,false,-31192529984,-31192529920⟩
    { al := (1370583/8192000), au := (171429/1024000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨183956536295,184070487147⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170094240512,170094240576⟩ : DyadicInterval 40),(⟨-201310515008,-201310514944⟩ : DyadicInterval 40),(⟨746662121139,746662140469⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170191854720,170191854784⟩ : DyadicInterval 40),(⟨-201447369728,-201447369664⟩ : DyadicInterval 40),(⟨746642869274,746642888603⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169976041280,169976041344⟩ : DyadicInterval 40),(⟨-201144839168,-201144839104⟩ : DyadicInterval 40),(⟨746685414288,746685433617⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170093304000,170093304064⟩ : DyadicInterval 40),(⟨-201309202112,-201309202048⟩ : DyadicInterval 40),(⟨746662305754,746662325083⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨58675625,70456932⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58674048,58674112⟩ : DyadicInterval 40),(⟨-58677248,-58677184⟩ : DyadicInterval 40),(⟨762123382020,762123401349⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70454656,70454720⟩ : DyadicInterval 40),(⟨-70459200,-70459136⟩ : DyadicInterval 40),(⟨762123381308,762123400638⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4544,-3072⟩ : DyadicInterval 40),(⟨762123385152,762123405152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183887548321,184012973970⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170035138816,170035138880⟩ : DyadicInterval 40),(⟨-201227668800,-201227668736⟩ : DyadicInterval 40),(⟨746673770651,746673789980⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170142588032,170142588096⟩ : DyadicInterval 40),(⟨-201378294400,-201378294336⟩ : DyadicInterval 40),(⟨746652587583,746652606913⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31235706368,-31192529920⟩ : DyadicInterval 40),(⟨777719648576,777741256064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170094240512,170191854784⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201447369728,-201310514944⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2837_ok : ecellOkT e2837 = true := by decide +kernel
theorem e2837_pos {a z : ℝ} (ha1 : ((1370583/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((171429/1024000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2837 e2837_ok ha1 ha2 hz1 hz2 hz

-- box ['684867/4096000', '1370583/8192000', '1599/1600', '1999/2000']  interval_lower 153033353/549755813888
noncomputable def e2838 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283354213220,0,true,169996617600,169996617664⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915669042332,0,false,-201173677248,-201173677184⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283468164072,0,true,170094240512,170094240576⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915555091480,0,false,-201310515008,-201310514944⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283239311603,0,true,169898171456,169898171520⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915783943949,0,false,-201035715008,-201035714944⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283376185805,0,true,170015442432,170015442496⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915647069747,0,false,-201200061696,-201200061632⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558538061,0,true,46909248,46909312⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464717491,0,false,-46911296,-46911232⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570304222,0,true,58674880,58674944⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452951330,0,false,-58678016,-58677952⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624644,0,false,-3136,-3072⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625775,0,false,-2048,-1984⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283296757980,0,true,169947391808,169947391872⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915726497572,0,false,-201104688640,-201104688576⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283422183649,0,true,170054849600,170054849664⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915601071903,0,false,-201255297408,-201255297344⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068749704293,0,false,-31200447744,-31200447680⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068791648805,0,false,-31157296768,-31157296704⟩
    { al := (684867/4096000), au := (1370583/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨183842585444,183956536296⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169996617600,169996617664⟩ : DyadicInterval 40),(⟨-201173677248,-201173677184⟩ : DyadicInterval 40),(⟨746681360846,746681380175⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170094240512,170094240576⟩ : DyadicInterval 40),(⟨-201310515008,-201310514944⟩ : DyadicInterval 40),(⟨746662121139,746662140468⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169898171456,169898171520⟩ : DyadicInterval 40),(⟨-201035715008,-201035714944⟩ : DyadicInterval 40),(⟨746700748737,746700768067⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170015442432,170015442496⟩ : DyadicInterval 40),(⟨-201200061696,-201200061632⟩ : DyadicInterval 40),(⟨746677651895,746677671225⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨46910285,58676446⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46909248,46909312⟩ : DyadicInterval 40),(⟨-46911296,-46911232⟩ : DyadicInterval 40),(⟨762123382574,762123401903⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58674880,58674944⟩ : DyadicInterval 40),(⟨-58678016,-58677952⟩ : DyadicInterval 40),(⟨762123381988,762123401317⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3136,-1984⟩ : DyadicInterval 40),(⟨762123384608,762123404448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183785130204,183910555873⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169947391808,169947391872⟩ : DyadicInterval 40),(⟨-201104688640,-201104688576⟩ : DyadicInterval 40),(⟨746691057097,746691076426⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170054849600,170054849664⟩ : DyadicInterval 40),(⟨-201255297408,-201255297344⟩ : DyadicInterval 40),(⟨746669886052,746669905381⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31200447744,-31157296704⟩ : DyadicInterval 40),(⟨777702031968,777723626752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169996617600,170094240576⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201310515008,-201173677184⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2838_ok : ecellOkT e2838 = true := by decide +kernel
theorem e2838_pos {a z : ℝ} (ha1 : ((684867/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1370583/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2838 e2838_ok ha1 ha2 hz1 hz2 hz

-- box ['1370583/8192000', '171429/1024000', '1599/1600', '1999/2000']  interval_lower 153734797/549755813888
noncomputable def e2839 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283468164071,0,true,170094240512,170094240576⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915555091481,0,false,-201310515008,-201310514944⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283582114923,0,true,170191854720,170191854784⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915441140629,0,false,-201447369728,-201447369664⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283353191235,0,true,169995742016,169995742080⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915670064317,0,false,-201172450048,-201172449984⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283490079680,0,true,170113014848,170113014912⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915533175872,0,false,-201336834240,-201336834176⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558568346,0,true,46939520,46939584⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464687206,0,false,-46941632,-46941568⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570342082,0,true,58712704,58712768⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452913470,0,false,-58715904,-58715840⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624640,0,false,-3200,-3136⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625773,0,false,-2048,-1984⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283410673220,0,true,170044988544,170044988608⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915612582332,0,false,-201241475008,-201241474944⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283536106020,0,true,170152442944,170152443008⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915487149532,0,false,-201392111104,-201392111040⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068711581885,0,false,-31239668160,-31239668096⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068753554773,0,false,-31196486464,-31196486400⟩
    { al := (1370583/8192000), au := (171429/1024000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨183956536295,184070487147⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170094240512,170094240576⟩ : DyadicInterval 40),(⟨-201310515008,-201310514944⟩ : DyadicInterval 40),(⟨746662121139,746662140469⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170191854720,170191854784⟩ : DyadicInterval 40),(⟨-201447369728,-201447369664⟩ : DyadicInterval 40),(⟨746642869274,746642888603⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169995742016,169995742080⟩ : DyadicInterval 40),(⟨-201172450048,-201172449984⟩ : DyadicInterval 40),(⟨746681533333,746681552663⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170113014848,170113014912⟩ : DyadicInterval 40),(⟨-201336834240,-201336834176⟩ : DyadicInterval 40),(⟨746658419448,746658438777⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨46940570,58714306⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46939520,46939584⟩ : DyadicInterval 40),(⟨-46941632,-46941568⟩ : DyadicInterval 40),(⟨762123382603,762123401933⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58712704,58712768⟩ : DyadicInterval 40),(⟨-58715904,-58715840⟩ : DyadicInterval 40),(⟨762123382016,762123401345⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3200,-1984⟩ : DyadicInterval 40),(⟨762123384608,762123404480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183899045444,184024478244⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170044988544,170044988608⟩ : DyadicInterval 40),(⟨-201241475008,-201241474944⟩ : DyadicInterval 40),(⟨746671829533,746671848863⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170152442944,170152443008⟩ : DyadicInterval 40),(⟨-201392111104,-201392111040⟩ : DyadicInterval 40),(⟨746650643903,746650663232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31239668160,-31196486400⟩ : DyadicInterval 40),(⟨777721626816,777743236960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170094240512,170191854784⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201447369728,-201310514944⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2839_ok : ecellOkT e2839 = true := by decide +kernel
theorem e2839_pos {a z : ℝ} (ha1 : ((1370583/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((171429/1024000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2839 e2839_ok ha1 ha2 hz1 hz2 hz

-- box ['8529/51200', '1365489/8192000', '1999/2000', '7997/8000']  interval_lower 297518871/1099511627776
noncomputable def e2840 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282670508113,0,true,169410698304,169410698368⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916352747439,0,false,-200353008256,-200353008192⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282784458965,0,true,169508373184,169508373248⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916238796587,0,false,-200489743872,-200489743808⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282578928672,0,true,169332193152,169332193216⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916444326880,0,false,-200243129536,-200243129472⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282715731654,0,true,169449463488,169449463552⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916307523898,0,false,-200407272320,-200407272256⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546674269,0,true,35045888,35045952⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476581283,0,false,-35047104,-35047040⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558387427,0,true,46758656,46758720⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464868125,0,false,-46760704,-46760640⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625787,0,false,-2048,-1984⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626659,0,false,-1152,-1088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282624713844,0,true,169371442496,169371442560⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916398541708,0,false,-200298062080,-200298062016⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282750103918,0,true,169478926080,169478926144⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916273151634,0,false,-200448517632,-200448517568⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068974125224,0,false,-30969591488,-30969591424⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069015904546,0,false,-30926619520,-30926619456⟩
    { al := (8529/51200), au := (1365489/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨183158880337,183272831189⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169410698304,169410698368⟩ : DyadicInterval 40),(⟨-200353008256,-200353008192⟩ : DyadicInterval 40),(⟨746796543867,746796563196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169508373184,169508373248⟩ : DyadicInterval 40),(⟨-200489743872,-200489743808⟩ : DyadicInterval 40),(⟨746777377070,746777396400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169332193152,169332193216⟩ : DyadicInterval 40),(⟨-200243129536,-200243129472⟩ : DyadicInterval 40),(⟨746811938919,746811958248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169449463488,169449463552⟩ : DyadicInterval 40),(⟨-200407272320,-200407272256⟩ : DyadicInterval 40),(⟨746788938597,746788957926⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨35046493,46759651⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35045888,35045952⟩ : DyadicInterval 40),(⟨-35047104,-35047040⟩ : DyadicInterval 40),(⟨762123383042,762123402371⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46758656,46758720⟩ : DyadicInterval 40),(⟨-46760704,-46760640⟩ : DyadicInterval 40),(⟨762123382587,762123401916⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2048,-1088⟩ : DyadicInterval 40),(⟨762123384160,762123403904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183113086068,183238476142⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169371442496,169371442560⟩ : DyadicInterval 40),(⟨-200298062080,-200298062016⟩ : DyadicInterval 40),(⟨746804243164,746804262493⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169478926080,169478926144⟩ : DyadicInterval 40),(⟨-200448517632,-200448517568⟩ : DyadicInterval 40),(⟨746783156946,746783176276⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30969591488,-30926619456⟩ : DyadicInterval 40),(⟨777586693344,777608198624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169410698304,169508373248⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200489743872,-200353008192⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2840_ok : ecellOkT e2840 = true := by decide +kernel
theorem e2840_pos {a z : ℝ} (ha1 : ((8529/51200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1365489/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2840 e2840_ok ha1 ha2 hz1 hz2 hz

-- box ['1365489/8192000', '683169/4096000', '1999/2000', '7997/8000']  interval_lower 149451165/549755813888
noncomputable def e2841 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282784458964,0,true,169508373184,169508373248⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916238796588,0,false,-200489743872,-200489743808⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282898409817,0,true,169606039424,169606039488⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916124845735,0,false,-200626496512,-200626496448⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282692822548,0,true,169429826176,169429826240⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916330433004,0,false,-200379783168,-200379783104⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282829639774,0,true,169547098304,169547098368⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916193615778,0,false,-200543963392,-200543963328⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546696972,0,true,35068608,35068672⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476558580,0,false,-35069760,-35069696⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558417701,0,true,46788928,46788992⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464837851,0,false,-46790976,-46790912⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625784,0,false,-2048,-1984⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626658,0,false,-1152,-1088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282738636202,0,true,169469096512,169469096576⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916284619350,0,false,-200434756672,-200434756608⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282864033405,0,true,169576576640,169576576704⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916159222147,0,false,-200585239552,-200585239488⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068936139713,0,false,-31008662848,-31008662784⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068977947396,0,false,-30965660160,-30965660096⟩
    { al := (1365489/8192000), au := (683169/4096000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨183272831188,183386782041⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169508373184,169508373248⟩ : DyadicInterval 40),(⟨-200489743872,-200489743808⟩ : DyadicInterval 40),(⟨746777377070,746777396400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169606039424,169606039488⟩ : DyadicInterval 40),(⟨-200626496512,-200626496448⟩ : DyadicInterval 40),(⟨746758198113,746758217442⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169429826176,169429826240⟩ : DyadicInterval 40),(⟨-200379783168,-200379783104⟩ : DyadicInterval 40),(⟨746792791480,746792810809⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169547098304,169547098368⟩ : DyadicInterval 40),(⟨-200543963392,-200543963328⟩ : DyadicInterval 40),(⟨746769774164,746769793493⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨35069196,46789925⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35068608,35068672⟩ : DyadicInterval 40),(⟨-35069760,-35069696⟩ : DyadicInterval 40),(⟨762123383009,762123402338⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46788928,46788992⟩ : DyadicInterval 40),(⟨-46790976,-46790912⟩ : DyadicInterval 40),(⟨762123382584,762123401913⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2048,-1088⟩ : DyadicInterval 40),(⟨762123384160,762123403904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183227008426,183352405629⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169469096512,169469096576⟩ : DyadicInterval 40),(⟨-200434756672,-200434756608⟩ : DyadicInterval 40),(⟨746785086000,746785105329⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169576576640,169576576704⟩ : DyadicInterval 40),(⟨-200585239552,-200585239488⟩ : DyadicInterval 40),(⟨746763985258,746764004588⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31008662848,-30965660096⟩ : DyadicInterval 40),(⟨777606213664,777627734304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169508373184,169606039488⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200626496512,-200489743808⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2841_ok : ecellOkT e2841 = true := by decide +kernel
theorem e2841_pos {a z : ℝ} (ha1 : ((1365489/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((683169/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2841 e2841_ok ha1 ha2 hz1 hz2 hz

-- box ['8529/51200', '1365489/8192000', '7997/8000', '3999/4000']  interval_lower 74330345/274877906944
noncomputable def e2842 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282670508113,0,true,169410698304,169410698368⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916352747439,0,false,-200353008256,-200353008192⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282784458965,0,true,169508373184,169508373248⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916238796587,0,false,-200489743872,-200489743808⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282601823532,0,true,169351819968,169351820032⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916421432020,0,false,-200270598208,-200270598144⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282738640758,0,true,169469100416,169469100480⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916284614794,0,false,-200434762176,-200434762112⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534992078,0,true,23364032,23364096⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488263474,0,false,-23364608,-23364544⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546697669,0,true,35069312,35069376⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476557883,0,false,-35070464,-35070400⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626657,0,false,-1152,-1088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627280,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282636161171,0,true,169381255552,169381255616⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916387094381,0,false,-200311796864,-200311796800⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282761558396,0,true,169488744256,169488744320⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916261697156,0,false,-200462262912,-200462262848⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068970307226,0,false,-30973518592,-30973518528⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069012091542,0,false,-30930541312,-30930541248⟩
    { al := (8529/51200), au := (1365489/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨183158880337,183272831189⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169410698304,169410698368⟩ : DyadicInterval 40),(⟨-200353008256,-200353008192⟩ : DyadicInterval 40),(⟨746796543867,746796563196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169508373184,169508373248⟩ : DyadicInterval 40),(⟨-200489743872,-200489743808⟩ : DyadicInterval 40),(⟨746777377070,746777396400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169351819968,169351820032⟩ : DyadicInterval 40),(⟨-200270598208,-200270598144⟩ : DyadicInterval 40),(⟨746808090899,746808110228⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169469100416,169469100480⟩ : DyadicInterval 40),(⟨-200434762176,-200434762112⟩ : DyadicInterval 40),(⟨746785085249,746785104579⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23364302,35069893⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23364032,23364096⟩ : DyadicInterval 40),(⟨-23364608,-23364544⟩ : DyadicInterval 40),(⟨762123383343,762123402672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35069312,35069376⟩ : DyadicInterval 40),(⟨-35070464,-35070400⟩ : DyadicInterval 40),(⟨762123383009,762123402338⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1152,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183124533395,183249930620⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169381255552,169381255616⟩ : DyadicInterval 40),(⟨-200311796864,-200311796800⟩ : DyadicInterval 40),(⟨746802318705,746802338034⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169488744256,169488744320⟩ : DyadicInterval 40),(⟨-200462262912,-200462262848⟩ : DyadicInterval 40),(⟨746781229986,746781249315⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30973518592,-30930541248⟩ : DyadicInterval 40),(⟨777588654240,777610162176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169410698304,169508373248⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200489743872,-200353008192⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2842_ok : ecellOkT e2842 = true := by decide +kernel
theorem e2842_pos {a z : ℝ} (ha1 : ((8529/51200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1365489/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2842 e2842_ok ha1 ha2 hz1 hz2 hz

-- box ['1365489/8192000', '683169/4096000', '7997/8000', '3999/4000']  interval_lower 149352095/549755813888
noncomputable def e2843 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282784458964,0,true,169508373184,169508373248⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916238796588,0,false,-200489743872,-200489743808⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282898409817,0,true,169606039424,169606039488⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916124845735,0,false,-200626496512,-200626496448⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282715731652,0,true,169449463488,169449463552⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916307523900,0,false,-200407272320,-200407272256⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282852563122,0,true,169566745664,169566745728⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916170692430,0,false,-200571473792,-200571473728⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535007214,0,true,23379136,23379200⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488248338,0,false,-23379712,-23379648⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546720375,0,true,35092032,35092096⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476535177,0,false,-35093184,-35093120⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626655,0,false,-1152,-1088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627279,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282750090654,0,true,169478914752,169478914816⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916273164898,0,false,-200448501760,-200448501696⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282875495001,0,true,169586400064,169586400128⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916147760551,0,false,-200598995072,-200598995008⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068932316967,0,false,-31012594944,-31012594880⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068974129646,0,false,-30969586944,-30969586880⟩
    { al := (1365489/8192000), au := (683169/4096000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨183272831188,183386782041⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169508373184,169508373248⟩ : DyadicInterval 40),(⟨-200489743872,-200489743808⟩ : DyadicInterval 40),(⟨746777377070,746777396400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169606039424,169606039488⟩ : DyadicInterval 40),(⟨-200626496512,-200626496448⟩ : DyadicInterval 40),(⟨746758198113,746758217442⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169449463488,169449463552⟩ : DyadicInterval 40),(⟨-200407272320,-200407272256⟩ : DyadicInterval 40),(⟨746788938597,746788957927⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169566745664,169566745728⟩ : DyadicInterval 40),(⟨-200571473792,-200571473728⟩ : DyadicInterval 40),(⟨746765916010,746765935340⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23379438,35092599⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23379136,23379200⟩ : DyadicInterval 40),(⟨-23379712,-23379648⟩ : DyadicInterval 40),(⟨762123383342,762123402671⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35092032,35092096⟩ : DyadicInterval 40),(⟨-35093184,-35093120⟩ : DyadicInterval 40),(⟨762123383007,762123402336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1152,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183238462878,183363867225⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169478914752,169478914816⟩ : DyadicInterval 40),(⟨-200448501760,-200448501696⟩ : DyadicInterval 40),(⟨746783159172,746783178501⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169586400064,169586400128⟩ : DyadicInterval 40),(⟨-200598995072,-200598995008⟩ : DyadicInterval 40),(⟨746762055862,746762075192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31012594944,-30969586880⟩ : DyadicInterval 40),(⟨777608177056,777629700352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169508373184,169606039488⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200626496512,-200489743808⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2843_ok : ecellOkT e2843 = true := by decide +kernel
theorem e2843_pos {a z : ℝ} (ha1 : ((1365489/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((683169/4096000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2843 e2843_ok ha1 ha2 hz1 hz2 hz

-- box ['683169/4096000', '1367187/8192000', '1999/2000', '7997/8000']  interval_lower 37536093/137438953472
noncomputable def e2844 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282898409816,0,true,169606039424,169606039488⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916124845736,0,false,-200626496512,-200626496448⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283012360668,0,true,169703696960,169703697024⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916010894884,0,false,-200763266176,-200763266112⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282806716424,0,true,169527450560,169527450624⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916216539128,0,false,-200516453760,-200516453696⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282943547894,0,true,169644724480,169644724544⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916079707658,0,false,-200680671552,-200680671488⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546719678,0,true,35091328,35091392⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476535874,0,false,-35092480,-35092416⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558447978,0,true,46819200,46819264⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464807574,0,false,-46821248,-46821184⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625782,0,false,-2048,-1984⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626657,0,false,-1152,-1088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282852558566,0,true,169566741760,169566741824⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916170696986,0,false,-200571468288,-200571468224⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282977962886,0,true,169674218496,169674218560⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916045292666,0,false,-200721978432,-200721978368⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068898130593,0,false,-31047759872,-31047759808⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068939966637,0,false,-31004726464,-31004726400⟩
    { al := (683169/4096000), au := (1367187/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨183386782040,183500732892⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169606039424,169606039488⟩ : DyadicInterval 40),(⟨-200626496512,-200626496448⟩ : DyadicInterval 40),(⟨746758198113,746758217443⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169703696960,169703697024⟩ : DyadicInterval 40),(⟨-200763266176,-200763266112⟩ : DyadicInterval 40),(⟨746739007030,746739026360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169527450560,169527450624⟩ : DyadicInterval 40),(⟨-200516453760,-200516453696⟩ : DyadicInterval 40),(⟨746773631879,746773651208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169644724480,169644724544⟩ : DyadicInterval 40),(⟨-200680671552,-200680671488⟩ : DyadicInterval 40),(⟨746750597614,746750616944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨35091902,46820202⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35091328,35091392⟩ : DyadicInterval 40),(⟨-35092480,-35092416⟩ : DyadicInterval 40),(⟨762123383007,762123402337⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46819200,46819264⟩ : DyadicInterval 40),(⟨-46821248,-46821184⟩ : DyadicInterval 40),(⟨762123382582,762123401911⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2048,-1088⟩ : DyadicInterval 40),(⟨762123384160,762123403904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183340930790,183466335110⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169566741760,169566741824⟩ : DyadicInterval 40),(⟨-200571468288,-200571468224⟩ : DyadicInterval 40),(⟨746765916761,746765936091⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169674218496,169674218560⟩ : DyadicInterval 40),(⟨-200721978432,-200721978368⟩ : DyadicInterval 40),(⟨746744801429,746744820759⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31047759872,-31004726400⟩ : DyadicInterval 40),(⟨777625746816,777647282816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169606039424,169703697024⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200763266176,-200626496448⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2844_ok : ecellOkT e2844 = true := by decide +kernel
theorem e2844_pos {a z : ℝ} (ha1 : ((683169/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1367187/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2844 e2844_ok ha1 ha2 hz1 hz2 hz

-- box ['1367187/8192000', '342009/2048000', '1999/2000', '7997/8000']  interval_lower 150839207/549755813888
noncomputable def e2845 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283012360667,0,true,169703696960,169703697024⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916010894885,0,false,-200763266176,-200763266112⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283126311519,0,true,169801345856,169801345920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915896944033,0,false,-200900052864,-200900052800⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282920610300,0,true,169625066240,169625066304⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916102645252,0,false,-200653141376,-200653141312⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283057456013,0,true,169742341952,169742342016⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915965799539,0,false,-200817396608,-200817396544⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546742385,0,true,35114048,35114112⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476513167,0,false,-35115200,-35115136⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558478256,0,true,46849472,46849536⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464777296,0,false,-46851520,-46851456⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625779,0,false,-2048,-1984⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626655,0,false,-1152,-1088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282966480922,0,true,169664378432,169664378496⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916056774630,0,false,-200708196928,-200708196864⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283091892372,0,true,169771851712,169771851776⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915931363180,0,false,-200858734272,-200858734208⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068860097862,0,false,-31086882560,-31086882496⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068901962274,0,false,-31043818432,-31043818368⟩
    { al := (1367187/8192000), au := (342009/2048000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨183500732891,183614683743⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169703696960,169703697024⟩ : DyadicInterval 40),(⟨-200763266176,-200763266112⟩ : DyadicInterval 40),(⟨746739007031,746739026360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169801345856,169801345920⟩ : DyadicInterval 40),(⟨-200900052864,-200900052800⟩ : DyadicInterval 40),(⟨746719803785,746719823114⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169625066240,169625066304⟩ : DyadicInterval 40),(⟨-200653141376,-200653141312⟩ : DyadicInterval 40),(⟨746754460178,746754479508⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169742341952,169742342016⟩ : DyadicInterval 40),(⟨-200817396608,-200817396544⟩ : DyadicInterval 40),(⟨746731408904,746731428234⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨35114609,46850480⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35114048,35114112⟩ : DyadicInterval 40),(⟨-35115200,-35115136⟩ : DyadicInterval 40),(⟨762123383006,762123402335⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46849472,46849536⟩ : DyadicInterval 40),(⟨-46851520,-46851456⟩ : DyadicInterval 40),(⟨762123382579,762123401908⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2048,-1088⟩ : DyadicInterval 40),(⟨762123384160,762123403904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183454853146,183580264596⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169664378432,169664378496⟩ : DyadicInterval 40),(⟨-200708196928,-200708196864⟩ : DyadicInterval 40),(⟨746746735337,746746754667⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169771851712,169771851776⟩ : DyadicInterval 40),(⟨-200858734272,-200858734208⟩ : DyadicInterval 40),(⟨746725605419,746725624749⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31086882560,-31043818368⟩ : DyadicInterval 40),(⟨777645292800,777666844160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169703696960,169801345920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200900052864,-200763266112⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2845_ok : ecellOkT e2845 = true := by decide +kernel
theorem e2845_pos {a z : ℝ} (ha1 : ((1367187/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((342009/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2845 e2845_ok ha1 ha2 hz1 hz2 hz

-- box ['683169/4096000', '1367187/8192000', '7997/8000', '3999/4000']  interval_lower 300090347/1099511627776
noncomputable def e2846 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282898409816,0,true,169606039424,169606039488⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916124845736,0,false,-200626496512,-200626496448⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283012360668,0,true,169703696960,169703697024⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916010894884,0,false,-200763266176,-200763266112⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282829639772,0,true,169547098304,169547098368⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916193615780,0,false,-200543963392,-200543963328⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282966485485,0,true,169664382336,169664382400⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916056770067,0,false,-200708202368,-200708202304⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535022351,0,true,23394304,23394368⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488233201,0,false,-23394880,-23394816⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546743082,0,true,35114688,35114752⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476512470,0,false,-35115904,-35115840⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626654,0,false,-1152,-1088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627279,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282864020139,0,true,169576565248,169576565312⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916159235413,0,false,-200585223616,-200585223552⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282989431612,0,true,169684047168,169684047232⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916033823940,0,false,-200735744192,-200735744128⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068894303092,0,false,-31051697024,-31051696960⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068936144138,0,false,-31008658304,-31008658240⟩
    { al := (683169/4096000), au := (1367187/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨183386782040,183500732892⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169606039424,169606039488⟩ : DyadicInterval 40),(⟨-200626496512,-200626496448⟩ : DyadicInterval 40),(⟨746758198113,746758217443⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169703696960,169703697024⟩ : DyadicInterval 40),(⟨-200763266176,-200763266112⟩ : DyadicInterval 40),(⟨746739007030,746739026360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169547098304,169547098368⟩ : DyadicInterval 40),(⟨-200543963392,-200543963328⟩ : DyadicInterval 40),(⟨746769774164,746769793494⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169664382336,169664382400⟩ : DyadicInterval 40),(⟨-200708202368,-200708202304⟩ : DyadicInterval 40),(⟨746746734557,746746753886⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23394575,35115306⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23394304,23394368⟩ : DyadicInterval 40),(⟨-23394880,-23394816⟩ : DyadicInterval 40),(⟨762123383342,762123402671⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35114688,35114752⟩ : DyadicInterval 40),(⟨-35115904,-35115840⟩ : DyadicInterval 40),(⟨762123383038,762123402367⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1152,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183352392363,183477803836⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169576565248,169576565312⟩ : DyadicInterval 40),(⟨-200585223616,-200585223552⟩ : DyadicInterval 40),(⟨746763987498,746764006827⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169684047168,169684047232⟩ : DyadicInterval 40),(⟨-200735744192,-200735744128⟩ : DyadicInterval 40),(⟨746742869593,746742888923⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31051697024,-31008658240⟩ : DyadicInterval 40),(⟨777627712736,777649251392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169606039424,169703697024⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200763266176,-200626496448⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2846_ok : ecellOkT e2846 = true := by decide +kernel
theorem e2846_pos {a z : ℝ} (ha1 : ((683169/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1367187/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2846 e2846_ok ha1 ha2 hz1 hz2 hz

-- box ['1367187/8192000', '342009/2048000', '7997/8000', '3999/4000']  interval_lower 150739797/549755813888
noncomputable def e2847 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283012360667,0,true,169703696960,169703697024⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916010894885,0,false,-200763266176,-200763266112⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283126311519,0,true,169801345856,169801345920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915896944033,0,false,-200900052864,-200900052800⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282943547892,0,true,169644724480,169644724544⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916079707660,0,false,-200680671552,-200680671488⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283080407849,0,true,169762010304,169762010368⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915942847703,0,false,-200844948032,-200844947968⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535037490,0,true,23409408,23409472⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488218062,0,false,-23409984,-23409920⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546765792,0,true,35137408,35137472⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476489760,0,false,-35138624,-35138560⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626653,0,false,-1152,-1088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627278,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282977949618,0,true,169674207104,169674207168⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916045305934,0,false,-200721962496,-200721962432⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283103368218,0,true,169781685568,169781685632⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915919887334,0,false,-200872510336,-200872510272⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068856265606,0,false,-31090824704,-31090824640⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068898135022,0,false,-31047755328,-31047755264⟩
    { al := (1367187/8192000), au := (342009/2048000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨183500732891,183614683743⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169703696960,169703697024⟩ : DyadicInterval 40),(⟨-200763266176,-200763266112⟩ : DyadicInterval 40),(⟨746739007031,746739026360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169801345856,169801345920⟩ : DyadicInterval 40),(⟨-200900052864,-200900052800⟩ : DyadicInterval 40),(⟨746719803785,746719823114⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169644724480,169644724544⟩ : DyadicInterval 40),(⟨-200680671552,-200680671488⟩ : DyadicInterval 40),(⟨746750597615,746750616944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169762010304,169762010368⟩ : DyadicInterval 40),(⟨-200844948032,-200844947968⟩ : DyadicInterval 40),(⟨746727541017,746727560347⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23409714,35138016⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23409408,23409472⟩ : DyadicInterval 40),(⟨-23409984,-23409920⟩ : DyadicInterval 40),(⟨762123383341,762123402670⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35137408,35137472⟩ : DyadicInterval 40),(⟨-35138624,-35138560⟩ : DyadicInterval 40),(⟨762123383037,762123402366⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1152,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183466321842,183591740442⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169674207104,169674207168⟩ : DyadicInterval 40),(⟨-200721962496,-200721962432⟩ : DyadicInterval 40),(⟨746744803673,746744823002⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169781685568,169781685632⟩ : DyadicInterval 40),(⟨-200872510336,-200872510272⟩ : DyadicInterval 40),(⟨746723671205,746723690534⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31090824704,-31047755264⟩ : DyadicInterval 40),(⟨777647261248,777668815232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169703696960,169801345920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200900052864,-200763266112⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2847_ok : ecellOkT e2847 = true := by decide +kernel
theorem e2847_pos {a z : ℝ} (ha1 : ((1367187/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((342009/2048000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2847 e2847_ok ha1 ha2 hz1 hz2 hz

-- box ['8529/51200', '1365489/8192000', '3999/4000', '7999/8000']  interval_lower 297123777/1099511627776
noncomputable def e2848 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282670508113,0,true,169410698304,169410698368⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916352747439,0,false,-200353008256,-200353008192⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282784458965,0,true,169508373184,169508373248⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916238796587,0,false,-200489743872,-200489743808⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282624718392,0,true,169371446400,169371446464⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916398537160,0,false,-200298067520,-200298067456⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282761549862,0,true,169488736960,169488737024⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916261705690,0,false,-200462252672,-200462252608⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523309828,0,true,11681984,11682048⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499945724,0,false,-11682176,-11682112⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535007850,0,true,23379776,23379840⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488247702,0,false,-23380352,-23380288⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627278,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627652,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282647608527,0,true,169391068480,169391068544⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916375647025,0,false,-200325531840,-200325531776⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282773012903,0,true,169498562432,169498562496⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916250242649,0,false,-200476008384,-200476008320⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068966488979,0,false,-30977445952,-30977445888⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069008278291,0,false,-30934463360,-30934463296⟩
    { al := (8529/51200), au := (1365489/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨183158880337,183272831189⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169410698304,169410698368⟩ : DyadicInterval 40),(⟨-200353008256,-200353008192⟩ : DyadicInterval 40),(⟨746796543867,746796563196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169508373184,169508373248⟩ : DyadicInterval 40),(⟨-200489743872,-200489743808⟩ : DyadicInterval 40),(⟨746777377070,746777396400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169371446400,169371446464⟩ : DyadicInterval 40),(⟨-200298067520,-200298067456⟩ : DyadicInterval 40),(⟨746804242389,746804261719⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169488736960,169488737024⟩ : DyadicInterval 40),(⟨-200462252672,-200462252608⟩ : DyadicInterval 40),(⟨746781231411,746781250740⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11682052,23380074⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11681984,11682048⟩ : DyadicInterval 40),(⟨-11682176,-11682112⟩ : DyadicInterval 40),(⟨762123383523,762123402852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23379776,23379840⟩ : DyadicInterval 40),(⟨-23380352,-23380288⟩ : DyadicInterval 40),(⟨762123383342,762123402671⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183135980751,183261385127⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169391068480,169391068544⟩ : DyadicInterval 40),(⟨-200325531840,-200325531776⟩ : DyadicInterval 40),(⟨746800394151,746800413480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169498562432,169498562496⟩ : DyadicInterval 40),(⟨-200476008384,-200476008320⟩ : DyadicInterval 40),(⟨746779302855,746779322184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30977445952,-30934463296⟩ : DyadicInterval 40),(⟨777590615264,777612125856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169410698304,169508373248⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200489743872,-200353008192⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2848_ok : ecellOkT e2848 = true := by decide +kernel
theorem e2848_pos {a z : ℝ} (ha1 : ((8529/51200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1365489/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2848 e2848_ok ha1 ha2 hz1 hz2 hz

-- box ['1365489/8192000', '683169/4096000', '3999/4000', '7999/8000']  interval_lower 298506221/1099511627776
noncomputable def e2849 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282784458964,0,true,169508373184,169508373248⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916238796588,0,false,-200489743872,-200489743808⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282898409817,0,true,169606039424,169606039488⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916124845735,0,false,-200626496512,-200626496448⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282738640756,0,true,169469100416,169469100480⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916284614796,0,false,-200434762176,-200434762112⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282875486470,0,true,169586392768,169586392832⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916147769082,0,false,-200598984832,-200598984768⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523317396,0,true,11689536,11689600⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499938156,0,false,-11689728,-11689664⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535022988,0,true,23394944,23395008⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488232564,0,false,-23395520,-23395456⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627278,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627652,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282761545133,0,true,169488732928,169488732992⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916261710419,0,false,-200462246976,-200462246912⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282886956635,0,true,169596223424,169596223488⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916136298917,0,false,-200612750784,-200612750720⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068928493969,0,false,-31016527360,-31016527296⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068970311648,0,false,-30973514048,-30973513984⟩
    { al := (1365489/8192000), au := (683169/4096000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨183272831188,183386782041⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169508373184,169508373248⟩ : DyadicInterval 40),(⟨-200489743872,-200489743808⟩ : DyadicInterval 40),(⟨746777377070,746777396400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169606039424,169606039488⟩ : DyadicInterval 40),(⟨-200626496512,-200626496448⟩ : DyadicInterval 40),(⟨746758198113,746758217442⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169469100416,169469100480⟩ : DyadicInterval 40),(⟨-200434762176,-200434762112⟩ : DyadicInterval 40),(⟨746785085250,746785104579⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169586392768,169586392832⟩ : DyadicInterval 40),(⟨-200598984832,-200598984768⟩ : DyadicInterval 40),(⟨746762057289,746762076618⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11689620,23395212⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11689536,11689600⟩ : DyadicInterval 40),(⟨-11689728,-11689664⟩ : DyadicInterval 40),(⟨762123383523,762123402852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23394944,23395008⟩ : DyadicInterval 40),(⟨-23395520,-23395456⟩ : DyadicInterval 40),(⟨762123383342,762123402671⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183249917357,183375328859⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169488732928,169488732992⟩ : DyadicInterval 40),(⟨-200462246976,-200462246912⟩ : DyadicInterval 40),(⟨746781232185,746781251514⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169596223424,169596223488⟩ : DyadicInterval 40),(⟨-200612750784,-200612750720⟩ : DyadicInterval 40),(⟨746760126332,746760145661⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31016527360,-30973513984⟩ : DyadicInterval 40),(⟨777610140608,777631666560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169508373184,169606039488⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200626496512,-200489743808⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2849_ok : ecellOkT e2849 = true := by decide +kernel
theorem e2849_pos {a z : ℝ} (ha1 : ((1365489/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((683169/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2849 e2849_ok ha1 ha2 hz1 hz2 hz

-- box ['8529/51200', '1365489/8192000', '7999/8000', '1']  interval_lower 296926001/1099511627776
noncomputable def e2850 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282670508113,0,true,169410698304,169410698368⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916352747439,0,false,-200353008256,-200353008192⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282784458965,0,true,169508373184,169508373248⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916238796587,0,false,-200489743872,-200489743808⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282647613252,0,true,169391072512,169391072576⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916375642300,0,false,-200325537536,-200325537472⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523317971,0,true,11690112,11690176⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499937581,0,false,-11690304,-11690240⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627651,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1282659055913,0,true,169400881344,169400881408⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨916364199639,0,false,-200339267072,-200339267008⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1282784467439,0,true,169508380480,169508380544⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨916238788113,0,false,-200489754048,-200489753984⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1068962670484,0,false,-30981373568,-30981373504⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1069004464791,0,false,-30938385664,-30938385600⟩
    { al := (8529/51200), au := (1365489/8192000), zl := (7999/8000), zu := 1,
      A := ⟨183158880337,183272831189⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169410698304,169410698368⟩ : DyadicInterval 40),(⟨-200353008256,-200353008192⟩ : DyadicInterval 40),(⟨746796543867,746796563196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169508373184,169508373248⟩ : DyadicInterval 40),(⟨-200489743872,-200489743808⟩ : DyadicInterval 40),(⟨746777377070,746777396400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169391072512,169391072576⟩ : DyadicInterval 40),(⟨-200325537536,-200325537472⟩ : DyadicInterval 40),(⟨746800393378,746800412708⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169508373184,169508373248⟩ : DyadicInterval 40),(⟨-200489743872,-200489743808⟩ : DyadicInterval 40),(⟨746777377070,746777396400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11690195⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11690112,11690176⟩ : DyadicInterval 40),(⟨-11690304,-11690240⟩ : DyadicInterval 40),(⟨762123383523,762123402852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨183147428137,183272839663⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169400881344,169400881408⟩ : DyadicInterval 40),(⟨-200339267072,-200339267008⟩ : DyadicInterval 40),(⟨746798469490,746798488820⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169508380480,169508380544⟩ : DyadicInterval 40),(⟨-200489754048,-200489753984⟩ : DyadicInterval 40),(⟨746777375628,746777394958⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30981373568,-30938385600⟩ : DyadicInterval 40),(⟨777592576416,777614089664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨169410698304,169508373248⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200489743872,-200353008192⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2850_ok : ecellOkT e2850 = true := by decide +kernel
theorem e2850_pos {a z : ℝ} (ha1 : ((8529/51200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1365489/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2850 e2850_ok ha1 ha2 hz1 hz2 hz

-- box ['1365489/8192000', '683169/4096000', '7999/8000', '1']  interval_lower 37288521/137438953472
noncomputable def e2851 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282784458964,0,true,169508373184,169508373248⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916238796588,0,false,-200489743872,-200489743808⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282898409817,0,true,169606039424,169606039488⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916124845735,0,false,-200626496512,-200626496448⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282761549860,0,true,169488736960,169488737024⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916261705692,0,false,-200462252672,-200462252608⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523325541,0,true,11697664,11697728⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499930011,0,false,-11697856,-11697792⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627651,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1282772999640,0,true,169498551040,169498551104⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨916250255912,0,false,-200475992448,-200475992384⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1282898418294,0,true,169606046720,169606046784⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨916124837258,0,false,-200626506688,-200626506624⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1068924670724,0,false,-31020459968,-31020459904⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1068966493401,0,false,-30977441408,-30977441344⟩
    { al := (1365489/8192000), au := (683169/4096000), zl := (7999/8000), zu := 1,
      A := ⟨183272831188,183386782041⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169508373184,169508373248⟩ : DyadicInterval 40),(⟨-200489743872,-200489743808⟩ : DyadicInterval 40),(⟨746777377070,746777396400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169606039424,169606039488⟩ : DyadicInterval 40),(⟨-200626496512,-200626496448⟩ : DyadicInterval 40),(⟨746758198113,746758217442⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169488736960,169488737024⟩ : DyadicInterval 40),(⟨-200462252672,-200462252608⟩ : DyadicInterval 40),(⟨746781231411,746781250741⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169606039424,169606039488⟩ : DyadicInterval 40),(⟨-200626496512,-200626496448⟩ : DyadicInterval 40),(⟨746758198113,746758217442⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11697765⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11697664,11697728⟩ : DyadicInterval 40),(⟨-11697856,-11697792⟩ : DyadicInterval 40),(⟨762123383523,762123402852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨183261371864,183386790518⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169498551040,169498551104⟩ : DyadicInterval 40),(⟨-200475992448,-200475992384⟩ : DyadicInterval 40),(⟨746779305091,746779324421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169606046720,169606046784⟩ : DyadicInterval 40),(⟨-200626506688,-200626506624⟩ : DyadicInterval 40),(⟨746758196669,746758215998⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31020459968,-30977441344⟩ : DyadicInterval 40),(⟨777612104288,777633632864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨169508373184,169606039488⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200626496512,-200489743808⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2851_ok : ecellOkT e2851 = true := by decide +kernel
theorem e2851_pos {a z : ℝ} (ha1 : ((1365489/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((683169/4096000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2851 e2851_ok ha1 ha2 hz1 hz2 hz

-- box ['683169/4096000', '1367187/8192000', '3999/4000', '7999/8000']  interval_lower 299891727/1099511627776
noncomputable def e2852 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282898409816,0,true,169606039424,169606039488⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916124845736,0,false,-200626496512,-200626496448⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283012360668,0,true,169703696960,169703697024⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916010894884,0,false,-200763266176,-200763266112⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282852563120,0,true,169566745664,169566745728⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916170692432,0,false,-200571473792,-200571473728⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282989423077,0,true,169684039808,169684039872⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916033832475,0,false,-200735733952,-200735733888⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523324965,0,true,11697088,11697152⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499930587,0,false,-11697280,-11697216⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535038126,0,true,23410048,23410112⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488217426,0,false,-23410624,-23410560⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627277,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627652,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282875481735,0,true,169586388672,169586388736⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916147773817,0,false,-200598979136,-200598979072⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283000900360,0,true,169693875712,169693875776⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916022355192,0,false,-200749510144,-200749510080⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068890475345,0,false,-31055634432,-31055634368⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068932321392,0,false,-31012590400,-31012590336⟩
    { al := (683169/4096000), au := (1367187/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨183386782040,183500732892⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169606039424,169606039488⟩ : DyadicInterval 40),(⟨-200626496512,-200626496448⟩ : DyadicInterval 40),(⟨746758198113,746758217443⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169703696960,169703697024⟩ : DyadicInterval 40),(⟨-200763266176,-200763266112⟩ : DyadicInterval 40),(⟨746739007030,746739026360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169566745664,169566745728⟩ : DyadicInterval 40),(⟨-200571473792,-200571473728⟩ : DyadicInterval 40),(⟨746765916010,746765935340⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169684039808,169684039872⟩ : DyadicInterval 40),(⟨-200735733952,-200735733888⟩ : DyadicInterval 40),(⟨746742871059,746742890389⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11697189,23410350⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11697088,11697152⟩ : DyadicInterval 40),(⟨-11697280,-11697216⟩ : DyadicInterval 40),(⟨762123383523,762123402852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23410048,23410112⟩ : DyadicInterval 40),(⟨-23410624,-23410560⟩ : DyadicInterval 40),(⟨762123383341,762123402670⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183363853959,183489272584⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169586388672,169586388736⟩ : DyadicInterval 40),(⟨-200598979136,-200598979072⟩ : DyadicInterval 40),(⟨746762058102,746762077432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169693875712,169693875776⟩ : DyadicInterval 40),(⟨-200749510144,-200749510080⟩ : DyadicInterval 40),(⟨746740937662,746740956991⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31055634432,-31012590336⟩ : DyadicInterval 40),(⟨777629678784,777651220096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169606039424,169703697024⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200763266176,-200626496448⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2852_ok : ecellOkT e2852 = true := by decide +kernel
theorem e2852_pos {a z : ℝ} (ha1 : ((683169/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1367187/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2852 e2852_ok ha1 ha2 hz1 hz2 hz

-- box ['1367187/8192000', '342009/2048000', '3999/4000', '7999/8000']  interval_lower 301280653/1099511627776
noncomputable def e2853 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283012360667,0,true,169703696960,169703697024⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916010894885,0,false,-200763266176,-200763266112⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283126311519,0,true,169801345856,169801345920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915896944033,0,false,-200900052864,-200900052800⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282966485483,0,true,169664382336,169664382400⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916056770069,0,false,-200708202368,-200708202304⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283103359684,0,true,169781678272,169781678336⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915919895868,0,false,-200872500096,-200872500032⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523332534,0,true,11704640,11704704⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499923018,0,false,-11704832,-11704768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535053266,0,true,23425216,23425280⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488202286,0,false,-23425792,-23425728⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627276,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627652,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282989418343,0,true,169684035776,169684035840⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916033837209,0,false,-200735728256,-200735728192⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283114844092,0,true,169791519360,169791519424⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915908411460,0,false,-200886286592,-200886286528⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068852433102,0,false,-31094767168,-31094767104⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068894307522,0,false,-31051692480,-31051692416⟩
    { al := (1367187/8192000), au := (342009/2048000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨183500732891,183614683743⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169703696960,169703697024⟩ : DyadicInterval 40),(⟨-200763266176,-200763266112⟩ : DyadicInterval 40),(⟨746739007031,746739026360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169801345856,169801345920⟩ : DyadicInterval 40),(⟨-200900052864,-200900052800⟩ : DyadicInterval 40),(⟨746719803785,746719823114⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169664382336,169664382400⟩ : DyadicInterval 40),(⟨-200708202368,-200708202304⟩ : DyadicInterval 40),(⟨746746734557,746746753887⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169781678272,169781678336⟩ : DyadicInterval 40),(⟨-200872500096,-200872500032⟩ : DyadicInterval 40),(⟨746723672635,746723691965⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11704758,23425490⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11704640,11704704⟩ : DyadicInterval 40),(⟨-11704832,-11704768⟩ : DyadicInterval 40),(⟨762123383523,762123402852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23425216,23425280⟩ : DyadicInterval 40),(⟨-23425792,-23425728⟩ : DyadicInterval 40),(⟨762123383340,762123402669⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183477790567,183603216316⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169684035776,169684035840⟩ : DyadicInterval 40),(⟨-200735728256,-200735728192⟩ : DyadicInterval 40),(⟨746742871836,746742891166⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169791519360,169791519424⟩ : DyadicInterval 40),(⟨-200886286592,-200886286528⟩ : DyadicInterval 40),(⟨746721736857,746721756186⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31094767168,-31051692416⟩ : DyadicInterval 40),(⟨777649229824,777670786464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169703696960,169801345920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200900052864,-200763266112⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2853_ok : ecellOkT e2853 = true := by decide +kernel
theorem e2853_pos {a z : ℝ} (ha1 : ((1367187/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((342009/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2853 e2853_ok ha1 ha2 hz1 hz2 hz

-- box ['683169/4096000', '1367187/8192000', '7999/8000', '1']  interval_lower 149846625/549755813888
noncomputable def e2854 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282898409816,0,true,169606039424,169606039488⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916124845736,0,false,-200626496512,-200626496448⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283012360668,0,true,169703696960,169703697024⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916010894884,0,false,-200763266176,-200763266112⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282875486468,0,true,169586392768,169586392832⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916147769084,0,false,-200598984768,-200598984704⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523333110,0,true,11705216,11705280⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499922442,0,false,-11705408,-11705344⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627651,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1282886943373,0,true,169596212032,169596212096⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨916136312179,0,false,-200612734848,-200612734784⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1283012369141,0,true,169703704256,169703704320⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨916010886411,0,false,-200763276352,-200763276288⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1068886647347,0,false,-31059572096,-31059572032⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1068928498394,0,false,-31016522752,-31016522688⟩
    { al := (683169/4096000), au := (1367187/8192000), zl := (7999/8000), zu := 1,
      A := ⟨183386782040,183500732892⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169606039424,169606039488⟩ : DyadicInterval 40),(⟨-200626496512,-200626496448⟩ : DyadicInterval 40),(⟨746758198113,746758217443⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169703696960,169703697024⟩ : DyadicInterval 40),(⟨-200763266176,-200763266112⟩ : DyadicInterval 40),(⟨746739007030,746739026360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169586392768,169586392832⟩ : DyadicInterval 40),(⟨-200598984768,-200598984704⟩ : DyadicInterval 40),(⟨746762057263,746762076592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169703696960,169703697024⟩ : DyadicInterval 40),(⟨-200763266176,-200763266112⟩ : DyadicInterval 40),(⟨746739007030,746739026360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11705334⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11705216,11705280⟩ : DyadicInterval 40),(⟨-11705408,-11705344⟩ : DyadicInterval 40),(⟨762123383523,762123402852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨183375315597,183500741365⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169596212032,169596212096⟩ : DyadicInterval 40),(⟨-200612734848,-200612734784⟩ : DyadicInterval 40),(⟨746760128571,746760147901⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169703704256,169703704320⟩ : DyadicInterval 40),(⟨-200763276352,-200763276288⟩ : DyadicInterval 40),(⟨746739005585,746739024915⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31059572096,-31016522688⟩ : DyadicInterval 40),(⟨777631644960,777653188928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨169606039424,169703697024⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200763266176,-200626496448⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2854_ok : ecellOkT e2854 = true := by decide +kernel
theorem e2854_pos {a z : ℝ} (ha1 : ((683169/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1367187/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2854 e2854_ok ha1 ha2 hz1 hz2 hz

-- box ['1367187/8192000', '342009/2048000', '7999/8000', '1']  interval_lower 150540827/549755813888
noncomputable def e2855 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283012360667,0,true,169703696960,169703697024⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916010894885,0,false,-200763266176,-200763266112⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283126311519,0,true,169801345856,169801345920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915896944033,0,false,-200900052864,-200900052800⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1282989423075,0,true,169684039808,169684039872⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨916033832477,0,false,-200735733952,-200735733888⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523340680,0,true,11712832,11712896⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499914872,0,false,-11713024,-11712960⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627651,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1283000887091,0,true,169693864384,169693864448⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨916022368461,0,false,-200749494208,-200749494144⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1283126319992,0,true,169801353152,169801353216⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨915896935560,0,false,-200900063040,-200900062976⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1068848600350,0,false,-31098709888,-31098709824⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1068890479775,0,false,-31055629824,-31055629760⟩
    { al := (1367187/8192000), au := (342009/2048000), zl := (7999/8000), zu := 1,
      A := ⟨183500732891,183614683743⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169703696960,169703697024⟩ : DyadicInterval 40),(⟨-200763266176,-200763266112⟩ : DyadicInterval 40),(⟨746739007031,746739026360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169801345856,169801345920⟩ : DyadicInterval 40),(⟨-200900052864,-200900052800⟩ : DyadicInterval 40),(⟨746719803785,746719823114⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169684039808,169684039872⟩ : DyadicInterval 40),(⟨-200735733952,-200735733888⟩ : DyadicInterval 40),(⟨746742871060,746742890389⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169801345856,169801345920⟩ : DyadicInterval 40),(⟨-200900052864,-200900052800⟩ : DyadicInterval 40),(⟨746719803785,746719823114⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11712904⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11712832,11712896⟩ : DyadicInterval 40),(⟨-11713024,-11712960⟩ : DyadicInterval 40),(⟨762123383523,762123402852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨183489259315,183614692216⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169693864384,169693864448⟩ : DyadicInterval 40),(⟨-200749494208,-200749494144⟩ : DyadicInterval 40),(⟨746740939868,746740959198⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169801353152,169801353216⟩ : DyadicInterval 40),(⟨-200900063040,-200900062976⟩ : DyadicInterval 40),(⟨746719802338,746719821667⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31098709888,-31055629760⟩ : DyadicInterval 40),(⟨777651198496,777672757824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨169703696960,169801345920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-200900052864,-200763266112⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2855_ok : ecellOkT e2855 = true := by decide +kernel
theorem e2855_pos {a z : ℝ} (ha1 : ((1367187/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((342009/2048000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2855 e2855_ok ha1 ha2 hz1 hz2 hz

-- box ['342009/2048000', '273777/1638400', '1999/2000', '7997/8000']  interval_lower 303071403/1099511627776
noncomputable def e2856 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283126311518,0,true,169801345856,169801345920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915896944034,0,false,-200900052864,-200900052800⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283240262370,0,true,169898986048,169898986112⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915782993182,0,false,-201036856512,-201036856448⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283034504176,0,true,169722673280,169722673344⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915988751376,0,false,-200789845952,-200789845888⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283171364133,0,true,169839950784,169839950848⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915851891419,0,false,-200954138752,-200954138688⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546765094,0,true,35136704,35136768⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476490458,0,false,-35137920,-35137856⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558508537,0,true,46879744,46879808⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464747015,0,false,-46881792,-46881728⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625777,0,false,-2048,-1984⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626654,0,false,-1152,-1088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283080403284,0,true,169762006400,169762006464⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915942852268,0,false,-200844942528,-200844942464⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283205821857,0,true,169869476224,169869476288⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915817433695,0,false,-200995507200,-200995507136⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068822041520,0,false,-31126030976,-31126030912⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068863934300,0,false,-31082936128,-31082936064⟩
    { al := (342009/2048000), au := (273777/1638400), zl := (1999/2000), zu := (7997/8000),
      A := ⟨183614683742,183728634594⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169801345856,169801345920⟩ : DyadicInterval 40),(⟨-200900052864,-200900052800⟩ : DyadicInterval 40),(⟨746719803785,746719823114⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169898986048,169898986112⟩ : DyadicInterval 40),(⟨-201036856512,-201036856448⟩ : DyadicInterval 40),(⟨746700588385,746700607714⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169722673280,169722673344⟩ : DyadicInterval 40),(⟨-200789845952,-200789845888⟩ : DyadicInterval 40),(⟨746735276313,746735295642⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169839950784,169839950848⟩ : DyadicInterval 40),(⟨-200954138752,-200954138688⟩ : DyadicInterval 40),(⟨746712208075,746712227405⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨35137318,46880761⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35136704,35136768⟩ : DyadicInterval 40),(⟨-35137920,-35137856⟩ : DyadicInterval 40),(⟨762123383037,762123402366⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46879744,46879808⟩ : DyadicInterval 40),(⟨-46881792,-46881728⟩ : DyadicInterval 40),(⟨762123382577,762123401906⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2048,-1088⟩ : DyadicInterval 40),(⟨762123384160,762123403904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183568775508,183694194081⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169762006400,169762006464⟩ : DyadicInterval 40),(⟨-200844942528,-200844942464⟩ : DyadicInterval 40),(⟨746727541772,746727561101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169869476224,169869476288⟩ : DyadicInterval 40),(⟨-200995507200,-200995507136⟩ : DyadicInterval 40),(⟨746706397317,746706416647⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31126030976,-31082936064⟩ : DyadicInterval 40),(⟨777664851648,777686418368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169801345856,169898986112⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201036856512,-200900052800⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2856_ok : ecellOkT e2856 = true := by decide +kernel
theorem e2856_pos {a z : ℝ} (ha1 : ((342009/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((273777/1638400 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2856 e2856_ok ha1 ha2 hz1 hz2 hz

-- box ['273777/1638400', '684867/4096000', '1999/2000', '7997/8000']  interval_lower 152233725/549755813888
noncomputable def e2857 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283240262369,0,true,169898986048,169898986112⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915782993183,0,false,-201036856512,-201036856448⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283354213221,0,true,169996617600,169996617664⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915669042331,0,false,-201173677248,-201173677184⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283148398051,0,true,169820271680,169820271744⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915874857501,0,false,-200926567488,-200926567424⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283285272252,0,true,169937550976,169937551040⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915737983300,0,false,-201090897856,-201090897792⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546787804,0,true,35159424,35159488⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476467748,0,false,-35160640,-35160576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558538821,0,true,46910016,46910080⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464716731,0,false,-46912064,-46912000⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625774,0,false,-2048,-1984⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626652,0,false,-1152,-1088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283194325649,0,true,169859625664,169859625728⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915828929903,0,false,-200981705152,-200981705088⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283319751344,0,true,169967092096,169967092160⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915703504208,0,false,-201132297088,-201132297024⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068783961568,0,false,-31165204992,-31165204928⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068825882719,0,false,-31122079488,-31122079424⟩
    { al := (273777/1638400), au := (684867/4096000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨183728634593,183842585445⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169898986048,169898986112⟩ : DyadicInterval 40),(⟨-201036856512,-201036856448⟩ : DyadicInterval 40),(⟨746700588385,746700607715⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169996617600,169996617664⟩ : DyadicInterval 40),(⟨-201173677248,-201173677184⟩ : DyadicInterval 40),(⟨746681360845,746681380175⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169820271680,169820271744⟩ : DyadicInterval 40),(⟨-200926567488,-200926567424⟩ : DyadicInterval 40),(⟨746716080281,746716099610⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169937550976,169937551040⟩ : DyadicInterval 40),(⟨-201090897856,-201090897792⟩ : DyadicInterval 40),(⟨746692995072,746693014402⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨35160028,46911045⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35159424,35159488⟩ : DyadicInterval 40),(⟨-35160640,-35160576⟩ : DyadicInterval 40),(⟨762123383035,762123402364⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46910016,46910080⟩ : DyadicInterval 40),(⟨-46912064,-46912000⟩ : DyadicInterval 40),(⟨762123382574,762123401903⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2048,-1088⟩ : DyadicInterval 40),(⟨762123384160,762123403904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183682697873,183808123568⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169859625664,169859625728⟩ : DyadicInterval 40),(⟨-200981705152,-200981705088⟩ : DyadicInterval 40),(⟨746708336092,746708355421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169967092096,169967092160⟩ : DyadicInterval 40),(⟨-201132297088,-201132297024⟩ : DyadicInterval 40),(⟨746687177032,746687196362⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31165204992,-31122079424⟩ : DyadicInterval 40),(⟨777684423328,777706005376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169898986048,169996617664⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201173677248,-201036856448⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2857_ok : ecellOkT e2857 = true := by decide +kernel
theorem e2857_pos {a z : ℝ} (ha1 : ((273777/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((684867/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2857 e2857_ok ha1 ha2 hz1 hz2 hz

-- box ['342009/2048000', '273777/1638400', '7997/8000', '3999/4000']  interval_lower 151436077/549755813888
noncomputable def e2858 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283126311518,0,true,169801345856,169801345920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915896944034,0,false,-200900052864,-200900052800⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283240262370,0,true,169898986048,169898986112⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915782993182,0,false,-201036856512,-201036856448⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283057456011,0,true,169742341952,169742342016⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915965799541,0,false,-200817396608,-200817396544⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283194330212,0,true,169859629568,169859629632⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915828925340,0,false,-200981710656,-200981710592⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535052629,0,true,23424576,23424640⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488202923,0,false,-23425152,-23425088⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546788503,0,true,35160128,35160192⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476467049,0,false,-35161344,-35161280⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626651,0,false,-1152,-1088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627277,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283091879101,0,true,169771840320,169771840384⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915931376451,0,false,-200858718336,-200858718272⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283217304824,0,true,169879315328,169879315392⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915805950728,0,false,-201009293504,-201009293440⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068818204507,0,false,-31129978112,-31129978048⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068860102294,0,false,-31086878016,-31086877952⟩
    { al := (342009/2048000), au := (273777/1638400), zl := (7997/8000), zu := (3999/4000),
      A := ⟨183614683742,183728634594⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169801345856,169801345920⟩ : DyadicInterval 40),(⟨-200900052864,-200900052800⟩ : DyadicInterval 40),(⟨746719803785,746719823114⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169898986048,169898986112⟩ : DyadicInterval 40),(⟨-201036856512,-201036856448⟩ : DyadicInterval 40),(⟨746700588385,746700607714⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169742341952,169742342016⟩ : DyadicInterval 40),(⟨-200817396608,-200817396544⟩ : DyadicInterval 40),(⟨746731408905,746731428234⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169859629568,169859629632⟩ : DyadicInterval 40),(⟨-200981710656,-200981710592⟩ : DyadicInterval 40),(⟨746708335336,746708354666⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23424853,35160727⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23424576,23424640⟩ : DyadicInterval 40),(⟨-23425152,-23425088⟩ : DyadicInterval 40),(⟨762123383340,762123402669⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35160128,35160192⟩ : DyadicInterval 40),(⟨-35161344,-35161280⟩ : DyadicInterval 40),(⟨762123383035,762123402364⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1152,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183580251325,183705677048⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169771840320,169771840384⟩ : DyadicInterval 40),(⟨-200858718336,-200858718272⟩ : DyadicInterval 40),(⟨746725607665,746725626995⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169879315328,169879315392⟩ : DyadicInterval 40),(⟨-201009293504,-201009293440⟩ : DyadicInterval 40),(⟨746704460658,746704479988⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31129978112,-31086877952⟩ : DyadicInterval 40),(⟨777666822592,777688391936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169801345856,169898986112⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201036856512,-200900052800⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2858_ok : ecellOkT e2858 = true := by decide +kernel
theorem e2858_pos {a z : ℝ} (ha1 : ((342009/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((273777/1638400 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2858 e2858_ok ha1 ha2 hz1 hz2 hz

-- box ['273777/1638400', '684867/4096000', '7997/8000', '3999/4000']  interval_lower 304267543/1099511627776
noncomputable def e2859 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283240262369,0,true,169898986048,169898986112⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915782993183,0,false,-201036856512,-201036856448⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283354213221,0,true,169996617600,169996617664⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915669042331,0,false,-201173677248,-201173677184⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283171364130,0,true,169839950784,169839950848⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915851891422,0,false,-200954138752,-200954138688⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283308252575,0,true,169957240192,169957240256⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915715002977,0,false,-201118490304,-201118490240⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535067770,0,true,23439744,23439808⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488187782,0,false,-23440256,-23440192⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546811215,0,true,35182848,35182912⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476444337,0,false,-35184064,-35184000⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626650,0,false,-1152,-1088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627277,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283205808582,0,true,169869464832,169869464896⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915817446970,0,false,-200995491264,-200995491200⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283331241430,0,true,169976936384,169976936448⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915692014122,0,false,-201146093632,-201146093568⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068780119795,0,false,-31169157248,-31169157184⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068822045957,0,false,-31126026368,-31126026304⟩
    { al := (273777/1638400), au := (684867/4096000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨183728634593,183842585445⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169898986048,169898986112⟩ : DyadicInterval 40),(⟨-201036856512,-201036856448⟩ : DyadicInterval 40),(⟨746700588385,746700607715⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169996617600,169996617664⟩ : DyadicInterval 40),(⟨-201173677248,-201173677184⟩ : DyadicInterval 40),(⟨746681360845,746681380175⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169839950784,169839950848⟩ : DyadicInterval 40),(⟨-200954138752,-200954138688⟩ : DyadicInterval 40),(⟨746712208076,746712227405⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169957240192,169957240256⟩ : DyadicInterval 40),(⟨-201118490304,-201118490240⟩ : DyadicInterval 40),(⟨746689117501,746689136831⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23439994,35183439⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23439744,23439808⟩ : DyadicInterval 40),(⟨-23440256,-23440192⟩ : DyadicInterval 40),(⟨762123383308,762123402637⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35182848,35182912⟩ : DyadicInterval 40),(⟨-35184064,-35184000⟩ : DyadicInterval 40),(⟨762123383034,762123402363⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1152,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183694180806,183819613654⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169869464832,169869464896⟩ : DyadicInterval 40),(⟨-200995491264,-200995491200⟩ : DyadicInterval 40),(⟨746706399567,746706418897⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169976936384,169976936448⟩ : DyadicInterval 40),(⟨-201146093632,-201146093568⟩ : DyadicInterval 40),(⟨746685237962,746685257291⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31169157248,-31126026304⟩ : DyadicInterval 40),(⟨777686396768,777707981504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169898986048,169996617664⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201173677248,-201036856448⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2859_ok : ecellOkT e2859 = true := by decide +kernel
theorem e2859_pos {a z : ℝ} (ha1 : ((273777/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((684867/4096000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2859 e2859_ok ha1 ha2 hz1 hz2 hz

-- box ['684867/4096000', '1370583/8192000', '1999/2000', '7997/8000']  interval_lower 305866455/1099511627776
noncomputable def e2860 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283354213220,0,true,169996617600,169996617664⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915669042332,0,false,-201173677248,-201173677184⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283468164072,0,true,170094240512,170094240576⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915555091480,0,false,-201310515008,-201310514944⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283262291927,0,true,169917861376,169917861440⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915760963625,0,false,-201063306112,-201063306048⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283399180371,0,true,170035142464,170035142528⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915624075181,0,false,-201227673984,-201227673920⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546810516,0,true,35182144,35182208⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476445036,0,false,-35183360,-35183296⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558569107,0,true,46940288,46940352⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464686445,0,false,-46942336,-46942272⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625771,0,false,-2048,-1984⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626651,0,false,-1152,-1088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283308248007,0,true,169957236288,169957236352⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915715007545,0,false,-201118484800,-201118484736⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283433680830,0,true,170064699264,170064699328⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915589574722,0,false,-201269104000,-201269103936⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068745858005,0,false,-31204404736,-31204404672⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068787807532,0,false,-31161248448,-31161248384⟩
    { al := (684867/4096000), au := (1370583/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨183842585444,183956536296⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169996617600,169996617664⟩ : DyadicInterval 40),(⟨-201173677248,-201173677184⟩ : DyadicInterval 40),(⟨746681360846,746681380175⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170094240512,170094240576⟩ : DyadicInterval 40),(⟨-201310515008,-201310514944⟩ : DyadicInterval 40),(⟨746662121139,746662140468⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169917861376,169917861440⟩ : DyadicInterval 40),(⟨-201063306112,-201063306048⟩ : DyadicInterval 40),(⟨746696872173,746696891502⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170035142464,170035142528⟩ : DyadicInterval 40),(⟨-201227673984,-201227673920⟩ : DyadicInterval 40),(⟨746673769958,746673789288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨35182740,46941331⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35182144,35182208⟩ : DyadicInterval 40),(⟨-35183360,-35183296⟩ : DyadicInterval 40),(⟨762123383034,762123402363⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46940288,46940352⟩ : DyadicInterval 40),(⟨-46942336,-46942272⟩ : DyadicInterval 40),(⟨762123382571,762123401900⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2048,-1088⟩ : DyadicInterval 40),(⟨762123384160,762123403904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183796620231,183922053054⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169957236288,169957236352⟩ : DyadicInterval 40),(⟨-201118484800,-201118484736⟩ : DyadicInterval 40),(⟨746689118259,746689137588⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170064699264,170064699328⟩ : DyadicInterval 40),(⟨-201269104000,-201269103936⟩ : DyadicInterval 40),(⟨746667944627,746667963956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31204404736,-31161248384⟩ : DyadicInterval 40),(⟨777704007808,777725605248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169996617600,170094240576⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201310515008,-201173677184⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2860_ok : ecellOkT e2860 = true := by decide +kernel
theorem e2860_pos {a z : ℝ} (ha1 : ((684867/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1370583/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2860 e2860_ok ha1 ha2 hz1 hz2 hz

-- box ['1370583/8192000', '171429/1024000', '1999/2000', '7997/8000']  interval_lower 307269087/1099511627776
noncomputable def e2861 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283468164071,0,true,170094240512,170094240576⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915555091481,0,false,-201310515008,-201310514944⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283582114923,0,true,170191854720,170191854784⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915441140629,0,false,-201447369728,-201447369664⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283376185802,0,true,170015442432,170015442496⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915647069750,0,false,-201200061696,-201200061632⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283513088491,0,true,170132725312,170132725376⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915510167061,0,false,-201364467072,-201364467008⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546833231,0,true,35204864,35204928⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476422321,0,false,-35206080,-35206016⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558599394,0,true,46970560,46970624⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464656158,0,false,-46972672,-46972608⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625769,0,false,-2048,-1984⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626649,0,false,-1152,-1088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283422170370,0,true,170054838272,170054838336⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915601085182,0,false,-201255281472,-201255281408⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283547610321,0,true,170162297792,170162297856⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915475645231,0,false,-201405928000,-201405927936⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068707730831,0,false,-31243630208,-31243630144⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068749708736,0,false,-31200443200,-31200443136⟩
    { al := (1370583/8192000), au := (171429/1024000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨183956536295,184070487147⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170094240512,170094240576⟩ : DyadicInterval 40),(⟨-201310515008,-201310514944⟩ : DyadicInterval 40),(⟨746662121139,746662140469⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170191854720,170191854784⟩ : DyadicInterval 40),(⟨-201447369728,-201447369664⟩ : DyadicInterval 40),(⟨746642869274,746642888603⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170015442432,170015442496⟩ : DyadicInterval 40),(⟨-201200061696,-201200061632⟩ : DyadicInterval 40),(⟨746677651895,746677671225⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170132725312,170132725376⟩ : DyadicInterval 40),(⟨-201364467072,-201364467008⟩ : DyadicInterval 40),(⟨746654532668,746654551997⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨35205455,46971618⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35204864,35204928⟩ : DyadicInterval 40),(⟨-35206080,-35206016⟩ : DyadicInterval 40),(⟨762123383032,762123402361⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46970560,46970624⟩ : DyadicInterval 40),(⟨-46972672,-46972608⟩ : DyadicInterval 40),(⟨762123382601,762123401930⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2048,-1088⟩ : DyadicInterval 40),(⟨762123384160,762123403904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183910542594,184035982545⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170054838272,170054838336⟩ : DyadicInterval 40),(⟨-201255281472,-201255281408⟩ : DyadicInterval 40),(⟨746669888270,746669907600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170162297792,170162297856⟩ : DyadicInterval 40),(⟨-201405928000,-201405927936⟩ : DyadicInterval 40),(⟨746648700088,746648719417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31243630208,-31200443136⟩ : DyadicInterval 40),(⟨777723605184,777745217984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170094240512,170191854784⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201447369728,-201310514944⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2861_ok : ecellOkT e2861 = true := by decide +kernel
theorem e2861_pos {a z : ℝ} (ha1 : ((1370583/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((171429/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2861 e2861_ok ha1 ha2 hz1 hz2 hz

-- box ['684867/4096000', '1370583/8192000', '7997/8000', '3999/4000']  interval_lower 38208277/137438953472
noncomputable def e2862 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283354213220,0,true,169996617600,169996617664⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915669042332,0,false,-201173677248,-201173677184⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283468164072,0,true,170094240512,170094240576⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915555091480,0,false,-201310515008,-201310514944⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283285272250,0,true,169937550976,169937551040⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915737983302,0,false,-201090897856,-201090897792⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283422174939,0,true,170054842176,170054842240⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915601080613,0,false,-201255286912,-201255286848⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535082912,0,true,23454848,23454912⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488172640,0,false,-23455424,-23455360⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546833929,0,true,35205568,35205632⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476421623,0,false,-35206720,-35206656⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626648,0,false,-1152,-1088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627276,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283319738067,0,true,169967080704,169967080768⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915703517485,0,false,-201132281152,-201132281088⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283445178044,0,true,170074548800,170074548864⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915578077508,0,false,-201282910848,-201282910784⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068742011466,0,false,-31208362048,-31208361984⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068783966008,0,false,-31165200448,-31165200384⟩
    { al := (684867/4096000), au := (1370583/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨183842585444,183956536296⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169996617600,169996617664⟩ : DyadicInterval 40),(⟨-201173677248,-201173677184⟩ : DyadicInterval 40),(⟨746681360846,746681380175⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170094240512,170094240576⟩ : DyadicInterval 40),(⟨-201310515008,-201310514944⟩ : DyadicInterval 40),(⟨746662121139,746662140468⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169937550976,169937551040⟩ : DyadicInterval 40),(⟨-201090897856,-201090897792⟩ : DyadicInterval 40),(⟨746692995073,746693014402⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170054842176,170054842240⟩ : DyadicInterval 40),(⟨-201255286912,-201255286848⟩ : DyadicInterval 40),(⟨746669887485,746669906815⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23455136,35206153⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23454848,23454912⟩ : DyadicInterval 40),(⟨-23455424,-23455360⟩ : DyadicInterval 40),(⟨762123383339,762123402668⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35205568,35205632⟩ : DyadicInterval 40),(⟨-35206720,-35206656⟩ : DyadicInterval 40),(⟨762123383000,762123402329⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1152,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨183808110291,183933550268⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169967080704,169967080768⟩ : DyadicInterval 40),(⟨-201132281152,-201132281088⟩ : DyadicInterval 40),(⟨746687179285,746687198615⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170074548800,170074548864⟩ : DyadicInterval 40),(⟨-201282910848,-201282910784⟩ : DyadicInterval 40),(⟨746666003130,746666022460⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31208362048,-31165200384⟩ : DyadicInterval 40),(⟨777705983808,777727583904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨169996617600,170094240576⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201310515008,-201173677184⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2862_ok : ecellOkT e2862 = true := by decide +kernel
theorem e2862_pos {a z : ℝ} (ha1 : ((684867/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1370583/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2862 e2862_ok ha1 ha2 hz1 hz2 hz

-- box ['1370583/8192000', '171429/1024000', '7997/8000', '3999/4000']  interval_lower 307068135/1099511627776

end CKLaneC2R.EpCells.B047


