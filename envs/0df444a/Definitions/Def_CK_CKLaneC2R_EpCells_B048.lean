-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B048
-- name    : CK_CKLaneC2R_EpCells_B048
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:26:52.955633+00:00
-- url     : https://prove2.me/theorems/cbe17869-dc27-4322-b796-03a4ec2057b9
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B048` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B048` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B048` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B048 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B048.lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheckT

-- ===== source module CKLaneC2R.EpCells.B048 =====
section

namespace CKLaneC2R.EpCells.B048

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['171429/1024000', '1372281/8192000', '3997/4000', '1599/1600']  interval_lower 309076711/1099511627776
noncomputable def e2880 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283582114922,0,true,170191854720,170191854784⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915441140630,0,false,-201447369728,-201447369664⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283696065774,0,true,170289460224,170289460288⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915327189778,0,false,-201584241536,-201584241472⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283444062056,0,true,170073592768,170073592832⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915579193496,0,false,-201281570688,-201281570624⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283580950501,0,true,170190857280,170190857344⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915442305051,0,false,-201445971200,-201445971136⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570341260,0,true,58711872,58711936⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452914292,0,false,-58715072,-58715008⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582130143,0,true,70500096,70500160⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441125409,0,false,-70504640,-70504576⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623255,0,false,-4544,-4480⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624641,0,false,-3136,-3072⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283513084219,0,true,170132721664,170132721728⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915510171333,0,false,-201364461952,-201364461888⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283638516985,0,true,170240167424,170240167488⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915384738567,0,false,-201515114816,-201515114752⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068677291445,0,false,-31274947392,-31274947328⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068719287689,0,false,-31231740288,-31231740224⟩
    { al := (171429/1024000), au := (1372281/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨184070487146,184184437998⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170191854720,170191854784⟩ : DyadicInterval 40),(⟨-201447369728,-201447369664⟩ : DyadicInterval 40),(⟨746642869274,746642888603⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170289460224,170289460288⟩ : DyadicInterval 40),(⟨-201584241536,-201584241472⟩ : DyadicInterval 40),(⟨746623605303,746623624633⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170073592768,170073592832⟩ : DyadicInterval 40),(⟨-201281570688,-201281570624⟩ : DyadicInterval 40),(⟨746666191587,746666210917⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170190857280,170190857344⟩ : DyadicInterval 40),(⟨-201445971200,-201445971136⟩ : DyadicInterval 40),(⟨746643066074,746643085404⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨58713484,70502367⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58711872,58711936⟩ : DyadicInterval 40),(⟨-58715072,-58715008⟩ : DyadicInterval 40),(⟨762123382016,762123401345⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70500096,70500160⟩ : DyadicInterval 40),(⟨-70504640,-70504576⟩ : DyadicInterval 40),(⟨762123381303,762123400632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4544,-3072⟩ : DyadicInterval 40),(⟨762123385152,762123405152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184001456443,184126889209⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170132721664,170132721728⟩ : DyadicInterval 40),(⟨-201364461952,-201364461888⟩ : DyadicInterval 40),(⟨746654533387,746654552717⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170240167424,170240167488⟩ : DyadicInterval 40),(⟨-201515114816,-201515114752⟩ : DyadicInterval 40),(⟨746633335747,746633355077⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31274947392,-31231740224⟩ : DyadicInterval 40),(⟨777739253728,777760876576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170191854720,170289460288⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201584241536,-201447369664⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2880_ok : ecellOkT e2880 = true := by decide +kernel
theorem e2880_pos {a z : ℝ} (ha1 : ((171429/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1372281/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2880 e2880_ok ha1 ha2 hz1 hz2 hz

-- box ['1372281/8192000', '137313/819200', '3997/4000', '1599/1600']  interval_lower 310486489/1099511627776
noncomputable def e2881 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283696065773,0,true,170289460224,170289460288⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915327189779,0,false,-201584241536,-201584241472⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283810016625,0,true,170387057088,170387057152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915213238927,0,false,-201721130432,-201721130368⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283557927444,0,true,170171135616,170171135680⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915465328108,0,false,-201418319232,-201418319168⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283694830133,0,true,170288401856,170288401920⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915328425419,0,false,-201582757312,-201582757248⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570379121,0,true,58749760,58749824⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452876431,0,false,-58752960,-58752896⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582175581,0,true,70545536,70545600⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441079971,0,false,-70550080,-70550016⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623249,0,false,-4544,-4480⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624637,0,false,-3200,-3136⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283626992334,0,true,170230295872,170230295936⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915396263218,0,false,-201501272128,-201501272064⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283752432219,0,true,170337738176,170337738240⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915270823333,0,false,-201651952320,-201651952256⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068639126599,0,false,-31314214080,-31314214016⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068681151218,0,false,-31270976256,-31270976192⟩
    { al := (1372281/8192000), au := (137313/819200), zl := (3997/4000), zu := (1599/1600),
      A := ⟨184184437997,184298388849⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170289460224,170289460288⟩ : DyadicInterval 40),(⟨-201584241536,-201584241472⟩ : DyadicInterval 40),(⟨746623605303,746623624633⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170387057088,170387057152⟩ : DyadicInterval 40),(⟨-201721130432,-201721130368⟩ : DyadicInterval 40),(⟨746604329187,746604348517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170171135616,170171135680⟩ : DyadicInterval 40),(⟨-201418319232,-201418319168⟩ : DyadicInterval 40),(⟨746646956754,746646976084⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170288401856,170288401920⟩ : DyadicInterval 40),(⟨-201582757312,-201582757248⟩ : DyadicInterval 40),(⟨746623814292,746623833621⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨58751345,70547805⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58749760,58749824⟩ : DyadicInterval 40),(⟨-58752960,-58752896⟩ : DyadicInterval 40),(⟨762123382012,762123401341⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70545536,70545600⟩ : DyadicInterval 40),(⟨-70550080,-70550016⟩ : DyadicInterval 40),(⟨762123381297,762123400626⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4544,-3136⟩ : DyadicInterval 40),(⟨762123385184,762123405152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184115364558,184240804443⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170230295872,170230295936⟩ : DyadicInterval 40),(⟨-201501272128,-201501272064⟩ : DyadicInterval 40),(⟨746635283974,746635303303⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170337738176,170337738240⟩ : DyadicInterval 40),(⟨-201651952320,-201651952256⟩ : DyadicInterval 40),(⟨746614071783,746614091113⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31314214080,-31270976192⟩ : DyadicInterval 40),(⟨777758871712,777780509920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170289460224,170387057152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201721130432,-201584241472⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2881_ok : ecellOkT e2881 = true := by decide +kernel
theorem e2881_pos {a z : ℝ} (ha1 : ((1372281/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((137313/819200 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2881 e2881_ok ha1 ha2 hz1 hz2 hz

-- box ['171429/1024000', '1372281/8192000', '1599/1600', '1999/2000']  interval_lower 308875623/1099511627776
noncomputable def e2882 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283582114922,0,true,170191854720,170191854784⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915441140630,0,false,-201447369728,-201447369664⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283696065774,0,true,170289460224,170289460288⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915327189778,0,false,-201584241536,-201584241472⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283467070867,0,true,170093304000,170093304064⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915556184685,0,false,-201309202112,-201309202048⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283603973556,0,true,170210578560,170210578624⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915419281996,0,false,-201473623872,-201473623808⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558598633,0,true,46969792,46969856⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464656919,0,false,-46971904,-46971840⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570379944,0,true,58750592,58750656⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452875608,0,false,-58753792,-58753728⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624636,0,false,-3200,-3136⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625770,0,false,-2048,-1984⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283524588465,0,true,170142576640,170142576704⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915498667087,0,false,-201378278464,-201378278400⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283650028379,0,true,170250027584,170250027648⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915373227173,0,false,-201528941824,-201528941760⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068673435873,0,false,-31278914176,-31278914112⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068715437135,0,false,-31235701760,-31235701696⟩
    { al := (171429/1024000), au := (1372281/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨184070487146,184184437998⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170191854720,170191854784⟩ : DyadicInterval 40),(⟨-201447369728,-201447369664⟩ : DyadicInterval 40),(⟨746642869274,746642888603⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170289460224,170289460288⟩ : DyadicInterval 40),(⟨-201584241536,-201584241472⟩ : DyadicInterval 40),(⟨746623605303,746623624633⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170093304000,170093304064⟩ : DyadicInterval 40),(⟨-201309202112,-201309202048⟩ : DyadicInterval 40),(⟨746662305754,746662325084⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170210578560,170210578624⟩ : DyadicInterval 40),(⟨-201473623872,-201473623808⟩ : DyadicInterval 40),(⟨746639174920,746639194249⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨46970857,58752168⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46969792,46969856⟩ : DyadicInterval 40),(⟨-46971904,-46971840⟩ : DyadicInterval 40),(⟨762123382601,762123401930⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58750592,58750656⟩ : DyadicInterval 40),(⟨-58753792,-58753728⟩ : DyadicInterval 40),(⟨762123382012,762123401341⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3200,-1984⟩ : DyadicInterval 40),(⟨762123384608,762123404480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184012960689,184138400603⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170142576640,170142576704⟩ : DyadicInterval 40),(⟨-201378278464,-201378278400⟩ : DyadicInterval 40),(⟨746652589842,746652609172⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170250027584,170250027648⟩ : DyadicInterval 40),(⟨-201528941824,-201528941760⟩ : DyadicInterval 40),(⟨746631389636,746631408966⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31278914176,-31235701696⟩ : DyadicInterval 40),(⟨777741234464,777762859968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170191854720,170289460288⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201584241536,-201447369664⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2882_ok : ecellOkT e2882 = true := by decide +kernel
theorem e2882_pos {a z : ℝ} (ha1 : ((171429/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1372281/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2882 e2882_ok ha1 ha2 hz1 hz2 hz

-- box ['1372281/8192000', '137313/819200', '1599/1600', '1999/2000']  interval_lower 19392799/68719476736
noncomputable def e2883 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283696065773,0,true,170289460224,170289460288⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915327189779,0,false,-201584241536,-201584241472⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283810016625,0,true,170387057088,170387057152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915213238927,0,false,-201721130432,-201721130368⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283580950499,0,true,170190857280,170190857344⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915442305053,0,false,-201445971200,-201445971136⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283717867431,0,true,170308133632,170308133696⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915305388121,0,false,-201610430528,-201610430464⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558628924,0,true,47000128,47000192⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464626628,0,false,-47002176,-47002112⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570417810,0,true,58788416,58788480⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452837742,0,false,-58791616,-58791552⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624632,0,false,-3200,-3136⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625767,0,false,-2048,-1984⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283638503701,0,true,170240156032,170240156096⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915384751851,0,false,-201515098880,-201515098816⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283763950738,0,true,170347603520,170347603584⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915259304814,0,false,-201665789568,-201665789504⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068635266253,0,false,-31318185984,-31318185920⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068677295895,0,false,-31274942784,-31274942720⟩
    { al := (1372281/8192000), au := (137313/819200), zl := (1599/1600), zu := (1999/2000),
      A := ⟨184184437997,184298388849⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170289460224,170289460288⟩ : DyadicInterval 40),(⟨-201584241536,-201584241472⟩ : DyadicInterval 40),(⟨746623605303,746623624633⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170387057088,170387057152⟩ : DyadicInterval 40),(⟨-201721130432,-201721130368⟩ : DyadicInterval 40),(⟨746604329187,746604348517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170190857280,170190857344⟩ : DyadicInterval 40),(⟨-201445971200,-201445971136⟩ : DyadicInterval 40),(⟨746643066075,746643085404⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170308133632,170308133696⟩ : DyadicInterval 40),(⟨-201610430528,-201610430464⟩ : DyadicInterval 40),(⟨746619918246,746619937575⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨47001148,58790034⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨47000128,47000192⟩ : DyadicInterval 40),(⟨-47002176,-47002112⟩ : DyadicInterval 40),(⟨762123382566,762123401895⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58788416,58788480⟩ : DyadicInterval 40),(⟨-58791616,-58791552⟩ : DyadicInterval 40),(⟨762123382008,762123401337⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3200,-1984⟩ : DyadicInterval 40),(⟨762123384608,762123404480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184126875925,184252322962⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170240156032,170240156096⟩ : DyadicInterval 40),(⟨-201515098880,-201515098816⟩ : DyadicInterval 40),(⟨746633338010,746633357339⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170347603520,170347603584⟩ : DyadicInterval 40),(⟨-201665789568,-201665789504⟩ : DyadicInterval 40),(⟨746612123249,746612142578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31318185984,-31274942720⟩ : DyadicInterval 40),(⟨777760854976,777782495872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170289460224,170387057152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201721130432,-201584241472⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2883_ok : ecellOkT e2883 = true := by decide +kernel
theorem e2883_pos {a z : ℝ} (ha1 : ((1372281/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((137313/819200 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2883 e2883_ok ha1 ha2 hz1 hz2 hz

-- box ['137313/819200', '1373979/8192000', '3997/4000', '1599/1600']  interval_lower 77974777/274877906944
noncomputable def e2884 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283810016624,0,true,170387057088,170387057152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915213238928,0,false,-201721130432,-201721130368⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283923967476,0,true,170484645312,170484645376⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915099288076,0,false,-201858036288,-201858036224⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283671792832,0,true,170268669760,170268669824⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915351462720,0,false,-201555084736,-201555084672⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283808709764,0,true,170385937856,170385937920⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915214545788,0,false,-201719560384,-201719560320⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570416987,0,true,58787584,58787648⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452838565,0,false,-58790784,-58790720⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582221023,0,true,70590976,70591040⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441034529,0,false,-70595520,-70595456⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623243,0,false,-4544,-4480⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624633,0,false,-3200,-3136⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283740900448,0,true,170327861376,170327861440⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915282355104,0,false,-201638099328,-201638099264⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283866347467,0,true,170435300288,170435300352⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915156908085,0,false,-201788806784,-201788806720⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068600938144,0,false,-31353506496,-31353506432⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068642991146,0,false,-31310237888,-31310237824⟩
    { al := (137313/819200), au := (1373979/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨184298388848,184412339700⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170387057088,170387057152⟩ : DyadicInterval 40),(⟨-201721130432,-201721130368⟩ : DyadicInterval 40),(⟨746604329187,746604348517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170484645312,170484645376⟩ : DyadicInterval 40),(⟨-201858036288,-201858036224⟩ : DyadicInterval 40),(⟨746585040873,746585060202⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170268669760,170268669824⟩ : DyadicInterval 40),(⟨-201555084736,-201555084672⟩ : DyadicInterval 40),(⟨746627709799,746627729128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170385937856,170385937920⟩ : DyadicInterval 40),(⟨-201719560384,-201719560320⟩ : DyadicInterval 40),(⟨746604550305,746604569635⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨58789211,70593247⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58787584,58787648⟩ : DyadicInterval 40),(⟨-58790784,-58790720⟩ : DyadicInterval 40),(⟨762123382008,762123401337⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70590976,70591040⟩ : DyadicInterval 40),(⟨-70595520,-70595456⟩ : DyadicInterval 40),(⟨762123381291,762123400620⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4544,-3136⟩ : DyadicInterval 40),(⟨762123385184,762123405152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184229272672,184354719691⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170327861376,170327861440⟩ : DyadicInterval 40),(⟨-201638099328,-201638099264⟩ : DyadicInterval 40),(⟨746616022446,746616041776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170435300288,170435300352⟩ : DyadicInterval 40),(⟨-201788806784,-201788806720⟩ : DyadicInterval 40),(⟨746594795633,746594814963⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31353506496,-31310237824⟩ : DyadicInterval 40),(⟨777778502528,777800156128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170387057088,170484645376⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201858036288,-201721130368⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2884_ok : ecellOkT e2884 = true := by decide +kernel
theorem e2884_pos {a z : ℝ} (ha1 : ((137313/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1373979/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2884 e2884_ok ha1 ha2 hz1 hz2 hz

-- box ['1373979/8192000', '343707/2048000', '3997/4000', '1599/1600']  interval_lower 313315343/1099511627776
noncomputable def e2885 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283923967475,0,true,170484645312,170484645376⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915099288077,0,false,-201858036288,-201858036224⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284037918327,0,true,170582224896,170582224960⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914985337225,0,false,-201994959232,-201994959168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283785658220,0,true,170366195328,170366195392⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915237597332,0,false,-201691867328,-201691867264⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283922589396,0,true,170483465152,170483465216⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915100666156,0,false,-201856380544,-201856380480⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570454855,0,true,58825472,58825536⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452800697,0,false,-58828672,-58828608⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582266467,0,true,70636416,70636480⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099440989085,0,false,-70641024,-70640960⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623237,0,false,-4544,-4480⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624629,0,false,-3200,-3136⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283854808569,0,true,170425418240,170425418304⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915168446983,0,false,-201774943552,-201774943488⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283980262708,0,true,170532853696,170532853760⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915042992844,0,false,-201925678336,-201925678272⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068562726087,0,false,-31392824576,-31392824512⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068604807470,0,false,-31349525248,-31349525184⟩
    { al := (1373979/8192000), au := (343707/2048000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨184412339699,184526290551⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170484645312,170484645376⟩ : DyadicInterval 40),(⟨-201858036288,-201858036224⟩ : DyadicInterval 40),(⟨746585040873,746585060202⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170582224896,170582224960⟩ : DyadicInterval 40),(⟨-201994959232,-201994959168⟩ : DyadicInterval 40),(⟨746565740411,746565759740⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170366195328,170366195392⟩ : DyadicInterval 40),(⟨-201691867328,-201691867264⟩ : DyadicInterval 40),(⟨746608450698,746608470027⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170483465152,170483465216⟩ : DyadicInterval 40),(⟨-201856380544,-201856380480⟩ : DyadicInterval 40),(⟨746585274240,746585293569⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨58827079,70638691⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58825472,58825536⟩ : DyadicInterval 40),(⟨-58828672,-58828608⟩ : DyadicInterval 40),(⟨762123382004,762123401333⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70636416,70636480⟩ : DyadicInterval 40),(⟨-70641024,-70640960⟩ : DyadicInterval 40),(⟨762123381317,762123400646⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4544,-3136⟩ : DyadicInterval 40),(⟨762123385184,762123405152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184343180793,184468634932⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170425418240,170425418304⟩ : DyadicInterval 40),(⟨-201774943552,-201774943488⟩ : DyadicInterval 40),(⟨746596748763,746596768093⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170532853696,170532853760⟩ : DyadicInterval 40),(⟨-201925678336,-201925678272⟩ : DyadicInterval 40),(⟨746575507390,746575526720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31392824576,-31349525184⟩ : DyadicInterval 40),(⟨777798146208,777819815168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170484645312,170582224960⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201994959232,-201858036224⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2885_ok : ecellOkT e2885 = true := by decide +kernel
theorem e2885_pos {a z : ℝ} (ha1 : ((1373979/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((343707/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2885 e2885_ok ha1 ha2 hz1 hz2 hz

-- box ['137313/819200', '1373979/8192000', '1599/1600', '1999/2000']  interval_lower 311697237/1099511627776
noncomputable def e2886 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283810016624,0,true,170387057088,170387057152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915213238928,0,false,-201721130432,-201721130368⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283923967476,0,true,170484645312,170484645376⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915099288076,0,false,-201858036288,-201858036224⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283694830130,0,true,170288401856,170288401920⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915328425422,0,false,-201582757312,-201582757248⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283831761307,0,true,170405680064,170405680128⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915191494245,0,false,-201747254208,-201747254144⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558659216,0,true,47030400,47030464⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464596336,0,false,-47032448,-47032384⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570455679,0,true,58826304,58826368⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452799873,0,false,-58829504,-58829440⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624628,0,false,-3200,-3136⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625765,0,false,-2048,-1984⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283752418933,0,true,170337726784,170337726848⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915270836619,0,false,-201651936320,-201651936256⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283877873105,0,true,170445170880,170445170944⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915145382447,0,false,-201802654336,-201802654272⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068597073024,0,false,-31357483456,-31357483392⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068639131053,0,false,-31314209536,-31314209472⟩
    { al := (137313/819200), au := (1373979/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨184298388848,184412339700⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170387057088,170387057152⟩ : DyadicInterval 40),(⟨-201721130432,-201721130368⟩ : DyadicInterval 40),(⟨746604329187,746604348517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170484645312,170484645376⟩ : DyadicInterval 40),(⟨-201858036288,-201858036224⟩ : DyadicInterval 40),(⟨746585040873,746585060202⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170288401856,170288401920⟩ : DyadicInterval 40),(⟨-201582757312,-201582757248⟩ : DyadicInterval 40),(⟨746623814293,746623833622⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170405680064,170405680128⟩ : DyadicInterval 40),(⟨-201747254208,-201747254144⟩ : DyadicInterval 40),(⟨746600649424,746600668754⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨47031440,58827903⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨47030400,47030464⟩ : DyadicInterval 40),(⟨-47032448,-47032384⟩ : DyadicInterval 40),(⟨762123382564,762123401893⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58826304,58826368⟩ : DyadicInterval 40),(⟨-58829504,-58829440⟩ : DyadicInterval 40),(⟨762123382004,762123401333⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3200,-1984⟩ : DyadicInterval 40),(⟨762123384608,762123404480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184240791157,184366245329⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170337726784,170337726848⟩ : DyadicInterval 40),(⟨-201651936320,-201651936256⟩ : DyadicInterval 40),(⟨746614074022,746614093351⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170445170880,170445170944⟩ : DyadicInterval 40),(⟨-201802654336,-201802654272⟩ : DyadicInterval 40),(⟨746592844662,746592863991⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31357483456,-31314209472⟩ : DyadicInterval 40),(⟨777780488352,777802144608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170387057088,170484645376⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201858036288,-201721130368⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2886_ok : ecellOkT e2886 = true := by decide +kernel
theorem e2886_pos {a z : ℝ} (ha1 : ((137313/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1373979/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2886 e2886_ok ha1 ha2 hz1 hz2 hz

-- box ['1373979/8192000', '343707/2048000', '1599/1600', '1999/2000']  interval_lower 39139087/137438953472
noncomputable def e2887 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283923967475,0,true,170484645312,170484645376⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915099288077,0,false,-201858036288,-201858036224⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284037918327,0,true,170582224896,170582224960⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914985337225,0,false,-201994959232,-201994959168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283808709762,0,true,170385937856,170385937920⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915214545790,0,false,-201719560384,-201719560320⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283945655182,0,true,170503217856,170503217920⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915077600370,0,false,-201884094848,-201884094784⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558689510,0,true,47060672,47060736⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464566042,0,false,-47062784,-47062720⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570493549,0,true,58864192,58864256⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452762003,0,false,-58867392,-58867328⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624624,0,false,-3200,-3136⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625762,0,false,-2048,-1984⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283866334177,0,true,170435288896,170435288960⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915156921375,0,false,-201788790848,-201788790784⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283991795475,0,true,170542729536,170542729600⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915031460077,0,false,-201939536128,-201939536064⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068558856186,0,false,-31396806592,-31396806528⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068600942602,0,false,-31353501888,-31353501824⟩
    { al := (1373979/8192000), au := (343707/2048000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨184412339699,184526290551⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170484645312,170484645376⟩ : DyadicInterval 40),(⟨-201858036288,-201858036224⟩ : DyadicInterval 40),(⟨746585040873,746585060202⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170582224896,170582224960⟩ : DyadicInterval 40),(⟨-201994959232,-201994959168⟩ : DyadicInterval 40),(⟨746565740411,746565759740⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170385937856,170385937920⟩ : DyadicInterval 40),(⟨-201719560384,-201719560320⟩ : DyadicInterval 40),(⟨746604550305,746604569635⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170503217856,170503217920⟩ : DyadicInterval 40),(⟨-201884094848,-201884094784⟩ : DyadicInterval 40),(⟨746581368428,746581387757⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨47061734,58865773⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨47060672,47060736⟩ : DyadicInterval 40),(⟨-47062784,-47062720⟩ : DyadicInterval 40),(⟨762123382593,762123401922⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58864192,58864256⟩ : DyadicInterval 40),(⟨-58867392,-58867328⟩ : DyadicInterval 40),(⟨762123382000,762123401329⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3200,-1984⟩ : DyadicInterval 40),(⟨762123384608,762123404480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184354706401,184480167699⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170435288896,170435288960⟩ : DyadicInterval 40),(⟨-201788790848,-201788790784⟩ : DyadicInterval 40),(⟨746594797902,746594817231⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170542729536,170542729600⟩ : DyadicInterval 40),(⟨-201939536128,-201939536064⟩ : DyadicInterval 40),(⟨746573553950,746573573280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31396806592,-31353501824⟩ : DyadicInterval 40),(⟨777800134528,777821806176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170484645312,170582224960⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201994959232,-201858036224⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2887_ok : ecellOkT e2887 = true := by decide +kernel
theorem e2887_pos {a z : ℝ} (ha1 : ((1373979/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((343707/2048000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2887 e2887_ok ha1 ha2 hz1 hz2 hz

-- box ['343707/2048000', '1375677/8192000', '999/1000', '7993/8000']  interval_lower 157569963/549755813888
noncomputable def e2888 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284037918326,0,true,170582224896,170582224960⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914985337226,0,false,-201994959232,-201994959168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284151869178,0,true,170679795776,170679795840⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914871386374,0,false,-202131899264,-202131899200⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283853392035,0,true,170424205120,170424205184⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915169863517,0,false,-201773241664,-201773241600⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283990308967,0,true,170541456576,170541456640⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915032946585,0,false,-201937749952,-201937749888⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594038378,0,true,82407488,82407552⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429217174,0,false,-82413696,-82413632⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099605872717,0,true,94240896,94240960⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099417382835,0,false,-94249024,-94248960⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619697,0,false,-8128,-8064⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621600,0,false,-6208,-6144⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283945651317,0,true,170503214528,170503214592⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915077604235,0,false,-201884090240,-201884090176⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1284071098273,0,true,170610636224,170610636288⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨914952157279,0,false,-202034831360,-202034831296⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068532239027,0,false,-31424195072,-31424195008⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068574338729,0,false,-31380875648,-31380875584⟩
    { al := (343707/2048000), au := (1375677/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨184526290550,184640241402⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170582224896,170582224960⟩ : DyadicInterval 40),(⟨-201994959232,-201994959168⟩ : DyadicInterval 40),(⟨746565740411,746565759740⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170679795776,170679795840⟩ : DyadicInterval 40),(⟨-202131899264,-202131899200⟩ : DyadicInterval 40),(⟨746546427837,746546447166⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170424205120,170424205184⟩ : DyadicInterval 40),(⟨-201773241664,-201773241600⟩ : DyadicInterval 40),(⟨746596988500,746597007829⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170541456576,170541456640⟩ : DyadicInterval 40),(⟨-201937749952,-201937749888⟩ : DyadicInterval 40),(⟨746573805770,746573825099⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨82410602,94244941⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82407488,82407552⟩ : DyadicInterval 40),(⟨-82413696,-82413632⟩ : DyadicInterval 40),(⟨762123380478,762123399808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨94240896,94240960⟩ : DyadicInterval 40),(⟨-94249024,-94248960⟩ : DyadicInterval 40),(⟨762123379537,762123398867⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8128,-6144⟩ : DyadicInterval 40),(⟨762123386688,762123406944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184434023541,184559470497⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170503214528,170503214592⟩ : DyadicInterval 40),(⟨-201884090240,-201884090176⟩ : DyadicInterval 40),(⟨746581369108,746581388438⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170610636224,170610636288⟩ : DyadicInterval 40),(⟨-202034831360,-202034831296⟩ : DyadicInterval 40),(⟨746560118293,746560137623⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31424195072,-31380875584⟩ : DyadicInterval 40),(⟨777813821408,777835500416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170582224896,170679795840⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-202131899264,-201994959168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2888_ok : ecellOkT e2888 = true := by decide +kernel
theorem e2888_pos {a z : ℝ} (ha1 : ((343707/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1375677/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2888 e2888_ok ha1 ha2 hz1 hz2 hz

-- box ['1375677/8192000', '688263/4096000', '999/1000', '7993/8000']  interval_lower 158281703/549755813888
noncomputable def e2889 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284151869177,0,true,170679795776,170679795840⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914871386375,0,false,-202131899264,-202131899200⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284265820029,0,true,170777358016,170777358080⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914757435523,0,false,-202268856320,-202268856256⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283967228935,0,true,170521692416,170521692480⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915056026617,0,false,-201910017088,-201910017024⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1284104160111,0,true,170638945728,170638945792⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨914919095441,0,false,-202074563008,-202074562944⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594091399,0,true,82460480,82460544⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429164153,0,false,-82466752,-82466688⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099605933320,0,true,94301440,94301504⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099417322232,0,false,-94309632,-94309568⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619687,0,false,-8128,-8064⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621592,0,false,-6208,-6144⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1284059545189,0,true,170600743616,170600743680⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨914963710363,0,false,-202020947968,-202020947904⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1284184999273,0,true,170708161920,170708161984⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨914838256279,0,false,-202171716416,-202171716352⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068493989327,0,false,-31463554432,-31463554368⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068536117413,0,false,-31420204288,-31420204224⟩
    { al := (1375677/8192000), au := (688263/4096000), zl := (999/1000), zu := (7993/8000),
      A := ⟨184640241401,184754192253⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170679795776,170679795840⟩ : DyadicInterval 40),(⟨-202131899264,-202131899200⟩ : DyadicInterval 40),(⟨746546427837,746546447166⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170777358016,170777358080⟩ : DyadicInterval 40),(⟨-202268856320,-202268856256⟩ : DyadicInterval 40),(⟨746527103087,746527122417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170521692416,170521692480⟩ : DyadicInterval 40),(⟨-201910017088,-201910017024⟩ : DyadicInterval 40),(⟨746577714888,746577734217⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170638945728,170638945792⟩ : DyadicInterval 40),(⟨-202074563008,-202074562944⟩ : DyadicInterval 40),(⟨746554515145,746554534475⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨82463623,94305544⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82460480,82460544⟩ : DyadicInterval 40),(⟨-82466752,-82466688⟩ : DyadicInterval 40),(⟨762123380502,762123399832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨94301440,94301504⟩ : DyadicInterval 40),(⟨-94309632,-94309568⟩ : DyadicInterval 40),(⟨762123379559,762123398888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8128,-6144⟩ : DyadicInterval 40),(⟨762123386688,762123406944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184547917413,184673371497⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170600743616,170600743680⟩ : DyadicInterval 40),(⟨-202020947968,-202020947904⟩ : DyadicInterval 40),(⟨746562076027,746562095356⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170708161920,170708161984⟩ : DyadicInterval 40),(⟨-202171716416,-202171716352⟩ : DyadicInterval 40),(⟨746540810611,746540829941⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31463554432,-31420204224⟩ : DyadicInterval 40),(⟨777833485728,777855180096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170679795776,170777358080⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-202268856320,-202131899200⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2889_ok : ecellOkT e2889 = true := by decide +kernel
theorem e2889_pos {a z : ℝ} (ha1 : ((1375677/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((688263/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2889 e2889_ok ha1 ha2 hz1 hz2 hz

-- box ['343707/2048000', '1375677/8192000', '7993/8000', '3997/4000']  interval_lower 314937259/1099511627776
noncomputable def e2890 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284037918326,0,true,170582224896,170582224960⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914985337226,0,false,-201994959232,-201994959168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284151869178,0,true,170679795776,170679795840⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914871386374,0,false,-202131899264,-202131899200⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283876457821,0,true,170443958784,170443958848⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915146797731,0,false,-201800953920,-201800953856⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1284013388998,0,true,170561220416,170561220480⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915009866554,0,false,-201965483456,-201965483392⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582265581,0,true,70635520,70635584⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099440989971,0,false,-70640128,-70640064⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594092348,0,true,82461440,82461504⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429163204,0,false,-82467712,-82467648⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621591,0,false,-6208,-6144⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623238,0,false,-4544,-4480⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283957183985,0,true,170513090496,170513090560⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915066071567,0,false,-201897947392,-201897947328⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1284082638099,0,true,170620517376,170620517440⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨914940617453,0,false,-202048699008,-202048698944⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068528364851,0,false,-31428181632,-31428181568⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068570469588,0,false,-31384856832,-31384856768⟩
    { al := (343707/2048000), au := (1375677/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨184526290550,184640241402⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170582224896,170582224960⟩ : DyadicInterval 40),(⟨-201994959232,-201994959168⟩ : DyadicInterval 40),(⟨746565740411,746565759740⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170679795776,170679795840⟩ : DyadicInterval 40),(⟨-202131899264,-202131899200⟩ : DyadicInterval 40),(⟨746546427837,746546447166⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170443958784,170443958848⟩ : DyadicInterval 40),(⟨-201800953920,-201800953856⟩ : DyadicInterval 40),(⟨746593084262,746593103592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170561220416,170561220480⟩ : DyadicInterval 40),(⟨-201965483456,-201965483392⟩ : DyadicInterval 40),(⟨746569896108,746569915438⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨70637805,82464572⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70635520,70635584⟩ : DyadicInterval 40),(⟨-70640128,-70640064⟩ : DyadicInterval 40),(⟨762123381317,762123400647⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82461440,82461504⟩ : DyadicInterval 40),(⟨-82467712,-82467648⟩ : DyadicInterval 40),(⟨762123380502,762123399832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6208,-4480⟩ : DyadicInterval 40),(⟨762123385856,762123405984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184445556209,184571010323⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170513090496,170513090560⟩ : DyadicInterval 40),(⟨-201897947392,-201897947328⟩ : DyadicInterval 40),(⟨746579416091,746579435421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170620517376,170620517440⟩ : DyadicInterval 40),(⟨-202048699008,-202048698944⟩ : DyadicInterval 40),(⟨746558162695,746558182025⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31428181632,-31384856768⟩ : DyadicInterval 40),(⟨777815812000,777837493696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170582224896,170679795840⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-202131899264,-201994959168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2890_ok : ecellOkT e2890 = true := by decide +kernel
theorem e2890_pos {a z : ℝ} (ha1 : ((343707/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1375677/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2890 e2890_ok ha1 ha2 hz1 hz2 hz

-- box ['1375677/8192000', '688263/4096000', '7993/8000', '3997/4000']  interval_lower 19772509/68719476736
noncomputable def e2891 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284151869177,0,true,170679795776,170679795840⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914871386375,0,false,-202131899264,-202131899200⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284265820029,0,true,170777358016,170777358080⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914757435523,0,false,-202268856320,-202268856256⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283990308965,0,true,170541456576,170541456640⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915032946587,0,false,-201937749952,-201937749888⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1284127254385,0,true,170658720000,170658720064⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨914896001167,0,false,-202102317056,-202102316992⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582311030,0,true,70680960,70681024⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099440944522,0,false,-70685568,-70685504⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594145375,0,true,82514496,82514560⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429110177,0,false,-82520704,-82520640⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621583,0,false,-6208,-6144⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623233,0,false,-4544,-4480⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1284071084979,0,true,170610624832,170610624896⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨914952170573,0,false,-202034815360,-202034815296⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1284196546221,0,true,170718048320,170718048384⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨914826709331,0,false,-202185594368,-202185594304⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068490110368,0,false,-31467546048,-31467545984⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068532243491,0,false,-31424190528,-31424190464⟩
    { al := (1375677/8192000), au := (688263/4096000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨184640241401,184754192253⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170679795776,170679795840⟩ : DyadicInterval 40),(⟨-202131899264,-202131899200⟩ : DyadicInterval 40),(⟨746546427837,746546447166⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170777358016,170777358080⟩ : DyadicInterval 40),(⟨-202268856320,-202268856256⟩ : DyadicInterval 40),(⟨746527103087,746527122417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170541456576,170541456640⟩ : DyadicInterval 40),(⟨-201937749952,-201937749888⟩ : DyadicInterval 40),(⟨746573805770,746573825099⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170658720000,170658720064⟩ : DyadicInterval 40),(⟨-202102317056,-202102316992⟩ : DyadicInterval 40),(⟨746550600606,746550619936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨70683254,82517599⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70680960,70681024⟩ : DyadicInterval 40),(⟨-70685568,-70685504⟩ : DyadicInterval 40),(⟨762123381311,762123400641⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82514496,82514560⟩ : DyadicInterval 40),(⟨-82520704,-82520640⟩ : DyadicInterval 40),(⟨762123380462,762123399792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6208,-4480⟩ : DyadicInterval 40),(⟨762123385856,762123405984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184559457203,184684918445⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170610624832,170610624896⟩ : DyadicInterval 40),(⟨-202034815360,-202034815296⟩ : DyadicInterval 40),(⟨746560120541,746560139870⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170718048320,170718048384⟩ : DyadicInterval 40),(⟨-202185594368,-202185594304⟩ : DyadicInterval 40),(⟨746538852567,746538871897⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31467546048,-31424190464⟩ : DyadicInterval 40),(⟨777835478848,777857175904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170679795776,170777358080⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-202268856320,-202131899200⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2891_ok : ecellOkT e2891 = true := by decide +kernel
theorem e2891_pos {a z : ℝ} (ha1 : ((1375677/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((688263/4096000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2891 e2891_ok ha1 ha2 hz1 hz2 hz

-- box ['343707/2048000', '1375677/8192000', '3997/4000', '1599/1600']  interval_lower 78683609/274877906944
noncomputable def e2892 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284037918326,0,true,170582224896,170582224960⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914985337226,0,false,-201994959232,-201994959168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284151869178,0,true,170679795776,170679795840⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914871386374,0,false,-202131899264,-202131899200⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283899523608,0,true,170463712192,170463712256⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915123731944,0,false,-201828666880,-201828666816⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1284036469028,0,true,170580983872,170580983936⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨914986786524,0,false,-201993217664,-201993217600⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570492726,0,true,58863360,58863424⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452762826,0,false,-58866560,-58866496⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582311917,0,true,70681856,70681920⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099440943635,0,false,-70686464,-70686400⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623231,0,false,-4608,-4544⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624625,0,false,-3200,-3136⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283968716689,0,true,170522966464,170522966528⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915054538863,0,false,-201911804800,-201911804736⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1284094177953,0,true,170630398528,170630398592⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨914929077599,0,false,-202062566912,-202062566848⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068524490424,0,false,-31432168384,-31432168320⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068566600193,0,false,-31388838272,-31388838208⟩
    { al := (343707/2048000), au := (1375677/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨184526290550,184640241402⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170582224896,170582224960⟩ : DyadicInterval 40),(⟨-201994959232,-201994959168⟩ : DyadicInterval 40),(⟨746565740411,746565759740⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170679795776,170679795840⟩ : DyadicInterval 40),(⟨-202131899264,-202131899200⟩ : DyadicInterval 40),(⟨746546427837,746546447166⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170463712192,170463712256⟩ : DyadicInterval 40),(⟨-201828666880,-201828666816⟩ : DyadicInterval 40),(⟨746589179472,746589198801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170580983872,170580983936⟩ : DyadicInterval 40),(⟨-201993217664,-201993217600⟩ : DyadicInterval 40),(⟨746565985967,746566005296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨58864950,70684141⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58863360,58863424⟩ : DyadicInterval 40),(⟨-58866560,-58866496⟩ : DyadicInterval 40),(⟨762123382000,762123401329⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70681856,70681920⟩ : DyadicInterval 40),(⟨-70686464,-70686400⟩ : DyadicInterval 40),(⟨762123381311,762123400641⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4608,-3136⟩ : DyadicInterval 40),(⟨762123385184,762123405184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184457088913,184582550177⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170522966464,170522966528⟩ : DyadicInterval 40),(⟨-201911804800,-201911804736⟩ : DyadicInterval 40),(⟨746577462926,746577482255⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170630398528,170630398592⟩ : DyadicInterval 40),(⟨-202062566912,-202062566848⟩ : DyadicInterval 40),(⟨746556206950,746556226279⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31432168384,-31388838208⟩ : DyadicInterval 40),(⟨777817802720,777839487072⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170582224896,170679795840⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-202131899264,-201994959168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2892_ok : ecellOkT e2892 = true := by decide +kernel
theorem e2892_pos {a z : ℝ} (ha1 : ((343707/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1375677/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2892 e2892_ok ha1 ha2 hz1 hz2 hz

-- box ['1375677/8192000', '688263/4096000', '3997/4000', '1599/1600']  interval_lower 39519631/137438953472
noncomputable def e2893 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284151869177,0,true,170679795776,170679795840⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914871386375,0,false,-202131899264,-202131899200⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284265820029,0,true,170777358016,170777358080⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914757435523,0,false,-202268856320,-202268856256⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1284013388995,0,true,170561220416,170561220480⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915009866557,0,false,-201965483456,-201965483392⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1284150348659,0,true,170678493888,170678493952⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨914872906893,0,false,-202130071872,-202130071808⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570530599,0,true,58901184,58901248⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452724953,0,false,-58904448,-58904384⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582357369,0,true,70727296,70727360⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099440898183,0,false,-70731904,-70731840⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623226,0,false,-4608,-4544⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624621,0,false,-3200,-3136⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1284082624805,0,true,170620506048,170620506112⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨914940630747,0,false,-202048683072,-202048683008⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1284208093193,0,true,170727934656,170727934720⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨914815162359,0,false,-202199472512,-202199472448⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068486231158,0,false,-31471537856,-31471537792⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068528369315,0,false,-31428177024,-31428176960⟩
    { al := (1375677/8192000), au := (688263/4096000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨184640241401,184754192253⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170679795776,170679795840⟩ : DyadicInterval 40),(⟨-202131899264,-202131899200⟩ : DyadicInterval 40),(⟨746546427837,746546447166⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170777358016,170777358080⟩ : DyadicInterval 40),(⟨-202268856320,-202268856256⟩ : DyadicInterval 40),(⟨746527103087,746527122417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170561220416,170561220480⟩ : DyadicInterval 40),(⟨-201965483456,-201965483392⟩ : DyadicInterval 40),(⟨746569896109,746569915438⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170678493888,170678493952⟩ : DyadicInterval 40),(⟨-202130071872,-202130071808⟩ : DyadicInterval 40),(⟨746546685613,746546704942⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨58902823,70729593⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58901184,58901248⟩ : DyadicInterval 40),(⟨-58904448,-58904384⟩ : DyadicInterval 40),(⟨762123382028,762123401357⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70727296,70727360⟩ : DyadicInterval 40),(⟨-70731904,-70731840⟩ : DyadicInterval 40),(⟨762123381305,762123400635⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4608,-3136⟩ : DyadicInterval 40),(⟨762123385184,762123405184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184570997029,184696465417⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170620506048,170620506112⟩ : DyadicInterval 40),(⟨-202048683072,-202048683008⟩ : DyadicInterval 40),(⟨746558164932,746558184262⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170727934656,170727934720⟩ : DyadicInterval 40),(⟨-202199472512,-202199472448⟩ : DyadicInterval 40),(⟨746536894387,746536913717⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31471537856,-31428176960⟩ : DyadicInterval 40),(⟨777837472096,777859171808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170679795776,170777358080⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-202268856320,-202131899200⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2893_ok : ecellOkT e2893 = true := by decide +kernel
theorem e2893_pos {a z : ℝ} (ha1 : ((1375677/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((688263/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2893 e2893_ok ha1 ha2 hz1 hz2 hz

-- box ['343707/2048000', '1375677/8192000', '1599/1600', '1999/2000']  interval_lower 314531623/1099511627776
noncomputable def e2894 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284037918326,0,true,170582224896,170582224960⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914985337226,0,false,-201994959232,-201994959168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284151869178,0,true,170679795776,170679795840⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914871386374,0,false,-202131899264,-202131899200⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283922589394,0,true,170483465152,170483465216⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915100666158,0,false,-201856380544,-201856380480⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1284059549058,0,true,170600746944,170600747008⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨914963706494,0,false,-202020952576,-202020952512⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558719807,0,true,47091008,47091072⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464535745,0,false,-47093056,-47092992⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570531424,0,true,58902016,58902080⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452724128,0,false,-58905280,-58905216⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624620,0,false,-3200,-3136⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625760,0,false,-2048,-1984⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283980249416,0,true,170532842304,170532842368⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915043006136,0,false,-201925662336,-201925662272⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1284105717833,0,true,170640279552,170640279616⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨914917537719,0,false,-202076435008,-202076434944⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068520615745,0,false,-31436155456,-31436155392⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068562730548,0,false,-31392819968,-31392819904⟩
    { al := (343707/2048000), au := (1375677/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨184526290550,184640241402⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170582224896,170582224960⟩ : DyadicInterval 40),(⟨-201994959232,-201994959168⟩ : DyadicInterval 40),(⟨746565740411,746565759740⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170679795776,170679795840⟩ : DyadicInterval 40),(⟨-202131899264,-202131899200⟩ : DyadicInterval 40),(⟨746546427837,746546447166⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170483465152,170483465216⟩ : DyadicInterval 40),(⟨-201856380544,-201856380480⟩ : DyadicInterval 40),(⟨746585274240,746585293569⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170600746944,170600747008⟩ : DyadicInterval 40),(⟨-202020952576,-202020952512⟩ : DyadicInterval 40),(⟨746562075346,746562094675⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨47092031,58903648⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨47091008,47091072⟩ : DyadicInterval 40),(⟨-47093056,-47092992⟩ : DyadicInterval 40),(⟨762123382559,762123401888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58902016,58902080⟩ : DyadicInterval 40),(⟨-58905280,-58905216⟩ : DyadicInterval 40),(⟨762123382028,762123401357⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3200,-1984⟩ : DyadicInterval 40),(⟨762123384608,762123404480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184468621640,184594090057⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170532842304,170532842368⟩ : DyadicInterval 40),(⟨-201925662336,-201925662272⟩ : DyadicInterval 40),(⟨746575509635,746575528965⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170640279552,170640279616⟩ : DyadicInterval 40),(⟨-202076435008,-202076434944⟩ : DyadicInterval 40),(⟨746554251106,746554270435⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31436155456,-31392819904⟩ : DyadicInterval 40),(⟨777819793568,777841480608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170582224896,170679795840⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-202131899264,-201994959168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2894_ok : ecellOkT e2894 = true := by decide +kernel
theorem e2894_pos {a z : ℝ} (ha1 : ((343707/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1375677/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2894 e2894_ok ha1 ha2 hz1 hz2 hz

-- box ['1375677/8192000', '688263/4096000', '1599/1600', '1999/2000']  interval_lower 78988459/274877906944
noncomputable def e2895 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284151869177,0,true,170679795776,170679795840⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914871386375,0,false,-202131899264,-202131899200⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284265820029,0,true,170777358016,170777358080⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914757435523,0,false,-202268856320,-202268856256⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1284036469026,0,true,170580983872,170580983936⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨914986786526,0,false,-201993217664,-201993217600⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1284173442934,0,true,170698267392,170698267456⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨914849812618,0,false,-202157827328,-202157827264⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558750107,0,true,47121280,47121344⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464505445,0,false,-47123392,-47123328⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570569302,0,true,58939904,58939968⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452686250,0,false,-58943168,-58943104⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624616,0,false,-3200,-3136⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625757,0,false,-2048,-1984⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1284094164658,0,true,170630387136,170630387200⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨914929090894,0,false,-202062550912,-202062550848⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1284219640197,0,true,170737820864,170737820928⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨914803615355,0,false,-202213350912,-202213350848⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068482351695,0,false,-31475529984,-31475529920⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068524494889,0,false,-31432163776,-31432163712⟩
    { al := (1375677/8192000), au := (688263/4096000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨184640241401,184754192253⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170679795776,170679795840⟩ : DyadicInterval 40),(⟨-202131899264,-202131899200⟩ : DyadicInterval 40),(⟨746546427837,746546447166⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170777358016,170777358080⟩ : DyadicInterval 40),(⟨-202268856320,-202268856256⟩ : DyadicInterval 40),(⟨746527103087,746527122417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170580983872,170580983936⟩ : DyadicInterval 40),(⟨-201993217664,-201993217600⟩ : DyadicInterval 40),(⟨746565985967,746566005296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170698267392,170698267456⟩ : DyadicInterval 40),(⟨-202157827328,-202157827264⟩ : DyadicInterval 40),(⟨746542770112,746542789441⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨47122331,58941526⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨47121280,47121344⟩ : DyadicInterval 40),(⟨-47123392,-47123328⟩ : DyadicInterval 40),(⟨762123382588,762123401917⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58939904,58939968⟩ : DyadicInterval 40),(⟨-58943168,-58943104⟩ : DyadicInterval 40),(⟨762123382024,762123401353⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3200,-1984⟩ : DyadicInterval 40),(⟨762123384608,762123404480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184582536882,184708012421⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170630387136,170630387200⟩ : DyadicInterval 40),(⟨-202062550912,-202062550848⟩ : DyadicInterval 40),(⟨746556209198,746556228528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170737820864,170737820928⟩ : DyadicInterval 40),(⟨-202213350912,-202213350848⟩ : DyadicInterval 40),(⟨746534936133,746534955463⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31475529984,-31432163712⟩ : DyadicInterval 40),(⟨777839465472,777861167872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170679795776,170777358080⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-202268856320,-202131899200⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2895_ok : ecellOkT e2895 = true := by decide +kernel
theorem e2895_pos {a z : ℝ} (ha1 : ((1375677/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((688263/4096000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2895 e2895_ok ha1 ha2 hz1 hz2 hz

-- box ['171429/1024000', '1372281/8192000', '1999/2000', '7997/8000']  interval_lower 77168619/274877906944
noncomputable def e2896 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283582114922,0,true,170191854720,170191854784⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915441140630,0,false,-201447369728,-201447369664⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283696065774,0,true,170289460224,170289460288⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915327189778,0,false,-201584241536,-201584241472⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283490079678,0,true,170113014848,170113014912⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915533175874,0,false,-201336834240,-201336834176⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283626996610,0,true,170230299520,170230299584⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915396258942,0,false,-201501277248,-201501277184⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546855947,0,true,35227584,35227648⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476399605,0,false,-35228736,-35228672⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558629685,0,true,47000896,47000960⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464625867,0,false,-47002944,-47002880⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625766,0,false,-2048,-1984⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626648,0,false,-1152,-1088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283536092739,0,true,170152431552,170152431616⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915487162813,0,false,-201392095168,-201392095104⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283661539804,0,true,170259887616,170259887680⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915361715748,0,false,-201542768960,-201542768896⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068669580049,0,false,-31282881280,-31282881216⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068711586331,0,false,-31239663552,-31239663488⟩
    { al := (171429/1024000), au := (1372281/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨184070487146,184184437998⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170191854720,170191854784⟩ : DyadicInterval 40),(⟨-201447369728,-201447369664⟩ : DyadicInterval 40),(⟨746642869274,746642888603⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170289460224,170289460288⟩ : DyadicInterval 40),(⟨-201584241536,-201584241472⟩ : DyadicInterval 40),(⟨746623605303,746623624633⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170113014848,170113014912⟩ : DyadicInterval 40),(⟨-201336834240,-201336834176⟩ : DyadicInterval 40),(⟨746658419448,746658438777⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170230299520,170230299584⟩ : DyadicInterval 40),(⟨-201501277248,-201501277184⟩ : DyadicInterval 40),(⟨746635283253,746635302582⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨35228171,47001909⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35227584,35227648⟩ : DyadicInterval 40),(⟨-35228736,-35228672⟩ : DyadicInterval 40),(⟨762123382999,762123402328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨47000896,47000960⟩ : DyadicInterval 40),(⟨-47002944,-47002880⟩ : DyadicInterval 40),(⟨762123382566,762123401895⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2048,-1088⟩ : DyadicInterval 40),(⟨762123384160,762123403904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184024464963,184149912028⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170152431552,170152431616⟩ : DyadicInterval 40),(⟨-201392095168,-201392095104⟩ : DyadicInterval 40),(⟨746650646162,746650665491⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170259887616,170259887680⟩ : DyadicInterval 40),(⟨-201542768960,-201542768896⟩ : DyadicInterval 40),(⟨746629443400,746629462730⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31282881280,-31239663488⟩ : DyadicInterval 40),(⟨777743215360,777764843520⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170191854720,170289460288⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201584241536,-201447369664⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2896_ok : ecellOkT e2896 = true := by decide +kernel
theorem e2896_pos {a z : ℝ} (ha1 : ((171429/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1372281/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2896 e2896_ok ha1 ha2 hz1 hz2 hz

-- box ['1372281/8192000', '137313/819200', '1999/2000', '7997/8000']  interval_lower 155041651/549755813888
noncomputable def e2897 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283696065773,0,true,170289460224,170289460288⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915327189779,0,false,-201584241536,-201584241472⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283810016625,0,true,170387057088,170387057152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915213238927,0,false,-201721130432,-201721130368⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283603973553,0,true,170210578560,170210578624⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915419281999,0,false,-201473623872,-201473623808⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283740904730,0,true,170327865024,170327865088⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915282350822,0,false,-201638104448,-201638104384⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546878664,0,true,35250304,35250368⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476376888,0,false,-35251456,-35251392⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558659978,0,true,47031168,47031232⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464595574,0,false,-47033216,-47033152⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625764,0,false,-2048,-1984⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626646,0,false,-1152,-1088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283650015095,0,true,170250016192,170250016256⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915373240457,0,false,-201528925824,-201528925760⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283775469285,0,true,170357468864,170357468928⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915247786267,0,false,-201679627008,-201679626944⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068631405657,0,false,-31322158144,-31322158080⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068673440323,0,false,-31278909632,-31278909568⟩
    { al := (1372281/8192000), au := (137313/819200), zl := (1999/2000), zu := (7997/8000),
      A := ⟨184184437997,184298388849⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170289460224,170289460288⟩ : DyadicInterval 40),(⟨-201584241536,-201584241472⟩ : DyadicInterval 40),(⟨746623605303,746623624633⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170387057088,170387057152⟩ : DyadicInterval 40),(⟨-201721130432,-201721130368⟩ : DyadicInterval 40),(⟨746604329187,746604348517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170210578560,170210578624⟩ : DyadicInterval 40),(⟨-201473623872,-201473623808⟩ : DyadicInterval 40),(⟨746639174920,746639194249⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170327865024,170327865088⟩ : DyadicInterval 40),(⟨-201638104448,-201638104384⟩ : DyadicInterval 40),(⟨746616021723,746616041052⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨35250888,47032202⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35250304,35250368⟩ : DyadicInterval 40),(⟨-35251456,-35251392⟩ : DyadicInterval 40),(⟨762123382997,762123402326⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨47031168,47031232⟩ : DyadicInterval 40),(⟨-47033216,-47033152⟩ : DyadicInterval 40),(⟨762123382564,762123401893⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2048,-1088⟩ : DyadicInterval 40),(⟨762123384160,762123403904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184138387319,184263841509⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170250016192,170250016256⟩ : DyadicInterval 40),(⟨-201528925824,-201528925760⟩ : DyadicInterval 40),(⟨746631391872,746631411202⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170357468864,170357468928⟩ : DyadicInterval 40),(⟨-201679627008,-201679626944⟩ : DyadicInterval 40),(⟨746610174541,746610193870⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31322158144,-31278909568⟩ : DyadicInterval 40),(⟨777762838400,777784481952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170289460224,170387057152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201721130432,-201584241472⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2897_ok : ecellOkT e2897 = true := by decide +kernel
theorem e2897_pos {a z : ℝ} (ha1 : ((1372281/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((137313/819200 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2897 e2897_ok ha1 ha2 hz1 hz2 hz

-- box ['171429/1024000', '1372281/8192000', '7997/8000', '3999/4000']  interval_lower 154236609/549755813888
noncomputable def e2898 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283582114922,0,true,170191854720,170191854784⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915441140630,0,false,-201447369728,-201447369664⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283696065774,0,true,170289460224,170289460288⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915327189778,0,false,-201584241536,-201584241472⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283513088489,0,true,170132725312,170132725376⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915510167063,0,false,-201364467072,-201364467008⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283650019665,0,true,170250020096,170250020160⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915373235887,0,false,-201528931328,-201528931264⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535113198,0,true,23485120,23485184⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488142354,0,false,-23485696,-23485632⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546879364,0,true,35251008,35251072⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476376188,0,false,-35252160,-35252096⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626645,0,false,-1152,-1088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627275,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283547597038,0,true,170162286400,170162286464⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915475658514,0,false,-201405912064,-201405912000⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283673051257,0,true,170269747648,170269747712⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915350204295,0,false,-201556596352,-201556596288⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068665723974,0,false,-31286848640,-31286848576⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068707735279,0,false,-31243625600,-31243625536⟩
    { al := (171429/1024000), au := (1372281/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨184070487146,184184437998⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170191854720,170191854784⟩ : DyadicInterval 40),(⟨-201447369728,-201447369664⟩ : DyadicInterval 40),(⟨746642869274,746642888603⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170289460224,170289460288⟩ : DyadicInterval 40),(⟨-201584241536,-201584241472⟩ : DyadicInterval 40),(⟨746623605303,746623624633⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170132725312,170132725376⟩ : DyadicInterval 40),(⟨-201364467072,-201364467008⟩ : DyadicInterval 40),(⟨746654532668,746654551998⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170250020096,170250020160⟩ : DyadicInterval 40),(⟨-201528931328,-201528931264⟩ : DyadicInterval 40),(⟨746631391112,746631410441⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23485422,35251588⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23485120,23485184⟩ : DyadicInterval 40),(⟨-23485696,-23485632⟩ : DyadicInterval 40),(⟨762123383338,762123402667⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35251008,35251072⟩ : DyadicInterval 40),(⟨-35252160,-35252096⟩ : DyadicInterval 40),(⟨762123382997,762123402326⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1152,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184035969262,184161423481⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170162286400,170162286464⟩ : DyadicInterval 40),(⟨-201405912064,-201405912000⟩ : DyadicInterval 40),(⟨746648702347,746648721677⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170269747648,170269747712⟩ : DyadicInterval 40),(⟨-201556596352,-201556596288⟩ : DyadicInterval 40),(⟨746627497018,746627516347⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31286848640,-31243625536⟩ : DyadicInterval 40),(⟨777745196384,777766827200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170191854720,170289460288⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201584241536,-201447369664⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2898_ok : ecellOkT e2898 = true := by decide +kernel
theorem e2898_pos {a z : ℝ} (ha1 : ((171429/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1372281/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2898 e2898_ok ha1 ha2 hz1 hz2 hz

-- box ['1372281/8192000', '137313/819200', '7997/8000', '3999/4000']  interval_lower 154940805/549755813888
noncomputable def e2899 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283696065773,0,true,170289460224,170289460288⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915327189779,0,false,-201584241536,-201584241472⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283810016625,0,true,170387057088,170387057152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915213238927,0,false,-201721130432,-201721130368⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283626996608,0,true,170230299520,170230299584⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915396258944,0,false,-201501277248,-201501277184⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283763942028,0,true,170347596096,170347596160⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915259313524,0,false,-201665779072,-201665779008⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535128343,0,true,23500288,23500352⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488127209,0,false,-23500864,-23500800⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546902083,0,true,35273728,35273792⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476353469,0,false,-35274880,-35274816⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626644,0,false,-1152,-1088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627274,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283661526520,0,true,170259876288,170259876352⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915361729032,0,false,-201542753024,-201542752960⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283786987863,0,true,170367334080,170367334144⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915236267689,0,false,-201693464640,-201693464576⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068627544809,0,false,-31326130560,-31326130496⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068669584500,0,false,-31282876736,-31282876672⟩
    { al := (1372281/8192000), au := (137313/819200), zl := (7997/8000), zu := (3999/4000),
      A := ⟨184184437997,184298388849⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170289460224,170289460288⟩ : DyadicInterval 40),(⟨-201584241536,-201584241472⟩ : DyadicInterval 40),(⟨746623605303,746623624633⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170387057088,170387057152⟩ : DyadicInterval 40),(⟨-201721130432,-201721130368⟩ : DyadicInterval 40),(⟨746604329187,746604348517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170230299520,170230299584⟩ : DyadicInterval 40),(⟨-201501277248,-201501277184⟩ : DyadicInterval 40),(⟨746635283253,746635302583⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170347596096,170347596160⟩ : DyadicInterval 40),(⟨-201665779072,-201665779008⟩ : DyadicInterval 40),(⟨746612124687,746612144017⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23500567,35274307⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23500288,23500352⟩ : DyadicInterval 40),(⟨-23500864,-23500800⟩ : DyadicInterval 40),(⟨762123383337,762123402666⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35273728,35273792⟩ : DyadicInterval 40),(⟨-35274880,-35274816⟩ : DyadicInterval 40),(⟨762123382996,762123402325⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1152,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184149898744,184275360087⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170259876288,170259876352⟩ : DyadicInterval 40),(⟨-201542753024,-201542752960⟩ : DyadicInterval 40),(⟨746629445625,746629464955⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170367334080,170367334144⟩ : DyadicInterval 40),(⟨-201693464640,-201693464576⟩ : DyadicInterval 40),(⟨746608225733,746608245063⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31326130560,-31282876672⟩ : DyadicInterval 40),(⟨777764821952,777786468160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170289460224,170387057152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201721130432,-201584241472⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2899_ok : ecellOkT e2899 = true := by decide +kernel
theorem e2899_pos {a z : ℝ} (ha1 : ((1372281/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((137313/819200 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2899 e2899_ok ha1 ha2 hz1 hz2 hz

-- box ['137313/819200', '1373979/8192000', '1999/2000', '7997/8000']  interval_lower 38936923/137438953472
noncomputable def e2900 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283810016624,0,true,170387057088,170387057152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915213238928,0,false,-201721130432,-201721130368⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283923967476,0,true,170484645312,170484645376⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915099288076,0,false,-201858036288,-201858036224⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283717867429,0,true,170308133632,170308133696⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915305388123,0,false,-201610430528,-201610430464⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283854812849,0,true,170425421888,170425421952⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915168442703,0,false,-201774948672,-201774948608⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546901383,0,true,35273024,35273088⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476354169,0,false,-35274176,-35274112⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558690272,0,true,47061440,47061504⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464565280,0,false,-47063552,-47063488⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625761,0,false,-2048,-1984⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626645,0,false,-1152,-1088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283763937451,0,true,170347592192,170347592256⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915259318101,0,false,-201665773568,-201665773504⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283889398772,0,true,170455041408,170455041472⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915133856780,0,false,-201816502016,-201816501952⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068593207653,0,false,-31361460608,-31361460544⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068635270708,0,false,-31318181376,-31318181312⟩
    { al := (137313/819200), au := (1373979/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨184298388848,184412339700⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170387057088,170387057152⟩ : DyadicInterval 40),(⟨-201721130432,-201721130368⟩ : DyadicInterval 40),(⟨746604329187,746604348517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170484645312,170484645376⟩ : DyadicInterval 40),(⟨-201858036288,-201858036224⟩ : DyadicInterval 40),(⟨746585040873,746585060202⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170308133632,170308133696⟩ : DyadicInterval 40),(⟨-201610430528,-201610430464⟩ : DyadicInterval 40),(⟨746619918246,746619937575⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170425421888,170425421952⟩ : DyadicInterval 40),(⟨-201774948672,-201774948608⟩ : DyadicInterval 40),(⟨746596748040,746596767369⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨35273607,47062496⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35273024,35273088⟩ : DyadicInterval 40),(⟨-35274176,-35274112⟩ : DyadicInterval 40),(⟨762123382996,762123402325⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨47061440,47061504⟩ : DyadicInterval 40),(⟨-47063552,-47063488⟩ : DyadicInterval 40),(⟨762123382593,762123401922⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2048,-1088⟩ : DyadicInterval 40),(⟨762123384160,762123403904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184252309675,184377770996⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170347592192,170347592256⟩ : DyadicInterval 40),(⟨-201665773568,-201665773504⟩ : DyadicInterval 40),(⟨746612125450,746612144779⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170455041408,170455041472⟩ : DyadicInterval 40),(⟨-201816502016,-201816501952⟩ : DyadicInterval 40),(⟨746590893528,746590912857⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31361460608,-31318181312⟩ : DyadicInterval 40),(⟨777782474272,777804133184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170387057088,170484645376⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201858036288,-201721130368⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2900_ok : ecellOkT e2900 = true := by decide +kernel
theorem e2900_pos {a z : ℝ} (ha1 : ((137313/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1373979/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2900 e2900_ok ha1 ha2 hz1 hz2 hz

-- box ['1373979/8192000', '343707/2048000', '1999/2000', '7997/8000']  interval_lower 312910323/1099511627776
noncomputable def e2901 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283923967475,0,true,170484645312,170484645376⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915099288077,0,false,-201858036288,-201858036224⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284037918327,0,true,170582224896,170582224960⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914985337225,0,false,-201994959232,-201994959168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283831761305,0,true,170405680064,170405680128⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915191494247,0,false,-201747254208,-201747254144⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283968720969,0,true,170522970112,170522970176⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915054534583,0,false,-201911809920,-201911809856⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546924104,0,true,35295744,35295808⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476331448,0,false,-35296896,-35296832⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558720570,0,true,47091776,47091840⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464534982,0,false,-47093824,-47093760⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625758,0,false,-2048,-1984⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626643,0,false,-1152,-1088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283877859816,0,true,170445159488,170445159552⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915145395736,0,false,-201802638336,-201802638272⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1284003328260,0,true,170552605248,170552605312⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915019927292,0,false,-201953394176,-201953394112⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068554986038,0,false,-31400788864,-31400788800⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068597077482,0,false,-31357478848,-31357478784⟩
    { al := (1373979/8192000), au := (343707/2048000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨184412339699,184526290551⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170484645312,170484645376⟩ : DyadicInterval 40),(⟨-201858036288,-201858036224⟩ : DyadicInterval 40),(⟨746585040873,746585060202⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170582224896,170582224960⟩ : DyadicInterval 40),(⟨-201994959232,-201994959168⟩ : DyadicInterval 40),(⟨746565740411,746565759740⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170405680064,170405680128⟩ : DyadicInterval 40),(⟨-201747254208,-201747254144⟩ : DyadicInterval 40),(⟨746600649425,746600668754⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170522970112,170522970176⟩ : DyadicInterval 40),(⟨-201911809920,-201911809856⟩ : DyadicInterval 40),(⟨746577462201,746577481531⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨35296328,47092794⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35295744,35295808⟩ : DyadicInterval 40),(⟨-35296896,-35296832⟩ : DyadicInterval 40),(⟨762123382994,762123402323⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨47091776,47091840⟩ : DyadicInterval 40),(⟨-47093824,-47093760⟩ : DyadicInterval 40),(⟨762123382558,762123401888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2048,-1088⟩ : DyadicInterval 40),(⟨762123384160,762123403904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184366232040,184491700484⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170445159488,170445159552⟩ : DyadicInterval 40),(⟨-201802638336,-201802638272⟩ : DyadicInterval 40),(⟨746592846904,746592866234⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170552605248,170552605312⟩ : DyadicInterval 40),(⟨-201953394176,-201953394112⟩ : DyadicInterval 40),(⟨746571600440,746571619770⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31400788864,-31357478784⟩ : DyadicInterval 40),(⟨777802123008,777823797312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170484645312,170582224960⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201994959232,-201858036224⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2901_ok : ecellOkT e2901 = true := by decide +kernel
theorem e2901_pos {a z : ℝ} (ha1 : ((1373979/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((343707/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2901 e2901_ok ha1 ha2 hz1 hz2 hz

-- box ['137313/819200', '1373979/8192000', '7997/8000', '3999/4000']  interval_lower 155646533/549755813888
noncomputable def e2902 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283810016624,0,true,170387057088,170387057152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915213238928,0,false,-201721130432,-201721130368⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283923967476,0,true,170484645312,170484645376⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915099288076,0,false,-201858036288,-201858036224⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283740904728,0,true,170327865024,170327865088⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915282350824,0,false,-201638104448,-201638104384⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283877864392,0,true,170445163392,170445163456⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915145391160,0,false,-201802643840,-201802643776⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535143490,0,true,23515456,23515520⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488112062,0,false,-23515968,-23515904⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546924805,0,true,35296448,35296512⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476330747,0,false,-35297600,-35297536⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626642,0,false,-1152,-1088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627274,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283775455998,0,true,170357457472,170357457536⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915247799554,0,false,-201679611008,-201679610944⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283900924471,0,true,170464911872,170464911936⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915122331081,0,false,-201830350016,-201830349952⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068589342029,0,false,-31365438080,-31365438016⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068631410111,0,false,-31322153536,-31322153472⟩
    { al := (137313/819200), au := (1373979/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨184298388848,184412339700⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170387057088,170387057152⟩ : DyadicInterval 40),(⟨-201721130432,-201721130368⟩ : DyadicInterval 40),(⟨746604329187,746604348517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170484645312,170484645376⟩ : DyadicInterval 40),(⟨-201858036288,-201858036224⟩ : DyadicInterval 40),(⟨746585040873,746585060202⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170327865024,170327865088⟩ : DyadicInterval 40),(⟨-201638104448,-201638104384⟩ : DyadicInterval 40),(⟨746616021723,746616041053⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170445163392,170445163456⟩ : DyadicInterval 40),(⟨-201802643840,-201802643776⟩ : DyadicInterval 40),(⟨746592846141,746592865470⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23515714,35297029⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23515456,23515520⟩ : DyadicInterval 40),(⟨-23515968,-23515904⟩ : DyadicInterval 40),(⟨762123383305,762123402634⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35296448,35296512⟩ : DyadicInterval 40),(⟨-35297600,-35297536⟩ : DyadicInterval 40),(⟨762123382994,762123402323⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1152,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184263828222,184389296695⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170357457472,170357457536⟩ : DyadicInterval 40),(⟨-201679611008,-201679610944⟩ : DyadicInterval 40),(⟨746610176780,746610196109⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170464911872,170464911936⟩ : DyadicInterval 40),(⟨-201830350016,-201830349952⟩ : DyadicInterval 40),(⟨746588942310,746588961639⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31365438080,-31322153472⟩ : DyadicInterval 40),(⟨777784460352,777806121920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170387057088,170484645376⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201858036288,-201721130368⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2902_ok : ecellOkT e2902 = true := by decide +kernel
theorem e2902_pos {a z : ℝ} (ha1 : ((137313/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1373979/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2902 e2902_ok ha1 ha2 hz1 hz2 hz

-- box ['1373979/8192000', '343707/2048000', '7997/8000', '3999/4000']  interval_lower 156353849/549755813888
noncomputable def e2903 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283923967475,0,true,170484645312,170484645376⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915099288077,0,false,-201858036288,-201858036224⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284037918327,0,true,170582224896,170582224960⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914985337225,0,false,-201994959232,-201994959168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283854812847,0,true,170425421888,170425421952⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915168442705,0,false,-201774948672,-201774948608⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283991786755,0,true,170542722048,170542722112⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915031468797,0,false,-201939525632,-201939525568⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535158637,0,true,23530560,23530624⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488096915,0,false,-23531136,-23531072⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546947528,0,true,35319168,35319232⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476308024,0,false,-35320320,-35320256⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626641,0,false,-1152,-1088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627273,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283889385483,0,true,170455030016,170455030080⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915133870069,0,false,-201816486080,-201816486016⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1284014861081,0,true,170562480960,170562481024⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915008394471,0,false,-201967252352,-201967252288⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068551115635,0,false,-31404771392,-31404771328⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068593212111,0,false,-31361456064,-31361456000⟩
    { al := (1373979/8192000), au := (343707/2048000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨184412339699,184526290551⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170484645312,170484645376⟩ : DyadicInterval 40),(⟨-201858036288,-201858036224⟩ : DyadicInterval 40),(⟨746585040873,746585060202⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170582224896,170582224960⟩ : DyadicInterval 40),(⟨-201994959232,-201994959168⟩ : DyadicInterval 40),(⟨746565740411,746565759740⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170425421888,170425421952⟩ : DyadicInterval 40),(⟨-201774948672,-201774948608⟩ : DyadicInterval 40),(⟨746596748040,746596767370⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170542722048,170542722112⟩ : DyadicInterval 40),(⟨-201939525632,-201939525568⟩ : DyadicInterval 40),(⟨746573555432,746573574762⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23530861,35319752⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23530560,23530624⟩ : DyadicInterval 40),(⟨-23531136,-23531072⟩ : DyadicInterval 40),(⟨762123383336,762123402665⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35319168,35319232⟩ : DyadicInterval 40),(⟨-35320320,-35320256⟩ : DyadicInterval 40),(⟨762123382993,762123402322⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1152,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184377757707,184503233305⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170455030016,170455030080⟩ : DyadicInterval 40),(⟨-201816486080,-201816486016⟩ : DyadicInterval 40),(⟨746590895796,746590915126⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170562480960,170562481024⟩ : DyadicInterval 40),(⟨-201967252352,-201967252288⟩ : DyadicInterval 40),(⟨746569646728,746569666058⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31404771392,-31361456000⟩ : DyadicInterval 40),(⟨777804111616,777825788576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170484645312,170582224960⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201994959232,-201858036224⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2903_ok : ecellOkT e2903 = true := by decide +kernel
theorem e2903_pos {a z : ℝ} (ha1 : ((1373979/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((343707/2048000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2903 e2903_ok ha1 ha2 hz1 hz2 hz

-- box ['171429/1024000', '1372281/8192000', '3999/4000', '7999/8000']  interval_lower 154135991/549755813888
noncomputable def e2904 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283582114922,0,true,170191854720,170191854784⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915441140630,0,false,-201447369728,-201447369664⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283696065774,0,true,170289460224,170289460288⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915327189778,0,false,-201584241536,-201584241472⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283536097300,0,true,170152435456,170152435520⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915487158252,0,false,-201392100608,-201392100544⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283673042720,0,true,170269740352,170269740416⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915350212832,0,false,-201556586112,-201556586048⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523370389,0,true,11742528,11742592⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499885163,0,false,-11742720,-11742656⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535128981,0,true,23500928,23500992⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488126571,0,false,-23501504,-23501440⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627273,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627651,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283559101371,0,true,170172141184,170172141248⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915464154181,0,false,-201419729152,-201419729088⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283684562740,0,true,170279607616,170279607680⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915338692812,0,false,-201570423936,-201570423872⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068661867649,0,false,-31290816320,-31290816256⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068703883974,0,false,-31247587904,-31247587840⟩
    { al := (171429/1024000), au := (1372281/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨184070487146,184184437998⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170191854720,170191854784⟩ : DyadicInterval 40),(⟨-201447369728,-201447369664⟩ : DyadicInterval 40),(⟨746642869274,746642888603⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170289460224,170289460288⟩ : DyadicInterval 40),(⟨-201584241536,-201584241472⟩ : DyadicInterval 40),(⟨746623605303,746623624633⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170152435456,170152435520⟩ : DyadicInterval 40),(⟨-201392100608,-201392100544⟩ : DyadicInterval 40),(⟨746650645377,746650664707⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170269740352,170269740416⟩ : DyadicInterval 40),(⟨-201556586112,-201556586048⟩ : DyadicInterval 40),(⟨746627498458,746627517788⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11742613,23501205⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11742528,11742592⟩ : DyadicInterval 40),(⟨-11742720,-11742656⟩ : DyadicInterval 40),(⟨762123383522,762123402851⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23500928,23500992⟩ : DyadicInterval 40),(⟨-23501504,-23501440⟩ : DyadicInterval 40),(⟨762123383337,762123402666⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184047473595,184172934964⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170172141184,170172141248⟩ : DyadicInterval 40),(⟨-201419729152,-201419729088⟩ : DyadicInterval 40),(⟨746646758397,746646777726⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170279607616,170279607680⟩ : DyadicInterval 40),(⟨-201570423936,-201570423872⟩ : DyadicInterval 40),(⟨746625550500,746625569829⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31290816320,-31247587840⟩ : DyadicInterval 40),(⟨777747177536,777768811040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170191854720,170289460288⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201584241536,-201447369664⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2904_ok : ecellOkT e2904 = true := by decide +kernel
theorem e2904_pos {a z : ℝ} (ha1 : ((171429/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1372281/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2904 e2904_ok ha1 ha2 hz1 hz2 hz

-- box ['1372281/8192000', '137313/819200', '3999/4000', '7999/8000']  interval_lower 77419917/274877906944
noncomputable def e2905 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283696065773,0,true,170289460224,170289460288⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915327189779,0,false,-201584241536,-201584241472⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283810016625,0,true,170387057088,170387057152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915213238927,0,false,-201721130432,-201721130368⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283650019663,0,true,170250020096,170250020160⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915373235889,0,false,-201528931328,-201528931264⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283786979327,0,true,170367326784,170367326848⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915236276225,0,false,-201693454400,-201693454336⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523377962,0,true,11750080,11750144⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499877590,0,false,-11750272,-11750208⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535144128,0,true,23516096,23516160⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488111424,0,false,-23516608,-23516544⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627273,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627651,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283673037972,0,true,170269736256,170269736320⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915350217580,0,false,-201556580416,-201556580352⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283798506467,0,true,170377199232,170377199296⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915224749085,0,false,-201707302528,-201707302464⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068623683710,0,false,-31330103232,-31330103168⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068665728426,0,false,-31286844096,-31286844032⟩
    { al := (1372281/8192000), au := (137313/819200), zl := (3999/4000), zu := (7999/8000),
      A := ⟨184184437997,184298388849⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170289460224,170289460288⟩ : DyadicInterval 40),(⟨-201584241536,-201584241472⟩ : DyadicInterval 40),(⟨746623605303,746623624633⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170387057088,170387057152⟩ : DyadicInterval 40),(⟨-201721130432,-201721130368⟩ : DyadicInterval 40),(⟨746604329187,746604348517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170250020096,170250020160⟩ : DyadicInterval 40),(⟨-201528931328,-201528931264⟩ : DyadicInterval 40),(⟨746631391112,746631410442⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170367326784,170367326848⟩ : DyadicInterval 40),(⟨-201693454400,-201693454336⟩ : DyadicInterval 40),(⟨746608227176,746608246505⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11750186,23516352⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11750080,11750144⟩ : DyadicInterval 40),(⟨-11750272,-11750208⟩ : DyadicInterval 40),(⟨762123383522,762123402851⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23516096,23516160⟩ : DyadicInterval 40),(⟨-23516608,-23516544⟩ : DyadicInterval 40),(⟨762123383305,762123402634⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184161410196,184286878691⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170269736256,170269736320⟩ : DyadicInterval 40),(⟨-201556580416,-201556580352⟩ : DyadicInterval 40),(⟨746627499281,746627518610⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170377199232,170377199296⟩ : DyadicInterval 40),(⟨-201707302528,-201707302464⟩ : DyadicInterval 40),(⟨746606276818,746606296147⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31330103232,-31286844032⟩ : DyadicInterval 40),(⟨777766805632,777788454496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170289460224,170387057152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201721130432,-201584241472⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2905_ok : ecellOkT e2905 = true := by decide +kernel
theorem e2905_pos {a z : ℝ} (ha1 : ((1372281/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((137313/819200 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2905 e2905_ok ha1 ha2 hz1 hz2 hz

-- box ['171429/1024000', '1372281/8192000', '7999/8000', '1']  interval_lower 154035361/549755813888
noncomputable def e2906 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283582114922,0,true,170191854720,170191854784⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915441140630,0,false,-201447369728,-201447369664⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283696065774,0,true,170289460224,170289460288⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915327189778,0,false,-201584241536,-201584241472⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283559106111,0,true,170172145280,170172145344⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915464149441,0,false,-201419734848,-201419734784⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523378538,0,true,11750656,11750720⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499877014,0,false,-11750848,-11750784⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627650,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1283570605733,0,true,170181995904,170181995968⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨915452649819,0,false,-201433546496,-201433546432⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1283696074253,0,true,170289467520,170289467584⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨915327181299,0,false,-201584251776,-201584251712⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1068658011072,0,false,-31294784256,-31294784192⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1068700032418,0,false,-31251550528,-31251550464⟩
    { al := (171429/1024000), au := (1372281/8192000), zl := (7999/8000), zu := 1,
      A := ⟨184070487146,184184437998⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170191854720,170191854784⟩ : DyadicInterval 40),(⟨-201447369728,-201447369664⟩ : DyadicInterval 40),(⟨746642869274,746642888603⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170289460224,170289460288⟩ : DyadicInterval 40),(⟨-201584241536,-201584241472⟩ : DyadicInterval 40),(⟨746623605303,746623624633⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170172145280,170172145344⟩ : DyadicInterval 40),(⟨-201419734848,-201419734784⟩ : DyadicInterval 40),(⟨746646757576,746646776905⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170289460224,170289460288⟩ : DyadicInterval 40),(⟨-201584241536,-201584241472⟩ : DyadicInterval 40),(⟨746623605303,746623624633⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11750762⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11750656,11750720⟩ : DyadicInterval 40),(⟨-11750848,-11750784⟩ : DyadicInterval 40),(⟨762123383522,762123402851⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨184058977957,184184446477⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170181995904,170181995968⟩ : DyadicInterval 40),(⟨-201433546496,-201433546432⟩ : DyadicInterval 40),(⟨746644814337,746644833666⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170289467520,170289467584⟩ : DyadicInterval 40),(⟨-201584251776,-201584251712⟩ : DyadicInterval 40),(⟨746623603872,746623623202⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31294784256,-31251550464⟩ : DyadicInterval 40),(⟨777749158848,777770795008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨170191854720,170289460288⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201584241536,-201447369664⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2906_ok : ecellOkT e2906 = true := by decide +kernel
theorem e2906_pos {a z : ℝ} (ha1 : ((171429/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1372281/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2906 e2906_ok ha1 ha2 hz1 hz2 hz

-- box ['1372281/8192000', '137313/819200', '7999/8000', '1']  interval_lower 309477951/1099511627776
noncomputable def e2907 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283696065773,0,true,170289460224,170289460288⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915327189779,0,false,-201584241536,-201584241472⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283810016625,0,true,170387057088,170387057152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915213238927,0,false,-201721130432,-201721130368⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283673042718,0,true,170269740352,170269740416⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915350212834,0,false,-201556586112,-201556586048⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523386111,0,true,11758272,11758336⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499869441,0,false,-11758400,-11758336⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627650,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1283684549455,0,true,170279596224,170279596288⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨915338706097,0,false,-201570408000,-201570407936⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1283810025099,0,true,170387064384,170387064448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨915213230453,0,false,-201721140608,-201721140544⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1068619822361,0,false,-31334076224,-31334076160⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1068661872101,0,false,-31290811712,-31290811648⟩
    { al := (1372281/8192000), au := (137313/819200), zl := (7999/8000), zu := 1,
      A := ⟨184184437997,184298388849⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170289460224,170289460288⟩ : DyadicInterval 40),(⟨-201584241536,-201584241472⟩ : DyadicInterval 40),(⟨746623605303,746623624633⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170387057088,170387057152⟩ : DyadicInterval 40),(⟨-201721130432,-201721130368⟩ : DyadicInterval 40),(⟨746604329187,746604348517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170269740352,170269740416⟩ : DyadicInterval 40),(⟨-201556586112,-201556586048⟩ : DyadicInterval 40),(⟨746627498458,746627517788⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170387057088,170387057152⟩ : DyadicInterval 40),(⟨-201721130432,-201721130368⟩ : DyadicInterval 40),(⟨746604329187,746604348517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11758335⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11758272,11758336⟩ : DyadicInterval 40),(⟨-11758400,-11758336⟩ : DyadicInterval 40),(⟨762123383490,762123402819⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨184172921679,184298397323⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170279596224,170279596288⟩ : DyadicInterval 40),(⟨-201570408000,-201570407936⟩ : DyadicInterval 40),(⟨746625552763,746625572093⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170387064384,170387064448⟩ : DyadicInterval 40),(⟨-201721140608,-201721140544⟩ : DyadicInterval 40),(⟨746604327729,746604347059⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31334076224,-31290811648⟩ : DyadicInterval 40),(⟨777768789440,777790440992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨170289460224,170387057152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201721130432,-201584241472⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2907_ok : ecellOkT e2907 = true := by decide +kernel
theorem e2907_pos {a z : ℝ} (ha1 : ((1372281/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((137313/819200 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2907 e2907_ok ha1 ha2 hz1 hz2 hz

-- box ['137313/819200', '1373979/8192000', '3999/4000', '7999/8000']  interval_lower 19443175/68719476736
noncomputable def e2908 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283810016624,0,true,170387057088,170387057152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915213238928,0,false,-201721130432,-201721130368⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283923967476,0,true,170484645312,170484645376⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915099288076,0,false,-201858036288,-201858036224⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283763942026,0,true,170347596096,170347596160⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915259313526,0,false,-201665779072,-201665779008⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1283900915934,0,true,170464904512,170464904576⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915122339618,0,false,-201830339712,-201830339648⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523385535,0,true,11757696,11757760⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499870017,0,false,-11757824,-11757760⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535159276,0,true,23531200,23531264⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488096276,0,false,-23531776,-23531712⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627272,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627651,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283786974575,0,true,170367322688,170367322752⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915236280977,0,false,-201693448704,-201693448640⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1283912450197,0,true,170474782272,170474782336⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨915110805355,0,false,-201844198144,-201844198080⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068585476155,0,false,-31369415872,-31369415808⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068627549264,0,false,-31326125952,-31326125888⟩
    { al := (137313/819200), au := (1373979/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨184298388848,184412339700⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170387057088,170387057152⟩ : DyadicInterval 40),(⟨-201721130432,-201721130368⟩ : DyadicInterval 40),(⟨746604329187,746604348517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170484645312,170484645376⟩ : DyadicInterval 40),(⟨-201858036288,-201858036224⟩ : DyadicInterval 40),(⟨746585040873,746585060202⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170347596096,170347596160⟩ : DyadicInterval 40),(⟨-201665779072,-201665779008⟩ : DyadicInterval 40),(⟨746612124688,746612144017⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170464904512,170464904576⟩ : DyadicInterval 40),(⟨-201830339712,-201830339648⟩ : DyadicInterval 40),(⟨746588943764,746588963093⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11757759,23531500⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11757696,11757760⟩ : DyadicInterval 40),(⟨-11757824,-11757760⟩ : DyadicInterval 40),(⟨762123383490,762123402819⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23531200,23531264⟩ : DyadicInterval 40),(⟨-23531776,-23531712⟩ : DyadicInterval 40),(⟨762123383336,762123402665⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184275346799,184400822421⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170367322688,170367322752⟩ : DyadicInterval 40),(⟨-201693448704,-201693448640⟩ : DyadicInterval 40),(⟨746608228000,746608247329⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170474782272,170474782336⟩ : DyadicInterval 40),(⟨-201844198144,-201844198080⟩ : DyadicInterval 40),(⟨746586990929,746587010259⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31369415872,-31326125888⟩ : DyadicInterval 40),(⟨777786446560,777808110816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170387057088,170484645376⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201858036288,-201721130368⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2908_ok : ecellOkT e2908 = true := by decide +kernel
theorem e2908_pos {a z : ℝ} (ha1 : ((137313/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1373979/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2908 e2908_ok ha1 ha2 hz1 hz2 hz

-- box ['1373979/8192000', '343707/2048000', '3999/4000', '7999/8000']  interval_lower 156252571/549755813888
noncomputable def e2909 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283923967475,0,true,170484645312,170484645376⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915099288077,0,false,-201858036288,-201858036224⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284037918327,0,true,170582224896,170582224960⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914985337225,0,false,-201994959232,-201994959168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283877864390,0,true,170445163392,170445163456⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915145391162,0,false,-201802643840,-201802643776⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1284014852541,0,true,170562473664,170562473728⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨915008403011,0,false,-201967242112,-201967242048⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523393109,0,true,11765248,11765312⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499862443,0,false,-11765440,-11765376⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535174425,0,true,23546368,23546432⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488081127,0,false,-23546944,-23546880⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627271,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627651,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283900911181,0,true,170464900480,170464900544⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915122344371,0,false,-201830334016,-201830333952⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1284026393931,0,true,170572356608,170572356672⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨914996861621,0,false,-201981110784,-201981110720⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068547244981,0,false,-31408754176,-31408754112⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068589346488,0,false,-31365433536,-31365433472⟩
    { al := (1373979/8192000), au := (343707/2048000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨184412339699,184526290551⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170484645312,170484645376⟩ : DyadicInterval 40),(⟨-201858036288,-201858036224⟩ : DyadicInterval 40),(⟨746585040873,746585060202⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170582224896,170582224960⟩ : DyadicInterval 40),(⟨-201994959232,-201994959168⟩ : DyadicInterval 40),(⟨746565740411,746565759740⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170445163392,170445163456⟩ : DyadicInterval 40),(⟨-201802643840,-201802643776⟩ : DyadicInterval 40),(⟨746592846141,746592865470⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170562473664,170562473728⟩ : DyadicInterval 40),(⟨-201967242112,-201967242048⟩ : DyadicInterval 40),(⟨746569648174,746569667504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11765333,23546649⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11765248,11765312⟩ : DyadicInterval 40),(⟨-11765440,-11765376⟩ : DyadicInterval 40),(⟨762123383522,762123402851⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23546368,23546432⟩ : DyadicInterval 40),(⟨-23546944,-23546880⟩ : DyadicInterval 40),(⟨762123383335,762123402664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184389283405,184514766155⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170464900480,170464900544⟩ : DyadicInterval 40),(⟨-201830334016,-201830333952⟩ : DyadicInterval 40),(⟨746588944552,746588963882⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170572356608,170572356672⟩ : DyadicInterval 40),(⟨-201981110784,-201981110720⟩ : DyadicInterval 40),(⟨746567692906,746567712235⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31408754176,-31365433472⟩ : DyadicInterval 40),(⟨777806100352,777827779968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170484645312,170582224960⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201994959232,-201858036224⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2909_ok : ecellOkT e2909 = true := by decide +kernel
theorem e2909_pos {a z : ℝ} (ha1 : ((1373979/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((343707/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2909 e2909_ok ha1 ha2 hz1 hz2 hz

-- box ['137313/819200', '1373979/8192000', '7999/8000', '1']  interval_lower 310888791/1099511627776
noncomputable def e2910 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283810016624,0,true,170387057088,170387057152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915213238928,0,false,-201721130432,-201721130368⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1283923967476,0,true,170484645312,170484645376⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨915099288076,0,false,-201858036288,-201858036224⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283786979325,0,true,170367326784,170367326848⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915236276227,0,false,-201693454400,-201693454336⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523393685,0,true,11765824,11765888⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499861867,0,false,-11766016,-11765952⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627650,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1283798493180,0,true,170377187904,170377187968⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨915224762372,0,false,-201707286528,-201707286464⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1283923975955,0,true,170484652608,170484652672⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨915099279597,0,false,-201858046528,-201858046464⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1068581610028,0,false,-31373393856,-31373393792⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1068623688165,0,false,-31330098624,-31330098560⟩
    { al := (137313/819200), au := (1373979/8192000), zl := (7999/8000), zu := 1,
      A := ⟨184298388848,184412339700⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170387057088,170387057152⟩ : DyadicInterval 40),(⟨-201721130432,-201721130368⟩ : DyadicInterval 40),(⟨746604329187,746604348517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170484645312,170484645376⟩ : DyadicInterval 40),(⟨-201858036288,-201858036224⟩ : DyadicInterval 40),(⟨746585040873,746585060202⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170367326784,170367326848⟩ : DyadicInterval 40),(⟨-201693454400,-201693454336⟩ : DyadicInterval 40),(⟨746608227176,746608246505⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170484645312,170484645376⟩ : DyadicInterval 40),(⟨-201858036288,-201858036224⟩ : DyadicInterval 40),(⟨746585040873,746585060202⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11765909⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11765824,11765888⟩ : DyadicInterval 40),(⟨-11766016,-11765952⟩ : DyadicInterval 40),(⟨762123383522,762123402851⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨184286865404,184412348179⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170377187904,170377187968⟩ : DyadicInterval 40),(⟨-201707286528,-201707286464⟩ : DyadicInterval 40),(⟨746606279020,746606298350⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170484652608,170484652672⟩ : DyadicInterval 40),(⟨-201858046528,-201858046464⟩ : DyadicInterval 40),(⟨746585039438,746585058768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31373393856,-31330098560⟩ : DyadicInterval 40),(⟨777788432896,777810099808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨170387057088,170484645376⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201858036288,-201721130368⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2910_ok : ecellOkT e2910 = true := by decide +kernel
theorem e2910_pos {a z : ℝ} (ha1 : ((137313/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1373979/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2910 e2910_ok ha1 ha2 hz1 hz2 hz

-- box ['1373979/8192000', '343707/2048000', '7999/8000', '1']  interval_lower 78075617/274877906944
noncomputable def e2911 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1283923967475,0,true,170484645312,170484645376⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨915099288077,0,false,-201858036288,-201858036224⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284037918327,0,true,170582224896,170582224960⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914985337225,0,false,-201994959232,-201994959168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283900915932,0,true,170464904512,170464904576⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915122339620,0,false,-201830339712,-201830339648⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523401260,0,true,11773376,11773440⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499854292,0,false,-11773568,-11773504⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627649,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1283912436907,0,true,170474770880,170474770944⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨915110818645,0,false,-201844182144,-201844182080⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1284037926810,0,true,170582232128,170582232192⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨914985328742,0,false,-201994969472,-201994969408⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1068543374075,0,false,-31412737280,-31412737216⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1068585480613,0,false,-31369411264,-31369411200⟩
    { al := (1373979/8192000), au := (343707/2048000), zl := (7999/8000), zu := 1,
      A := ⟨184412339699,184526290551⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170484645312,170484645376⟩ : DyadicInterval 40),(⟨-201858036288,-201858036224⟩ : DyadicInterval 40),(⟨746585040873,746585060202⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170582224896,170582224960⟩ : DyadicInterval 40),(⟨-201994959232,-201994959168⟩ : DyadicInterval 40),(⟨746565740411,746565759740⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170464904512,170464904576⟩ : DyadicInterval 40),(⟨-201830339712,-201830339648⟩ : DyadicInterval 40),(⟨746588943764,746588963094⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170582224896,170582224960⟩ : DyadicInterval 40),(⟨-201994959232,-201994959168⟩ : DyadicInterval 40),(⟨746565740411,746565759740⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11773484⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11773376,11773440⟩ : DyadicInterval 40),(⟨-11773568,-11773504⟩ : DyadicInterval 40),(⟨762123383521,762123402850⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨184400809131,184526299034⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170474770880,170474770944⟩ : DyadicInterval 40),(⟨-201844182144,-201844182080⟩ : DyadicInterval 40),(⟨746586993172,746587012502⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170582232128,170582232192⟩ : DyadicInterval 40),(⟨-201994969472,-201994969408⟩ : DyadicInterval 40),(⟨746565739011,746565758341⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31412737280,-31369411200⟩ : DyadicInterval 40),(⟨777808089216,777829771520⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨170484645312,170582224960⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-201994959232,-201858036224⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2911_ok : ecellOkT e2911 = true := by decide +kernel
theorem e2911_pos {a z : ℝ} (ha1 : ((1373979/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((343707/2048000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2911 e2911_ok ha1 ha2 hz1 hz2 hz

-- box ['343707/2048000', '1375677/8192000', '1999/2000', '7997/8000']  interval_lower 314328715/1099511627776
noncomputable def e2912 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284037918326,0,true,170582224896,170582224960⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914985337226,0,false,-201994959232,-201994959168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284151869178,0,true,170679795776,170679795840⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914871386374,0,false,-202131899264,-202131899200⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283945655180,0,true,170503217856,170503217920⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915077600372,0,false,-201884094848,-201884094784⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1284082629088,0,true,170620509696,170620509760⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨914940626464,0,false,-202048688192,-202048688128⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546946828,0,true,35318464,35318528⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476308724,0,false,-35319680,-35319616⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558750869,0,true,47122048,47122112⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464504683,0,false,-47124160,-47124096⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625756,0,false,-2048,-1984⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626642,0,false,-1152,-1088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1283991782182,0,true,170542718144,170542718208⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915031473370,0,false,-201939520192,-201939520128⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1284117257745,0,true,170650160512,170650160576⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨914905997807,0,false,-202090303296,-202090303232⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068516740814,0,false,-31440142784,-31440142720⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068558860648,0,false,-31396801984,-31396801920⟩
    { al := (343707/2048000), au := (1375677/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨184526290550,184640241402⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170582224896,170582224960⟩ : DyadicInterval 40),(⟨-201994959232,-201994959168⟩ : DyadicInterval 40),(⟨746565740411,746565759740⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170679795776,170679795840⟩ : DyadicInterval 40),(⟨-202131899264,-202131899200⟩ : DyadicInterval 40),(⟨746546427837,746546447166⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170503217856,170503217920⟩ : DyadicInterval 40),(⟨-201884094848,-201884094784⟩ : DyadicInterval 40),(⟨746581368428,746581387758⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170620509696,170620509760⟩ : DyadicInterval 40),(⟨-202048688192,-202048688128⟩ : DyadicInterval 40),(⟨746558164207,746558183536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨35319052,47123093⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35318464,35318528⟩ : DyadicInterval 40),(⟨-35319680,-35319616⟩ : DyadicInterval 40),(⟨762123383025,762123402354⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨47122048,47122112⟩ : DyadicInterval 40),(⟨-47124160,-47124096⟩ : DyadicInterval 40),(⟨762123382588,762123401917⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2048,-1088⟩ : DyadicInterval 40),(⟨762123384160,762123403904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184480154406,184605629969⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170542718144,170542718208⟩ : DyadicInterval 40),(⟨-201939520192,-201939520128⟩ : DyadicInterval 40),(⟨746573556223,746573575552⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170650160512,170650160576⟩ : DyadicInterval 40),(⟨-202090303296,-202090303232⟩ : DyadicInterval 40),(⟨746552295124,746552314453⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31440142784,-31396801920⟩ : DyadicInterval 40),(⟨777821784576,777843474272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170582224896,170679795840⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-202131899264,-201994959168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2912_ok : ecellOkT e2912 = true := by decide +kernel
theorem e2912_pos {a z : ℝ} (ha1 : ((343707/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1375677/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2912 e2912_ok ha1 ha2 hz1 hz2 hz

-- box ['1375677/8192000', '688263/4096000', '1999/2000', '7997/8000']  interval_lower 78937563/274877906944
noncomputable def e2913 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284151869177,0,true,170679795776,170679795840⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914871386375,0,false,-202131899264,-202131899200⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284265820029,0,true,170777358016,170777358080⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914757435523,0,false,-202268856320,-202268856256⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1284059549056,0,true,170600746944,170600747008⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨914963706496,0,false,-202020952576,-202020952512⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1284196537207,0,true,170718040576,170718040640⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨914826718345,0,false,-202185583552,-202185583488⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546969553,0,true,35341184,35341248⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476285999,0,false,-35342400,-35342336⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558781172,0,true,47152384,47152448⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464474380,0,false,-47154432,-47154368⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625753,0,false,-2048,-1984⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626641,0,false,-1152,-1088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1284105704538,0,true,170640268160,170640268224⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨914917551014,0,false,-202076419008,-202076418944⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1284231187227,0,true,170747707072,170747707136⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨914792068325,0,false,-202227229504,-202227229440⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068478471980,0,false,-31479522368,-31479522304⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068520620210,0,false,-31436150848,-31436150784⟩
    { al := (1375677/8192000), au := (688263/4096000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨184640241401,184754192253⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170679795776,170679795840⟩ : DyadicInterval 40),(⟨-202131899264,-202131899200⟩ : DyadicInterval 40),(⟨746546427837,746546447166⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170777358016,170777358080⟩ : DyadicInterval 40),(⟨-202268856320,-202268856256⟩ : DyadicInterval 40),(⟨746527103087,746527122417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170600746944,170600747008⟩ : DyadicInterval 40),(⟨-202020952576,-202020952512⟩ : DyadicInterval 40),(⟨746562075346,746562094675⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170718040576,170718040640⟩ : DyadicInterval 40),(⟨-202185583552,-202185583488⟩ : DyadicInterval 40),(⟨746538854119,746538873448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨35341777,47153396⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35341184,35341248⟩ : DyadicInterval 40),(⟨-35342400,-35342336⟩ : DyadicInterval 40),(⟨762123383023,762123402353⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨47152384,47152448⟩ : DyadicInterval 40),(⟨-47154432,-47154368⟩ : DyadicInterval 40),(⟨762123382553,762123401882⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2048,-1088⟩ : DyadicInterval 40),(⟨762123384160,762123403904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184594076762,184719559451⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170640268160,170640268224⟩ : DyadicInterval 40),(⟨-202076419008,-202076418944⟩ : DyadicInterval 40),(⟨746554253354,746554272684⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170747707072,170747707136⟩ : DyadicInterval 40),(⟨-202227229504,-202227229440⟩ : DyadicInterval 40),(⟨746532977705,746532997034⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31479522368,-31436150784⟩ : DyadicInterval 40),(⟨777841459008,777863164064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170679795776,170777358080⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-202268856320,-202131899200⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2913_ok : ecellOkT e2913 = true := by decide +kernel
theorem e2913_pos {a z : ℝ} (ha1 : ((1375677/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((688263/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2913 e2913_ok ha1 ha2 hz1 hz2 hz

-- box ['343707/2048000', '1375677/8192000', '7997/8000', '3999/4000']  interval_lower 4908215/17179869184
noncomputable def e2914 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284037918326,0,true,170582224896,170582224960⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914985337226,0,false,-201994959232,-201994959168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284151869178,0,true,170679795776,170679795840⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914871386374,0,false,-202131899264,-202131899200⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283968720966,0,true,170522970112,170522970176⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915054534586,0,false,-201911809920,-201911809856⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1284105709118,0,true,170640272064,170640272128⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨914917546434,0,false,-202076424512,-202076424448⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535173786,0,true,23545728,23545792⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488081766,0,false,-23546304,-23546240⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546970253,0,true,35341888,35341952⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476285299,0,false,-35343104,-35343040⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626639,0,false,-1152,-1088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627272,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1284003314968,0,true,170552593920,170552593984⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915019940584,0,false,-201953378176,-201953378112⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1284128797685,0,true,170660041408,170660041472⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨914894457867,0,false,-202104171776,-202104171712⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068512865630,0,false,-31444130368,-31444130304⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068554990499,0,false,-31400784256,-31400784192⟩
    { al := (343707/2048000), au := (1375677/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨184526290550,184640241402⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170582224896,170582224960⟩ : DyadicInterval 40),(⟨-201994959232,-201994959168⟩ : DyadicInterval 40),(⟨746565740411,746565759740⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170679795776,170679795840⟩ : DyadicInterval 40),(⟨-202131899264,-202131899200⟩ : DyadicInterval 40),(⟨746546427837,746546447166⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170522970112,170522970176⟩ : DyadicInterval 40),(⟨-201911809920,-201911809856⟩ : DyadicInterval 40),(⟨746577462202,746577481532⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170640272064,170640272128⟩ : DyadicInterval 40),(⟨-202076424512,-202076424448⟩ : DyadicInterval 40),(⟨746554252589,746554271918⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23546010,35342477⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23545728,23545792⟩ : DyadicInterval 40),(⟨-23546304,-23546240⟩ : DyadicInterval 40),(⟨762123383335,762123402664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35341888,35341952⟩ : DyadicInterval 40),(⟨-35343104,-35343040⟩ : DyadicInterval 40),(⟨762123383023,762123402352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1152,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184491687192,184617169909⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170552593920,170552593984⟩ : DyadicInterval 40),(⟨-201953378176,-201953378112⟩ : DyadicInterval 40),(⟨746571602649,746571621978⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170660041408,170660041472⟩ : DyadicInterval 40),(⟨-202104171776,-202104171712⟩ : DyadicInterval 40),(⟨746550339005,746550358335⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31444130368,-31400784192⟩ : DyadicInterval 40),(⟨777823775712,777845468064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170582224896,170679795840⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-202131899264,-201994959168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2914_ok : ecellOkT e2914 = true := by decide +kernel
theorem e2914_pos {a z : ℝ} (ha1 : ((343707/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1375677/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2914 e2914_ok ha1 ha2 hz1 hz2 hz

-- box ['1375677/8192000', '688263/4096000', '7997/8000', '3999/4000']  interval_lower 157773395/549755813888
noncomputable def e2915 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284151869177,0,true,170679795776,170679795840⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914871386375,0,false,-202131899264,-202131899200⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284265820029,0,true,170777358016,170777358080⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914757435523,0,false,-202268856320,-202268856256⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1284082629086,0,true,170620509696,170620509760⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨914940626466,0,false,-202048688192,-202048688128⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1284219631482,0,true,170737813440,170737813504⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨914803624070,0,false,-202213340416,-202213340352⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535188936,0,true,23560896,23560960⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488066616,0,false,-23561472,-23561408⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546992980,0,true,35364608,35364672⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476262572,0,false,-35365824,-35365760⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626638,0,false,-1152,-1088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627272,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1284117244451,0,true,170650149120,170650149184⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨914906011101,0,false,-202090287296,-202090287232⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1284242734296,0,true,170757593216,170757593280⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨914780521256,0,false,-202241108288,-202241108224⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068474592010,0,false,-31483515072,-31483515008⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068516745279,0,false,-31440138176,-31440138112⟩
    { al := (1375677/8192000), au := (688263/4096000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨184640241401,184754192253⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170679795776,170679795840⟩ : DyadicInterval 40),(⟨-202131899264,-202131899200⟩ : DyadicInterval 40),(⟨746546427837,746546447166⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170777358016,170777358080⟩ : DyadicInterval 40),(⟨-202268856320,-202268856256⟩ : DyadicInterval 40),(⟨746527103087,746527122417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170620509696,170620509760⟩ : DyadicInterval 40),(⟨-202048688192,-202048688128⟩ : DyadicInterval 40),(⟨746558164207,746558183536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170737813440,170737813504⟩ : DyadicInterval 40),(⟨-202213340416,-202213340352⟩ : DyadicInterval 40),(⟨746534937580,746534956910⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23561160,35365204⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23560896,23560960⟩ : DyadicInterval 40),(⟨-23561472,-23561408⟩ : DyadicInterval 40),(⟨762123383335,762123402664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35364608,35364672⟩ : DyadicInterval 40),(⟨-35365824,-35365760⟩ : DyadicInterval 40),(⟨762123383022,762123402351⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1152,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184605616675,184731106520⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170650149120,170650149184⟩ : DyadicInterval 40),(⟨-202090287296,-202090287232⟩ : DyadicInterval 40),(⟨746552297373,746552316702⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170757593216,170757593280⟩ : DyadicInterval 40),(⟨-202241108288,-202241108224⟩ : DyadicInterval 40),(⟨746531019138,746531038467⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31483515072,-31440138112⟩ : DyadicInterval 40),(⟨777843452672,777865160416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170679795776,170777358080⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-202268856320,-202131899200⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2915_ok : ecellOkT e2915 = true := by decide +kernel
theorem e2915_pos {a z : ℝ} (ha1 : ((1375677/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((688263/4096000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2915 e2915_ok ha1 ha2 hz1 hz2 hz

-- box ['343707/2048000', '1375677/8192000', '3999/4000', '7999/8000']  interval_lower 156961237/549755813888
noncomputable def e2916 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284037918326,0,true,170582224896,170582224960⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914985337226,0,false,-201994959232,-201994959168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284151869178,0,true,170679795776,170679795840⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914871386374,0,false,-202131899264,-202131899200⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1283991786753,0,true,170542722048,170542722112⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915031468799,0,false,-201939525632,-201939525568⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1284128789148,0,true,170660034112,170660034176⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨914894466404,0,false,-202104161536,-202104161472⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523400683,0,true,11772800,11772864⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499854869,0,false,-11772992,-11772928⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535189575,0,true,23561536,23561600⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488065977,0,false,-23562112,-23562048⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627271,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627650,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1284014847788,0,true,170562469568,170562469632⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨915008407764,0,false,-201967236416,-201967236352⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1284140337656,0,true,170669922240,170669922304⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨914882917896,0,false,-202118040512,-202118040448⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068508990195,0,false,-31448118208,-31448118144⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068551120098,0,false,-31404766784,-31404766720⟩
    { al := (343707/2048000), au := (1375677/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨184526290550,184640241402⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170582224896,170582224960⟩ : DyadicInterval 40),(⟨-201994959232,-201994959168⟩ : DyadicInterval 40),(⟨746565740411,746565759740⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170679795776,170679795840⟩ : DyadicInterval 40),(⟨-202131899264,-202131899200⟩ : DyadicInterval 40),(⟨746546427837,746546447166⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170542722048,170542722112⟩ : DyadicInterval 40),(⟨-201939525632,-201939525568⟩ : DyadicInterval 40),(⟨746573555433,746573574762⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170660034112,170660034176⟩ : DyadicInterval 40),(⟨-202104161536,-202104161472⟩ : DyadicInterval 40),(⟨746550340453,746550359782⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11772907,23561799⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11772800,11772864⟩ : DyadicInterval 40),(⟨-11772992,-11772928⟩ : DyadicInterval 40),(⟨762123383521,762123402850⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23561536,23561600⟩ : DyadicInterval 40),(⟨-23562112,-23562048⟩ : DyadicInterval 40),(⟨762123383335,762123402664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184503220012,184628709880⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170562469568,170562469632⟩ : DyadicInterval 40),(⟨-201967236416,-201967236352⟩ : DyadicInterval 40),(⟨746569649001,746569668330⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170669922240,170669922304⟩ : DyadicInterval 40),(⟨-202118040512,-202118040448⟩ : DyadicInterval 40),(⟨746548382776,746548402105⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31448118208,-31404766720⟩ : DyadicInterval 40),(⟨777825766976,777847461984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170582224896,170679795840⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-202131899264,-201994959168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2916_ok : ecellOkT e2916 = true := by decide +kernel
theorem e2916_pos {a z : ℝ} (ha1 : ((343707/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1375677/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2916 e2916_ok ha1 ha2 hz1 hz2 hz

-- box ['1375677/8192000', '688263/4096000', '3999/4000', '7999/8000']  interval_lower 157671515/549755813888
noncomputable def e2917 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284151869177,0,true,170679795776,170679795840⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914871386375,0,false,-202131899264,-202131899200⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284265820029,0,true,170777358016,170777358080⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914757435523,0,false,-202268856320,-202268856256⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1284105709116,0,true,170640272064,170640272128⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨914917546436,0,false,-202076424512,-202076424448⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1284242725756,0,true,170757585920,170757585984⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨914780529796,0,false,-202241097984,-202241097920⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523408259,0,true,11780416,11780480⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499847293,0,false,-11780608,-11780544⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535204727,0,true,23576640,23576704⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488050825,0,false,-23577216,-23577152⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627270,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627650,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1284128784390,0,true,170660030016,170660030080⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨914894471162,0,false,-202104155840,-202104155776⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1284254281389,0,true,170767479296,170767479360⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨914768974163,0,false,-202254987264,-202254987200⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068470711789,0,false,-31487507968,-31487507904⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068512870096,0,false,-31444125760,-31444125696⟩
    { al := (1375677/8192000), au := (688263/4096000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨184640241401,184754192253⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170679795776,170679795840⟩ : DyadicInterval 40),(⟨-202131899264,-202131899200⟩ : DyadicInterval 40),(⟨746546427837,746546447166⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170777358016,170777358080⟩ : DyadicInterval 40),(⟨-202268856320,-202268856256⟩ : DyadicInterval 40),(⟨746527103087,746527122417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170640272064,170640272128⟩ : DyadicInterval 40),(⟨-202076424512,-202076424448⟩ : DyadicInterval 40),(⟨746554252589,746554271918⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170757585920,170757585984⟩ : DyadicInterval 40),(⟨-202241097984,-202241097920⟩ : DyadicInterval 40),(⟨746531020561,746531039890⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11780483,23576951⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11780416,11780480⟩ : DyadicInterval 40),(⟨-11780608,-11780544⟩ : DyadicInterval 40),(⟨762123383521,762123402850⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23576640,23576704⟩ : DyadicInterval 40),(⟨-23577216,-23577152⟩ : DyadicInterval 40),(⟨762123383334,762123402663⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184617156614,184742653613⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170660030016,170660030080⟩ : DyadicInterval 40),(⟨-202104155840,-202104155776⟩ : DyadicInterval 40),(⟨746550341281,746550360611⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170767479296,170767479360⟩ : DyadicInterval 40),(⟨-202254987264,-202254987200⟩ : DyadicInterval 40),(⟨746529060434,746529079764⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31487507968,-31444125696⟩ : DyadicInterval 40),(⟨777845446464,777867156864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170679795776,170777358080⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-202268856320,-202131899200⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2917_ok : ecellOkT e2917 = true := by decide +kernel
theorem e2917_pos {a z : ℝ} (ha1 : ((1375677/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((688263/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2917 e2917_ok ha1 ha2 hz1 hz2 hz

-- box ['343707/2048000', '1375677/8192000', '7999/8000', '1']  interval_lower 156859689/549755813888
noncomputable def e2918 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284037918326,0,true,170582224896,170582224960⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914985337226,0,false,-201994959232,-201994959168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284151869178,0,true,170679795776,170679795840⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914871386374,0,false,-202131899264,-202131899200⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1284014852539,0,true,170562473664,170562473728⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨915008403013,0,false,-201967242112,-201967242048⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523408835,0,true,11780992,11781056⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499846717,0,false,-11781184,-11781120⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627649,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1284026380638,0,true,170572345216,170572345280⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨914996874914,0,false,-201981094848,-201981094784⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1284151877656,0,true,170679803008,170679803072⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨914871377896,0,false,-202131909440,-202131909376⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1068505114507,0,false,-31452106368,-31452106304⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1068547249444,0,false,-31408749568,-31408749504⟩
    { al := (343707/2048000), au := (1375677/8192000), zl := (7999/8000), zu := 1,
      A := ⟨184526290550,184640241402⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170582224896,170582224960⟩ : DyadicInterval 40),(⟨-201994959232,-201994959168⟩ : DyadicInterval 40),(⟨746565740411,746565759740⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170679795776,170679795840⟩ : DyadicInterval 40),(⟨-202131899264,-202131899200⟩ : DyadicInterval 40),(⟨746546427837,746546447166⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170562473664,170562473728⟩ : DyadicInterval 40),(⟨-201967242112,-201967242048⟩ : DyadicInterval 40),(⟨746569648174,746569667504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170679795776,170679795840⟩ : DyadicInterval 40),(⟨-202131899264,-202131899200⟩ : DyadicInterval 40),(⟨746546427837,746546447166⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11781059⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11780992,11781056⟩ : DyadicInterval 40),(⟨-11781184,-11781120⟩ : DyadicInterval 40),(⟨762123383521,762123402850⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨184514752862,184640249880⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170572345216,170572345280⟩ : DyadicInterval 40),(⟨-201981094848,-201981094784⟩ : DyadicInterval 40),(⟨746567695179,746567714509⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170679803008,170679803072⟩ : DyadicInterval 40),(⟨-202131909440,-202131909376⟩ : DyadicInterval 40),(⟨746546426410,746546445740⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31452106368,-31408749504⟩ : DyadicInterval 40),(⟨777827758368,777849456064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨170582224896,170679795840⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-202131899264,-201994959168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2918_ok : ecellOkT e2918 = true := by decide +kernel
theorem e2918_pos {a z : ℝ} (ha1 : ((343707/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1375677/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2918 e2918_ok ha1 ha2 hz1 hz2 hz

-- box ['1375677/8192000', '688263/4096000', '7999/8000', '1']  interval_lower 157569813/549755813888
noncomputable def e2919 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284151869177,0,true,170679795776,170679795840⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914871386375,0,false,-202131899264,-202131899200⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284265820029,0,true,170777358016,170777358080⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914757435523,0,false,-202268856320,-202268856256⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1284128789146,0,true,170660034112,170660034176⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨914894466406,0,false,-202104161536,-202104161472⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523416411,0,true,11788544,11788608⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499839141,0,false,-11788736,-11788672⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627649,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1284140324361,0,true,170669910848,170669910912⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨914882931191,0,false,-202118024512,-202118024448⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1284265828507,0,true,170777365248,170777365312⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨914757427045,0,false,-202268866496,-202268866432⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1068466831317,0,false,-31491501184,-31491501120⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1068508994661,0,false,-31448113664,-31448113600⟩
    { al := (1375677/8192000), au := (688263/4096000), zl := (7999/8000), zu := 1,
      A := ⟨184640241401,184754192253⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170679795776,170679795840⟩ : DyadicInterval 40),(⟨-202131899264,-202131899200⟩ : DyadicInterval 40),(⟨746546427837,746546447166⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170777358016,170777358080⟩ : DyadicInterval 40),(⟨-202268856320,-202268856256⟩ : DyadicInterval 40),(⟨746527103087,746527122417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170660034112,170660034176⟩ : DyadicInterval 40),(⟨-202104161536,-202104161472⟩ : DyadicInterval 40),(⟨746550340453,746550359782⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170777358016,170777358080⟩ : DyadicInterval 40),(⟨-202268856320,-202268856256⟩ : DyadicInterval 40),(⟨746527103087,746527122417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11788635⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11788544,11788608⟩ : DyadicInterval 40),(⟨-11788736,-11788672⟩ : DyadicInterval 40),(⟨762123383521,762123402850⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨184628696585,184754200731⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170669910848,170669910912⟩ : DyadicInterval 40),(⟨-202118024512,-202118024448⟩ : DyadicInterval 40),(⟨746548385026,746548404355⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170777365248,170777365312⟩ : DyadicInterval 40),(⟨-202268866496,-202268866432⟩ : DyadicInterval 40),(⟨746527101658,746527120987⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31491501184,-31448113600⟩ : DyadicInterval 40),(⟨777847440416,777869153472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨170679795776,170777358080⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-202268856320,-202131899200⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2919_ok : ecellOkT e2919 = true := by decide +kernel
theorem e2919_pos {a z : ℝ} (ha1 : ((1375677/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((688263/4096000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2919 e2919_ok ha1 ha2 hz1 hz2 hz

-- box ['818211/819200', '8182959/8192000', '7999/8000', '1']  interval_lower 81010528721883821/1099511627776
noncomputable def e2920 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2197695842222,0,true,761459476608,761459495552⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨1327413330,9,false,-7388046721600,-7388046548160⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2197809793074,0,true,761516484928,761516503936⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨1213462478,9,false,-7486732683328,-7486732509056⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2197558569194,0,true,761390796480,761390815424⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨1464686358,9,false,-7279844941632,-7279844768192⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1109652663599,0,true,10094554880,10094554944⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1089370591953,0,false,-10188091904,-10188091840⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099418094788,0,false,-93537024,-93536960⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨2197627421379,0,true,761425244992,761425263936⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1395834173,9,false,-7332785238400,-7332785064960⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨2197809806331,0,true,761516491584,761516510592⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1213449221,9,false,-7486744695488,-7486744521216⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨2425559248,8,false,-6725228184832,-6725228029824⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨2789896330,8,false,-6571359973888,-6571359819712⟩
    { al := (818211/819200), au := (8182959/8192000), zl := (7999/8000), zu := 1,
      A := ⟨1098184214446,1098298165298⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761459476608,761459495552⟩ : DyadicInterval 40),(⟨-7388046721600,-7388046548160⟩ : DyadicInterval 40),(⟨5583237109,5583275413⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761516484928,761516503936⟩ : DyadicInterval 40),(⟨-7486732683328,-7486732509056⟩ : DyadicInterval 40),(⟨5158418941,5158457301⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761390796480,761390815424⟩ : DyadicInterval 40),(⟨-7279844941632,-7279844768192⟩ : DyadicInterval 40),(⟨6088531586,6088569898⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761516484928,761516503936⟩ : DyadicInterval 40),(⟨-7486732683328,-7486732509056⟩ : DyadicInterval 40),(⟨5158418941,5158457301⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10141035823⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10094554880,10094554944⟩ : DyadicInterval 40),(⟨-10188091904,-10188091840⟩ : DyadicInterval 40),(⟨762076616423,762076635753⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-93537024,0⟩ : DyadicInterval 40),(⟨762123383616,762170171392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨1098115793603,1098298178555⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761425244992,761425263936⟩ : DyadicInterval 40),(⟨-7332785238400,-7332785064960⟩ : DyadicInterval 40),(⟨5835935003,5835973311⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761516491584,761516510592⟩ : DyadicInterval 40),(⟨-7486744695488,-7486744521216⟩ : DyadicInterval 40),(⟨5158369193,5158407552⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6725228184832,-6571359819712⟩ : DyadicInterval 40),(⟨4047803293472,4124737495296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨761459476608,761516503936⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-7486732683328,-7388046548160⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2920_ok : ecellOkT e2920 = true := by decide +kernel
theorem e2920_pos {a z : ℝ} (ha1 : ((818211/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((8182959/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2920 e2920_ok ha1 ha2 hz1 hz2 hz

-- box ['8182959/8192000', '999/1000', '7999/8000', '1']  interval_lower 86135367424277601/1099511627776
noncomputable def e2921 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2197809793073,0,true,761516484928,761516503936⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨1213462479,9,false,-7486732682432,-7486732508160⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2197923743925,0,true,761573490368,761573509376⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627,9,false,-7595157425088,-7595157240640⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2197672505801,0,true,761447801280,761447820224⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨1350749751,9,false,-7368884844672,-7368884671232⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1110576322607,0,true,11009391936,11009392000⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1088446932945,0,false,-11120744768,-11120744704⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099400280639,0,false,-111352832,-111352768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨2197741382758,0,true,761482260352,761482279360⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1281872794,9,false,-7426430733056,-7426430559488⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨2197923757126,0,true,761573496960,761573515968⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099498426,9,false,-7595170626176,-7595170441728⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨2197897366,8,false,-6833597110464,-6833596945216⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨2562251109,8,false,-6664948453120,-6664948298816⟩
    { al := (8182959/8192000), au := (999/1000), zl := (7999/8000), zu := 1,
      A := ⟨1098298165297,1098412116149⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761516484928,761516503936⟩ : DyadicInterval 40),(⟨-7486732682432,-7486732508160⟩ : DyadicInterval 40),(⟨5158418945,5158457304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761573490368,761573509376⟩ : DyadicInterval 40),(⟨-7595157425088,-7595157240640⟩ : DyadicInterval 40),(⟨4728239611,4728277967⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761447801280,761447820224⟩ : DyadicInterval 40),(⟨-7368884844672,-7368884671232⟩ : DyadicInterval 40),(⟨5669619075,5669657380⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761573490368,761573509376⟩ : DyadicInterval 40),(⟨-7595157425088,-7595157240640⟩ : DyadicInterval 40),(⟨4728239611,4728277967⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11064694831⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11009391936,11009392000⟩ : DyadicInterval 40),(⟨-11120744768,-11120744704⟩ : DyadicInterval 40),(⟨762067709072,762067728401⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-111352832,0⟩ : DyadicInterval 40),(⟨762123383616,762179079296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨1098229754982,1098412129350⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761482260352,761482279360⟩ : DyadicInterval 40),(⟨-7426430733056,-7426430559488⟩ : DyadicInterval 40),(⟨5414070017,5414108380⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761573496960,761573515968⟩ : DyadicInterval 40),(⟨-7595170626176,-7595170441728⟩ : DyadicInterval 40),(⟨4728189456,4728227813⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6833597110464,-6664948298816⟩ : DyadicInterval 40),(⟨4094597533024,4178921958112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨761516484928,761573509376⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-7595157425088,-7486732508160⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2921_ok : ecellOkT e2921 = true := by decide +kernel
theorem e2921_pos {a z : ℝ} (ha1 : ((8182959/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2921 e2921_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B048

end


