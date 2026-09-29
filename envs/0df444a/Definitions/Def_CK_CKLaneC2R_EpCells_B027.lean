-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B027
-- name    : CK_CKLaneC2R_EpCells_B027
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:37:02.192927+00:00
-- url     : https://prove2.me/theorems/7e8fb5b4-7645-4d9e-8427-84f72c6155f9
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B027` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B027` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B027` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B027 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B027.lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheckT

-- ===== source module CKLaneC2R.EpCells.B027 =====
section

namespace CKLaneC2R.EpCells.B027

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['620343/4096000', '248307/1638400', '3997/4000', '1599/1600']  interval_lower 127391617/1099511627776
noncomputable def e1620 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266033683857,0,true,155056234112,155056234176⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932989571695,0,false,-180569893952,-180569893888⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266147634709,0,true,155155192512,155155192576⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932875620843,0,false,-180704191232,-180704191168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265908792314,0,true,154947764288,154947764352⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933114463238,0,false,-180422721344,-180422721280⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266043487205,0,true,155064747968,155064748032⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932979768347,0,false,-180581447104,-180581447040⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564543922,0,true,52914816,52914880⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458711630,0,false,-52917440,-52917376⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575172780,0,true,63543104,63543168⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448082772,0,false,-63546880,-63546816⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624103,0,false,-3712,-3648⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625230,0,false,-2560,-2496⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265971234328,0,true,155001997248,155001997312⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933052021224,0,false,-180496300800,-180496300736⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266095565585,0,true,155109975168,155109975232⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932927689967,0,false,-180642822912,-180642822848⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074272960321,0,false,-25532847680,-25532847616⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074310620426,0,false,-25494303488,-25494303424⟩
    { al := (620343/4096000), au := (248307/1638400), zl := (3997/4000), zu := (1599/1600),
      A := ⟨166522056081,166636006933⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155056234112,155056234176⟩ : DyadicInterval 40),(⟨-180569893952,-180569893888⟩ : DyadicInterval 40),(⟨749464769238,749464788567⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155155192512,155155192576⟩ : DyadicInterval 40),(⟨-180704191232,-180704191168⟩ : DyadicInterval 40),(⟨749447371437,749447390766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154947764288,154947764352⟩ : DyadicInterval 40),(⟨-180422721344,-180422721280⟩ : DyadicInterval 40),(⟨749483823552,749483842881⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155064747968,155064748032⟩ : DyadicInterval 40),(⟨-180581447104,-180581447040⟩ : DyadicInterval 40),(⟨749463272976,749463292305⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨52916146,63545004⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52914816,52914880⟩ : DyadicInterval 40),(⟨-52917440,-52917376⟩ : DyadicInterval 40),(⟨762123382317,762123401646⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63543104,63543168⟩ : DyadicInterval 40),(⟨-63546880,-63546816⟩ : DyadicInterval 40),(⟨762123381767,762123401096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3712,-2496⟩ : DyadicInterval 40),(⟨762123384864,762123404736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166459606552,166583937809⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155001997248,155001997312⟩ : DyadicInterval 40),(⟨-180496300800,-180496300736⟩ : DyadicInterval 40),(⟨749474298816,749474318145⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155109975168,155109975232⟩ : DyadicInterval 40),(⟨-180642822912,-180642822848⟩ : DyadicInterval 40),(⟨749455322775,749455342105⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25532847680,-25494303424⟩ : DyadicInterval 40),(⟨774870535328,774889826720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155056234112,155155192576⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180704191232,-180569893888⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1620_ok : ecellOkT e1620 = true := by decide +kernel
theorem e1620_pos {a z : ℝ} (ha1 : ((620343/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((248307/1638400 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1620 e1620_ok ha1 ha2 hz1 hz2 hz

-- box ['248307/1638400', '77649/512000', '3997/4000', '1599/1600']  interval_lower 64180509/549755813888
noncomputable def e1621 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266147634708,0,true,155155192512,155155192576⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932875620844,0,false,-180704191232,-180704191168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266261585560,0,true,155254141952,155254142016⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932761669992,0,false,-180838504896,-180838504832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266022657702,0,true,155046658176,155046658240⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933000597850,0,false,-180556899904,-180556899840⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266157366837,0,true,155163643776,155163643840⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932865888715,0,false,-180715661824,-180715661760⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564581361,0,true,52952256,52952320⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458674191,0,false,-52954880,-52954816⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575217711,0,true,63588096,63588160⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448037841,0,false,-63591808,-63591744⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624098,0,false,-3712,-3648⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625226,0,false,-2560,-2496⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266085142444,0,true,155100923392,155100923456⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932938113108,0,false,-180630538688,-180630538624⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266209480827,0,true,155208897792,155208897856⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932813774725,0,false,-180777087104,-180777087040⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074238430558,0,false,-25568189248,-25568189184⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074276118585,0,false,-25529615232,-25529615168⟩
    { al := (248307/1638400), au := (77649/512000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨166636006932,166749957784⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155155192512,155155192576⟩ : DyadicInterval 40),(⟨-180704191232,-180704191168⟩ : DyadicInterval 40),(⟨749447371437,749447390766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155254141952,155254142016⟩ : DyadicInterval 40),(⟨-180838504896,-180838504832⟩ : DyadicInterval 40),(⟨749429961571,749429980900⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155046658176,155046658240⟩ : DyadicInterval 40),(⟨-180556899904,-180556899840⟩ : DyadicInterval 40),(⟨749466452059,749466471388⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155163643776,155163643840⟩ : DyadicInterval 40),(⟨-180715661824,-180715661760⟩ : DyadicInterval 40),(⟨749445884989,749445904319⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨52953585,63589935⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52952256,52952320⟩ : DyadicInterval 40),(⟨-52954880,-52954816⟩ : DyadicInterval 40),(⟨762123382313,762123401642⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63588096,63588160⟩ : DyadicInterval 40),(⟨-63591808,-63591744⟩ : DyadicInterval 40),(⟨762123381730,762123401059⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3712,-2496⟩ : DyadicInterval 40),(⟨762123384864,762123404736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166573514668,166697853051⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155100923392,155100923456⟩ : DyadicInterval 40),(⟨-180630538688,-180630538624⟩ : DyadicInterval 40),(⟨749456914162,749456933492⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155208897792,155208897856⟩ : DyadicInterval 40),(⟨-180777087104,-180777087040⟩ : DyadicInterval 40),(⟨749437923851,749437943181⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25568189248,-25529615168⟩ : DyadicInterval 40),(⟨774888191200,774907497504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155155192512,155254142016⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180838504896,-180704191168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1621_ok : ecellOkT e1621 = true := by decide +kernel
theorem e1621_pos {a z : ℝ} (ha1 : ((248307/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((77649/512000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1621 e1621_ok ha1 ha2 hz1 hz2 hz

-- box ['620343/4096000', '248307/1638400', '1599/1600', '1999/2000']  interval_lower 127250851/1099511627776
noncomputable def e1622 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266033683857,0,true,155056234112,155056234176⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932989571695,0,false,-180569893952,-180569893888⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266147634709,0,true,155155192512,155155192576⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932875620843,0,false,-180704191232,-180704191168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265929607571,0,true,154965843328,154965843392⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933093647981,0,false,-180447248768,-180447248704⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266064316706,0,true,155082837504,155082837568⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932958938846,0,false,-180605994816,-180605994752⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099553960731,0,true,42332096,42332160⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469294821,0,false,-42333824,-42333760⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564582102,0,true,52953024,52953088⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458673450,0,false,-52955648,-52955584⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625225,0,false,-2560,-2496⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626147,0,false,-1664,-1600⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265981641580,0,true,155011036032,155011036096⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933041613972,0,false,-180508564800,-180508564736⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266105980241,0,true,155119019520,155119019584⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932917275311,0,false,-180655097280,-180655097216⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074269804431,0,false,-25536077760,-25536077696⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074307469134,0,false,-25497528704,-25497528640⟩
    { al := (620343/4096000), au := (248307/1638400), zl := (1599/1600), zu := (1999/2000),
      A := ⟨166522056081,166636006933⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155056234112,155056234176⟩ : DyadicInterval 40),(⟨-180569893952,-180569893888⟩ : DyadicInterval 40),(⟨749464769238,749464788567⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155155192512,155155192576⟩ : DyadicInterval 40),(⟨-180704191232,-180704191168⟩ : DyadicInterval 40),(⟨749447371437,749447390766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154965843328,154965843392⟩ : DyadicInterval 40),(⟨-180447248768,-180447248704⟩ : DyadicInterval 40),(⟨749480648855,749480668185⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155082837504,155082837568⟩ : DyadicInterval 40),(⟨-180605994816,-180605994752⟩ : DyadicInterval 40),(⟨749460093450,749460112780⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨42332955,52954326⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42332096,42332160⟩ : DyadicInterval 40),(⟨-42333824,-42333760⟩ : DyadicInterval 40),(⟨762123382786,762123402115⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52953024,52953088⟩ : DyadicInterval 40),(⟨-52955648,-52955584⟩ : DyadicInterval 40),(⟨762123382313,762123401642⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2560,-1600⟩ : DyadicInterval 40),(⟨762123384416,762123404160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166470013804,166594352465⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155011036032,155011036096⟩ : DyadicInterval 40),(⟨-180508564800,-180508564736⟩ : DyadicInterval 40),(⟨749472710962,749472730292⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155119019520,155119019584⟩ : DyadicInterval 40),(⟨-180655097280,-180655097216⟩ : DyadicInterval 40),(⟨749453732574,749453751904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25536077760,-25497528640⟩ : DyadicInterval 40),(⟨774872147936,774891441760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155056234112,155155192576⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180704191232,-180569893888⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1622_ok : ecellOkT e1622 = true := by decide +kernel
theorem e1622_pos {a z : ℝ} (ha1 : ((620343/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((248307/1638400 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1622 e1622_ok ha1 ha2 hz1 hz2 hz

-- box ['248307/1638400', '77649/512000', '1599/1600', '1999/2000']  interval_lower 64110075/549755813888
noncomputable def e1623 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266147634708,0,true,155155192512,155155192576⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932875620844,0,false,-180704191232,-180704191168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266261585560,0,true,155254141952,155254142016⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932761669992,0,false,-180838504896,-180838504832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266043487203,0,true,155064747968,155064748032⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932979768349,0,false,-180581447104,-180581447040⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266178210582,0,true,155181744000,155181744064⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932845044970,0,false,-180740229376,-180740229312⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099553990682,0,true,42362048,42362112⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469264870,0,false,-42363776,-42363712⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564619543,0,true,52990464,52990528⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458636009,0,false,-52993088,-52993024⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625222,0,false,-2560,-2496⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626144,0,false,-1664,-1600⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266095556818,0,true,155109967552,155109967616⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932927698734,0,false,-180642812608,-180642812544⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266219902599,0,true,155217947520,155217947584⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932803352953,0,false,-180789371328,-180789371264⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074235270352,0,false,-25571423808,-25571423744⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074272962978,0,false,-25532844992,-25532844928⟩
    { al := (248307/1638400), au := (77649/512000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨166636006932,166749957784⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155155192512,155155192576⟩ : DyadicInterval 40),(⟨-180704191232,-180704191168⟩ : DyadicInterval 40),(⟨749447371437,749447390766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155254141952,155254142016⟩ : DyadicInterval 40),(⟨-180838504896,-180838504832⟩ : DyadicInterval 40),(⟨749429961571,749429980900⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155064747968,155064748032⟩ : DyadicInterval 40),(⟨-180581447104,-180581447040⟩ : DyadicInterval 40),(⟨749463272976,749463292305⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155181744000,155181744064⟩ : DyadicInterval 40),(⟨-180740229376,-180740229312⟩ : DyadicInterval 40),(⟨749442701134,749442720463⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨42362906,52991767⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42362048,42362112⟩ : DyadicInterval 40),(⟨-42363776,-42363712⟩ : DyadicInterval 40),(⟨762123382783,762123402112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52990464,52990528⟩ : DyadicInterval 40),(⟨-52993088,-52993024⟩ : DyadicInterval 40),(⟨762123382309,762123401639⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2560,-1600⟩ : DyadicInterval 40),(⟨762123384416,762123404160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166583929042,166708274823⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155109967552,155109967616⟩ : DyadicInterval 40),(⟨-180642812608,-180642812544⟩ : DyadicInterval 40),(⟨749455324127,749455343457⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155217947520,155217947584⟩ : DyadicInterval 40),(⟨-180789371328,-180789371264⟩ : DyadicInterval 40),(⟨749436331440,749436350769⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25571423808,-25532844928⟩ : DyadicInterval 40),(⟨774889806080,774909114784⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155155192512,155254142016⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180838504896,-180704191168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1623_ok : ecellOkT e1623 = true := by decide +kernel
theorem e1623_pos {a z : ℝ} (ha1 : ((248307/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((77649/512000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1623 e1623_ok ha1 ha2 hz1 hz2 hz

-- box ['154449/1024000', '1236441/8192000', '1999/2000', '7997/8000']  interval_lower 60675111/549755813888
noncomputable def e1624 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265349978750,0,true,154462296704,154462296768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933673276802,0,false,-179764454720,-179764454656⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265463929603,0,true,154561308544,154561308608⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933559325949,0,false,-179898653632,-179898653568⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265267059574,0,true,154390242624,154390242688⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933756195978,0,false,-179666811840,-179666811776⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265401697490,0,true,154507236160,154507236224⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933621558062,0,false,-179825361408,-179825361344⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543242746,0,true,31614464,31614528⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099480012806,0,false,-31615488,-31615424⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099553811699,0,true,42183104,42183168⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469443853,0,false,-42184768,-42184704⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626157,0,false,-1664,-1600⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626867,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265308514943,0,true,154426266560,154426266624⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933714740609,0,false,-179715627264,-179715627200⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265432817998,0,true,154534276544,154534276608⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933590437554,0,false,-179862012160,-179862012096⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074473382914,0,false,-25327735552,-25327735488⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074510884629,0,false,-25289360640,-25289360576⟩
    { al := (154449/1024000), au := (1236441/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨165838350974,165952301827⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154462296704,154462296768⟩ : DyadicInterval 40),(⟨-179764454720,-179764454656⟩ : DyadicInterval 40),(⟨749568902242,749568921571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154561308544,154561308608⟩ : DyadicInterval 40),(⟨-179898653632,-179898653568⟩ : DyadicInterval 40),(⟨749551576964,749551596293⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154390242624,154390242688⟩ : DyadicInterval 40),(⟨-179666811840,-179666811776⟩ : DyadicInterval 40),(⟨749581501843,749581521173⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154507236160,154507236224⟩ : DyadicInterval 40),(⟨-179825361408,-179825361344⟩ : DyadicInterval 40),(⟨749561040363,749561059693⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨31614970,42183923⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31614464,31614528⟩ : DyadicInterval 40),(⟨-31615488,-31615424⟩ : DyadicInterval 40),(⟨762123383154,762123402483⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42183104,42183168⟩ : DyadicInterval 40),(⟨-42184768,-42184704⟩ : DyadicInterval 40),(⟨762123382765,762123402094⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1664,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165796887167,165921190222⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154426266560,154426266624⟩ : DyadicInterval 40),(⟨-179715627264,-179715627200⟩ : DyadicInterval 40),(⟨749575203515,749575222844⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154534276544,154534276608⟩ : DyadicInterval 40),(⟨-179862012160,-179862012096⟩ : DyadicInterval 40),(⟨749556308445,749556327775⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25327735552,-25289360576⟩ : DyadicInterval 40),(⟨774768063904,774787270656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154462296704,154561308608⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179898653632,-179764454656⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1624_ok : ecellOkT e1624 = true := by decide +kernel
theorem e1624_pos {a z : ℝ} (ha1 : ((154449/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1236441/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1624 e1624_ok ha1 ha2 hz1 hz2 hz

-- box ['1236441/8192000', '123729/819200', '1999/2000', '7997/8000']  interval_lower 30576011/274877906944
noncomputable def e1625 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265463929602,0,true,154561308544,154561308608⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933559325950,0,false,-179898653632,-179898653568⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265577880454,0,true,154660311488,154660311552⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933445375098,0,false,-180032868928,-180032868864⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265380953451,0,true,154489211456,154489211520⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933642302101,0,false,-179800931776,-179800931712⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265515605610,0,true,154606206848,154606206912⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933507649942,0,false,-179959517440,-179959517376⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543265200,0,true,31636928,31636992⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479990352,0,false,-31637888,-31637824⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099553841641,0,true,42212992,42213056⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469413911,0,false,-42214720,-42214656⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626155,0,false,-1664,-1600⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626866,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265422437301,0,true,154525256896,154525256960⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933600818251,0,false,-179849786624,-179849786560⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265546747483,0,true,154633263360,154633263424⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933476508069,0,false,-179996197824,-179996197760⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074438986177,0,false,-25362934400,-25362934336⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074476515803,0,false,-25324529664,-25324529600⟩
    { al := (1236441/8192000), au := (123729/819200), zl := (1999/2000), zu := (7997/8000),
      A := ⟨165952301826,166066252678⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154561308544,154561308608⟩ : DyadicInterval 40),(⟨-179898653632,-179898653568⟩ : DyadicInterval 40),(⟨749551576964,749551596293⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154660311488,154660311552⟩ : DyadicInterval 40),(⟨-180032868928,-180032868864⟩ : DyadicInterval 40),(⟨749534239591,749534258920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154489211456,154489211520⟩ : DyadicInterval 40),(⟨-179800931776,-179800931712⟩ : DyadicInterval 40),(⟨749564194031,749564213360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154606206848,154606206912⟩ : DyadicInterval 40),(⟨-179959517440,-179959517376⟩ : DyadicInterval 40),(⟨749543716096,749543735426⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨31637424,42213865⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31636928,31636992⟩ : DyadicInterval 40),(⟨-31637888,-31637824⟩ : DyadicInterval 40),(⟨762123383121,762123402450⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42212992,42213056⟩ : DyadicInterval 40),(⟨-42214720,-42214656⟩ : DyadicInterval 40),(⟨762123382795,762123402124⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1664,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165910809525,166035119707⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154525256896,154525256960⟩ : DyadicInterval 40),(⟨-179849786624,-179849786560⟩ : DyadicInterval 40),(⟨749557886946,749557906276⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154633263360,154633263424⟩ : DyadicInterval 40),(⟨-179996197824,-179996197760⟩ : DyadicInterval 40),(⟨749538977626,749538996955⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25362934400,-25324529600⟩ : DyadicInterval 40),(⟨774785648416,774804870080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154561308544,154660311552⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180032868928,-179898653568⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1625_ok : ecellOkT e1625 = true := by decide +kernel
theorem e1625_pos {a z : ℝ} (ha1 : ((1236441/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((123729/819200 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1625 e1625_ok ha1 ha2 hz1 hz2 hz

-- box ['154449/1024000', '1236441/8192000', '7997/8000', '3999/4000']  interval_lower 60605955/549755813888
noncomputable def e1626 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265349978750,0,true,154462296704,154462296768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933673276802,0,false,-179764454720,-179764454656⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265463929603,0,true,154561308544,154561308608⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933559325949,0,false,-179898653632,-179898653568⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265287789368,0,true,154408256576,154408256640⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933735466184,0,false,-179691221760,-179691221696⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265422441528,0,true,154525260608,154525260672⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933600814024,0,false,-179849791616,-179849791552⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532704381,0,true,21076352,21076416⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490551171,0,false,-21076864,-21076800⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543265849,0,true,31637568,31637632⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479989703,0,false,-31638592,-31638528⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626865,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627372,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265318879764,0,true,154435273216,154435273280⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933704375788,0,false,-179727832576,-179727832512⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265443189965,0,true,154543288512,154543288576⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933580065587,0,false,-179874227520,-179874227456⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074470252464,0,false,-25330938944,-25330938880⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074507758679,0,false,-25292559296,-25292559232⟩
    { al := (154449/1024000), au := (1236441/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨165838350974,165952301827⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154462296704,154462296768⟩ : DyadicInterval 40),(⟨-179764454720,-179764454656⟩ : DyadicInterval 40),(⟨749568902242,749568921571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154561308544,154561308608⟩ : DyadicInterval 40),(⟨-179898653632,-179898653568⟩ : DyadicInterval 40),(⟨749551576964,749551596293⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154408256576,154408256640⟩ : DyadicInterval 40),(⟨-179691221760,-179691221696⟩ : DyadicInterval 40),(⟨749578352554,749578371884⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154525260608,154525260672⟩ : DyadicInterval 40),(⟨-179849791616,-179849791552⟩ : DyadicInterval 40),(⟨749557886287,749557905616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21076605,31638073⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21076352,21076416⟩ : DyadicInterval 40),(⟨-21076864,-21076800⟩ : DyadicInterval 40),(⟨762123383403,762123402732⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31637568,31637632⟩ : DyadicInterval 40),(⟨-31638592,-31638528⟩ : DyadicInterval 40),(⟨762123383153,762123402482⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165807251988,165931562189⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154435273216,154435273280⟩ : DyadicInterval 40),(⟨-179727832576,-179727832512⟩ : DyadicInterval 40),(⟨749573628516,749573647845⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154543288512,154543288576⟩ : DyadicInterval 40),(⟨-179874227520,-179874227456⟩ : DyadicInterval 40),(⟨749554731170,749554750500⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25330938944,-25292559232⟩ : DyadicInterval 40),(⟨774769663232,774788872352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154462296704,154561308608⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179898653632,-179764454656⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1626_ok : ecellOkT e1626 = true := by decide +kernel
theorem e1626_pos {a z : ℝ} (ha1 : ((154449/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1236441/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1626 e1626_ok ha1 ha2 hz1 hz2 hz

-- box ['1236441/8192000', '123729/819200', '7997/8000', '3999/4000']  interval_lower 122165527/1099511627776
noncomputable def e1627 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265463929602,0,true,154561308544,154561308608⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933559325950,0,false,-179898653632,-179898653568⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265577880454,0,true,154660311488,154660311552⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933445375098,0,false,-180032868928,-180032868864⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265401697488,0,true,154507236160,154507236224⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933621558064,0,false,-179825361408,-179825361344⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265536363891,0,true,154624242048,154624242112⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933486891661,0,false,-179983967360,-179983967296⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532719351,0,true,21091328,21091392⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490536201,0,false,-21091840,-21091776⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543288305,0,true,31660032,31660096⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479967247,0,false,-31660992,-31660928⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626864,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627372,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265432809502,0,true,154534269184,154534269248⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933590446050,0,false,-179862002176,-179862002112⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265557126573,0,true,154642280704,154642280768⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933466128979,0,false,-180008423040,-180008422976⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074435851427,0,false,-25366142336,-25366142272⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074473385479,0,false,-25327732928,-25327732864⟩
    { al := (1236441/8192000), au := (123729/819200), zl := (7997/8000), zu := (3999/4000),
      A := ⟨165952301826,166066252678⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154561308544,154561308608⟩ : DyadicInterval 40),(⟨-179898653632,-179898653568⟩ : DyadicInterval 40),(⟨749551576964,749551596293⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154660311488,154660311552⟩ : DyadicInterval 40),(⟨-180032868928,-180032868864⟩ : DyadicInterval 40),(⟨749534239591,749534258920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154507236160,154507236224⟩ : DyadicInterval 40),(⟨-179825361408,-179825361344⟩ : DyadicInterval 40),(⟨749561040363,749561059693⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154624242048,154624242112⟩ : DyadicInterval 40),(⟨-179983967360,-179983967296⟩ : DyadicInterval 40),(⟨749540557635,749540576964⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21091575,31660529⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21091328,21091392⟩ : DyadicInterval 40),(⟨-21091840,-21091776⟩ : DyadicInterval 40),(⟨762123383403,762123402732⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31660032,31660096⟩ : DyadicInterval 40),(⟨-31660992,-31660928⟩ : DyadicInterval 40),(⟨762123383120,762123402449⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165921181726,166045498797⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154534269184,154534269248⟩ : DyadicInterval 40),(⟨-179862002176,-179862002112⟩ : DyadicInterval 40),(⟨749556309734,749556329063⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154642280704,154642280768⟩ : DyadicInterval 40),(⟨-180008423040,-180008422976⟩ : DyadicInterval 40),(⟨749537398157,749537417486⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25366142336,-25327732864⟩ : DyadicInterval 40),(⟨774787250048,774806474048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154561308544,154660311552⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180032868928,-179898653568⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1627_ok : ecellOkT e1627 = true := by decide +kernel
theorem e1627_pos {a z : ℝ} (ha1 : ((1236441/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((123729/819200 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1627 e1627_ok ha1 ha2 hz1 hz2 hz

-- box ['123729/819200', '1238139/8192000', '1999/2000', '7997/8000']  interval_lower 30815079/274877906944
noncomputable def e1628 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265577880453,0,true,154660311488,154660311552⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933445375099,0,false,-180032868928,-180032868864⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265691831305,0,true,154759305472,154759305536⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933331424247,0,false,-180167100608,-180167100544⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265494847326,0,true,154588171392,154588171456⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933528408226,0,false,-179935068032,-179935067968⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265629513729,0,true,154705168640,154705168704⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933393741823,0,false,-180093689792,-180093689728⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543287656,0,true,31659392,31659456⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479967896,0,false,-31660352,-31660288⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099553871583,0,true,42242944,42243008⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469383969,0,false,-42244672,-42244608⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626152,0,false,-1664,-1600⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626865,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265536359663,0,true,154624238336,154624238400⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933486895889,0,false,-179983962432,-179983962368⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265660676968,0,true,154732241280,154732241344⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933362578584,0,false,-180130399808,-180130399744⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074404565831,0,false,-25398158528,-25398158464⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074442123369,0,false,-25359724032,-25359723968⟩
    { al := (123729/819200), au := (1238139/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨166066252677,166180203529⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154660311488,154660311552⟩ : DyadicInterval 40),(⟨-180032868928,-180032868864⟩ : DyadicInterval 40),(⟨749534239591,749534258920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154759305472,154759305536⟩ : DyadicInterval 40),(⟨-180167100608,-180167100544⟩ : DyadicInterval 40),(⟨749516890159,749516909488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154588171392,154588171456⟩ : DyadicInterval 40),(⟨-179935068032,-179935067968⟩ : DyadicInterval 40),(⟨749546874121,749546893451⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154705168640,154705168704⟩ : DyadicInterval 40),(⟨-180093689792,-180093689728⟩ : DyadicInterval 40),(⟨749526379725,749526399055⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨31659880,42243807⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31659392,31659456⟩ : DyadicInterval 40),(⟨-31660352,-31660288⟩ : DyadicInterval 40),(⟨762123383120,762123402449⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42242944,42243008⟩ : DyadicInterval 40),(⟨-42244672,-42244608⟩ : DyadicInterval 40),(⟨762123382792,762123402122⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1664,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166024731887,166149049192⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154624238336,154624238400⟩ : DyadicInterval 40),(⟨-179983962432,-179983962368⟩ : DyadicInterval 40),(⟨749540558322,749540577652⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154732241280,154732241344⟩ : DyadicInterval 40),(⟨-180130399808,-180130399744⟩ : DyadicInterval 40),(⟨749521634692,749521654022⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25398158528,-25359723968⟩ : DyadicInterval 40),(⟨774803245600,774822482144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154660311488,154759305536⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180167100608,-180032868864⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1628_ok : ecellOkT e1628 = true := by decide +kernel
theorem e1628_pos {a z : ℝ} (ha1 : ((123729/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1238139/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1628 e1628_ok ha1 ha2 hz1 hz2 hz

-- box ['1238139/8192000', '309747/2048000', '1999/2000', '7997/8000']  interval_lower 31054769/274877906944
noncomputable def e1629 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265691831304,0,true,154759305472,154759305536⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933331424248,0,false,-180167100608,-180167100544⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265805782156,0,true,154858290624,154858290688⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933217473396,0,false,-180301348672,-180301348608⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265608741202,0,true,154687122432,154687122496⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933414514350,0,false,-180069220608,-180069220544⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265743421849,0,true,154804121472,154804121536⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933279833703,0,false,-180227878528,-180227878464⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543310114,0,true,31681856,31681920⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479945438,0,false,-31682816,-31682752⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099553901529,0,true,42272896,42272960⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469354023,0,false,-42274624,-42274560⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626150,0,false,-1664,-1600⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626864,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265650282025,0,true,154723210880,154723210944⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933372973527,0,false,-180118154560,-180118154496⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265774606456,0,true,154831210240,154831210304⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933248649096,0,false,-180264618240,-180264618176⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074370121873,0,false,-25433407936,-25433407872⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074407707328,0,false,-25394943616,-25394943552⟩
    { al := (1238139/8192000), au := (309747/2048000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨166180203528,166294154380⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154759305472,154759305536⟩ : DyadicInterval 40),(⟨-180167100608,-180167100544⟩ : DyadicInterval 40),(⟨749516890159,749516909488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154858290624,154858290688⟩ : DyadicInterval 40),(⟨-180301348672,-180301348608⟩ : DyadicInterval 40),(⟨749499528592,749499547922⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154687122432,154687122496⟩ : DyadicInterval 40),(⟨-180069220608,-180069220544⟩ : DyadicInterval 40),(⟨749529542114,749529561443⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154804121472,154804121536⟩ : DyadicInterval 40),(⟨-180227878528,-180227878464⟩ : DyadicInterval 40),(⟨749509031312,749509050642⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨31682338,42273753⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31681856,31681920⟩ : DyadicInterval 40),(⟨-31682816,-31682752⟩ : DyadicInterval 40),(⟨762123383119,762123402448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42272896,42272960⟩ : DyadicInterval 40),(⟨-42274624,-42274560⟩ : DyadicInterval 40),(⟨762123382790,762123402119⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1664,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166138654249,166262978680⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154723210880,154723210944⟩ : DyadicInterval 40),(⟨-180118154560,-180118154496⟩ : DyadicInterval 40),(⟨749523217587,749523236917⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154831210240,154831210304⟩ : DyadicInterval 40),(⟨-180264618240,-180264618176⟩ : DyadicInterval 40),(⟨749504279735,749504299065⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25433407936,-25394943552⟩ : DyadicInterval 40),(⟨774820855392,774840106848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154759305472,154858290688⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180301348672,-180167100544⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1629_ok : ecellOkT e1629 = true := by decide +kernel
theorem e1629_pos {a z : ℝ} (ha1 : ((1238139/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((309747/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1629 e1629_ok ha1 ha2 hz1 hz2 hz

-- box ['123729/819200', '1238139/8192000', '7997/8000', '3999/4000']  interval_lower 3847535/34359738368
noncomputable def e1630 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265577880453,0,true,154660311488,154660311552⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933445375099,0,false,-180032868928,-180032868864⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265691831305,0,true,154759305472,154759305536⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933331424247,0,false,-180167100608,-180167100544⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265515605608,0,true,154606206848,154606206912⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933507649944,0,false,-179959517440,-179959517376⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265650286255,0,true,154723214528,154723214592⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933372969297,0,false,-180118159552,-180118159488⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532734321,0,true,21106304,21106368⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490521231,0,false,-21106752,-21106688⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543310763,0,true,31682496,31682560⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479944789,0,false,-31683456,-31683392⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626863,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627371,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265546738729,0,true,154633255744,154633255808⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933476516823,0,false,-179996187520,-179996187456⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265671063173,0,true,154741264000,154741264064⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933352192379,0,false,-180142634944,-180142634880⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074401426779,0,false,-25401370944,-25401370880⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074438988822,0,false,-25362931712,-25362931648⟩
    { al := (123729/819200), au := (1238139/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨166066252677,166180203529⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154660311488,154660311552⟩ : DyadicInterval 40),(⟨-180032868928,-180032868864⟩ : DyadicInterval 40),(⟨749534239591,749534258920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154759305472,154759305536⟩ : DyadicInterval 40),(⟨-180167100608,-180167100544⟩ : DyadicInterval 40),(⟨749516890159,749516909488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154606206848,154606206912⟩ : DyadicInterval 40),(⟨-179959517440,-179959517376⟩ : DyadicInterval 40),(⟨749543716097,749543735426⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154723214528,154723214592⟩ : DyadicInterval 40),(⟨-180118159552,-180118159488⟩ : DyadicInterval 40),(⟨749523216963,749523236292⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21106545,31682987⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21106304,21106368⟩ : DyadicInterval 40),(⟨-21106752,-21106688⟩ : DyadicInterval 40),(⟨762123383370,762123402699⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31682496,31682560⟩ : DyadicInterval 40),(⟨-31683456,-31683392⟩ : DyadicInterval 40),(⟨762123383119,762123402448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166035110953,166159435397⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154633255744,154633255808⟩ : DyadicInterval 40),(⟨-179996187520,-179996187456⟩ : DyadicInterval 40),(⟨749538978967,749538998296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154741264000,154741264064⟩ : DyadicInterval 40),(⟨-180142634944,-180142634880⟩ : DyadicInterval 40),(⟨749520053055,749520072385⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25401370944,-25362931648⟩ : DyadicInterval 40),(⟨774804849440,774824088352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154660311488,154759305536⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180167100608,-180032868864⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1630_ok : ecellOkT e1630 = true := by decide +kernel
theorem e1630_pos {a z : ℝ} (ha1 : ((123729/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1238139/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1630 e1630_ok ha1 ha2 hz1 hz2 hz

-- box ['1238139/8192000', '309747/2048000', '7997/8000', '3999/4000']  interval_lower 62039935/549755813888
noncomputable def e1631 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265691831304,0,true,154759305472,154759305536⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933331424248,0,false,-180167100608,-180167100544⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265805782156,0,true,154858290624,154858290688⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933217473396,0,false,-180301348672,-180301348608⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265629513727,0,true,154705168640,154705168704⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933393741825,0,false,-180093689792,-180093689728⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265764208618,0,true,154822178176,154822178240⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933259046934,0,false,-180252368064,-180252368000⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532749293,0,true,21121280,21121344⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490506259,0,false,-21121728,-21121664⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543333222,0,true,31704960,31705024⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479922330,0,false,-31705920,-31705856⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626861,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627371,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265660668467,0,true,154732233856,154732233920⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933362587085,0,false,-180130389824,-180130389760⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265784999785,0,true,154840238336,154840238400⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933238255767,0,false,-180276863296,-180276863232⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074366978514,0,false,-25436624896,-25436624832⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074404568401,0,false,-25398155904,-25398155840⟩
    { al := (1238139/8192000), au := (309747/2048000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨166180203528,166294154380⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154759305472,154759305536⟩ : DyadicInterval 40),(⟨-180167100608,-180167100544⟩ : DyadicInterval 40),(⟨749516890159,749516909488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154858290624,154858290688⟩ : DyadicInterval 40),(⟨-180301348672,-180301348608⟩ : DyadicInterval 40),(⟨749499528592,749499547922⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154705168640,154705168704⟩ : DyadicInterval 40),(⟨-180093689792,-180093689728⟩ : DyadicInterval 40),(⟨749526379726,749526399055⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154822178176,154822178240⟩ : DyadicInterval 40),(⟨-180252368064,-180252368000⟩ : DyadicInterval 40),(⟨749505864142,749505883471⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21121517,31705446⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21121280,21121344⟩ : DyadicInterval 40),(⟨-21121728,-21121664⟩ : DyadicInterval 40),(⟨762123383370,762123402699⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31704960,31705024⟩ : DyadicInterval 40),(⟨-31705920,-31705856⟩ : DyadicInterval 40),(⟨762123383117,762123402446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166149040691,166273372009⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154732233856,154732233920⟩ : DyadicInterval 40),(⟨-180130389824,-180130389760⟩ : DyadicInterval 40),(⟨749521636022,749521655352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154840238336,154840238400⟩ : DyadicInterval 40),(⟨-180276863296,-180276863232⟩ : DyadicInterval 40),(⟨749502695925,749502715255⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25436624896,-25398155840⟩ : DyadicInterval 40),(⟨774822461536,774841715328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154759305472,154858290688⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180301348672,-180167100544⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1631_ok : ecellOkT e1631 = true := by decide +kernel
theorem e1631_pos {a z : ℝ} (ha1 : ((1238139/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((309747/2048000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1631 e1631_ok ha1 ha2 hz1 hz2 hz

-- box ['154449/1024000', '1236441/8192000', '3999/4000', '7999/8000']  interval_lower 121073687/1099511627776
noncomputable def e1632 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265349978750,0,true,154462296704,154462296768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933673276802,0,false,-179764454720,-179764454656⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265463929603,0,true,154561308544,154561308608⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933559325949,0,false,-179898653632,-179898653568⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265308519162,0,true,154426270272,154426270336⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933714736390,0,false,-179715632192,-179715632128⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265443185566,0,true,154543284736,154543284800⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933580069986,0,false,-179874222336,-179874222272⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522165972,0,true,10538112,10538176⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099501089580,0,false,-10538304,-10538240⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532719954,0,true,21091968,21092032⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490535598,0,false,-21092416,-21092352⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627371,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627675,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265329244866,0,true,154444280064,154444280128⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933694010686,0,false,-179740038400,-179740038336⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265453561954,0,true,154552300480,154552300544⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933569693598,0,false,-179886443072,-179886443008⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074467121812,0,false,-25334142592,-25334142528⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074504632450,0,false,-25295758272,-25295758208⟩
    { al := (154449/1024000), au := (1236441/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨165838350974,165952301827⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154462296704,154462296768⟩ : DyadicInterval 40),(⟨-179764454720,-179764454656⟩ : DyadicInterval 40),(⟨749568902242,749568921571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154561308544,154561308608⟩ : DyadicInterval 40),(⟨-179898653632,-179898653568⟩ : DyadicInterval 40),(⟨749551576964,749551596293⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154426270272,154426270336⟩ : DyadicInterval 40),(⟨-179715632192,-179715632128⟩ : DyadicInterval 40),(⟨749575202830,749575222160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154543284736,154543284800⟩ : DyadicInterval 40),(⟨-179874222336,-179874222272⟩ : DyadicInterval 40),(⟨749554731811,749554751141⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10538196,21092178⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10538112,10538176⟩ : DyadicInterval 40),(⟨-10538304,-10538240⟩ : DyadicInterval 40),(⟨762123383546,762123402875⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21091968,21092032⟩ : DyadicInterval 40),(⟨-21092416,-21092352⟩ : DyadicInterval 40),(⟨762123383371,762123402700⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165817617090,165941934178⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154444280064,154444280128⟩ : DyadicInterval 40),(⟨-179740038400,-179740038336⟩ : DyadicInterval 40),(⟨749572053381,749572072710⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154552300480,154552300544⟩ : DyadicInterval 40),(⟨-179886443072,-179886443008⟩ : DyadicInterval 40),(⟨749553153773,749553173103⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25334142592,-25295758208⟩ : DyadicInterval 40),(⟨774771262720,774790474176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154462296704,154561308608⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179898653632,-179764454656⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1632_ok : ecellOkT e1632 = true := by decide +kernel
theorem e1632_pos {a z : ℝ} (ha1 : ((154449/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1236441/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1632 e1632_ok ha1 ha2 hz1 hz2 hz

-- box ['1236441/8192000', '123729/819200', '3999/4000', '7999/8000']  interval_lower 122026717/1099511627776
noncomputable def e1633 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265463929602,0,true,154561308544,154561308608⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933559325950,0,false,-179898653632,-179898653568⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265577880454,0,true,154660311488,154660311552⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933445375098,0,false,-180032868928,-180032868864⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265422441526,0,true,154525260608,154525260672⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933600814026,0,false,-179849791616,-179849791552⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265557122173,0,true,154642276928,154642276992⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933466133379,0,false,-180008417920,-180008417856⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522173456,0,true,10545600,10545664⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099501082096,0,false,-10545792,-10545728⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532734926,0,true,21106944,21107008⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490520626,0,false,-21107392,-21107328⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627370,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627675,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265443181469,0,true,154543281152,154543281216⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933580074083,0,false,-179874217536,-179874217472⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265567505681,0,true,154651298048,154651298112⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933455749871,0,false,-180020648512,-180020648448⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074432716475,0,false,-25369350464,-25369350400⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074470255029,0,false,-25330936320,-25330936256⟩
    { al := (1236441/8192000), au := (123729/819200), zl := (3999/4000), zu := (7999/8000),
      A := ⟨165952301826,166066252678⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154561308544,154561308608⟩ : DyadicInterval 40),(⟨-179898653632,-179898653568⟩ : DyadicInterval 40),(⟨749551576964,749551596293⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154660311488,154660311552⟩ : DyadicInterval 40),(⟨-180032868928,-180032868864⟩ : DyadicInterval 40),(⟨749534239591,749534258920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154525260608,154525260672⟩ : DyadicInterval 40),(⟨-179849791616,-179849791552⟩ : DyadicInterval 40),(⟨749557886287,749557905617⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154642276928,154642276992⟩ : DyadicInterval 40),(⟨-180008417920,-180008417856⟩ : DyadicInterval 40),(⟨749537398827,749537418156⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10545680,21107150⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10545600,10545664⟩ : DyadicInterval 40),(⟨-10545792,-10545728⟩ : DyadicInterval 40),(⟨762123383546,762123402875⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21106944,21107008⟩ : DyadicInterval 40),(⟨-21107392,-21107328⟩ : DyadicInterval 40),(⟨762123383370,762123402699⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165931553693,166055877905⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154543281152,154543281216⟩ : DyadicInterval 40),(⟨-179874217536,-179874217472⟩ : DyadicInterval 40),(⟨749554732459,749554751788⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154651298048,154651298112⟩ : DyadicInterval 40),(⟨-180020648512,-180020648448⟩ : DyadicInterval 40),(⟨749535818594,749535837923⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25369350464,-25330936256⟩ : DyadicInterval 40),(⟨774788851744,774808078112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154561308544,154660311552⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180032868928,-179898653568⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1633_ok : ecellOkT e1633 = true := by decide +kernel
theorem e1633_pos {a z : ℝ} (ha1 : ((1236441/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((123729/819200 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1633 e1633_ok ha1 ha2 hz1 hz2 hz

-- box ['154449/1024000', '1236441/8192000', '7999/8000', '1']  interval_lower 120934897/1099511627776
noncomputable def e1634 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265349978750,0,true,154462296704,154462296768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933673276802,0,false,-179764454720,-179764454656⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265463929603,0,true,154561308544,154561308608⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933559325949,0,false,-179898653632,-179898653568⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265329248956,0,true,154444283648,154444283712⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933694006596,0,false,-179740043200,-179740043136⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522174016,0,true,10546176,10546240⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099501081536,0,false,-10546304,-10546240⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627674,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1265339609475,0,true,154453286400,154453286464⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨933683646077,0,false,-179752243776,-179752243712⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1265463933959,0,true,154561312320,154561312384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨933559321593,0,false,-179898658752,-179898658688⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1074463990960,0,false,-25337346432,-25337346368⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1074501506174,0,false,-25298957312,-25298957248⟩
    { al := (154449/1024000), au := (1236441/8192000), zl := (7999/8000), zu := 1,
      A := ⟨165838350974,165952301827⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154462296704,154462296768⟩ : DyadicInterval 40),(⟨-179764454720,-179764454656⟩ : DyadicInterval 40),(⟨749568902242,749568921571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154561308544,154561308608⟩ : DyadicInterval 40),(⟨-179898653632,-179898653568⟩ : DyadicInterval 40),(⟨749551576964,749551596293⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154444283648,154444283712⟩ : DyadicInterval 40),(⟨-179740043200,-179740043136⟩ : DyadicInterval 40),(⟨749572052735,749572072065⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154561308544,154561308608⟩ : DyadicInterval 40),(⟨-179898653632,-179898653568⟩ : DyadicInterval 40),(⟨749551576964,749551596293⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10546240⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10546176,10546240⟩ : DyadicInterval 40),(⟨-10546304,-10546240⟩ : DyadicInterval 40),(⟨762123383514,762123402843⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨165827981699,165952306183⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154453286400,154453286464⟩ : DyadicInterval 40),(⟨-179752243776,-179752243712⟩ : DyadicInterval 40),(⟨749570478225,749570497555⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154561312320,154561312384⟩ : DyadicInterval 40),(⟨-179898658752,-179898658688⟩ : DyadicInterval 40),(⟨749551576302,749551595631⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25337346432,-25298957248⟩ : DyadicInterval 40),(⟨774772862240,774792076096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨154462296704,154561308608⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179898653632,-179764454656⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1634_ok : ecellOkT e1634 = true := by decide +kernel
theorem e1634_pos {a z : ℝ} (ha1 : ((154449/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1236441/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1634 e1634_ok ha1 ha2 hz1 hz2 hz

-- box ['1236441/8192000', '123729/819200', '7999/8000', '1']  interval_lower 121888009/1099511627776
noncomputable def e1635 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265463929602,0,true,154561308544,154561308608⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933559325950,0,false,-179898653632,-179898653568⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265577880454,0,true,154660311488,154660311552⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933445375098,0,false,-180032868928,-180032868864⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265443185564,0,true,154543284736,154543284800⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933580069988,0,false,-179874222336,-179874222272⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522181501,0,true,10553664,10553728⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099501074051,0,false,-10553792,-10553728⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627674,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1265453553458,0,true,154552293056,154552293120⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨933569702094,0,false,-179886433088,-179886433024⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1265577884810,0,true,154660315264,154660315328⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨933445370742,0,false,-180032874048,-180032873984⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1074429581321,0,false,-25372558784,-25372558720⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1074467124378,0,false,-25334139968,-25334139904⟩
    { al := (1236441/8192000), au := (123729/819200), zl := (7999/8000), zu := 1,
      A := ⟨165952301826,166066252678⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154561308544,154561308608⟩ : DyadicInterval 40),(⟨-179898653632,-179898653568⟩ : DyadicInterval 40),(⟨749551576964,749551596293⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154660311488,154660311552⟩ : DyadicInterval 40),(⟨-180032868928,-180032868864⟩ : DyadicInterval 40),(⟨749534239591,749534258920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154543284736,154543284800⟩ : DyadicInterval 40),(⟨-179874222336,-179874222272⟩ : DyadicInterval 40),(⟨749554731812,749554751141⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154660311488,154660311552⟩ : DyadicInterval 40),(⟨-180032868928,-180032868864⟩ : DyadicInterval 40),(⟨749534239591,749534258920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10553725⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10553664,10553728⟩ : DyadicInterval 40),(⟨-10553792,-10553728⟩ : DyadicInterval 40),(⟨762123383514,762123402843⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨165941925682,166066257034⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154552293056,154552293120⟩ : DyadicInterval 40),(⟨-179886433088,-179886433024⟩ : DyadicInterval 40),(⟨749553155099,749553174428⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154660315264,154660315328⟩ : DyadicInterval 40),(⟨-180032874048,-180032873984⟩ : DyadicInterval 40),(⟨749534238928,749534258257⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25372558784,-25334139904⟩ : DyadicInterval 40),(⟨774790453568,774809682272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨154561308544,154660311552⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180032868928,-179898653568⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1635_ok : ecellOkT e1635 = true := by decide +kernel
theorem e1635_pos {a z : ℝ} (ha1 : ((1236441/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((123729/819200 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1635 e1635_ok ha1 ha2 hz1 hz2 hz

-- box ['123729/819200', '1238139/8192000', '3999/4000', '7999/8000']  interval_lower 122982283/1099511627776
noncomputable def e1636 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265577880453,0,true,154660311488,154660311552⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933445375099,0,false,-180032868928,-180032868864⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265691831305,0,true,154759305472,154759305536⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933331424247,0,false,-180167100608,-180167100544⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265536363889,0,true,154624242048,154624242112⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933486891663,0,false,-179983967360,-179983967296⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265671058780,0,true,154741260160,154741260224⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933352196772,0,false,-180142629824,-180142629760⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522180942,0,true,10553088,10553152⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099501074610,0,false,-10553280,-10553216⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532749898,0,true,21121856,21121920⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490505654,0,false,-21122368,-21122304⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627370,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627675,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265557117820,0,true,154642273152,154642273216⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933466137732,0,false,-180008412736,-180008412672⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265681449405,0,true,154750286656,154750286720⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933341806147,0,false,-180154870272,-180154870208⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074398287523,0,false,-25404583552,-25404583488⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074435854072,0,false,-25366139584,-25366139520⟩
    { al := (123729/819200), au := (1238139/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨166066252677,166180203529⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154660311488,154660311552⟩ : DyadicInterval 40),(⟨-180032868928,-180032868864⟩ : DyadicInterval 40),(⟨749534239591,749534258920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154759305472,154759305536⟩ : DyadicInterval 40),(⟨-180167100608,-180167100544⟩ : DyadicInterval 40),(⟨749516890159,749516909488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154624242048,154624242112⟩ : DyadicInterval 40),(⟨-179983967360,-179983967296⟩ : DyadicInterval 40),(⟨749540557635,749540576965⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154741260160,154741260224⟩ : DyadicInterval 40),(⟨-180142629824,-180142629760⟩ : DyadicInterval 40),(⟨749520053762,749520073091⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10553166,21122122⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10553088,10553152⟩ : DyadicInterval 40),(⟨-10553280,-10553216⟩ : DyadicInterval 40),(⟨762123383546,762123402875⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21121856,21121920⟩ : DyadicInterval 40),(⟨-21122368,-21122304⟩ : DyadicInterval 40),(⟨762123383402,762123402731⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166045490044,166169821629⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154642273152,154642273216⟩ : DyadicInterval 40),(⟨-180008412736,-180008412672⟩ : DyadicInterval 40),(⟨749537399461,749537418791⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154750286656,154750286720⟩ : DyadicInterval 40),(⟨-180154870272,-180154870208⟩ : DyadicInterval 40),(⟨749518471332,749518490661⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25404583552,-25366139520⟩ : DyadicInterval 40),(⟨774806453376,774825694656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154660311488,154759305536⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180167100608,-180032868864⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1636_ok : ecellOkT e1636 = true := by decide +kernel
theorem e1636_pos {a z : ℝ} (ha1 : ((123729/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1238139/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1636 e1636_ok ha1 ha2 hz1 hz2 hz

-- box ['1238139/8192000', '309747/2048000', '3999/4000', '7999/8000']  interval_lower 123940471/1099511627776
noncomputable def e1637 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265691831304,0,true,154759305472,154759305536⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933331424248,0,false,-180167100608,-180167100544⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265805782156,0,true,154858290624,154858290688⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933217473396,0,false,-180301348672,-180301348608⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265650286253,0,true,154723214528,154723214592⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933372969299,0,false,-180118159552,-180118159488⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265784995387,0,true,154840234560,154840234624⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933238260165,0,false,-180276858112,-180276858048⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522188428,0,true,10560576,10560640⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099501067124,0,false,-10560704,-10560640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532764871,0,true,21136832,21136896⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490490681,0,false,-21137344,-21137280⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627369,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627675,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265671054673,0,true,154741256576,154741256640⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933352200879,0,false,-180142624960,-180142624896⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265795393139,0,true,154849266432,154849266496⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933227862413,0,false,-180289108480,-180289108416⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074363834951,0,false,-25439842048,-25439841984⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074401429349,0,false,-25401368320,-25401368256⟩
    { al := (1238139/8192000), au := (309747/2048000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨166180203528,166294154380⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154759305472,154759305536⟩ : DyadicInterval 40),(⟨-180167100608,-180167100544⟩ : DyadicInterval 40),(⟨749516890159,749516909488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154858290624,154858290688⟩ : DyadicInterval 40),(⟨-180301348672,-180301348608⟩ : DyadicInterval 40),(⟨749499528592,749499547922⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154723214528,154723214592⟩ : DyadicInterval 40),(⟨-180118159552,-180118159488⟩ : DyadicInterval 40),(⟨749523216963,749523236293⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154840234560,154840234624⟩ : DyadicInterval 40),(⟨-180276858112,-180276858048⟩ : DyadicInterval 40),(⟨749502696568,749502715898⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10560652,21137095⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10560576,10560640⟩ : DyadicInterval 40),(⟨-10560704,-10560640⟩ : DyadicInterval 40),(⟨762123383514,762123402843⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21136832,21136896⟩ : DyadicInterval 40),(⟨-21137344,-21137280⟩ : DyadicInterval 40),(⟨762123383401,762123402730⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166159426897,166283765363⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154741256576,154741256640⟩ : DyadicInterval 40),(⟨-180142624960,-180142624896⟩ : DyadicInterval 40),(⟨749520054385,749520073715⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154849266432,154849266496⟩ : DyadicInterval 40),(⟨-180289108480,-180289108416⟩ : DyadicInterval 40),(⟨749501111965,749501131294⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25439842048,-25401368256⟩ : DyadicInterval 40),(⟨774824067744,774843323904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154759305472,154858290688⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180301348672,-180167100544⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1637_ok : ecellOkT e1637 = true := by decide +kernel
theorem e1637_pos {a z : ℝ} (ha1 : ((1238139/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((309747/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1637 e1637_ok ha1 ha2 hz1 hz2 hz

-- box ['123729/819200', '1238139/8192000', '7999/8000', '1']  interval_lower 61421467/549755813888
noncomputable def e1638 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265577880453,0,true,154660311488,154660311552⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933445375099,0,false,-180032868928,-180032868864⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265691831305,0,true,154759305472,154759305536⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933331424247,0,false,-180167100608,-180167100544⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265557122171,0,true,154642276928,154642276992⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933466133381,0,false,-180008417856,-180008417792⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522188987,0,true,10561152,10561216⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099501066565,0,false,-10561280,-10561216⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627674,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1265567496929,0,true,154651290432,154651290496⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨933455758623,0,false,-180020638208,-180020638144⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1265691835656,0,true,154759309248,154759309312⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨933331419896,0,false,-180167105728,-180167105664⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1074395148065,0,false,-25407796416,-25407796352⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1074432719120,0,false,-25369347712,-25369347648⟩
    { al := (123729/819200), au := (1238139/8192000), zl := (7999/8000), zu := 1,
      A := ⟨166066252677,166180203529⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154660311488,154660311552⟩ : DyadicInterval 40),(⟨-180032868928,-180032868864⟩ : DyadicInterval 40),(⟨749534239591,749534258920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154759305472,154759305536⟩ : DyadicInterval 40),(⟨-180167100608,-180167100544⟩ : DyadicInterval 40),(⟨749516890159,749516909488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154642276928,154642276992⟩ : DyadicInterval 40),(⟨-180008417856,-180008417792⟩ : DyadicInterval 40),(⟨749537398800,749537418129⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154759305472,154759305536⟩ : DyadicInterval 40),(⟨-180167100608,-180167100544⟩ : DyadicInterval 40),(⟨749516890159,749516909488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10561211⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10561152,10561216⟩ : DyadicInterval 40),(⟨-10561280,-10561216⟩ : DyadicInterval 40),(⟨762123383514,762123402843⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨166055869153,166180207880⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154651290432,154651290496⟩ : DyadicInterval 40),(⟨-180020638208,-180020638144⟩ : DyadicInterval 40),(⟨749535819935,749535839265⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154759309248,154759309312⟩ : DyadicInterval 40),(⟨-180167105728,-180167105664⟩ : DyadicInterval 40),(⟨749516889496,749516908825⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25407796416,-25369347648⟩ : DyadicInterval 40),(⟨774808057440,774827301088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨154660311488,154759305536⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180167100608,-180032868864⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1638_ok : ecellOkT e1638 = true := by decide +kernel
theorem e1638_pos {a z : ℝ} (ha1 : ((123729/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1238139/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1638 e1638_ok ha1 ha2 hz1 hz2 hz

-- box ['1238139/8192000', '309747/2048000', '7999/8000', '1']  interval_lower 30950137/274877906944
noncomputable def e1639 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265691831304,0,true,154759305472,154759305536⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933331424248,0,false,-180167100608,-180167100544⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265805782156,0,true,154858290624,154858290688⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933217473396,0,false,-180301348672,-180301348608⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265671058778,0,true,154741260160,154741260224⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933352196774,0,false,-180142629824,-180142629760⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522196474,0,true,10568640,10568704⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099501059078,0,false,-10568768,-10568704⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627674,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1265681440648,0,true,154750279040,154750279104⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨933341814904,0,false,-180154859968,-180154859904⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1265805786513,0,true,154858294400,154858294464⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨933217469039,0,false,-180301353792,-180301353728⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1074360691186,0,false,-25443059392,-25443059328⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1074398290171,0,false,-25404580864,-25404580800⟩
    { al := (1238139/8192000), au := (309747/2048000), zl := (7999/8000), zu := 1,
      A := ⟨166180203528,166294154380⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154759305472,154759305536⟩ : DyadicInterval 40),(⟨-180167100608,-180167100544⟩ : DyadicInterval 40),(⟨749516890159,749516909488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154858290624,154858290688⟩ : DyadicInterval 40),(⟨-180301348672,-180301348608⟩ : DyadicInterval 40),(⟨749499528592,749499547922⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154741260160,154741260224⟩ : DyadicInterval 40),(⟨-180142629824,-180142629760⟩ : DyadicInterval 40),(⟨749520053762,749520073091⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154858290624,154858290688⟩ : DyadicInterval 40),(⟨-180301348672,-180301348608⟩ : DyadicInterval 40),(⟨749499528592,749499547922⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10568698⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10568640,10568704⟩ : DyadicInterval 40),(⟨-10568768,-10568704⟩ : DyadicInterval 40),(⟨762123383514,762123402843⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨166169812872,166294158737⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154750279040,154750279104⟩ : DyadicInterval 40),(⟨-180154859968,-180154859904⟩ : DyadicInterval 40),(⟨749518472676,749518492005⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154858294400,154858294464⟩ : DyadicInterval 40),(⟨-180301353792,-180301353728⟩ : DyadicInterval 40),(⟨749499527928,749499547257⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25443059392,-25404580800⟩ : DyadicInterval 40),(⟨774825674016,774844932576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨154759305472,154858290688⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180301348672,-180167100544⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1639_ok : ecellOkT e1639 = true := by decide +kernel
theorem e1639_pos {a z : ℝ} (ha1 : ((1238139/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((309747/2048000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1639 e1639_ok ha1 ha2 hz1 hz2 hz

-- box ['309747/2048000', '1239837/8192000', '1999/2000', '7997/8000']  interval_lower 15647541/137438953472
noncomputable def e1640 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265805782155,0,true,154858290624,154858290688⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933217473397,0,false,-180301348672,-180301348608⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265919733007,0,true,154957266816,154957266880⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933103522545,0,false,-180435613120,-180435613056⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265722635077,0,true,154786064512,154786064576⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933300620475,0,false,-180203389632,-180203389568⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265857329968,0,true,154903065472,154903065536⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933165925584,0,false,-180362083712,-180362083648⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543332572,0,true,31704320,31704384⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479922980,0,false,-31705280,-31705216⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099553931477,0,true,42302848,42302912⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469324075,0,false,-42304576,-42304512⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626148,0,false,-1664,-1600⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626862,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265764204385,0,true,154822174464,154822174528⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933259051167,0,false,-180252363072,-180252363008⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265888535941,0,true,154930170368,154930170432⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933134719611,0,false,-180398853056,-180398852992⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074335654306,0,false,-25468682688,-25468682624⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074373267680,0,false,-25430188544,-25430188480⟩
    { al := (309747/2048000), au := (1239837/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨166294154379,166408105231⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154858290624,154858290688⟩ : DyadicInterval 40),(⟨-180301348672,-180301348608⟩ : DyadicInterval 40),(⟨749499528593,749499547922⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154957266816,154957266880⟩ : DyadicInterval 40),(⟨-180435613120,-180435613056⟩ : DyadicInterval 40),(⟨749482154965,749482174294⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154786064512,154786064576⟩ : DyadicInterval 40),(⟨-180203389632,-180203389568⟩ : DyadicInterval 40),(⟨749512198098,749512217427⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154903065472,154903065536⟩ : DyadicInterval 40),(⟨-180362083712,-180362083648⟩ : DyadicInterval 40),(⟨749491670810,749491690140⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨31704796,42303701⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31704320,31704384⟩ : DyadicInterval 40),(⟨-31705280,-31705216⟩ : DyadicInterval 40),(⟨762123383117,762123402446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42302848,42302912⟩ : DyadicInterval 40),(⟨-42304576,-42304512⟩ : DyadicInterval 40),(⟨762123382788,762123402117⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1664,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166252576609,166376908165⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154822174464,154822174528⟩ : DyadicInterval 40),(⟨-180252363072,-180252363008⟩ : DyadicInterval 40),(⟨749505864805,749505884134⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154930170368,154930170432⟩ : DyadicInterval 40),(⟨-180398853056,-180398852992⟩ : DyadicInterval 40),(⟨749486912652,749486931981⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25468682688,-25430188480⟩ : DyadicInterval 40),(⟨774838477856,774857744224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154858290624,154957266880⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180435613120,-180301348608⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1640_ok : ecellOkT e1640 = true := by decide +kernel
theorem e1640_pos {a z : ℝ} (ha1 : ((309747/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1239837/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1640 e1640_ok ha1 ha2 hz1 hz2 hz

-- box ['1239837/8192000', '620343/4096000', '1999/2000', '7997/8000']  interval_lower 15768077/137438953472
noncomputable def e1641 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265919733006,0,true,154957266816,154957266880⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933103522546,0,false,-180435613120,-180435613056⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266033683858,0,true,155056234112,155056234176⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932989571694,0,false,-180569893952,-180569893888⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265836528953,0,true,154884997760,154884997824⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933186726599,0,false,-180337574976,-180337574912⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265971238088,0,true,155002000512,155002000576⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933052017464,0,false,-180496305216,-180496305152⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543355033,0,true,31726784,31726848⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479900519,0,false,-31727744,-31727680⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099553961427,0,true,42332800,42332864⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469294125,0,false,-42334528,-42334464⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626146,0,false,-1664,-1600⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626861,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265878127004,0,true,154921129408,154921129472⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933145128548,0,false,-180386588288,-180386588224⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266002465427,0,true,155029121536,155029121600⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933020790125,0,false,-180533104256,-180533104192⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074301163128,0,false,-25503982656,-25503982592⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074338804346,0,false,-25465458816,-25465458752⟩
    { al := (1239837/8192000), au := (620343/4096000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨166408105230,166522056082⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154957266816,154957266880⟩ : DyadicInterval 40),(⟨-180435613120,-180435613056⟩ : DyadicInterval 40),(⟨749482154965,749482174294⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155056234112,155056234176⟩ : DyadicInterval 40),(⟨-180569893952,-180569893888⟩ : DyadicInterval 40),(⟨749464769237,749464788567⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154884997760,154884997824⟩ : DyadicInterval 40),(⟨-180337574976,-180337574912⟩ : DyadicInterval 40),(⟨749494841945,749494861274⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155002000512,155002000576⟩ : DyadicInterval 40),(⟨-180496305216,-180496305152⟩ : DyadicInterval 40),(⟨749474298237,749474317566⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨31727257,42333651⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31726784,31726848⟩ : DyadicInterval 40),(⟨-31727744,-31727680⟩ : DyadicInterval 40),(⟨762123383116,762123402445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42332800,42332864⟩ : DyadicInterval 40),(⟨-42334528,-42334464⟩ : DyadicInterval 40),(⟨762123382786,762123402115⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1664,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166366499228,166490837651⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154921129408,154921129472⟩ : DyadicInterval 40),(⟨-180386588288,-180386588224⟩ : DyadicInterval 40),(⟨749488499886,749488519215⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155029121536,155029121600⟩ : DyadicInterval 40),(⟨-180533104256,-180533104192⟩ : DyadicInterval 40),(⟨749469533516,749469552845⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25503982656,-25465458752⟩ : DyadicInterval 40),(⟨774856112992,774875394208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154957266816,155056234176⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180569893952,-180435613056⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1641_ok : ecellOkT e1641 = true := by decide +kernel
theorem e1641_pos {a z : ℝ} (ha1 : ((1239837/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((620343/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1641 e1641_ok ha1 ha2 hz1 hz2 hz

-- box ['309747/2048000', '1239837/8192000', '7997/8000', '3999/4000']  interval_lower 31260111/274877906944
noncomputable def e1642 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265805782155,0,true,154858290624,154858290688⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933217473397,0,false,-180301348672,-180301348608⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265919733007,0,true,154957266816,154957266880⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933103522545,0,false,-180435613120,-180435613056⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265743421847,0,true,154804121472,154804121536⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933279833705,0,false,-180227878528,-180227878464⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265878130981,0,true,154921132864,154921132928⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933145124571,0,false,-180386592960,-180386592896⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532764266,0,true,21136256,21136320⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490491286,0,false,-21136704,-21136640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543355683,0,true,31727424,31727488⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479899869,0,false,-31728384,-31728320⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626860,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627370,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265774597696,0,true,154831202624,154831202688⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933248657856,0,false,-180264607936,-180264607872⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265898936392,0,true,154939203840,154939203904⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933124319160,0,false,-180411107968,-180411107904⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074332506637,0,false,-25471904128,-25471904064⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074370124523,0,false,-25433405248,-25433405184⟩
    { al := (309747/2048000), au := (1239837/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨166294154379,166408105231⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154858290624,154858290688⟩ : DyadicInterval 40),(⟨-180301348672,-180301348608⟩ : DyadicInterval 40),(⟨749499528593,749499547922⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154957266816,154957266880⟩ : DyadicInterval 40),(⟨-180435613120,-180435613056⟩ : DyadicInterval 40),(⟨749482154965,749482174294⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154804121472,154804121536⟩ : DyadicInterval 40),(⟨-180227878528,-180227878464⟩ : DyadicInterval 40),(⟨749509031312,749509050642⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154921132864,154921132928⟩ : DyadicInterval 40),(⟨-180386592960,-180386592896⟩ : DyadicInterval 40),(⟨749488499272,749488518602⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21136490,31727907⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21136256,21136320⟩ : DyadicInterval 40),(⟨-21136704,-21136640⟩ : DyadicInterval 40),(⟨762123383369,762123402698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31727424,31727488⟩ : DyadicInterval 40),(⟨-31728384,-31728320⟩ : DyadicInterval 40),(⟨762123383116,762123402445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166262969920,166387308616⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154831202624,154831202688⟩ : DyadicInterval 40),(⟨-180264607936,-180264607872⟩ : DyadicInterval 40),(⟨749504281081,749504300410⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154939203840,154939203904⟩ : DyadicInterval 40),(⟨-180411107968,-180411107904⟩ : DyadicInterval 40),(⟨749485326639,749485345968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25471904128,-25433405184⟩ : DyadicInterval 40),(⟨774840086208,774859354944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154858290624,154957266880⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180435613120,-180301348608⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1642_ok : ecellOkT e1642 = true := by decide +kernel
theorem e1642_pos {a z : ℝ} (ha1 : ((309747/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1239837/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1642 e1642_ok ha1 ha2 hz1 hz2 hz

-- box ['1239837/8192000', '620343/4096000', '7997/8000', '3999/4000']  interval_lower 126004081/1099511627776
noncomputable def e1643 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265919733006,0,true,154957266816,154957266880⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933103522546,0,false,-180435613120,-180435613056⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266033683858,0,true,155056234112,155056234176⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932989571694,0,false,-180569893952,-180569893888⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265857329966,0,true,154903065472,154903065536⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933165925586,0,false,-180362083712,-180362083648⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265992053345,0,true,155020078656,155020078720⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933031202207,0,false,-180520834240,-180520834176⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532779240,0,true,21151232,21151296⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490476312,0,false,-21151680,-21151616⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543378145,0,true,31749888,31749952⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479877407,0,false,-31750848,-31750784⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626859,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627370,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265888527179,0,true,154930162752,154930162816⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933134728373,0,false,-180398842688,-180398842624⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266012873002,0,true,155038160384,155038160448⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933010382550,0,false,-180545369024,-180545368960⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074298011147,0,false,-25507208640,-25507208576⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074335656958,0,false,-25468679936,-25468679872⟩
    { al := (1239837/8192000), au := (620343/4096000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨166408105230,166522056082⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154957266816,154957266880⟩ : DyadicInterval 40),(⟨-180435613120,-180435613056⟩ : DyadicInterval 40),(⟨749482154965,749482174294⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155056234112,155056234176⟩ : DyadicInterval 40),(⟨-180569893952,-180569893888⟩ : DyadicInterval 40),(⟨749464769237,749464788567⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154903065472,154903065536⟩ : DyadicInterval 40),(⟨-180362083712,-180362083648⟩ : DyadicInterval 40),(⟨749491670811,749491690140⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155020078656,155020078720⟩ : DyadicInterval 40),(⟨-180520834240,-180520834176⟩ : DyadicInterval 40),(⟨749471122315,749471141645⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21151464,31750369⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21151232,21151296⟩ : DyadicInterval 40),(⟨-21151680,-21151616⟩ : DyadicInterval 40),(⟨762123383369,762123402698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31749888,31749952⟩ : DyadicInterval 40),(⟨-31750848,-31750784⟩ : DyadicInterval 40),(⟨762123383115,762123402444⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166376899403,166501245226⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154930162752,154930162816⟩ : DyadicInterval 40),(⟨-180398842688,-180398842624⟩ : DyadicInterval 40),(⟨749486913973,749486933302⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155038160384,155038160448⟩ : DyadicInterval 40),(⟨-180545369024,-180545368960⟩ : DyadicInterval 40),(⟨749467945296,749467964626⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25507208640,-25468679872⟩ : DyadicInterval 40),(⟨774857723552,774877007200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154957266816,155056234176⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180569893952,-180435613056⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1643_ok : ecellOkT e1643 = true := by decide +kernel
theorem e1643_pos {a z : ℝ} (ha1 : ((1239837/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((620343/4096000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1643 e1643_ok ha1 ha2 hz1 hz2 hz

-- box ['620343/4096000', '248307/1638400', '1999/2000', '7997/8000']  interval_lower 63555475/549755813888
noncomputable def e1644 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266033683857,0,true,155056234112,155056234176⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932989571695,0,false,-180569893952,-180569893888⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266147634709,0,true,155155192512,155155192576⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932875620843,0,false,-180704191232,-180704191168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265950422828,0,true,154983922048,154983922112⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933072832724,0,false,-180471776704,-180471776640⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266085146207,0,true,155100926656,155100926720⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932938109345,0,false,-180630543104,-180630543040⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543377496,0,true,31749248,31749312⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479878056,0,false,-31750208,-31750144⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099553991378,0,true,42362752,42362816⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469264174,0,false,-42364480,-42364416⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626143,0,false,-1664,-1600⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626860,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265992049365,0,true,155020075200,155020075264⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933031206187,0,false,-180520829568,-180520829504⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266116394912,0,true,155128063808,155128063872⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932906860640,0,false,-180667371776,-180667371712⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074266648340,0,false,-25539307968,-25539307904⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074304317483,0,false,-25500754304,-25500754240⟩
    { al := (620343/4096000), au := (248307/1638400), zl := (1999/2000), zu := (7997/8000),
      A := ⟨166522056081,166636006933⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155056234112,155056234176⟩ : DyadicInterval 40),(⟨-180569893952,-180569893888⟩ : DyadicInterval 40),(⟨749464769238,749464788567⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155155192512,155155192576⟩ : DyadicInterval 40),(⟨-180704191232,-180704191168⟩ : DyadicInterval 40),(⟨749447371437,749447390766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154983922048,154983922112⟩ : DyadicInterval 40),(⟨-180471776704,-180471776640⟩ : DyadicInterval 40),(⟨749477473754,749477493083⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155100926656,155100926720⟩ : DyadicInterval 40),(⟨-180630543104,-180630543040⟩ : DyadicInterval 40),(⟨749456913582,749456932911⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨31749720,42363602⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31749248,31749312⟩ : DyadicInterval 40),(⟨-31750208,-31750144⟩ : DyadicInterval 40),(⟨762123383115,762123402444⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42362752,42362816⟩ : DyadicInterval 40),(⟨-42364480,-42364416⟩ : DyadicInterval 40),(⟨762123382783,762123402112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1664,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166480421589,166604767136⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155020075200,155020075264⟩ : DyadicInterval 40),(⟨-180520829568,-180520829504⟩ : DyadicInterval 40),(⟨749471122930,749471142259⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155128063808,155128063872⟩ : DyadicInterval 40),(⟨-180667371776,-180667371712⟩ : DyadicInterval 40),(⟨749452142261,749452161590⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25539307968,-25500754240⟩ : DyadicInterval 40),(⟨774873760736,774893056864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155056234112,155155192576⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180704191232,-180569893888⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1644_ok : ecellOkT e1644 = true := by decide +kernel
theorem e1644_pos {a z : ℝ} (ha1 : ((620343/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((248307/1638400 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1644 e1644_ok ha1 ha2 hz1 hz2 hz

-- box ['248307/1638400', '77649/512000', '1999/2000', '7997/8000']  interval_lower 16009937/137438953472
noncomputable def e1645 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266147634708,0,true,155155192512,155155192576⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932875620844,0,false,-180704191232,-180704191168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266261585560,0,true,155254141952,155254142016⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932761669992,0,false,-180838504896,-180838504832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266064316704,0,true,155082837504,155082837568⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932958938848,0,false,-180605994816,-180605994752⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266199054326,0,true,155199843904,155199843968⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932824201226,0,false,-180764797440,-180764797376⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543399959,0,true,31771712,31771776⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479855593,0,false,-31772672,-31772608⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554021332,0,true,42392704,42392768⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469234220,0,false,-42394432,-42394368⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626141,0,false,-1664,-1600⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626858,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266105971474,0,true,155119011904,155119011968⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932917284078,0,false,-180655086976,-180655086912⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266230324393,0,true,155226997120,155226997184⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932792931159,0,false,-180801655808,-180801655744⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074232109943,0,false,-25574658624,-25574658560⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074269807089,0,false,-25536075008,-25536074944⟩
    { al := (248307/1638400), au := (77649/512000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨166636006932,166749957784⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155155192512,155155192576⟩ : DyadicInterval 40),(⟨-180704191232,-180704191168⟩ : DyadicInterval 40),(⟨749447371437,749447390766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155254141952,155254142016⟩ : DyadicInterval 40),(⟨-180838504896,-180838504832⟩ : DyadicInterval 40),(⟨749429961571,749429980900⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155082837504,155082837568⟩ : DyadicInterval 40),(⟨-180605994816,-180605994752⟩ : DyadicInterval 40),(⟨749460093450,749460112780⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155199843904,155199843968⟩ : DyadicInterval 40),(⟨-180764797440,-180764797376⟩ : DyadicInterval 40),(⟨749439516870,749439536200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨31772183,42393556⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31771712,31771776⟩ : DyadicInterval 40),(⟨-31772672,-31772608⟩ : DyadicInterval 40),(⟨762123383113,762123402442⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42392704,42392768⟩ : DyadicInterval 40),(⟨-42394432,-42394368⟩ : DyadicInterval 40),(⟨762123382781,762123402110⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1664,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166594343698,166718696617⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155119011904,155119011968⟩ : DyadicInterval 40),(⟨-180655086976,-180655086912⟩ : DyadicInterval 40),(⟨749453733927,749453753256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155226997120,155226997184⟩ : DyadicInterval 40),(⟨-180801655808,-180801655744⟩ : DyadicInterval 40),(⟨749434739005,749434758335⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25574658624,-25536074944⟩ : DyadicInterval 40),(⟨774891421088,774910732192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155155192512,155254142016⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180838504896,-180704191168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1645_ok : ecellOkT e1645 = true := by decide +kernel
theorem e1645_pos {a z : ℝ} (ha1 : ((248307/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((77649/512000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1645 e1645_ok ha1 ha2 hz1 hz2 hz

-- box ['620343/4096000', '248307/1638400', '7997/8000', '3999/4000']  interval_lower 126970355/1099511627776
noncomputable def e1646 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266033683857,0,true,155056234112,155056234176⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932989571695,0,false,-180569893952,-180569893888⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266147634709,0,true,155155192512,155155192576⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932875620843,0,false,-180704191232,-180704191168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265971238085,0,true,155002000512,155002000576⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933052017467,0,false,-180496305216,-180496305152⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266105975708,0,true,155119015552,155119015616⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932917279844,0,false,-180655091968,-180655091904⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532794214,0,true,21166208,21166272⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490461338,0,false,-21166656,-21166592⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543400609,0,true,31772352,31772416⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479854943,0,false,-31773312,-31773248⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626857,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627369,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266002456918,0,true,155029114112,155029114176⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933020798634,0,false,-180533094208,-180533094144⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266126809607,0,true,155137107968,155137108032⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932896445945,0,false,-180679646464,-180679646400⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074263492044,0,false,-25542538496,-25542538432⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074301165706,0,false,-25503980032,-25503979968⟩
    { al := (620343/4096000), au := (248307/1638400), zl := (7997/8000), zu := (3999/4000),
      A := ⟨166522056081,166636006933⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155056234112,155056234176⟩ : DyadicInterval 40),(⟨-180569893952,-180569893888⟩ : DyadicInterval 40),(⟨749464769238,749464788567⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155155192512,155155192576⟩ : DyadicInterval 40),(⟨-180704191232,-180704191168⟩ : DyadicInterval 40),(⟨749447371437,749447390766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155002000512,155002000576⟩ : DyadicInterval 40),(⟨-180496305216,-180496305152⟩ : DyadicInterval 40),(⟨749474298238,749474317567⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155119015552,155119015616⟩ : DyadicInterval 40),(⟨-180655091968,-180655091904⟩ : DyadicInterval 40),(⟨749453733298,749453752627⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21166438,31772833⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21166208,21166272⟩ : DyadicInterval 40),(⟨-21166656,-21166592⟩ : DyadicInterval 40),(⟨762123383368,762123402697⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31772352,31772416⟩ : DyadicInterval 40),(⟨-31773312,-31773248⟩ : DyadicInterval 40),(⟨762123383113,762123402442⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166490829142,166615181831⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155029114112,155029114176⟩ : DyadicInterval 40),(⟨-180533094208,-180533094144⟩ : DyadicInterval 40),(⟨749469534825,749469554154⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155137107968,155137108032⟩ : DyadicInterval 40),(⟨-180679646464,-180679646400⟩ : DyadicInterval 40),(⟨749450551897,749450571226⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25542538496,-25503979968⟩ : DyadicInterval 40),(⟨774875373600,774894672128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155056234112,155155192576⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180704191232,-180569893888⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1646_ok : ecellOkT e1646 = true := by decide +kernel
theorem e1646_pos {a z : ℝ} (ha1 : ((620343/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((248307/1638400 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1646 e1646_ok ha1 ha2 hz1 hz2 hz

-- box ['248307/1638400', '77649/512000', '7997/8000', '3999/4000']  interval_lower 63969493/549755813888
noncomputable def e1647 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266147634708,0,true,155155192512,155155192576⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932875620844,0,false,-180704191232,-180704191168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266261585560,0,true,155254141952,155254142016⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932761669992,0,false,-180838504896,-180838504832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266085146205,0,true,155100926656,155100926720⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932938109347,0,false,-180630543104,-180630543040⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266219898071,0,true,155217943552,155217943616⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932803357481,0,false,-180789366016,-180789365952⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532809190,0,true,21181184,21181248⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490446362,0,false,-21181632,-21181568⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543423075,0,true,31794816,31794880⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099479832477,0,false,-31795776,-31795712⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626856,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627368,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266116386400,0,true,155128056384,155128056448⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932906869152,0,false,-180667361792,-180667361728⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266240746213,0,true,155236046720,155236046784⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932782509339,0,false,-180813940352,-180813940288⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074228949328,0,false,-25577893568,-25577893504⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074266650920,0,false,-25539305344,-25539305280⟩
    { al := (248307/1638400), au := (77649/512000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨166636006932,166749957784⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155155192512,155155192576⟩ : DyadicInterval 40),(⟨-180704191232,-180704191168⟩ : DyadicInterval 40),(⟨749447371437,749447390766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155254141952,155254142016⟩ : DyadicInterval 40),(⟨-180838504896,-180838504832⟩ : DyadicInterval 40),(⟨749429961571,749429980900⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155100926656,155100926720⟩ : DyadicInterval 40),(⟨-180630543104,-180630543040⟩ : DyadicInterval 40),(⟨749456913582,749456932912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155217943552,155217943616⟩ : DyadicInterval 40),(⟨-180789366016,-180789365952⟩ : DyadicInterval 40),(⟨749436332163,749436351493⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21181414,31795299⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21181184,21181248⟩ : DyadicInterval 40),(⟨-21181632,-21181568⟩ : DyadicInterval 40),(⟨762123383367,762123402696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31794816,31794880⟩ : DyadicInterval 40),(⟨-31795776,-31795712⟩ : DyadicInterval 40),(⟨762123383112,762123402441⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166604758624,166729118437⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155128056384,155128056448⟩ : DyadicInterval 40),(⟨-180667361792,-180667361728⟩ : DyadicInterval 40),(⟨749452143599,749452162929⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155236046720,155236046784⟩ : DyadicInterval 40),(⟨-180813940352,-180813940288⟩ : DyadicInterval 40),(⟨749433146392,749433165721⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25577893568,-25539305280⟩ : DyadicInterval 40),(⟨774893036256,774912349664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155155192512,155254142016⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180838504896,-180704191168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1647_ok : ecellOkT e1647 = true := by decide +kernel
theorem e1647_pos {a z : ℝ} (ha1 : ((248307/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((77649/512000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1647 e1647_ok ha1 ha2 hz1 hz2 hz

-- box ['309747/2048000', '1239837/8192000', '3999/4000', '7999/8000']  interval_lower 124900759/1099511627776
noncomputable def e1648 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265805782155,0,true,154858290624,154858290688⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933217473397,0,false,-180301348672,-180301348608⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265919733007,0,true,154957266816,154957266880⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933103522545,0,false,-180435613120,-180435613056⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265764208616,0,true,154822178176,154822178240⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933259046936,0,false,-180252368064,-180252368000⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265898931994,0,true,154939200000,154939200064⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933124323558,0,false,-180411102784,-180411102720⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522195914,0,true,10568064,10568128⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099501059638,0,false,-10568192,-10568128⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532779845,0,true,21151808,21151872⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490475707,0,false,-21152320,-21152256⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627369,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627675,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265784991026,0,true,154840230720,154840230784⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933238264526,0,false,-180276852928,-180276852864⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265909336868,0,true,154948237248,154948237312⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933113918684,0,false,-180423363008,-180423362944⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074329358765,0,false,-25475125760,-25475125696⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074366981164,0,false,-25436622144,-25436622080⟩
    { al := (309747/2048000), au := (1239837/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨166294154379,166408105231⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154858290624,154858290688⟩ : DyadicInterval 40),(⟨-180301348672,-180301348608⟩ : DyadicInterval 40),(⟨749499528593,749499547922⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154957266816,154957266880⟩ : DyadicInterval 40),(⟨-180435613120,-180435613056⟩ : DyadicInterval 40),(⟨749482154965,749482174294⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154822178176,154822178240⟩ : DyadicInterval 40),(⟨-180252368064,-180252368000⟩ : DyadicInterval 40),(⟨749505864142,749505883472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154939200000,154939200064⟩ : DyadicInterval 40),(⟨-180411102784,-180411102720⟩ : DyadicInterval 40),(⟨749485327320,749485346650⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10568138,21152069⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10568064,10568128⟩ : DyadicInterval 40),(⟨-10568192,-10568128⟩ : DyadicInterval 40),(⟨762123383514,762123402843⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21151808,21151872⟩ : DyadicInterval 40),(⟨-21152320,-21152256⟩ : DyadicInterval 40),(⟨762123383401,762123402730⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166273363250,166397709092⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154840230720,154840230784⟩ : DyadicInterval 40),(⟨-180276852928,-180276852864⟩ : DyadicInterval 40),(⟨749502697243,749502716573⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154948237248,154948237312⟩ : DyadicInterval 40),(⟨-180423363008,-180423362944⟩ : DyadicInterval 40),(⟨749483740512,749483759841⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25475125760,-25436622080⟩ : DyadicInterval 40),(⟨774841694656,774860965760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154858290624,154957266880⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180435613120,-180301348608⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1648_ok : ecellOkT e1648 = true := by decide +kernel
theorem e1648_pos {a z : ℝ} (ha1 : ((309747/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1239837/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1648 e1648_ok ha1 ha2 hz1 hz2 hz

-- box ['1239837/8192000', '620343/4096000', '3999/4000', '7999/8000']  interval_lower 3933251/34359738368
noncomputable def e1649 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265919733006,0,true,154957266816,154957266880⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933103522546,0,false,-180435613120,-180435613056⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266033683858,0,true,155056234112,155056234176⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932989571694,0,false,-180569893952,-180569893888⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265878130979,0,true,154921132864,154921132928⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933145124573,0,false,-180386592960,-180386592896⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266012868602,0,true,155038156544,155038156608⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933010386950,0,false,-180545363840,-180545363776⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522203401,0,true,10575552,10575616⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099501052151,0,false,-10575680,-10575616⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532794820,0,true,21166784,21166848⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490460732,0,false,-21167296,-21167232⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627368,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627675,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265898927630,0,true,154939196224,154939196288⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933124327922,0,false,-180411097600,-180411097536⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266023280599,0,true,155047199168,155047199232⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932999974953,0,false,-180557633984,-180557633920⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074294858962,0,false,-25510434816,-25510434752⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074332509290,0,false,-25471901376,-25471901312⟩
    { al := (1239837/8192000), au := (620343/4096000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨166408105230,166522056082⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154957266816,154957266880⟩ : DyadicInterval 40),(⟨-180435613120,-180435613056⟩ : DyadicInterval 40),(⟨749482154965,749482174294⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155056234112,155056234176⟩ : DyadicInterval 40),(⟨-180569893952,-180569893888⟩ : DyadicInterval 40),(⟨749464769237,749464788567⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154921132864,154921132928⟩ : DyadicInterval 40),(⟨-180386592960,-180386592896⟩ : DyadicInterval 40),(⟨749488499273,749488518602⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155038156544,155038156608⟩ : DyadicInterval 40),(⟨-180545363840,-180545363776⟩ : DyadicInterval 40),(⟨749467945979,749467965309⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10575625,21167044⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10575552,10575616⟩ : DyadicInterval 40),(⟨-10575680,-10575616⟩ : DyadicInterval 40),(⟨762123383514,762123402843⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21166784,21166848⟩ : DyadicInterval 40),(⟨-21167296,-21167232⟩ : DyadicInterval 40),(⟨762123383400,762123402729⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166387299854,166511652823⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154939196224,154939196288⟩ : DyadicInterval 40),(⟨-180411097600,-180411097536⟩ : DyadicInterval 40),(⟨749485327960,749485347289⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155047199168,155047199232⟩ : DyadicInterval 40),(⟨-180557633984,-180557633920⟩ : DyadicInterval 40),(⟨749466356990,749466376320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25510434816,-25471901312⟩ : DyadicInterval 40),(⟨774859334272,774878620288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154957266816,155056234176⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180569893952,-180435613056⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1649_ok : ecellOkT e1649 = true := by decide +kernel
theorem e1649_pos {a z : ℝ} (ha1 : ((1239837/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((620343/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1649 e1649_ok ha1 ha2 hz1 hz2 hz

-- box ['309747/2048000', '1239837/8192000', '7999/8000', '1']  interval_lower 124761027/1099511627776
noncomputable def e1650 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265805782155,0,true,154858290624,154858290688⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933217473397,0,false,-180301348672,-180301348608⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265919733007,0,true,154957266816,154957266880⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933103522545,0,false,-180435613120,-180435613056⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265784995385,0,true,154840234560,154840234624⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933238260167,0,false,-180276858112,-180276858048⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522203961,0,true,10576128,10576192⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099501051591,0,false,-10576256,-10576192⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627674,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1265795384379,0,true,154849258816,154849258880⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨933227871173,0,false,-180289098112,-180289098048⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1265919737363,0,true,154957270592,154957270656⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨933103518189,0,false,-180435618240,-180435618176⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1074326210690,0,false,-25478347648,-25478347584⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1074363837602,0,false,-25439839296,-25439839232⟩
    { al := (309747/2048000), au := (1239837/8192000), zl := (7999/8000), zu := 1,
      A := ⟨166294154379,166408105231⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154858290624,154858290688⟩ : DyadicInterval 40),(⟨-180301348672,-180301348608⟩ : DyadicInterval 40),(⟨749499528593,749499547922⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154957266816,154957266880⟩ : DyadicInterval 40),(⟨-180435613120,-180435613056⟩ : DyadicInterval 40),(⟨749482154965,749482174294⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154840234560,154840234624⟩ : DyadicInterval 40),(⟨-180276858112,-180276858048⟩ : DyadicInterval 40),(⟨749502696569,749502715898⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154957266816,154957266880⟩ : DyadicInterval 40),(⟨-180435613120,-180435613056⟩ : DyadicInterval 40),(⟨749482154965,749482174294⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10576185⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10576128,10576192⟩ : DyadicInterval 40),(⟨-10576256,-10576192⟩ : DyadicInterval 40),(⟨762123383514,762123402843⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨166283756603,166408109587⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154849258816,154849258880⟩ : DyadicInterval 40),(⟨-180289098112,-180289098048⟩ : DyadicInterval 40),(⟨749501113283,749501132613⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154957270592,154957270656⟩ : DyadicInterval 40),(⟨-180435618240,-180435618176⟩ : DyadicInterval 40),(⟨749482154299,749482173629⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25478347648,-25439839232⟩ : DyadicInterval 40),(⟨774843303232,774862576704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨154858290624,154957266880⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180435613120,-180301348608⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1650_ok : ecellOkT e1650 = true := by decide +kernel
theorem e1650_pos {a z : ℝ} (ha1 : ((309747/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1239837/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1650 e1650_ok ha1 ha2 hz1 hz2 hz

-- box ['1239837/8192000', '620343/4096000', '7999/8000', '1']  interval_lower 62862051/549755813888
noncomputable def e1651 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265919733006,0,true,154957266816,154957266880⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933103522546,0,false,-180435613120,-180435613056⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266033683858,0,true,155056234112,155056234176⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932989571694,0,false,-180569893952,-180569893888⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265898931992,0,true,154939200000,154939200064⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933124323560,0,false,-180411102784,-180411102720⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522211449,0,true,10583616,10583680⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099501044103,0,false,-10583744,-10583680⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627674,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1265909328361,0,true,154948229824,154948229888⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨933113927191,0,false,-180423353024,-180423352960⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1266033688217,0,true,155056237888,155056237952⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨932989567335,0,false,-180569899136,-180569899072⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1074291706573,0,false,-25513661184,-25513661120⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1074329361341,0,false,-25475123136,-25475123072⟩
    { al := (1239837/8192000), au := (620343/4096000), zl := (7999/8000), zu := 1,
      A := ⟨166408105230,166522056082⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154957266816,154957266880⟩ : DyadicInterval 40),(⟨-180435613120,-180435613056⟩ : DyadicInterval 40),(⟨749482154965,749482174294⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155056234112,155056234176⟩ : DyadicInterval 40),(⟨-180569893952,-180569893888⟩ : DyadicInterval 40),(⟨749464769237,749464788567⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154939200000,154939200064⟩ : DyadicInterval 40),(⟨-180411102784,-180411102720⟩ : DyadicInterval 40),(⟨749485327321,749485346650⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155056234112,155056234176⟩ : DyadicInterval 40),(⟨-180569893952,-180569893888⟩ : DyadicInterval 40),(⟨749464769237,749464788567⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10583673⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10583616,10583680⟩ : DyadicInterval 40),(⟨-10583744,-10583680⟩ : DyadicInterval 40),(⟨762123383514,762123402843⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨166397700585,166522060441⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154948229824,154948229888⟩ : DyadicInterval 40),(⟨-180423353024,-180423352960⟩ : DyadicInterval 40),(⟨749483741847,749483761176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155056237888,155056237952⟩ : DyadicInterval 40),(⟨-180569899136,-180569899072⟩ : DyadicInterval 40),(⟨749464768598,749464787927⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25513661184,-25475123072⟩ : DyadicInterval 40),(⟨774860945152,774880233472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨154957266816,155056234176⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180569893952,-180435613056⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1651_ok : ecellOkT e1651 = true := by decide +kernel
theorem e1651_pos {a z : ℝ} (ha1 : ((1239837/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((620343/4096000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1651 e1651_ok ha1 ha2 hz1 hz2 hz

-- box ['620343/4096000', '248307/1638400', '3999/4000', '7999/8000']  interval_lower 126829591/1099511627776
noncomputable def e1652 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266033683857,0,true,155056234112,155056234176⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932989571695,0,false,-180569893952,-180569893888⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266147634709,0,true,155155192512,155155192576⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932875620843,0,false,-180704191232,-180704191168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265992053342,0,true,155020078656,155020078720⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933031202210,0,false,-180520834240,-180520834176⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266126805209,0,true,155137104192,155137104256⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932896450343,0,false,-180679641280,-180679641216⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522210889,0,true,10583040,10583104⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099501044663,0,false,-10583168,-10583104⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532809795,0,true,21181760,21181824⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490445757,0,false,-21182272,-21182208⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627367,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627675,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266012864235,0,true,155038152768,155038152832⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933010391317,0,false,-180545358720,-180545358656⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266137224329,0,true,155146152192,155146152256⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932886031223,0,false,-180691921344,-180691921280⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074260335542,0,false,-25545769152,-25545769088⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074298013803,0,false,-25507205888,-25507205824⟩
    { al := (620343/4096000), au := (248307/1638400), zl := (3999/4000), zu := (7999/8000),
      A := ⟨166522056081,166636006933⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155056234112,155056234176⟩ : DyadicInterval 40),(⟨-180569893952,-180569893888⟩ : DyadicInterval 40),(⟨749464769238,749464788567⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155155192512,155155192576⟩ : DyadicInterval 40),(⟨-180704191232,-180704191168⟩ : DyadicInterval 40),(⟨749447371437,749447390766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155020078656,155020078720⟩ : DyadicInterval 40),(⟨-180520834240,-180520834176⟩ : DyadicInterval 40),(⟨749471122316,749471141645⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155137104192,155137104256⟩ : DyadicInterval 40),(⟨-180679641280,-180679641216⟩ : DyadicInterval 40),(⟨749450552543,749450571873⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10583113,21182019⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10583040,10583104⟩ : DyadicInterval 40),(⟨-10583168,-10583104⟩ : DyadicInterval 40),(⟨762123383514,762123402843⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21181760,21181824⟩ : DyadicInterval 40),(⟨-21182272,-21182208⟩ : DyadicInterval 40),(⟨762123383399,762123402728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166501236459,166625596553⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155038152768,155038152832⟩ : DyadicInterval 40),(⟨-180545358720,-180545358656⟩ : DyadicInterval 40),(⟨749467946647,749467965976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155146152192,155146152256⟩ : DyadicInterval 40),(⟨-180691921344,-180691921280⟩ : DyadicInterval 40),(⟨749448961371,749448980700⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25545769152,-25507205824⟩ : DyadicInterval 40),(⟨774876986528,774896287456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155056234112,155155192576⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180704191232,-180569893888⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1652_ok : ecellOkT e1652 = true := by decide +kernel
theorem e1652_pos {a z : ℝ} (ha1 : ((620343/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((248307/1638400 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1652 e1652_ok ha1 ha2 hz1 hz2 hz

-- box ['248307/1638400', '77649/512000', '3999/4000', '7999/8000']  interval_lower 127797945/1099511627776
noncomputable def e1653 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266147634708,0,true,155155192512,155155192576⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932875620844,0,false,-180704191232,-180704191168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266261585560,0,true,155254141952,155254142016⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932761669992,0,false,-180838504896,-180838504832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266105975706,0,true,155119015552,155119015616⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932917279846,0,false,-180655091968,-180655091904⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266240741816,0,true,155236042944,155236043008⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932782513736,0,false,-180813935168,-180813935104⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522218377,0,true,10590528,10590592⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099501037175,0,false,-10590656,-10590592⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532824773,0,true,21196736,21196800⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490430779,0,false,-21197248,-21197184⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627367,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627674,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266126800839,0,true,155137100416,155137100480⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932896454713,0,false,-180679636160,-180679636096⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266251168055,0,true,155245096256,155245096320⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932772087497,0,false,-180826225088,-180826225024⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074225788508,0,false,-25581128832,-25581128768⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074263494702,0,false,-25542535744,-25542535680⟩
    { al := (248307/1638400), au := (77649/512000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨166636006932,166749957784⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155155192512,155155192576⟩ : DyadicInterval 40),(⟨-180704191232,-180704191168⟩ : DyadicInterval 40),(⟨749447371437,749447390766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155254141952,155254142016⟩ : DyadicInterval 40),(⟨-180838504896,-180838504832⟩ : DyadicInterval 40),(⟨749429961571,749429980900⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155119015552,155119015616⟩ : DyadicInterval 40),(⟨-180655091968,-180655091904⟩ : DyadicInterval 40),(⟨749453733298,749453752627⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155236042944,155236043008⟩ : DyadicInterval 40),(⟨-180813935168,-180813935104⟩ : DyadicInterval 40),(⟨749433147039,749433166368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10590601,21196997⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10590528,10590592⟩ : DyadicInterval 40),(⟨-10590656,-10590592⟩ : DyadicInterval 40),(⟨762123383513,762123402842⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21196736,21196800⟩ : DyadicInterval 40),(⟨-21197248,-21197184⟩ : DyadicInterval 40),(⟨762123383399,762123402728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166615173063,166739540279⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155137100416,155137100480⟩ : DyadicInterval 40),(⟨-180679636160,-180679636096⟩ : DyadicInterval 40),(⟨749450553213,749450572542⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155245096256,155245096320⟩ : DyadicInterval 40),(⟨-180826225088,-180826225024⟩ : DyadicInterval 40),(⟨749431553690,749431573020⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25581128832,-25542535680⟩ : DyadicInterval 40),(⟨774894651456,774913967296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155155192512,155254142016⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180838504896,-180704191168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1653_ok : ecellOkT e1653 = true := by decide +kernel
theorem e1653_pos {a z : ℝ} (ha1 : ((248307/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((77649/512000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1653 e1653_ok ha1 ha2 hz1 hz2 hz

-- box ['620343/4096000', '248307/1638400', '7999/8000', '1']  interval_lower 126689043/1099511627776
noncomputable def e1654 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266033683857,0,true,155056234112,155056234176⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932989571695,0,false,-180569893952,-180569893888⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266147634709,0,true,155155192512,155155192576⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932875620843,0,false,-180704191232,-180704191168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266012868599,0,true,155038156544,155038156608⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933010386953,0,false,-180545363840,-180545363776⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522218937,0,true,10591104,10591168⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099501036615,0,false,-10591232,-10591168⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627673,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1266023271833,0,true,155047191552,155047191616⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨932999983719,0,false,-180557623680,-180557623616⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1266147639068,0,true,155155196288,155155196352⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨932875616484,0,false,-180704196352,-180704196288⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1074257178838,0,false,-25549000064,-25549000000⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1074294861618,0,false,-25510432064,-25510432000⟩
    { al := (620343/4096000), au := (248307/1638400), zl := (7999/8000), zu := 1,
      A := ⟨166522056081,166636006933⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155056234112,155056234176⟩ : DyadicInterval 40),(⟨-180569893952,-180569893888⟩ : DyadicInterval 40),(⟨749464769238,749464788567⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155155192512,155155192576⟩ : DyadicInterval 40),(⟨-180704191232,-180704191168⟩ : DyadicInterval 40),(⟨749447371437,749447390766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155038156544,155038156608⟩ : DyadicInterval 40),(⟨-180545363840,-180545363776⟩ : DyadicInterval 40),(⟨749467945979,749467965309⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155155192512,155155192576⟩ : DyadicInterval 40),(⟨-180704191232,-180704191168⟩ : DyadicInterval 40),(⟨749447371437,749447390766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10591161⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10591104,10591168⟩ : DyadicInterval 40),(⟨-10591232,-10591168⟩ : DyadicInterval 40),(⟨762123383513,762123402842⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨166511644057,166636011292⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155047191552,155047191616⟩ : DyadicInterval 40),(⟨-180557623680,-180557623616⟩ : DyadicInterval 40),(⟨749466358341,749466377671⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155155196288,155155196352⟩ : DyadicInterval 40),(⟨-180704196352,-180704196288⟩ : DyadicInterval 40),(⟨749447370769,749447390099⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25549000064,-25510432000⟩ : DyadicInterval 40),(⟨774878599616,774897902912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨155056234112,155155192576⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180704191232,-180569893888⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1654_ok : ecellOkT e1654 = true := by decide +kernel
theorem e1654_pos {a z : ℝ} (ha1 : ((620343/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((248307/1638400 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1654 e1654_ok ha1 ha2 hz1 hz2 hz

-- box ['248307/1638400', '77649/512000', '7999/8000', '1']  interval_lower 127657153/1099511627776
noncomputable def e1655 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266147634708,0,true,155155192512,155155192576⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932875620844,0,false,-180704191232,-180704191168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266261585560,0,true,155254141952,155254142016⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932761669992,0,false,-180838504896,-180838504832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266126805207,0,true,155137104192,155137104256⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932896450345,0,false,-180679641280,-180679641216⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522226425,0,true,10598592,10598656⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099501029127,0,false,-10598720,-10598656⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627673,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1266137215561,0,true,155146144576,155146144640⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨932886039991,0,false,-180691911040,-180691910976⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1266261589913,0,true,155254145728,155254145792⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨932761665639,0,false,-180838510016,-180838509952⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1074222627486,0,false,-25584364224,-25584364160⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1074260338201,0,false,-25545766464,-25545766400⟩
    { al := (248307/1638400), au := (77649/512000), zl := (7999/8000), zu := 1,
      A := ⟨166636006932,166749957784⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155155192512,155155192576⟩ : DyadicInterval 40),(⟨-180704191232,-180704191168⟩ : DyadicInterval 40),(⟨749447371437,749447390766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155254141952,155254142016⟩ : DyadicInterval 40),(⟨-180838504896,-180838504832⟩ : DyadicInterval 40),(⟨749429961571,749429980900⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155137104192,155137104256⟩ : DyadicInterval 40),(⟨-180679641280,-180679641216⟩ : DyadicInterval 40),(⟨749450552543,749450571873⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155254141952,155254142016⟩ : DyadicInterval 40),(⟨-180838504896,-180838504832⟩ : DyadicInterval 40),(⟨749429961571,749429980900⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10598649⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10598592,10598656⟩ : DyadicInterval 40),(⟨-10598720,-10598656⟩ : DyadicInterval 40),(⟨762123383513,762123402842⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨166625587785,166749962137⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155146144576,155146144640⟩ : DyadicInterval 40),(⟨-180691911040,-180691910976⟩ : DyadicInterval 40),(⟨749448962724,749448982054⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155254145728,155254145792⟩ : DyadicInterval 40),(⟨-180838510016,-180838509952⟩ : DyadicInterval 40),(⟨749429960903,749429980233⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25584364224,-25545766400⟩ : DyadicInterval 40),(⟨774896266816,774915584992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨155155192512,155254142016⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180838504896,-180704191168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1655_ok : ecellOkT e1655 = true := by decide +kernel
theorem e1655_pos {a z : ℝ} (ha1 : ((248307/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((77649/512000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1655 e1655_ok ha1 ha2 hz1 hz2 hz

-- box ['77649/512000', '1243233/8192000', '999/1000', '7993/8000']  interval_lower 64807227/549755813888
noncomputable def e1656 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266261585559,0,true,155254141952,155254142016⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932761669993,0,false,-180838504896,-180838504832⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266375536411,0,true,155353082560,155353082624⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932647719141,0,false,-180972834944,-180972834880⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266094835601,0,true,155109341248,155109341312⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932928419951,0,false,-180641962560,-180641962496⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266229530491,0,true,155226307776,155226307840⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932793725061,0,false,-180800720000,-180800719936⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585815001,0,true,74184704,74184768⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437440551,0,false,-74189760,-74189696⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099596473820,0,true,84842752,84842816⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099426781732,0,false,-84849344,-84849280⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621228,0,false,-6592,-6528⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622771,0,false,-5056,-4992⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266178206865,0,true,155181740736,155181740800⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932845048687,0,false,-180740224960,-180740224896⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266302538342,0,true,155289701248,155289701312⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932720717210,0,false,-180886779840,-180886779776⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074210205631,0,false,-25597078592,-25597078528⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074247912611,0,false,-25558484160,-25558484096⟩
    { al := (77649/512000), au := (1243233/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨166749957783,166863908635⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155254141952,155254142016⟩ : DyadicInterval 40),(⟨-180838504896,-180838504832⟩ : DyadicInterval 40),(⟨749429961571,749429980900⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155353082560,155353082624⟩ : DyadicInterval 40),(⟨-180972834944,-180972834880⟩ : DyadicInterval 40),(⟨749412539565,749412558895⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155109341248,155109341312⟩ : DyadicInterval 40),(⟨-180641962560,-180641962496⟩ : DyadicInterval 40),(⟨749455434211,749455453540⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155226307776,155226307840⟩ : DyadicInterval 40),(⟨-180800720000,-180800719936⟩ : DyadicInterval 40),(⟨749434860298,749434879627⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨74187225,84846044⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74184704,74184768⟩ : DyadicInterval 40),(⟨-74189760,-74189696⟩ : DyadicInterval 40),(⟨762123381074,762123400403⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨84842752,84842816⟩ : DyadicInterval 40),(⟨-84849344,-84849280⟩ : DyadicInterval 40),(⟨762123380300,762123399629⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6592,-4992⟩ : DyadicInterval 40),(⟨762123386112,762123406176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166666579089,166790910566⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155181740736,155181740800⟩ : DyadicInterval 40),(⟨-180740224960,-180740224896⟩ : DyadicInterval 40),(⟨749442701707,749442721037⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155289701248,155289701312⟩ : DyadicInterval 40),(⟨-180886779840,-180886779776⟩ : DyadicInterval 40),(⟨749423701648,749423720978⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25597078592,-25558484096⟩ : DyadicInterval 40),(⟨774902625664,774921942176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155254141952,155353082624⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180972834944,-180838504832⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1656_ok : ecellOkT e1656 = true := by decide +kernel
theorem e1656_pos {a z : ℝ} (ha1 : ((77649/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1243233/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1656 e1656_ok ha1 ha2 hz1 hz2 hz

-- box ['1243233/8192000', '622041/4096000', '999/1000', '7993/8000']  interval_lower 130589939/1099511627776
noncomputable def e1657 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266375536410,0,true,155353082560,155353082624⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932647719142,0,false,-180972834944,-180972834880⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266489487262,0,true,155452014208,155452014272⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932533768290,0,false,-181107181440,-181107181376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266208672501,0,true,155208195904,155208195968⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932814583051,0,false,-180776134336,-180776134272⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266343381635,0,true,155325164288,155325164352⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932679873917,0,false,-180934927872,-180934927808⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585867422,0,true,74237120,74237184⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437388130,0,false,-74242176,-74242112⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099596533734,0,true,84902656,84902720⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099426721818,0,false,-84909248,-84909184⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621219,0,false,-6592,-6528⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622764,0,false,-5056,-4992⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266292100740,0,true,155280638400,155280638464⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932731154812,0,false,-180874475840,-180874475776⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266416439341,0,true,155388595328,155388595392⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932606816211,0,false,-181021057088,-181021057024⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074175637305,0,false,-25632461696,-25632461632⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074213372206,0,false,-25593837440,-25593837376⟩
    { al := (1243233/8192000), au := (622041/4096000), zl := (999/1000), zu := (7993/8000),
      A := ⟨166863908634,166977859486⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155353082560,155353082624⟩ : DyadicInterval 40),(⟨-180972834944,-180972834880⟩ : DyadicInterval 40),(⟨749412539565,749412558895⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155452014208,155452014272⟩ : DyadicInterval 40),(⟨-181107181440,-181107181376⟩ : DyadicInterval 40),(⟨749395105519,749395124849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155208195904,155208195968⟩ : DyadicInterval 40),(⟨-180776134336,-180776134272⟩ : DyadicInterval 40),(⟨749438047346,749438066675⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155325164288,155325164352⟩ : DyadicInterval 40),(⟨-180934927872,-180934927808⟩ : DyadicInterval 40),(⟨749417456949,749417476278⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨74239646,84905958⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74237120,74237184⟩ : DyadicInterval 40),(⟨-74242176,-74242112⟩ : DyadicInterval 40),(⟨762123381067,762123400396⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨84902656,84902720⟩ : DyadicInterval 40),(⟨-84909248,-84909184⟩ : DyadicInterval 40),(⟨762123380291,762123399620⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6592,-4992⟩ : DyadicInterval 40),(⟨762123386112,762123406176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166780472964,166904811565⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155280638400,155280638464⟩ : DyadicInterval 40),(⟨-180874475840,-180874475776⟩ : DyadicInterval 40),(⟨749425297250,749425316580⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155388595328,155388595392⟩ : DyadicInterval 40),(⟨-181021057088,-181021057024⟩ : DyadicInterval 40),(⟨749406282983,749406302313⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25632461696,-25593837376⟩ : DyadicInterval 40),(⟨774920302304,774939633728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155353082560,155452014272⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181107181440,-180972834880⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1657_ok : ecellOkT e1657 = true := by decide +kernel
theorem e1657_pos {a z : ℝ} (ha1 : ((1243233/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((622041/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1657 e1657_ok ha1 ha2 hz1 hz2 hz

-- box ['77649/512000', '1243233/8192000', '7993/8000', '3997/4000']  interval_lower 129473747/1099511627776
noncomputable def e1658 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266261585559,0,true,155254141952,155254142016⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932761669993,0,false,-180838504896,-180838504832⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266375536411,0,true,155353082560,155353082624⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932647719141,0,false,-180972834944,-180972834880⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266115679345,0,true,155127442368,155127442432⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932907576207,0,false,-180666528448,-180666528384⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266250388480,0,true,155244419328,155244419392⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932772867072,0,false,-180825306176,-180825306112⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575216925,0,true,63587264,63587328⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448038627,0,false,-63591040,-63590976⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585868255,0,true,74237952,74238016⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437387297,0,false,-74243008,-74242944⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622763,0,false,-5056,-4992⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624099,0,false,-3712,-3648⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266188628571,0,true,155190790656,155190790720⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932834626981,0,false,-180752508736,-180752508672⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266312967196,0,true,155298756416,155298756480⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932710288356,0,false,-180899073728,-180899073664⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074207041512,0,false,-25600317248,-25600317184⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074244753018,0,false,-25561718080,-25561718016⟩
    { al := (77649/512000), au := (1243233/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨166749957783,166863908635⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155254141952,155254142016⟩ : DyadicInterval 40),(⟨-180838504896,-180838504832⟩ : DyadicInterval 40),(⟨749429961571,749429980900⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155353082560,155353082624⟩ : DyadicInterval 40),(⟨-180972834944,-180972834880⟩ : DyadicInterval 40),(⟨749412539565,749412558895⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155127442368,155127442432⟩ : DyadicInterval 40),(⟨-180666528448,-180666528384⟩ : DyadicInterval 40),(⟨749452251560,749452270889⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155244419328,155244419392⟩ : DyadicInterval 40),(⟨-180825306176,-180825306112⟩ : DyadicInterval 40),(⟨749431672842,749431692171⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨63589149,74240479⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63587264,63587328⟩ : DyadicInterval 40),(⟨-63591040,-63590976⟩ : DyadicInterval 40),(⟨762123381762,762123401091⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74237952,74238016⟩ : DyadicInterval 40),(⟨-74243008,-74242944⟩ : DyadicInterval 40),(⟨762123381067,762123400396⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5056,-3648⟩ : DyadicInterval 40),(⟨762123385440,762123405408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166677000795,166801339420⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155190790656,155190790720⟩ : DyadicInterval 40),(⟨-180752508736,-180752508672⟩ : DyadicInterval 40),(⟨749441109612,749441128942⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155298756416,155298756480⟩ : DyadicInterval 40),(⟨-180899073728,-180899073664⟩ : DyadicInterval 40),(⟨749422107315,749422126644⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25600317248,-25561718016⟩ : DyadicInterval 40),(⟨774904242624,774923561504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155254141952,155353082624⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180972834944,-180838504832⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1658_ok : ecellOkT e1658 = true := by decide +kernel
theorem e1658_pos {a z : ℝ} (ha1 : ((77649/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1243233/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1658 e1658_ok ha1 ha2 hz1 hz2 hz

-- box ['1243233/8192000', '622041/4096000', '7993/8000', '3997/4000']  interval_lower 130449017/1099511627776
noncomputable def e1659 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266375536410,0,true,155353082560,155353082624⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932647719142,0,false,-180972834944,-180972834880⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266489487262,0,true,155452014208,155452014272⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932533768290,0,false,-181107181440,-181107181376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266229530489,0,true,155226307776,155226307840⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932793725063,0,false,-180800720000,-180800719936⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266364253868,0,true,155343286592,155343286656⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932659001684,0,false,-180959533888,-180959533824⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575261857,0,true,63632192,63632256⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447993695,0,false,-63635968,-63635904⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585920680,0,true,74290368,74290432⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437334872,0,false,-74295424,-74295360⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622756,0,false,-5056,-4992⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624094,0,false,-3712,-3648⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266302529826,0,true,155289693824,155289693888⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932720725726,0,false,-180886769856,-180886769792⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266426875314,0,true,155397655872,155397655936⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932596380238,0,false,-181033360768,-181033360704⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074172468865,0,false,-25635704896,-25635704832⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074210208215,0,false,-25597075968,-25597075904⟩
    { al := (1243233/8192000), au := (622041/4096000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨166863908634,166977859486⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155353082560,155353082624⟩ : DyadicInterval 40),(⟨-180972834944,-180972834880⟩ : DyadicInterval 40),(⟨749412539565,749412558895⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155452014208,155452014272⟩ : DyadicInterval 40),(⟨-181107181440,-181107181376⟩ : DyadicInterval 40),(⟨749395105519,749395124849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155226307776,155226307840⟩ : DyadicInterval 40),(⟨-180800720000,-180800719936⟩ : DyadicInterval 40),(⟨749434860298,749434879628⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155343286592,155343286656⟩ : DyadicInterval 40),(⟨-180959533888,-180959533824⟩ : DyadicInterval 40),(⟨749414265116,749414284445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨63634081,74292904⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63632192,63632256⟩ : DyadicInterval 40),(⟨-63635968,-63635904⟩ : DyadicInterval 40),(⟨762123381757,762123401086⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74290368,74290432⟩ : DyadicInterval 40),(⟨-74295424,-74295360⟩ : DyadicInterval 40),(⟨762123381059,762123400389⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5056,-3648⟩ : DyadicInterval 40),(⟨762123385440,762123405408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166790902050,166915247538⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155289693824,155289693888⟩ : DyadicInterval 40),(⟨-180886769856,-180886769792⟩ : DyadicInterval 40),(⟨749423702991,749423722320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155397655872,155397655936⟩ : DyadicInterval 40),(⟨-181033360768,-181033360704⟩ : DyadicInterval 40),(⟨749404686406,749404705735⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25635704896,-25597075904⟩ : DyadicInterval 40),(⟨774921921568,774941255328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155353082560,155452014272⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181107181440,-180972834880⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1659_ok : ecellOkT e1659 = true := by decide +kernel
theorem e1659_pos {a z : ℝ} (ha1 : ((1243233/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((622041/4096000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1659 e1659_ok ha1 ha2 hz1 hz2 hz

-- box ['622041/4096000', '1244931/8192000', '999/1000', '7993/8000']  interval_lower 65783919/549755813888
noncomputable def e1660 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266489487261,0,true,155452014208,155452014272⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932533768291,0,false,-181107181440,-181107181376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266603438113,0,true,155550936960,155550937024⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932419817439,0,false,-181241544320,-181241544256⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266322509401,0,true,155307041664,155307041728⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932700746151,0,false,-180910322432,-180910322368⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266457232780,0,true,155424011904,155424011968⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932566022772,0,false,-181069152192,-181069152128⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585919846,0,true,74289536,74289600⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437335706,0,false,-74294592,-74294528⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099596593653,0,true,84962560,84962624⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099426661899,0,false,-84969216,-84969152⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621210,0,false,-6592,-6528⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622757,0,false,-5056,-4992⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266405994613,0,true,155379527104,155379527168⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932617260939,0,false,-181008743168,-181008743104⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266530340338,0,true,155487480512,155487480576⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932492915214,0,false,-181155350656,-181155350592⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074141045381,0,false,-25667870080,-25667870016⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074178808206,0,false,-25629216000,-25629215936⟩
    { al := (622041/4096000), au := (1244931/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨166977859485,167091810337⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155452014208,155452014272⟩ : DyadicInterval 40),(⟨-181107181440,-181107181376⟩ : DyadicInterval 40),(⟨749395105519,749395124849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155550936960,155550937024⟩ : DyadicInterval 40),(⟨-181241544320,-181241544256⟩ : DyadicInterval 40),(⟨749377659368,749377678697⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155307041664,155307041728⟩ : DyadicInterval 40),(⟨-180910322432,-180910322368⟩ : DyadicInterval 40),(⟨749420648399,749420667729⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155424011904,155424011968⟩ : DyadicInterval 40),(⟨-181069152192,-181069152128⟩ : DyadicInterval 40),(⟨749400041564,749400060894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨74292070,84965877⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74289536,74289600⟩ : DyadicInterval 40),(⟨-74294592,-74294528⟩ : DyadicInterval 40),(⟨762123381060,762123400389⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨84962560,84962624⟩ : DyadicInterval 40),(⟨-84969216,-84969152⟩ : DyadicInterval 40),(⟨762123380313,762123399643⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6592,-4992⟩ : DyadicInterval 40),(⟨762123386112,762123406176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166894366837,167018712562⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155379527104,155379527168⟩ : DyadicInterval 40),(⟨-181008743168,-181008743104⟩ : DyadicInterval 40),(⟨749407880777,749407900107⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155487480512,155487480576⟩ : DyadicInterval 40),(⟨-181155350656,-181155350592⟩ : DyadicInterval 40),(⟨749388852208,749388871538⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25667870080,-25629215936⟩ : DyadicInterval 40),(⟨774937991584,774957337920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155452014208,155550937024⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181241544320,-181107181376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1660_ok : ecellOkT e1660 = true := by decide +kernel
theorem e1660_pos {a z : ℝ} (ha1 : ((622041/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1244931/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1660 e1660_ok ha1 ha2 hz1 hz2 hz

-- box ['1244931/8192000', '62289/409600', '999/1000', '7993/8000']  interval_lower 8284271/68719476736
noncomputable def e1661 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266603438112,0,true,155550936960,155550937024⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932419817440,0,false,-181241544320,-181241544256⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266717388964,0,true,155649850880,155649850944⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932305866588,0,false,-181375923648,-181375923584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266436346301,0,true,155405878528,155405878592⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932586909251,0,false,-181044526912,-181044526848⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266571083924,0,true,155522850624,155522850688⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932452171628,0,false,-181203392896,-181203392832⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585972275,0,true,74341952,74342016⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437283277,0,false,-74347072,-74347008⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099596653575,0,true,85022464,85022528⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099426601977,0,false,-85029120,-85029056⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621200,0,false,-6592,-6528⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622750,0,false,-5056,-4992⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266519888486,0,true,155478406912,155478406976⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932503367066,0,false,-181143026816,-181143026752⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266644241338,0,true,155586356800,155586356864⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932379014214,0,false,-181289660672,-181289660608⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074106429858,0,false,-25703303808,-25703303744⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074144220611,0,false,-25664619904,-25664619840⟩
    { al := (1244931/8192000), au := (62289/409600), zl := (999/1000), zu := (7993/8000),
      A := ⟨167091810336,167205761188⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155550936960,155550937024⟩ : DyadicInterval 40),(⟨-181241544320,-181241544256⟩ : DyadicInterval 40),(⟨749377659368,749377678698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155649850880,155649850944⟩ : DyadicInterval 40),(⟨-181375923648,-181375923584⟩ : DyadicInterval 40),(⟨749360201100,749360220430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155405878528,155405878592⟩ : DyadicInterval 40),(⟨-181044526912,-181044526848⟩ : DyadicInterval 40),(⟨749403237397,749403256727⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155522850624,155522850688⟩ : DyadicInterval 40),(⟨-181203392896,-181203392832⟩ : DyadicInterval 40),(⟨749382614118,749382633447⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨74344499,85025799⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74341952,74342016⟩ : DyadicInterval 40),(⟨-74347072,-74347008⟩ : DyadicInterval 40),(⟨762123381084,762123400414⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨85022464,85022528⟩ : DyadicInterval 40),(⟨-85029120,-85029056⟩ : DyadicInterval 40),(⟨762123380304,762123399634⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6592,-4992⟩ : DyadicInterval 40),(⟨762123386112,762123406176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167008260710,167132613562⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155478406912,155478406976⟩ : DyadicInterval 40),(⟨-181143026816,-181143026752⟩ : DyadicInterval 40),(⟨749390452198,749390471527⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155586356800,155586356864⟩ : DyadicInterval 40),(⟨-181289660672,-181289660608⟩ : DyadicInterval 40),(⟨749371409375,749371428705⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25703303808,-25664619840⟩ : DyadicInterval 40),(⟨774955693536,774975054784⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155550936960,155649850944⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181375923648,-181241544256⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1661_ok : ecellOkT e1661 = true := by decide +kernel
theorem e1661_pos {a z : ℝ} (ha1 : ((1244931/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((62289/409600 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1661 e1661_ok ha1 ha2 hz1 hz2 hz

-- box ['622041/4096000', '1244931/8192000', '7993/8000', '3997/4000']  interval_lower 32856675/274877906944
noncomputable def e1662 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266489487261,0,true,155452014208,155452014272⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932533768291,0,false,-181107181440,-181107181376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266603438113,0,true,155550936960,155550937024⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932419817439,0,false,-181241544320,-181241544256⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266343381633,0,true,155325164288,155325164352⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932679873919,0,false,-180934927872,-180934927808⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266478119256,0,true,155442144960,155442145024⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932545136296,0,false,-181093777984,-181093777920⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575306793,0,true,63677120,63677184⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447948759,0,false,-63680896,-63680832⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585973109,0,true,74342784,74342848⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437282443,0,false,-74347904,-74347840⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622749,0,false,-5056,-4992⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624088,0,false,-3712,-3648⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266416430822,0,true,155388587904,155388587968⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932606824730,0,false,-181021047040,-181021046976⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266540783435,0,true,155496546432,155496546496⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932482472117,0,false,-181167664256,-181167664192⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074137872614,0,false,-25671117824,-25671117760⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074175639892,0,false,-25632459072,-25632459008⟩
    { al := (622041/4096000), au := (1244931/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨166977859485,167091810337⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155452014208,155452014272⟩ : DyadicInterval 40),(⟨-181107181440,-181107181376⟩ : DyadicInterval 40),(⟨749395105519,749395124849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155550936960,155550937024⟩ : DyadicInterval 40),(⟨-181241544320,-181241544256⟩ : DyadicInterval 40),(⟨749377659368,749377678697⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155325164288,155325164352⟩ : DyadicInterval 40),(⟨-180934927872,-180934927808⟩ : DyadicInterval 40),(⟨749417456949,749417476279⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155442144960,155442145024⟩ : DyadicInterval 40),(⟨-181093777984,-181093777920⟩ : DyadicInterval 40),(⟨749396845322,749396864651⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨63679017,74345333⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63677120,63677184⟩ : DyadicInterval 40),(⟨-63680896,-63680832⟩ : DyadicInterval 40),(⟨762123381751,762123401081⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74342784,74342848⟩ : DyadicInterval 40),(⟨-74347904,-74347840⟩ : DyadicInterval 40),(⟨762123381084,762123400414⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5056,-3648⟩ : DyadicInterval 40),(⟨762123385440,762123405408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166904803046,167029155659⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155388587904,155388587968⟩ : DyadicInterval 40),(⟨-181021047040,-181021046976⟩ : DyadicInterval 40),(⟨749406284301,749406303630⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155496546432,155496546496⟩ : DyadicInterval 40),(⟨-181167664256,-181167664192⟩ : DyadicInterval 40),(⟨749387253437,749387272767⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25671117824,-25632459008⟩ : DyadicInterval 40),(⟨774939613120,774958961792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155452014208,155550937024⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181241544320,-181107181376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1662_ok : ecellOkT e1662 = true := by decide +kernel
theorem e1662_pos {a z : ℝ} (ha1 : ((622041/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1244931/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1662 e1662_ok ha1 ha2 hz1 hz2 hz

-- box ['1244931/8192000', '62289/409600', '7993/8000', '3997/4000']  interval_lower 132406479/1099511627776
noncomputable def e1663 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266603438112,0,true,155550936960,155550937024⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932419817440,0,false,-181241544320,-181241544256⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266717388964,0,true,155649850880,155649850944⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932305866588,0,false,-181375923648,-181375923584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266457232777,0,true,155424011904,155424011968⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932566022775,0,false,-181069152192,-181069152128⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266591984644,0,true,155540994432,155540994496⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932431270908,0,false,-181228038464,-181228038400⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575351731,0,true,63722048,63722112⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447903821,0,false,-63725824,-63725760⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586025542,0,true,74395200,74395264⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437230010,0,false,-74400320,-74400256⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622741,0,false,-5056,-4992⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624083,0,false,-3712,-3648⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266530331560,0,true,155487472896,155487472960⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932492923992,0,false,-181155340288,-181155340224⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266654691558,0,true,155595428096,155595428160⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932368563994,0,false,-181301984192,-181301984128⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074103252762,0,false,-25706556032,-25706555968⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074141048049,0,false,-25667867392,-25667867328⟩
    { al := (1244931/8192000), au := (62289/409600), zl := (7993/8000), zu := (3997/4000),
      A := ⟨167091810336,167205761188⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155550936960,155550937024⟩ : DyadicInterval 40),(⟨-181241544320,-181241544256⟩ : DyadicInterval 40),(⟨749377659368,749377678698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155649850880,155649850944⟩ : DyadicInterval 40),(⟨-181375923648,-181375923584⟩ : DyadicInterval 40),(⟨749360201100,749360220430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155424011904,155424011968⟩ : DyadicInterval 40),(⟨-181069152192,-181069152128⟩ : DyadicInterval 40),(⟨749400041565,749400060894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155540994432,155540994496⟩ : DyadicInterval 40),(⟨-181228038464,-181228038400⟩ : DyadicInterval 40),(⟨749379413459,749379432788⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨63723955,74397766⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63722048,63722112⟩ : DyadicInterval 40),(⟨-63725824,-63725760⟩ : DyadicInterval 40),(⟨762123381746,762123401075⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74395200,74395264⟩ : DyadicInterval 40),(⟨-74400320,-74400256⟩ : DyadicInterval 40),(⟨762123381077,762123400407⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5056,-3648⟩ : DyadicInterval 40),(⟨762123385440,762123405408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167018703784,167143063782⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155487472896,155487472960⟩ : DyadicInterval 40),(⟨-181155340288,-181155340224⟩ : DyadicInterval 40),(⟨749388853542,749388872872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155595428096,155595428160⟩ : DyadicInterval 40),(⟨-181301984192,-181301984128⟩ : DyadicInterval 40),(⟨749369808408,749369827737⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25706556032,-25667867328⟩ : DyadicInterval 40),(⟨774957317280,774976680896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155550936960,155649850944⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181375923648,-181241544256⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1663_ok : ecellOkT e1663 = true := by decide +kernel
theorem e1663_pos {a z : ℝ} (ha1 : ((1244931/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((62289/409600 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1663 e1663_ok ha1 ha2 hz1 hz2 hz

-- box ['77649/512000', '1243233/8192000', '3997/4000', '1599/1600']  interval_lower 4041651/34359738368
noncomputable def e1664 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266261585559,0,true,155254141952,155254142016⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932761669993,0,false,-180838504896,-180838504832⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266375536411,0,true,155353082560,155353082624⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932647719141,0,false,-180972834944,-180972834880⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266136523090,0,true,155145543232,155145543296⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932886732462,0,false,-180691094848,-180691094784⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266271246469,0,true,155262530624,155262530688⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932752009083,0,false,-180849892928,-180849892864⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564618802,0,true,52989696,52989760⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458636750,0,false,-52992320,-52992256⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575262644,0,true,63633024,63633088⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447992908,0,false,-63636736,-63636672⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624093,0,false,-3712,-3648⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625223,0,false,-2560,-2496⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266199050305,0,true,155199840448,155199840512⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932824205247,0,false,-180764792640,-180764792576⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266323396071,0,true,155307811520,155307811584⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932699859481,0,false,-180911367680,-180911367616⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074203877190,0,false,-25603556096,-25603556032⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074241593220,0,false,-25564952192,-25564952128⟩
    { al := (77649/512000), au := (1243233/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨166749957783,166863908635⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155254141952,155254142016⟩ : DyadicInterval 40),(⟨-180838504896,-180838504832⟩ : DyadicInterval 40),(⟨749429961571,749429980900⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155353082560,155353082624⟩ : DyadicInterval 40),(⟨-180972834944,-180972834880⟩ : DyadicInterval 40),(⟨749412539565,749412558895⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155145543232,155145543296⟩ : DyadicInterval 40),(⟨-180691094848,-180691094784⟩ : DyadicInterval 40),(⟨749449068465,749449087794⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155262530624,155262530688⟩ : DyadicInterval 40),(⟨-180849892928,-180849892864⟩ : DyadicInterval 40),(⟨749428484968,749428504297⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨52991026,63634868⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52989696,52989760⟩ : DyadicInterval 40),(⟨-52992320,-52992256⟩ : DyadicInterval 40),(⟨762123382310,762123401639⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63633024,63633088⟩ : DyadicInterval 40),(⟨-63636736,-63636672⟩ : DyadicInterval 40),(⟨762123381724,762123401054⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3712,-2496⟩ : DyadicInterval 40),(⟨762123384864,762123404736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166687422529,166811768295⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155199840448,155199840512⟩ : DyadicInterval 40),(⟨-180764792640,-180764792576⟩ : DyadicInterval 40),(⟨749439517439,749439536768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155307811520,155307811584⟩ : DyadicInterval 40),(⟨-180911367680,-180911367616⟩ : DyadicInterval 40),(⟨749420512840,749420532170⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25603556096,-25564952128⟩ : DyadicInterval 40),(⟨774905859680,774925180928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155254141952,155353082624⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180972834944,-180838504832⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1664_ok : ecellOkT e1664 = true := by decide +kernel
theorem e1664_pos {a z : ℝ} (ha1 : ((77649/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1243233/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1664 e1664_ok ha1 ha2 hz1 hz2 hz

-- box ['1243233/8192000', '622041/4096000', '3997/4000', '1599/1600']  interval_lower 65153863/549755813888
noncomputable def e1665 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266375536410,0,true,155353082560,155353082624⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932647719142,0,false,-180972834944,-180972834880⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266489487262,0,true,155452014208,155452014272⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932533768290,0,false,-181107181440,-181107181376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266250388478,0,true,155244419328,155244419392⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932772867074,0,false,-180825306176,-180825306112⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266385126100,0,true,155361408640,155361408704⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932638129452,0,false,-180984140416,-180984140352⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564656247,0,true,53027136,53027200⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458599305,0,false,-53029760,-53029696⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575307580,0,true,63677952,63678016⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447947972,0,false,-63681664,-63681600⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624087,0,false,-3712,-3648⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625219,0,false,-2560,-2496⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266312958679,0,true,155298748992,155298749056⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932710296873,0,false,-180899063680,-180899063616⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266437311313,0,true,155406716352,155406716416⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932585944239,0,false,-181045664704,-181045664640⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074169300218,0,false,-25638948288,-25638948224⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074207044098,0,false,-25600314624,-25600314560⟩
    { al := (1243233/8192000), au := (622041/4096000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨166863908634,166977859486⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155353082560,155353082624⟩ : DyadicInterval 40),(⟨-180972834944,-180972834880⟩ : DyadicInterval 40),(⟨749412539565,749412558895⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155452014208,155452014272⟩ : DyadicInterval 40),(⟨-181107181440,-181107181376⟩ : DyadicInterval 40),(⟨749395105519,749395124849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155244419328,155244419392⟩ : DyadicInterval 40),(⟨-180825306176,-180825306112⟩ : DyadicInterval 40),(⟨749431672842,749431692172⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155361408640,155361408704⟩ : DyadicInterval 40),(⟨-180984140416,-180984140352⟩ : DyadicInterval 40),(⟨749411072836,749411092166⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨53028471,63679804⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53027136,53027200⟩ : DyadicInterval 40),(⟨-53029760,-53029696⟩ : DyadicInterval 40),(⟨762123382306,762123401635⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63677952,63678016⟩ : DyadicInterval 40),(⟨-63681664,-63681600⟩ : DyadicInterval 40),(⟨762123381719,762123401048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3712,-2496⟩ : DyadicInterval 40),(⟨762123384864,762123404736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166801330903,166925683537⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155298748992,155298749056⟩ : DyadicInterval 40),(⟨-180899063680,-180899063616⟩ : DyadicInterval 40),(⟨749422108631,749422127960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155406716352,155406716416⟩ : DyadicInterval 40),(⟨-181045664704,-181045664640⟩ : DyadicInterval 40),(⟨749403089767,749403109097⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25638948288,-25600314560⟩ : DyadicInterval 40),(⟨774923540896,774942877024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155353082560,155452014272⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181107181440,-180972834880⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1665_ok : ecellOkT e1665 = true := by decide +kernel
theorem e1665_pos {a z : ℝ} (ha1 : ((1243233/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((622041/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1665 e1665_ok ha1 ha2 hz1 hz2 hz

-- box ['77649/512000', '1243233/8192000', '1599/1600', '1999/2000']  interval_lower 64596007/549755813888
noncomputable def e1666 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266261585559,0,true,155254141952,155254142016⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932761669993,0,false,-180838504896,-180838504832⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266375536411,0,true,155353082560,155353082624⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932647719141,0,false,-180972834944,-180972834880⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266157366835,0,true,155163643776,155163643840⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932865888717,0,false,-180715661824,-180715661760⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266292104457,0,true,155280641600,155280641664⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932731151095,0,false,-180874480256,-180874480192⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554020636,0,true,42392000,42392064⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469234916,0,false,-42393728,-42393664⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564656989,0,true,53027904,53027968⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458598563,0,false,-53030528,-53030464⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625218,0,false,-2560,-2496⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626142,0,false,-1664,-1600⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266209472057,0,true,155208890176,155208890240⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932813783495,0,false,-180777076736,-180777076672⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266333824965,0,true,155316866624,155316866688⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932689430587,0,false,-180923661824,-180923661760⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074200712664,0,false,-25606795200,-25606795136⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074238433218,0,false,-25568186560,-25568186496⟩
    { al := (77649/512000), au := (1243233/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨166749957783,166863908635⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155254141952,155254142016⟩ : DyadicInterval 40),(⟨-180838504896,-180838504832⟩ : DyadicInterval 40),(⟨749429961571,749429980900⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155353082560,155353082624⟩ : DyadicInterval 40),(⟨-180972834944,-180972834880⟩ : DyadicInterval 40),(⟨749412539565,749412558895⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155163643776,155163643840⟩ : DyadicInterval 40),(⟨-180715661824,-180715661760⟩ : DyadicInterval 40),(⟨749445884989,749445904319⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155280641600,155280641664⟩ : DyadicInterval 40),(⟨-180874480256,-180874480192⟩ : DyadicInterval 40),(⟨749425296712,749425316041⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨42392860,53029213⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42392000,42392064⟩ : DyadicInterval 40),(⟨-42393728,-42393664⟩ : DyadicInterval 40),(⟨762123382781,762123402110⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53027904,53027968⟩ : DyadicInterval 40),(⟨-53030528,-53030464⟩ : DyadicInterval 40),(⟨762123382306,762123401635⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2560,-1600⟩ : DyadicInterval 40),(⟨762123384416,762123404160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166697844281,166822197189⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155208890176,155208890240⟩ : DyadicInterval 40),(⟨-180777076736,-180777076672⟩ : DyadicInterval 40),(⟨749437925178,749437944508⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155316866624,155316866688⟩ : DyadicInterval 40),(⟨-180923661824,-180923661760⟩ : DyadicInterval 40),(⟨749418918241,749418937570⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25606795200,-25568186496⟩ : DyadicInterval 40),(⟨774907476864,774926800480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155254141952,155353082624⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180972834944,-180838504832⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1666_ok : ecellOkT e1666 = true := by decide +kernel
theorem e1666_pos {a z : ℝ} (ha1 : ((77649/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1243233/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1666 e1666_ok ha1 ha2 hz1 hz2 hz

-- box ['1243233/8192000', '622041/4096000', '1599/1600', '1999/2000']  interval_lower 130166109/1099511627776
noncomputable def e1667 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266375536410,0,true,155353082560,155353082624⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932647719142,0,false,-180972834944,-180972834880⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266489487262,0,true,155452014208,155452014272⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932533768290,0,false,-181107181440,-181107181376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266271246467,0,true,155262530624,155262530688⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932752009085,0,false,-180849892928,-180849892864⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266405998333,0,true,155379530304,155379530368⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932617257219,0,false,-181008747520,-181008747456⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554050592,0,true,42421952,42422016⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469204960,0,false,-42423680,-42423616⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564694436,0,true,53065344,53065408⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458561116,0,false,-53067968,-53067904⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625214,0,false,-2624,-2560⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626140,0,false,-1664,-1600⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266323387298,0,true,155307803904,155307803968⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932699868254,0,false,-180911357376,-180911357312⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266447747328,0,true,155415776832,155415776896⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932575508224,0,false,-181057968704,-181057968640⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074166131369,0,false,-25642191872,-25642191808⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074203879853,0,false,-25603553408,-25603553344⟩
    { al := (1243233/8192000), au := (622041/4096000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨166863908634,166977859486⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155353082560,155353082624⟩ : DyadicInterval 40),(⟨-180972834944,-180972834880⟩ : DyadicInterval 40),(⟨749412539565,749412558895⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155452014208,155452014272⟩ : DyadicInterval 40),(⟨-181107181440,-181107181376⟩ : DyadicInterval 40),(⟨749395105519,749395124849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155262530624,155262530688⟩ : DyadicInterval 40),(⟨-180849892928,-180849892864⟩ : DyadicInterval 40),(⟨749428484968,749428504297⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155379530304,155379530368⟩ : DyadicInterval 40),(⟨-181008747520,-181008747456⟩ : DyadicInterval 40),(⟨749407880211,749407899541⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨42422816,53066660⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42421952,42422016⟩ : DyadicInterval 40),(⟨-42423680,-42423616⟩ : DyadicInterval 40),(⟨762123382779,762123402108⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53065344,53065408⟩ : DyadicInterval 40),(⟨-53067968,-53067904⟩ : DyadicInterval 40),(⟨762123382302,762123401631⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2624,-1600⟩ : DyadicInterval 40),(⟨762123384416,762123404192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166811759522,166936119552⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155307803904,155307803968⟩ : DyadicInterval 40),(⟨-180911357376,-180911357312⟩ : DyadicInterval 40),(⟨749420514196,749420533526⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155415776832,155415776896⟩ : DyadicInterval 40),(⟨-181057968704,-181057968640⟩ : DyadicInterval 40),(⟨749401492951,749401512280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25642191872,-25603553344⟩ : DyadicInterval 40),(⟨774925160288,774944498816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155353082560,155452014272⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181107181440,-180972834880⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1667_ok : ecellOkT e1667 = true := by decide +kernel
theorem e1667_pos {a z : ℝ} (ha1 : ((1243233/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((622041/4096000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1667 e1667_ok ha1 ha2 hz1 hz2 hz

-- box ['622041/4096000', '1244931/8192000', '3997/4000', '1599/1600']  interval_lower 131284617/1099511627776
noncomputable def e1668 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266489487261,0,true,155452014208,155452014272⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932533768291,0,false,-181107181440,-181107181376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266603438113,0,true,155550936960,155550937024⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932419817439,0,false,-181241544320,-181241544256⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266364253866,0,true,155343286592,155343286656⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932659001686,0,false,-180959533888,-180959533824⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266499005732,0,true,155460277696,155460277760⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932524249820,0,false,-181118404352,-181118404288⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564693694,0,true,53064576,53064640⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458561858,0,false,-53067200,-53067136⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575352519,0,true,63722880,63722944⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447903033,0,false,-63726592,-63726528⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624082,0,false,-3712,-3648⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625215,0,false,-2624,-2560⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266426866539,0,true,155397648256,155397648320⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932596389013,0,false,-181033350464,-181033350400⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266551226551,0,true,155505612288,155505612352⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932472029001,0,false,-181179978048,-181179977984⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074134699643,0,false,-25674365760,-25674365696⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074172471530,0,false,-25635702144,-25635702080⟩
    { al := (622041/4096000), au := (1244931/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨166977859485,167091810337⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155452014208,155452014272⟩ : DyadicInterval 40),(⟨-181107181440,-181107181376⟩ : DyadicInterval 40),(⟨749395105519,749395124849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155550936960,155550937024⟩ : DyadicInterval 40),(⟨-181241544320,-181241544256⟩ : DyadicInterval 40),(⟨749377659368,749377678697⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155343286592,155343286656⟩ : DyadicInterval 40),(⟨-180959533888,-180959533824⟩ : DyadicInterval 40),(⟨749414265116,749414284445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155460277696,155460277760⟩ : DyadicInterval 40),(⟨-181118404352,-181118404288⟩ : DyadicInterval 40),(⟨749393648695,749393668025⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨53065918,63724743⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53064576,53064640⟩ : DyadicInterval 40),(⟨-53067200,-53067136⟩ : DyadicInterval 40),(⟨762123382302,762123401631⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63722880,63722944⟩ : DyadicInterval 40),(⟨-63726592,-63726528⟩ : DyadicInterval 40),(⟨762123381714,762123401043⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3712,-2560⟩ : DyadicInterval 40),(⟨762123384896,762123404736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166915238763,167039598775⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155397648256,155397648320⟩ : DyadicInterval 40),(⟨-181033350464,-181033350400⟩ : DyadicInterval 40),(⟨749404687765,749404707094⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155505612288,155505612352⟩ : DyadicInterval 40),(⟨-181179978048,-181179977984⟩ : DyadicInterval 40),(⟨749385654579,749385673908⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25674365760,-25635702080⟩ : DyadicInterval 40),(⟨774941234656,774960585760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155452014208,155550937024⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181241544320,-181107181376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1668_ok : ecellOkT e1668 = true := by decide +kernel
theorem e1668_pos {a z : ℝ} (ha1 : ((622041/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1244931/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1668 e1668_ok ha1 ha2 hz1 hz2 hz

-- box ['1244931/8192000', '62289/409600', '3997/4000', '1599/1600']  interval_lower 66132229/549755813888
noncomputable def e1669 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266603438112,0,true,155550936960,155550937024⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932419817440,0,false,-181241544320,-181241544256⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266717388964,0,true,155649850880,155649850944⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932305866588,0,false,-181375923648,-181375923584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266478119254,0,true,155442144960,155442145024⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932545136298,0,false,-181093777984,-181093777920⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266612885364,0,true,155559137920,155559137984⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932410370188,0,false,-181252684608,-181252684544⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564731143,0,true,53102080,53102144⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458524409,0,false,-53104704,-53104640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575397462,0,true,63767808,63767872⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447858090,0,false,-63771584,-63771520⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624077,0,false,-3712,-3648⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625212,0,false,-2624,-2560⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266540774657,0,true,155496538816,155496538880⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932482480895,0,false,-181167653952,-181167653888⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266665141798,0,true,155604499328,155604499392⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932358113754,0,false,-181314307904,-181314307840⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074100075461,0,false,-25709808512,-25709808448⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074137875282,0,false,-25671115072,-25671115008⟩
    { al := (1244931/8192000), au := (62289/409600), zl := (3997/4000), zu := (1599/1600),
      A := ⟨167091810336,167205761188⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155550936960,155550937024⟩ : DyadicInterval 40),(⟨-181241544320,-181241544256⟩ : DyadicInterval 40),(⟨749377659368,749377678698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155649850880,155649850944⟩ : DyadicInterval 40),(⟨-181375923648,-181375923584⟩ : DyadicInterval 40),(⟨749360201100,749360220430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155442144960,155442145024⟩ : DyadicInterval 40),(⟨-181093777984,-181093777920⟩ : DyadicInterval 40),(⟨749396845322,749396864651⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155559137920,155559137984⟩ : DyadicInterval 40),(⟨-181252684608,-181252684544⟩ : DyadicInterval 40),(⟨749376212414,749376231744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨53103367,63769686⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53102080,53102144⟩ : DyadicInterval 40),(⟨-53104704,-53104640⟩ : DyadicInterval 40),(⟨762123382299,762123401628⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63767808,63767872⟩ : DyadicInterval 40),(⟨-63771584,-63771520⟩ : DyadicInterval 40),(⟨762123381741,762123401070⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3712,-2560⟩ : DyadicInterval 40),(⟨762123384896,762123404736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167029146881,167153514022⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155496538816,155496538880⟩ : DyadicInterval 40),(⟨-181167653952,-181167653888⟩ : DyadicInterval 40),(⟨749387254798,749387274128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155604499328,155604499392⟩ : DyadicInterval 40),(⟨-181314307904,-181314307840⟩ : DyadicInterval 40),(⟨749368207351,749368226681⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25709808512,-25671115008⟩ : DyadicInterval 40),(⟨774958941120,774978307136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155550936960,155649850944⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181375923648,-181241544256⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1669_ok : ecellOkT e1669 = true := by decide +kernel
theorem e1669_pos {a z : ℝ} (ha1 : ((1244931/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((62289/409600 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1669 e1669_ok ha1 ha2 hz1 hz2 hz

-- box ['622041/4096000', '1244931/8192000', '1599/1600', '1999/2000']  interval_lower 131142949/1099511627776
noncomputable def e1670 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266489487261,0,true,155452014208,155452014272⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932533768291,0,false,-181107181440,-181107181376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266603438113,0,true,155550936960,155550937024⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932419817439,0,false,-181241544320,-181241544256⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266385126098,0,true,155361408640,155361408704⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932638129454,0,false,-180984140416,-180984140352⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266519892208,0,true,155478410176,155478410240⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932503363344,0,false,-181143031232,-181143031168⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554080548,0,true,42451904,42451968⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469175004,0,false,-42453632,-42453568⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564731885,0,true,53102784,53102848⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458523667,0,false,-53105408,-53105344⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625211,0,false,-2624,-2560⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626137,0,false,-1664,-1600⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266437302537,0,true,155406708736,155406708800⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932585953015,0,false,-181045654336,-181045654272⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266561669693,0,true,155514678080,155514678144⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932461585859,0,false,-181192292032,-181192291968⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074131526466,0,false,-25677613888,-25677613824⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074169302884,0,false,-25638945536,-25638945472⟩
    { al := (622041/4096000), au := (1244931/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨166977859485,167091810337⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155452014208,155452014272⟩ : DyadicInterval 40),(⟨-181107181440,-181107181376⟩ : DyadicInterval 40),(⟨749395105519,749395124849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155550936960,155550937024⟩ : DyadicInterval 40),(⟨-181241544320,-181241544256⟩ : DyadicInterval 40),(⟨749377659368,749377678697⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155361408640,155361408704⟩ : DyadicInterval 40),(⟨-180984140416,-180984140352⟩ : DyadicInterval 40),(⟨749411072837,749411092166⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155478410176,155478410240⟩ : DyadicInterval 40),(⟨-181143031232,-181143031168⟩ : DyadicInterval 40),(⟨749390451621,749390470950⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨42452772,53104109⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42451904,42451968⟩ : DyadicInterval 40),(⟨-42453632,-42453568⟩ : DyadicInterval 40),(⟨762123382776,762123402105⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53102784,53102848⟩ : DyadicInterval 40),(⟨-53105408,-53105344⟩ : DyadicInterval 40),(⟨762123382299,762123401628⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2624,-1600⟩ : DyadicInterval 40),(⟨762123384416,762123404192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166925674761,167050041917⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155406708736,155406708800⟩ : DyadicInterval 40),(⟨-181045654336,-181045654272⟩ : DyadicInterval 40),(⟨749403091099,749403110429⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155514678080,155514678144⟩ : DyadicInterval 40),(⟨-181192292032,-181192291968⟩ : DyadicInterval 40),(⟨749384055631,749384074960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25677613888,-25638945472⟩ : DyadicInterval 40),(⟨774942856352,774962209824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155452014208,155550937024⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181241544320,-181107181376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1670_ok : ecellOkT e1670 = true := by decide +kernel
theorem e1670_pos {a z : ℝ} (ha1 : ((622041/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1244931/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1670 e1670_ok ha1 ha2 hz1 hz2 hz

-- box ['1244931/8192000', '62289/409600', '1599/1600', '1999/2000']  interval_lower 132122315/1099511627776
noncomputable def e1671 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266603438112,0,true,155550936960,155550937024⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932419817440,0,false,-181241544320,-181241544256⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266717388964,0,true,155649850880,155649850944⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932305866588,0,false,-181375923648,-181375923584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266499005730,0,true,155460277696,155460277760⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932524249822,0,false,-181118404352,-181118404288⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266633786084,0,true,155577281088,155577281152⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932389469468,0,false,-181277331328,-181277331264⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099554110509,0,true,42481856,42481920⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469145043,0,false,-42483584,-42483520⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564769338,0,true,53140224,53140288⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458486214,0,false,-53142848,-53142784⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625207,0,false,-2624,-2560⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626135,0,false,-1664,-1600⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266551217772,0,true,155505604672,155505604736⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932472037780,0,false,-181179967744,-181179967680⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266675592057,0,true,155613570496,155613570560⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932347663495,0,false,-181326631744,-181326631680⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074096897955,0,false,-25713061184,-25713061120⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074134702311,0,false,-25674363008,-25674362944⟩
    { al := (1244931/8192000), au := (62289/409600), zl := (1599/1600), zu := (1999/2000),
      A := ⟨167091810336,167205761188⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155550936960,155550937024⟩ : DyadicInterval 40),(⟨-181241544320,-181241544256⟩ : DyadicInterval 40),(⟨749377659368,749377678698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155649850880,155649850944⟩ : DyadicInterval 40),(⟨-181375923648,-181375923584⟩ : DyadicInterval 40),(⟨749360201100,749360220430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155460277696,155460277760⟩ : DyadicInterval 40),(⟨-181118404352,-181118404288⟩ : DyadicInterval 40),(⟨749393648695,749393668025⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155577281088,155577281152⟩ : DyadicInterval 40),(⟨-181277331328,-181277331264⟩ : DyadicInterval 40),(⟨749373010985,749373030315⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨42482733,53141562⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42481856,42481920⟩ : DyadicInterval 40),(⟨-42483584,-42483520⟩ : DyadicInterval 40),(⟨762123382774,762123402103⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53140224,53140288⟩ : DyadicInterval 40),(⟨-53142848,-53142784⟩ : DyadicInterval 40),(⟨762123382295,762123401624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2624,-1600⟩ : DyadicInterval 40),(⟨762123384416,762123404192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167039589996,167163964281⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155505604672,155505604736⟩ : DyadicInterval 40),(⟨-181179967744,-181179967680⟩ : DyadicInterval 40),(⟨749385655940,749385675269⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155613570496,155613570560⟩ : DyadicInterval 40),(⟨-181326631744,-181326631680⟩ : DyadicInterval 40),(⟨749366606181,749366625510⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25713061184,-25674362944⟩ : DyadicInterval 40),(⟨774960565088,774979933472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155550936960,155649850944⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181375923648,-181241544256⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1671_ok : ecellOkT e1671 = true := by decide +kernel
theorem e1671_pos {a z : ℝ} (ha1 : ((1244931/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((62289/409600 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1671 e1671_ok ha1 ha2 hz1 hz2 hz

-- box ['62289/409600', '1246629/8192000', '999/1000', '7993/8000']  interval_lower 8345699/68719476736
noncomputable def e1672 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266717388963,0,true,155649850880,155649850944⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932305866589,0,false,-181375923648,-181375923584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266831339815,0,true,155748755840,155748755904⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932191915737,0,false,-181510319424,-181510319360⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266550183201,0,true,155504706560,155504706624⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932473072351,0,false,-181178747840,-181178747776⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266684935068,0,true,155621680512,155621680576⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932338320484,0,false,-181337649920,-181337649856⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586024707,0,true,74394368,74394432⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437230845,0,false,-74399488,-74399424⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099596713502,0,true,85082432,85082496⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099426542050,0,false,-85089024,-85088960⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621191,0,false,-6592,-6528⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622743,0,false,-5056,-4992⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266633782364,0,true,155577277888,155577277952⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932389473188,0,false,-181277326912,-181277326848⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266758142339,0,true,155685224256,155685224320⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932265113213,0,false,-181423987072,-181423987008⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074071790736,0,false,-25738762816,-25738762752⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074109609418,0,false,-25700049024,-25700048960⟩
    { al := (62289/409600), au := (1246629/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨167205761187,167319712039⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155649850880,155649850944⟩ : DyadicInterval 40),(⟨-181375923648,-181375923584⟩ : DyadicInterval 40),(⟨749360201100,749360220430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155748755840,155748755904⟩ : DyadicInterval 40),(⟨-181510319424,-181510319360⟩ : DyadicInterval 40),(⟨749342730789,749342750118⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155504706560,155504706624⟩ : DyadicInterval 40),(⟨-181178747840,-181178747776⟩ : DyadicInterval 40),(⟨749385814329,749385833659⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155621680512,155621680576⟩ : DyadicInterval 40),(⟨-181337649920,-181337649856⟩ : DyadicInterval 40),(⟨749365174543,749365193873⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨74396931,85085726⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74394368,74394432⟩ : DyadicInterval 40),(⟨-74399488,-74399424⟩ : DyadicInterval 40),(⟨762123381077,762123400407⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨85082432,85082496⟩ : DyadicInterval 40),(⟨-85089024,-85088960⟩ : DyadicInterval 40),(⟨762123380263,762123399592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6592,-4992⟩ : DyadicInterval 40),(⟨762123386112,762123406176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167122154588,167246514563⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155577277888,155577277952⟩ : DyadicInterval 40),(⟨-181277326912,-181277326848⟩ : DyadicInterval 40),(⟨749373011526,749373030856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155685224256,155685224320⟩ : DyadicInterval 40),(⟨-181423987072,-181423987008⟩ : DyadicInterval 40),(⟨749353954419,749353973749⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25738762816,-25700048960⟩ : DyadicInterval 40),(⟨774973408096,774992784288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155649850880,155748755904⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181510319424,-181375923584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1672_ok : ecellOkT e1672 = true := by decide +kernel
theorem e1672_pos {a z : ℝ} (ha1 : ((62289/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1246629/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1672 e1672_ok ha1 ha2 hz1 hz2 hz

-- box ['1246629/8192000', '623739/4096000', '999/1000', '7993/8000']  interval_lower 67258317/549755813888
noncomputable def e1673 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266831339814,0,true,155748755840,155748755904⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932191915738,0,false,-181510319424,-181510319360⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266945290666,0,true,155847651904,155847651968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932077964886,0,false,-181644731584,-181644731520⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266664020101,0,true,155603525696,155603525760⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932359235451,0,false,-181312985088,-181312985024⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266798786212,0,true,155720501440,155720501504⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932224469340,0,false,-181471923392,-181471923328⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586077142,0,true,74446784,74446848⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437178410,0,false,-74451904,-74451840⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099596773433,0,true,85142336,85142400⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099426482119,0,false,-85148992,-85148928⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621182,0,false,-6656,-6592⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622735,0,false,-5056,-4992⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266747676237,0,true,155676139904,155676139968⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932275579315,0,false,-181411643456,-181411643392⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266872043335,0,true,155784082752,155784082816⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932151212217,0,false,-181558329856,-181558329792⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074037128017,0,false,-25774247104,-25774247040⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074074974631,0,false,-25735503488,-25735503424⟩
    { al := (1246629/8192000), au := (623739/4096000), zl := (999/1000), zu := (7993/8000),
      A := ⟨167319712038,167433662890⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155748755840,155748755904⟩ : DyadicInterval 40),(⟨-181510319424,-181510319360⟩ : DyadicInterval 40),(⟨749342730789,749342750118⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155847651904,155847651968⟩ : DyadicInterval 40),(⟨-181644731584,-181644731520⟩ : DyadicInterval 40),(⟨749325248369,749325267698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155603525696,155603525760⟩ : DyadicInterval 40),(⟨-181312985088,-181312985024⟩ : DyadicInterval 40),(⟨749368379176,749368398505⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155720501440,155720501504⟩ : DyadicInterval 40),(⟨-181471923392,-181471923328⟩ : DyadicInterval 40),(⟨749347722967,749347742297⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨74449366,85145657⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74446784,74446848⟩ : DyadicInterval 40),(⟨-74451904,-74451840⟩ : DyadicInterval 40),(⟨762123381070,762123400400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨85142336,85142400⟩ : DyadicInterval 40),(⟨-85148992,-85148928⟩ : DyadicInterval 40),(⟨762123380286,762123399615⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6656,-4992⟩ : DyadicInterval 40),(⟨762123386112,762123406208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167236048461,167360415559⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155676139904,155676139968⟩ : DyadicInterval 40),(⟨-181411643456,-181411643392⟩ : DyadicInterval 40),(⟨749355558836,749355578166⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155784082752,155784082816⟩ : DyadicInterval 40),(⟨-181558329856,-181558329792⟩ : DyadicInterval 40),(⟨749336487414,749336506744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25774247104,-25735503424⟩ : DyadicInterval 40),(⟨774991135328,775010526432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155748755840,155847651968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181644731584,-181510319360⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1673_ok : ecellOkT e1673 = true := by decide +kernel
theorem e1673_pos {a z : ℝ} (ha1 : ((1246629/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((623739/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1673 e1673_ok ha1 ha2 hz1 hz2 hz

-- box ['62289/409600', '1246629/8192000', '7993/8000', '3997/4000']  interval_lower 133388849/1099511627776
noncomputable def e1674 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266717388963,0,true,155649850880,155649850944⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932305866589,0,false,-181375923648,-181375923584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266831339815,0,true,155748755840,155748755904⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932191915737,0,false,-181510319424,-181510319360⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266571083921,0,true,155522850624,155522850688⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932452171631,0,false,-181203392896,-181203392832⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266705850032,0,true,155639835008,155639835072⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932317405520,0,false,-181362315328,-181362315264⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575396674,0,true,63767040,63767104⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447858878,0,false,-63770752,-63770688⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586077978,0,true,74447680,74447744⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437177574,0,false,-74452736,-74452672⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622734,0,false,-5056,-4992⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624078,0,false,-3712,-3648⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266644232557,0,true,155586349184,155586349248⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932379022995,0,false,-181289650304,-181289650240⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266768599677,0,true,155694300864,155694300928⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932254655875,0,false,-181436320512,-181436320448⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074068609309,0,false,-25742019584,-25742019520⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074106432529,0,false,-25703301056,-25703300992⟩
    { al := (62289/409600), au := (1246629/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨167205761187,167319712039⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155649850880,155649850944⟩ : DyadicInterval 40),(⟨-181375923648,-181375923584⟩ : DyadicInterval 40),(⟨749360201100,749360220430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155748755840,155748755904⟩ : DyadicInterval 40),(⟨-181510319424,-181510319360⟩ : DyadicInterval 40),(⟨749342730789,749342750118⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155522850624,155522850688⟩ : DyadicInterval 40),(⟨-181203392896,-181203392832⟩ : DyadicInterval 40),(⟨749382614118,749382633448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155639835008,155639835072⟩ : DyadicInterval 40),(⟨-181362315328,-181362315264⟩ : DyadicInterval 40),(⟨749361969525,749361988855⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨63768898,74450202⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63767040,63767104⟩ : DyadicInterval 40),(⟨-63770752,-63770688⟩ : DyadicInterval 40),(⟨762123381709,762123401038⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74447680,74447744⟩ : DyadicInterval 40),(⟨-74452736,-74452672⟩ : DyadicInterval 40),(⟨762123381038,762123400367⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5056,-3648⟩ : DyadicInterval 40),(⟨762123385440,762123405408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167132604781,167256971901⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155586349184,155586349248⟩ : DyadicInterval 40),(⟨-181289650304,-181289650240⟩ : DyadicInterval 40),(⟨749371410712,749371430041⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155694300864,155694300928⟩ : DyadicInterval 40),(⟨-181436320512,-181436320448⟩ : DyadicInterval 40),(⟨749352351289,749352370619⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25742019584,-25703300992⟩ : DyadicInterval 40),(⟨774975034112,774994412672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155649850880,155748755904⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181510319424,-181375923584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1674_ok : ecellOkT e1674 = true := by decide +kernel
theorem e1674_pos {a z : ℝ} (ha1 : ((62289/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1246629/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1674 e1674_ok ha1 ha2 hz1 hz2 hz

-- box ['1246629/8192000', '623739/4096000', '7993/8000', '3997/4000']  interval_lower 134374677/1099511627776
noncomputable def e1675 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266831339814,0,true,155748755840,155748755904⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932191915738,0,false,-181510319424,-181510319360⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266945290666,0,true,155847651904,155847651968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932077964886,0,false,-181644731584,-181644731520⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266684935065,0,true,155621680512,155621680576⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932338320487,0,false,-181337649920,-181337649856⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266819715419,0,true,155738666688,155738666752⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932203540133,0,false,-181496608640,-181496608576⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575441618,0,true,63811968,63812032⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447813934,0,false,-63815744,-63815680⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586130418,0,true,74500096,74500160⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437125134,0,false,-74505216,-74505152⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622727,0,false,-5056,-4992⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624073,0,false,-3712,-3648⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266758133811,0,true,155685216832,155685216896⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932265121741,0,false,-181423977024,-181423976960⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266882507794,0,true,155793164800,155793164864⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932140747758,0,false,-181570673216,-181570673152⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074033942256,0,false,-25777508416,-25777508352⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074071793332,0,false,-25738760128,-25738760064⟩
    { al := (1246629/8192000), au := (623739/4096000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨167319712038,167433662890⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155748755840,155748755904⟩ : DyadicInterval 40),(⟨-181510319424,-181510319360⟩ : DyadicInterval 40),(⟨749342730789,749342750118⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155847651904,155847651968⟩ : DyadicInterval 40),(⟨-181644731584,-181644731520⟩ : DyadicInterval 40),(⟨749325248369,749325267698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155621680512,155621680576⟩ : DyadicInterval 40),(⟨-181337649920,-181337649856⟩ : DyadicInterval 40),(⟨749365174544,749365193873⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155738666688,155738666752⟩ : DyadicInterval 40),(⟨-181496608640,-181496608576⟩ : DyadicInterval 40),(⟨749344513548,749344532877⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨63813842,74502642⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63811968,63812032⟩ : DyadicInterval 40),(⟨-63815744,-63815680⟩ : DyadicInterval 40),(⟨762123381736,762123401065⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74500096,74500160⟩ : DyadicInterval 40),(⟨-74505216,-74505152⟩ : DyadicInterval 40),(⟨762123381063,762123400392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5056,-3648⟩ : DyadicInterval 40),(⟨762123385440,762123405408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167246506035,167370880018⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155685216832,155685216896⟩ : DyadicInterval 40),(⟨-181423977024,-181423976960⟩ : DyadicInterval 40),(⟨749353955744,749353975073⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155793164800,155793164864⟩ : DyadicInterval 40),(⟨-181570673216,-181570673152⟩ : DyadicInterval 40),(⟨749334882045,749334901374⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25777508416,-25738760064⟩ : DyadicInterval 40),(⟨774992763648,775012157088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155748755840,155847651968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181644731584,-181510319360⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1675_ok : ecellOkT e1675 = true := by decide +kernel
theorem e1675_pos {a z : ℝ} (ha1 : ((1246629/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((623739/4096000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1675 e1675_ok ha1 ha2 hz1 hz2 hz

-- box ['623739/4096000', '1248327/8192000', '999/1000', '7993/8000']  interval_lower 33876229/274877906944
noncomputable def e1676 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266945290665,0,true,155847651904,155847651968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932077964887,0,false,-181644731584,-181644731520⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267059241518,0,true,155946539072,155946539136⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931964014034,0,false,-181779160192,-181779160128⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266777857002,0,true,155702335872,155702335936⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932245398550,0,false,-181447238720,-181447238656⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266912637357,0,true,155819313536,155819313600⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932110618195,0,false,-181606213312,-181606213248⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586129582,0,true,74499264,74499328⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437125970,0,false,-74504384,-74504320⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099596833368,0,true,85202240,85202304⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099426422184,0,false,-85208896,-85208832⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621173,0,false,-6656,-6592⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622728,0,false,-5056,-4992⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266861570110,0,true,155774993088,155774993152⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932161685442,0,false,-181545976320,-181545976256⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266985944333,0,true,155882932416,155882932480⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932037311219,0,false,-181692689088,-181692689024⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074002441699,0,false,-25809756672,-25809756608⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074040316249,0,false,-25770983232,-25770983168⟩
    { al := (623739/4096000), au := (1248327/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨167433662889,167547613742⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155847651904,155847651968⟩ : DyadicInterval 40),(⟨-181644731584,-181644731520⟩ : DyadicInterval 40),(⟨749325248369,749325267698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155946539072,155946539136⟩ : DyadicInterval 40),(⟨-181779160192,-181779160128⟩ : DyadicInterval 40),(⟨749307753865,749307773195⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155702335872,155702335936⟩ : DyadicInterval 40),(⟨-181447238720,-181447238656⟩ : DyadicInterval 40),(⟨749350932001,749350951330⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155819313536,155819313600⟩ : DyadicInterval 40),(⟨-181606213312,-181606213248⟩ : DyadicInterval 40),(⟨749330259316,749330278645⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨74501806,85205592⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74499264,74499328⟩ : DyadicInterval 40),(⟨-74504384,-74504320⟩ : DyadicInterval 40),(⟨762123381063,762123400393⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨85202240,85202304⟩ : DyadicInterval 40),(⟨-85208896,-85208832⟩ : DyadicInterval 40),(⟨762123380276,762123399606⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6656,-4992⟩ : DyadicInterval 40),(⟨762123386112,762123406208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167349942334,167474316557⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155774993088,155774993152⟩ : DyadicInterval 40),(⟨-181545976320,-181545976256⟩ : DyadicInterval 40),(⟨749338093999,749338113328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155882932416,155882932480⟩ : DyadicInterval 40),(⟨-181692689088,-181692689024⟩ : DyadicInterval 40),(⟨749319008311,749319027640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25809756672,-25770983168⟩ : DyadicInterval 40),(⟨775008875200,775028281216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155847651904,155946539136⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181779160192,-181644731520⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1676_ok : ecellOkT e1676 = true := by decide +kernel
theorem e1676_pos {a z : ℝ} (ha1 : ((623739/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1248327/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1676 e1676_ok ha1 ha2 hz1 hz2 hz

-- box ['1248327/8192000', '156147/1024000', '999/1000', '7993/8000']  interval_lower 136495569/1099511627776
noncomputable def e1677 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267059241517,0,true,155946539072,155946539136⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931964014035,0,false,-181779160192,-181779160128⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267173192369,0,true,156045417408,156045417472⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931850063183,0,false,-181913605248,-181913605184⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266891693903,0,true,155801137280,155801137344⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932131561649,0,false,-181581508800,-181581508736⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267026488501,0,true,155918116736,155918116800⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931996767051,0,false,-181740519552,-181740519488⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586182025,0,true,74551680,74551744⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437073527,0,false,-74556800,-74556736⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099596893308,0,true,85262208,85262272⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099426362244,0,false,-85268864,-85268800⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621163,0,false,-6656,-6592⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622721,0,false,-5056,-4992⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266975463986,0,true,155873837376,155873837440⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932047791566,0,false,-181680325632,-181680325568⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267099845334,0,true,155981773184,155981773248⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931923410218,0,false,-181827064768,-181827064704⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073967731781,0,false,-25845291584,-25845291520⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074005634270,0,false,-25806488256,-25806488192⟩
    { al := (1248327/8192000), au := (156147/1024000), zl := (999/1000), zu := (7993/8000),
      A := ⟨167547613741,167661564593⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155946539072,155946539136⟩ : DyadicInterval 40),(⟨-181779160192,-181779160128⟩ : DyadicInterval 40),(⟨749307753865,749307773195⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156045417408,156045417472⟩ : DyadicInterval 40),(⟨-181913605248,-181913605184⟩ : DyadicInterval 40),(⟨749290247241,749290266571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155801137280,155801137344⟩ : DyadicInterval 40),(⟨-181581508800,-181581508736⟩ : DyadicInterval 40),(⟨749333472719,749333492049⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155918116736,155918116800⟩ : DyadicInterval 40),(⟨-181740519552,-181740519488⟩ : DyadicInterval 40),(⟨749312783570,749312802899⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨74554249,85265532⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74551680,74551744⟩ : DyadicInterval 40),(⟨-74556800,-74556736⟩ : DyadicInterval 40),(⟨762123381056,762123400385⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨85262208,85262272⟩ : DyadicInterval 40),(⟨-85268864,-85268800⟩ : DyadicInterval 40),(⟨762123380267,762123399597⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6656,-4992⟩ : DyadicInterval 40),(⟨762123386112,762123406208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167463836210,167588217558⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155873837376,155873837440⟩ : DyadicInterval 40),(⟨-181680325632,-181680325568⟩ : DyadicInterval 40),(⟨749320617103,749320636432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155981773184,155981773248⟩ : DyadicInterval 40),(⟨-181827064768,-181827064704⟩ : DyadicInterval 40),(⟨749301517145,749301536474⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25845291584,-25806488192⟩ : DyadicInterval 40),(⟨775026627712,775046048672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155946539072,156045417472⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181913605248,-181779160128⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1677_ok : ecellOkT e1677 = true := by decide +kernel
theorem e1677_pos {a z : ℝ} (ha1 : ((1248327/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((156147/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1677 e1677_ok ha1 ha2 hz1 hz2 hz

-- box ['623739/4096000', '1248327/8192000', '7993/8000', '3997/4000']  interval_lower 135362033/1099511627776
noncomputable def e1678 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266945290665,0,true,155847651904,155847651968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932077964887,0,false,-181644731584,-181644731520⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267059241518,0,true,155946539072,155946539136⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931964014034,0,false,-181779160192,-181779160128⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266798786209,0,true,155720501440,155720501504⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932224469343,0,false,-181471923392,-181471923328⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266933580808,0,true,155837489536,155837489600⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932089674744,0,false,-181630918336,-181630918272⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575486567,0,true,63856896,63856960⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447768985,0,false,-63860672,-63860608⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586182862,0,true,74552512,74552576⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437072690,0,false,-74557632,-74557568⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622720,0,false,-5120,-5056⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624068,0,false,-3712,-3648⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266872034549,0,true,155784075136,155784075200⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932151221003,0,false,-181558319488,-181558319424⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266996415916,0,true,155892019776,155892019840⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932026839636,0,false,-181705042368,-181705042304⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073999251599,0,false,-25813022528,-25813022464⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074037130693,0,false,-25774244352,-25774244288⟩
    { al := (623739/4096000), au := (1248327/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨167433662889,167547613742⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155847651904,155847651968⟩ : DyadicInterval 40),(⟨-181644731584,-181644731520⟩ : DyadicInterval 40),(⟨749325248369,749325267698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155946539072,155946539136⟩ : DyadicInterval 40),(⟨-181779160192,-181779160128⟩ : DyadicInterval 40),(⟨749307753865,749307773195⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155720501440,155720501504⟩ : DyadicInterval 40),(⟨-181471923392,-181471923328⟩ : DyadicInterval 40),(⟨749347722968,749347742298⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155837489536,155837489600⟩ : DyadicInterval 40),(⟨-181630918336,-181630918272⟩ : DyadicInterval 40),(⟨749327045461,749327064790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨63858791,74555086⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63856896,63856960⟩ : DyadicInterval 40),(⟨-63860672,-63860608⟩ : DyadicInterval 40),(⟨762123381731,762123401060⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74552512,74552576⟩ : DyadicInterval 40),(⟨-74557632,-74557568⟩ : DyadicInterval 40),(⟨762123381056,762123400385⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5120,-3648⟩ : DyadicInterval 40),(⟨762123385440,762123405440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167360406773,167484788140⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155784075136,155784075200⟩ : DyadicInterval 40),(⟨-181558319488,-181558319424⟩ : DyadicInterval 40),(⟨749336488755,749336508084⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155892019776,155892019840⟩ : DyadicInterval 40),(⟨-181705042368,-181705042304⟩ : DyadicInterval 40),(⟨749317400772,749317420101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25813022528,-25774244288⟩ : DyadicInterval 40),(⟨775010505760,775029914144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155847651904,155946539136⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181779160192,-181644731520⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1678_ok : ecellOkT e1678 = true := by decide +kernel
theorem e1678_pos {a z : ℝ} (ha1 : ((623739/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1248327/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1678 e1678_ok ha1 ha2 hz1 hz2 hz

-- box ['1248327/8192000', '156147/1024000', '7993/8000', '3997/4000']  interval_lower 68176199/549755813888
noncomputable def e1679 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1267059241517,0,true,155946539072,155946539136⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨931964014035,0,false,-181779160192,-181779160128⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1267173192369,0,true,156045417408,156045417472⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨931850063183,0,false,-181913605248,-181913605184⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266912637354,0,true,155819313536,155819313600⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨932110618198,0,false,-181606213248,-181606213184⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1267047446196,0,true,155936303488,155936303552⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨931975809356,0,false,-181765244416,-181765244352⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575531519,0,true,63901824,63901888⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099447724033,0,false,-63905664,-63905600⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586235309,0,true,74604992,74605056⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437020243,0,false,-74610112,-74610048⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622713,0,false,-5120,-5056⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624062,0,false,-3776,-3712⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266985935546,0,true,155882924800,155882924864⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932037320006,0,false,-181692678720,-181692678656⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1267110324042,0,true,155990865920,155990865984⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨931912931510,0,false,-181839427968,-181839427904⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1073964537340,0,false,-25848561984,-25848561920⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074002444377,0,false,-25809753920,-25809753856⟩
    { al := (1248327/8192000), au := (156147/1024000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨167547613741,167661564593⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155946539072,155946539136⟩ : DyadicInterval 40),(⟨-181779160192,-181779160128⟩ : DyadicInterval 40),(⟨749307753865,749307773195⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨156045417408,156045417472⟩ : DyadicInterval 40),(⟨-181913605248,-181913605184⟩ : DyadicInterval 40),(⟨749290247241,749290266571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155819313536,155819313600⟩ : DyadicInterval 40),(⟨-181606213248,-181606213184⟩ : DyadicInterval 40),(⟨749330259289,749330278619⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155936303488,155936303552⟩ : DyadicInterval 40),(⟨-181765244416,-181765244352⟩ : DyadicInterval 40),(⟨749309565300,749309584630⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨63903743,74607533⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63901824,63901888⟩ : DyadicInterval 40),(⟨-63905664,-63905600⟩ : DyadicInterval 40),(⟨762123381757,762123401087⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74604992,74605056⟩ : DyadicInterval 40),(⟨-74610112,-74610048⟩ : DyadicInterval 40),(⟨762123381049,762123400378⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5120,-3712⟩ : DyadicInterval 40),(⟨762123385472,762123405440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨167474307770,167598696266⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155882924800,155882924864⟩ : DyadicInterval 40),(⟨-181692678720,-181692678656⟩ : DyadicInterval 40),(⟨749319009653,749319028983⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155990865920,155990865984⟩ : DyadicInterval 40),(⟨-181839427968,-181839427904⟩ : DyadicInterval 40),(⟨749299907396,749299926726⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25848561984,-25809753856⟩ : DyadicInterval 40),(⟨775028260544,775047683872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155946539072,156045417472⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-181913605248,-181779160128⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1679_ok : ecellOkT e1679 = true := by decide +kernel
theorem e1679_pos {a z : ℝ} (ha1 : ((1248327/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((156147/1024000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1679 e1679_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B027

end


