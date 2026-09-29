-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B045
-- name    : CK_CKLaneC2R_EpCells_B045
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:25:14.859604+00:00
-- url     : https://prove2.me/theorems/843cfd8f-10ad-4764-bb95-3ef2de2682ac
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B045` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B045` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B045` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B045 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B045.lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheckT

-- ===== source module CKLaneC2R.EpCells.B045 =====
section

namespace CKLaneC2R.EpCells.B045

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['27123/163840', '1356999/8192000', '999/1000', '7993/8000']  interval_lower 35578661/137438953472
noncomputable def e2700 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281530999603,0,true,168433471680,168433471744⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917492255949,0,false,-198986586304,-198986586240⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281644950455,0,true,168531233472,168531233536⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917378305097,0,false,-199123152128,-199123152064⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281348980231,0,true,168277293952,168277294016⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917674275321,0,false,-198768478144,-198768478080⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281485583798,0,true,168394505728,168394505792⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917537671754,0,false,-198932161920,-198932161856⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592872912,0,true,81242112,81242176⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430382640,0,false,-81248192,-81248128⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099604540646,0,true,92908928,92908992⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099418714906,0,false,-92916800,-92916736⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619924,0,false,-7872,-7808⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621773,0,false,-6016,-5952⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281439986065,0,true,168355382272,168355382336⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917583269487,0,false,-198877522176,-198877522112⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281565276294,0,true,168462879616,168462879680⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917457979258,0,false,-199027663872,-199027663808⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069367761989,0,false,-30564784192,-30564784128⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069409238030,0,false,-30522139840,-30522139776⟩
    { al := (27123/163840), au := (1356999/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨182019371827,182133322679⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168433471680,168433471744⟩ : DyadicInterval 40),(⟨-198986586304,-198986586240⟩ : DyadicInterval 40),(⟨746987543913,746987563243⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168531233472,168531233536⟩ : DyadicInterval 40),(⟨-199123152128,-199123152064⟩ : DyadicInterval 40),(⟨746968498543,746968517872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168277293952,168277294016⟩ : DyadicInterval 40),(⟨-198768478144,-198768478080⟩ : DyadicInterval 40),(⟨747017940814,747017960144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168394505728,168394505792⟩ : DyadicInterval 40),(⟨-198932161920,-198932161856⟩ : DyadicInterval 40),(⟨746995131173,746995150502⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨81245136,92912870⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81242112,81242176⟩ : DyadicInterval 40),(⟨-81248192,-81248128⟩ : DyadicInterval 40),(⟨762123380588,762123399917⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨92908928,92908992⟩ : DyadicInterval 40),(⟨-92916800,-92916736⟩ : DyadicInterval 40),(⟨762123379636,762123398965⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7872,-5952⟩ : DyadicInterval 40),(⟨762123386592,762123406816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181928358289,182053648518⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168355382272,168355382336⟩ : DyadicInterval 40),(⟨-198877522176,-198877522112⟩ : DyadicInterval 40),(⟨747002746876,747002766206⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168462879616,168462879680⟩ : DyadicInterval 40),(⟨-199027663872,-199027663808⟩ : DyadicInterval 40),(⟨746981816283,746981835613⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30564784192,-30522139776⟩ : DyadicInterval 40),(⟨777384453504,777405794976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168433471680,168531233536⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199123152128,-198986586240⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2700_ok : ecellOkT e2700 = true := by decide +kernel
theorem e2700_pos {a z : ℝ} (ha1 : ((27123/163840 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1356999/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2700 e2700_ok ha1 ha2 hz1 hz2 hz

-- box ['1356999/8192000', '169731/1024000', '999/1000', '7993/8000']  interval_lower 285983423/1099511627776
noncomputable def e2701 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281644950454,0,true,168531233472,168531233536⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917378305098,0,false,-199123152128,-199123152064⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281758901306,0,true,168628986496,168628986560⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917264354246,0,false,-199259734848,-199259734784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281462817131,0,true,168374971840,168374971904⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917560438421,0,false,-198904880320,-198904880256⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281599434942,0,true,168492185408,168492185472⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917423820610,0,false,-199068601472,-199068601408⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592925845,0,true,81295040,81295104⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430329707,0,false,-81301120,-81301056⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099604601146,0,true,92969408,92969472⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099418654406,0,false,-92977344,-92977280⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619914,0,false,-7872,-7808⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621765,0,false,-6016,-5952⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281553879942,0,true,168453102144,168453102208⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917469375610,0,false,-199014006144,-199014006080⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281679177293,0,true,168560595968,168560596032⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917344078259,0,false,-199164174976,-199164174912⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069330031457,0,false,-30603579008,-30603578944⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069371535815,0,false,-30560904000,-30560903936⟩
    { al := (1356999/8192000), au := (169731/1024000), zl := (999/1000), zu := (7993/8000),
      A := ⟨182133322678,182247273530⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168531233472,168531233536⟩ : DyadicInterval 40),(⟨-199123152128,-199123152064⟩ : DyadicInterval 40),(⟨746968498543,746968517872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168628986496,168628986560⟩ : DyadicInterval 40),(⟨-199259734848,-199259734784⟩ : DyadicInterval 40),(⟨746949441046,746949460376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168374971840,168374971904⟩ : DyadicInterval 40),(⟨-198904880320,-198904880256⟩ : DyadicInterval 40),(⟨746998933878,746998953208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168492185408,168492185472⟩ : DyadicInterval 40),(⟨-199068601472,-199068601408⟩ : DyadicInterval 40),(⟨746976107323,746976126652⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨81298069,92973370⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81295040,81295104⟩ : DyadicInterval 40),(⟨-81301120,-81301056⟩ : DyadicInterval 40),(⟨762123380580,762123399910⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨92969408,92969472⟩ : DyadicInterval 40),(⟨-92977344,-92977280⟩ : DyadicInterval 40),(⟨762123379657,762123398987⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7872,-5952⟩ : DyadicInterval 40),(⟨762123386592,762123406816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182042252166,182167549517⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168453102144,168453102208⟩ : DyadicInterval 40),(⟨-199014006144,-199014006080⟩ : DyadicInterval 40),(⟨746983720702,746983740032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168560595968,168560596032⟩ : DyadicInterval 40),(⟨-199164174976,-199164174912⟩ : DyadicInterval 40),(⟨746962775602,746962794931⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30603579008,-30560903936⟩ : DyadicInterval 40),(⟨777403835584,777425192384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168531233472,168628986560⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199259734848,-199123152064⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2701_ok : ecellOkT e2701 = true := by decide +kernel
theorem e2701_pos {a z : ℝ} (ha1 : ((1356999/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((169731/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2701 e2701_ok ha1 ha2 hz1 hz2 hz

-- box ['27123/163840', '1356999/8192000', '7993/8000', '3997/4000']  interval_lower 142218339/549755813888
noncomputable def e2702 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281530999603,0,true,168433471680,168433471744⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917492255949,0,false,-198986586304,-198986586240⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281644950455,0,true,168531233472,168531233536⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917378305097,0,false,-199123152128,-199123152064⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281371732652,0,true,168296817408,168296817472⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917651522900,0,false,-198795739264,-198795739200⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281508350464,0,true,168414039296,168414039360⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917514905088,0,false,-198959444160,-198959444096⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581266605,0,true,69636608,69636672⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441988947,0,false,-69641088,-69641024⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592926776,0,true,81295936,81296000⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430328776,0,false,-81302016,-81301952⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621764,0,false,-6016,-5952⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623366,0,false,-4416,-4352⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281451362065,0,true,168365143168,168365143232⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917571893487,0,false,-198891153792,-198891153728⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281576659445,0,true,168472645632,168472645696⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917446596107,0,false,-199041305856,-199041305792⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069363992299,0,false,-30568660160,-30568660096⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069405473301,0,false,-30526010560,-30526010496⟩
    { al := (27123/163840), au := (1356999/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨182019371827,182133322679⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168433471680,168433471744⟩ : DyadicInterval 40),(⟨-198986586304,-198986586240⟩ : DyadicInterval 40),(⟨746987543913,746987563243⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168531233472,168531233536⟩ : DyadicInterval 40),(⟨-199123152128,-199123152064⟩ : DyadicInterval 40),(⟨746968498543,746968517872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168296817408,168296817472⟩ : DyadicInterval 40),(⟨-198795739264,-198795739200⟩ : DyadicInterval 40),(⟨747014142866,747014162196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168414039296,168414039360⟩ : DyadicInterval 40),(⟨-198959444160,-198959444096⟩ : DyadicInterval 40),(⟨746991327951,746991347281⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨69638829,81299000⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69636608,69636672⟩ : DyadicInterval 40),(⟨-69641088,-69641024⟩ : DyadicInterval 40),(⟨762123381381,762123400710⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81295936,81296000⟩ : DyadicInterval 40),(⟨-81302016,-81301952⟩ : DyadicInterval 40),(⟨762123380580,762123399909⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6016,-4352⟩ : DyadicInterval 40),(⟨762123385792,762123405888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181939734289,182065031669⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168365143168,168365143232⟩ : DyadicInterval 40),(⟨-198891153792,-198891153728⟩ : DyadicInterval 40),(⟨747000847048,747000866377⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168472645632,168472645696⟩ : DyadicInterval 40),(⟨-199041305856,-199041305792⟩ : DyadicInterval 40),(⟨746979913935,746979933265⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30568660160,-30526010496⟩ : DyadicInterval 40),(⟨777386388864,777407732960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168433471680,168531233536⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199123152128,-198986586240⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2702_ok : ecellOkT e2702 = true := by decide +kernel
theorem e2702_pos {a z : ℝ} (ha1 : ((27123/163840 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1356999/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2702 e2702_ok ha1 ha2 hz1 hz2 hz

-- box ['1356999/8192000', '169731/1024000', '7993/8000', '3997/4000']  interval_lower 285789943/1099511627776
noncomputable def e2703 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281644950454,0,true,168531233472,168531233536⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917378305098,0,false,-199123152128,-199123152064⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281758901306,0,true,168628986496,168628986560⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917264354246,0,false,-199259734848,-199259734784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281485583796,0,true,168394505728,168394505792⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917537671756,0,false,-198932161920,-198932161856⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281622215851,0,true,168511729472,168511729536⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917401039701,0,false,-199095904192,-199095904128⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581311976,0,true,69681984,69682048⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441943576,0,false,-69686464,-69686400⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592979715,0,true,81348928,81348992⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430275837,0,false,-81355008,-81354944⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621756,0,false,-6080,-6016⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623360,0,false,-4480,-4416⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281565263060,0,true,168462868224,168462868288⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917457992492,0,false,-199027648000,-199027647936⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281690567565,0,true,168570367296,168570367360⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917332687987,0,false,-199177827264,-199177827200⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069326257049,0,false,-30607459968,-30607459904⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069367766372,0,false,-30564779712,-30564779648⟩
    { al := (1356999/8192000), au := (169731/1024000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨182133322678,182247273530⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168531233472,168531233536⟩ : DyadicInterval 40),(⟨-199123152128,-199123152064⟩ : DyadicInterval 40),(⟨746968498543,746968517872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168628986496,168628986560⟩ : DyadicInterval 40),(⟨-199259734848,-199259734784⟩ : DyadicInterval 40),(⟨746949441046,746949460376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168394505728,168394505792⟩ : DyadicInterval 40),(⟨-198932161920,-198932161856⟩ : DyadicInterval 40),(⟨746995131173,746995150502⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168511729472,168511729536⟩ : DyadicInterval 40),(⟨-199095904192,-199095904128⟩ : DyadicInterval 40),(⟨746972299299,746972318629⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨69684200,81351939⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69681984,69682048⟩ : DyadicInterval 40),(⟨-69686464,-69686400⟩ : DyadicInterval 40),(⟨762123381375,762123400704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81348928,81348992⟩ : DyadicInterval 40),(⟨-81355008,-81354944⟩ : DyadicInterval 40),(⟨762123380572,762123399902⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6080,-4416⟩ : DyadicInterval 40),(⟨762123385824,762123405920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182053635284,182178939789⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168462868224,168462868288⟩ : DyadicInterval 40),(⟨-199027648000,-199027647936⟩ : DyadicInterval 40),(⟨746981818512,746981837842⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168570367296,168570367360⟩ : DyadicInterval 40),(⟨-199177827264,-199177827200⟩ : DyadicInterval 40),(⟨746960870841,746960890170⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30607459968,-30564779648⟩ : DyadicInterval 40),(⟨777405773440,777427132864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168531233472,168628986560⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199259734848,-199123152064⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2703_ok : ecellOkT e2703 = true := by decide +kernel
theorem e2703_pos {a z : ℝ} (ha1 : ((1356999/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((169731/1024000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2703 e2703_ok ha1 ha2 hz1 hz2 hz

-- box ['338613/2048000', '1355301/8192000', '3997/4000', '1599/1600']  interval_lower 281547373/1099511627776
noncomputable def e2704 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281303097901,0,true,168237922112,168237922176⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917720157651,0,false,-198713505600,-198713505536⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281417048753,0,true,168335701248,168335701312⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917606206799,0,false,-198850037440,-198850037376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281166754298,0,true,168120916736,168120916800⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917856501254,0,false,-198550165760,-198550165696⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281303357865,0,true,168238145216,168238145280⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917719897687,0,false,-198713817024,-198713816960⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569584626,0,true,57955264,57955328⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453670926,0,false,-57958400,-57958336⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581222106,0,true,69592064,69592128⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099442033446,0,false,-69596544,-69596480⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623370,0,false,-4416,-4352⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624722,0,false,-3072,-3008⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281234921854,0,true,168179417344,168179417408⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917788333698,0,false,-198631827520,-198631827456⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281360212138,0,true,168286931904,168286931968⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917663043414,0,false,-198781935744,-198781935680⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069435631489,0,false,-30495003776,-30495003712⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069477060814,0,false,-30452410176,-30452410112⟩
    { al := (338613/2048000), au := (1355301/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨181791470125,181905420977⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168237922112,168237922176⟩ : DyadicInterval 40),(⟨-198713505600,-198713505536⟩ : DyadicInterval 40),(⟨747025598197,747025617527⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168335701248,168335701312⟩ : DyadicInterval 40),(⟨-198850037440,-198850037376⟩ : DyadicInterval 40),(⟨747006577109,747006596439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168120916736,168120916800⟩ : DyadicInterval 40),(⟨-198550165760,-198550165696⟩ : DyadicInterval 40),(⟨747048341179,747048360508⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168238145216,168238145280⟩ : DyadicInterval 40),(⟨-198713817024,-198713816960⟩ : DyadicInterval 40),(⟨747025554788,747025574118⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57956850,69594330⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57955264,57955328⟩ : DyadicInterval 40),(⟨-57958400,-57958336⟩ : DyadicInterval 40),(⟨762123382064,762123401394⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69592064,69592128⟩ : DyadicInterval 40),(⟨-69596544,-69596480⟩ : DyadicInterval 40),(⟨762123381386,762123400716⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4416,-3008⟩ : DyadicInterval 40),(⟨762123385120,762123405088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181723294078,181848584362⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168179417344,168179417408⟩ : DyadicInterval 40),(⟨-198631827520,-198631827456⟩ : DyadicInterval 40),(⟨747036972548,747036991877⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168286931904,168286931968⟩ : DyadicInterval 40),(⟨-198781935744,-198781935680⟩ : DyadicInterval 40),(⟨747016065996,747016085325⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30495003776,-30452410112⟩ : DyadicInterval 40),(⟨777349588672,777370904768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168237922112,168335701312⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198850037440,-198713505536⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2704_ok : ecellOkT e2704 = true := by decide +kernel
theorem e2704_pos {a z : ℝ} (ha1 : ((338613/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1355301/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2704 e2704_ok ha1 ha2 hz1 hz2 hz

-- box ['1355301/8192000', '27123/163840', '3997/4000', '1599/1600']  interval_lower 282894131/1099511627776
noncomputable def e2705 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281417048752,0,true,168335701248,168335701312⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917606206800,0,false,-198850037440,-198850037376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281530999604,0,true,168433471744,168433471808⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917492255948,0,false,-198986586304,-198986586240⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281280619686,0,true,168218632960,168218633024⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917742635866,0,false,-198686574976,-198686574912⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281417237497,0,true,168335863232,168335863296⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917606018055,0,false,-198850263616,-198850263552⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569622431,0,true,57993088,57993152⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453633121,0,false,-57996224,-57996160⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581267475,0,true,69637440,69637504⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441988077,0,false,-69641920,-69641856⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623365,0,false,-4416,-4352⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624718,0,false,-3072,-3008⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281348829975,0,true,168277165056,168277165120⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917674425577,0,false,-198768298112,-198768298048⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281474127383,0,true,168384676096,168384676160⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917549128169,0,false,-198918433408,-198918433344⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069397938728,0,false,-30533757248,-30533757184⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069439396371,0,false,-30491133056,-30491132992⟩
    { al := (1355301/8192000), au := (27123/163840), zl := (3997/4000), zu := (1599/1600),
      A := ⟨181905420976,182019371828⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168335701248,168335701312⟩ : DyadicInterval 40),(⟨-198850037440,-198850037376⟩ : DyadicInterval 40),(⟨747006577109,747006596439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168433471744,168433471808⟩ : DyadicInterval 40),(⟨-198986586304,-198986586240⟩ : DyadicInterval 40),(⟨746987543875,746987563205⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168218632960,168218633024⟩ : DyadicInterval 40),(⟨-198686574976,-198686574912⟩ : DyadicInterval 40),(⟨747029348885,747029368214⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168335863232,168335863296⟩ : DyadicInterval 40),(⟨-198850263616,-198850263552⟩ : DyadicInterval 40),(⟨747006545580,747006564910⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57994655,69639699⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57993088,57993152⟩ : DyadicInterval 40),(⟨-57996224,-57996160⟩ : DyadicInterval 40),(⟨762123382060,762123401390⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69637440,69637504⟩ : DyadicInterval 40),(⟨-69641920,-69641856⟩ : DyadicInterval 40),(⟨762123381381,762123400710⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4416,-3008⟩ : DyadicInterval 40),(⟨762123385120,762123405088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181837202199,181962499607⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168277165056,168277165120⟩ : DyadicInterval 40),(⟨-198768298112,-198768298048⟩ : DyadicInterval 40),(⟨747017965871,747017985201⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168384676096,168384676160⟩ : DyadicInterval 40),(⟨-198918433408,-198918433344⟩ : DyadicInterval 40),(⟨746997044787,746997064116⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30533757248,-30491132992⟩ : DyadicInterval 40),(⟨777368950112,777390281504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168335701248,168433471808⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198986586304,-198850037376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2705_ok : ecellOkT e2705 = true := by decide +kernel
theorem e2705_pos {a z : ℝ} (ha1 : ((1355301/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((27123/163840 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2705 e2705_ok ha1 ha2 hz1 hz2 hz

-- box ['338613/2048000', '1355301/8192000', '1599/1600', '1999/2000']  interval_lower 140677583/549755813888
noncomputable def e2706 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281303097901,0,true,168237922112,168237922176⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917720157651,0,false,-198713505600,-198713505536⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281417048753,0,true,168335701248,168335701312⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917606206799,0,false,-198850037440,-198850037376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281189478232,0,true,168140418496,168140418560⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917833777320,0,false,-198577387392,-198577387328⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281326096043,0,true,168257657088,168257657152⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917697159509,0,false,-198741059776,-198741059712⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557993322,0,true,46364544,46364608⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465262230,0,false,-46366528,-46366464⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569623242,0,true,57993920,57993984⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453632310,0,false,-57997056,-57996992⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624716,0,false,-3072,-3008⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625821,0,false,-1984,-1920⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281246283664,0,true,168189167616,168189167680⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917776971888,0,false,-198645439104,-198645439040⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281371581097,0,true,168296687360,168296687424⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917651674455,0,false,-198795557696,-198795557632⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069431870739,0,false,-30498870336,-30498870272⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069473305019,0,false,-30456271424,-30456271360⟩
    { al := (338613/2048000), au := (1355301/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨181791470125,181905420977⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168237922112,168237922176⟩ : DyadicInterval 40),(⟨-198713505600,-198713505536⟩ : DyadicInterval 40),(⟨747025598197,747025617527⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168335701248,168335701312⟩ : DyadicInterval 40),(⟨-198850037440,-198850037376⟩ : DyadicInterval 40),(⟨747006577109,747006596439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168140418496,168140418560⟩ : DyadicInterval 40),(⟨-198577387392,-198577387328⟩ : DyadicInterval 40),(⟨747044551893,747044571223⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168257657088,168257657152⟩ : DyadicInterval 40),(⟨-198741059776,-198741059712⟩ : DyadicInterval 40),(⟨747021760243,747021779572⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨46365546,57995466⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46364544,46364608⟩ : DyadicInterval 40),(⟨-46366528,-46366464⟩ : DyadicInterval 40),(⟨762123382588,762123401917⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57993920,57993984⟩ : DyadicInterval 40),(⟨-57997056,-57996992⟩ : DyadicInterval 40),(⟨762123382060,762123401390⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3072,-1920⟩ : DyadicInterval 40),(⟨762123384576,762123404416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181734655888,181859953321⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168189167616,168189167680⟩ : DyadicInterval 40),(⟨-198645439104,-198645439040⟩ : DyadicInterval 40),(⟨747035077279,747035096608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168296687360,168296687424⟩ : DyadicInterval 40),(⟨-198795557696,-198795557632⟩ : DyadicInterval 40),(⟨747014168177,747014187506⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30498870336,-30456271360⟩ : DyadicInterval 40),(⟨777351519296,777372838048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168237922112,168335701312⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198850037440,-198713505536⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2706_ok : ecellOkT e2706 = true := by decide +kernel
theorem e2706_pos {a z : ℝ} (ha1 : ((338613/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1355301/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2706 e2706_ok ha1 ha2 hz1 hz2 hz

-- box ['1355301/8192000', '27123/163840', '1599/1600', '1999/2000']  interval_lower 282701423/1099511627776
noncomputable def e2707 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281417048752,0,true,168335701248,168335701312⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917606206800,0,false,-198850037440,-198850037376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281530999604,0,true,168433471744,168433471808⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917492255948,0,false,-198986586304,-198986586240⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281303357863,0,true,168238145216,168238145280⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917719897689,0,false,-198713817024,-198713816960⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281439989919,0,true,168355385600,168355385664⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917583265633,0,false,-198877526784,-198877526720⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558023566,0,true,46394752,46394816⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465231986,0,false,-46396800,-46396736⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569661049,0,true,58031680,58031744⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453594503,0,false,-58034816,-58034752⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624712,0,false,-3072,-3008⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625819,0,false,-1984,-1920⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281360198908,0,true,168286920512,168286920576⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917663056644,0,false,-198781919872,-198781919808⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281485503466,0,true,168394436800,168394436864⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917537752086,0,false,-198932065664,-198932065600⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069394173265,0,false,-30537628800,-30537628736⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069435635866,0,false,-30494999296,-30494999232⟩
    { al := (1355301/8192000), au := (27123/163840), zl := (1599/1600), zu := (1999/2000),
      A := ⟨181905420976,182019371828⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168335701248,168335701312⟩ : DyadicInterval 40),(⟨-198850037440,-198850037376⟩ : DyadicInterval 40),(⟨747006577109,747006596439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168433471744,168433471808⟩ : DyadicInterval 40),(⟨-198986586304,-198986586240⟩ : DyadicInterval 40),(⟨746987543875,746987563205⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168238145216,168238145280⟩ : DyadicInterval 40),(⟨-198713817024,-198713816960⟩ : DyadicInterval 40),(⟨747025554788,747025574118⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168355385600,168355385664⟩ : DyadicInterval 40),(⟨-198877526784,-198877526720⟩ : DyadicInterval 40),(⟨747002746216,747002765546⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨46395790,58033273⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46394752,46394816⟩ : DyadicInterval 40),(⟨-46396800,-46396736⟩ : DyadicInterval 40),(⟨762123382618,762123401947⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58031680,58031744⟩ : DyadicInterval 40),(⟨-58034816,-58034752⟩ : DyadicInterval 40),(⟨762123382056,762123401386⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3072,-1920⟩ : DyadicInterval 40),(⟨762123384576,762123404416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181848571132,181973875690⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168286920512,168286920576⟩ : DyadicInterval 40),(⟨-198781919872,-198781919808⟩ : DyadicInterval 40),(⟨747016068219,747016087548⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168394436800,168394436864⟩ : DyadicInterval 40),(⟨-198932065664,-198932065600⟩ : DyadicInterval 40),(⟨746995144597,746995163926⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30537628800,-30494999232⟩ : DyadicInterval 40),(⟨777370883232,777392217280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168335701248,168433471808⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198986586304,-198850037376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2707_ok : ecellOkT e2707 = true := by decide +kernel
theorem e2707_pos {a z : ℝ} (ha1 : ((1355301/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((27123/163840 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2707 e2707_ok ha1 ha2 hz1 hz2 hz

-- box ['27123/163840', '1356999/8192000', '3997/4000', '1599/1600']  interval_lower 284243687/1099511627776
noncomputable def e2708 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281530999603,0,true,168433471680,168433471744⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917492255949,0,false,-198986586304,-198986586240⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281644950455,0,true,168531233472,168531233536⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917378305097,0,false,-199123152128,-199123152064⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281394485074,0,true,168316340480,168316340544⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917628770478,0,false,-198823001088,-198823001024⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281531117129,0,true,168433572544,168433572608⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917492138423,0,false,-198986727168,-198986727104⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569660238,0,true,58030912,58030976⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453595314,0,false,-58034048,-58033984⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581312848,0,true,69682816,69682880⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441942704,0,false,-69687296,-69687232⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623359,0,false,-4480,-4416⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624714,0,false,-3072,-3008⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281462738091,0,true,168374904000,168374904064⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917560517461,0,false,-198904785600,-198904785536⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281588042620,0,true,168482411648,168482411712⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917435212932,0,false,-199054948096,-199054948032⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069360222365,0,false,-30572536384,-30572536320⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069401708328,0,false,-30529881536,-30529881472⟩
    { al := (27123/163840), au := (1356999/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨182019371827,182133322679⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168433471680,168433471744⟩ : DyadicInterval 40),(⟨-198986586304,-198986586240⟩ : DyadicInterval 40),(⟨746987543913,746987563243⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168531233472,168531233536⟩ : DyadicInterval 40),(⟨-199123152128,-199123152064⟩ : DyadicInterval 40),(⟨746968498543,746968517872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168316340480,168316340544⟩ : DyadicInterval 40),(⟨-198823001088,-198823001024⟩ : DyadicInterval 40),(⟨747010344467,747010363797⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168433572544,168433572608⟩ : DyadicInterval 40),(⟨-198986727168,-198986727104⟩ : DyadicInterval 40),(⟨746987524268,746987543597⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨58032462,69685072⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58030912,58030976⟩ : DyadicInterval 40),(⟨-58034048,-58033984⟩ : DyadicInterval 40),(⟨762123382056,762123401386⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69682816,69682880⟩ : DyadicInterval 40),(⟨-69687296,-69687232⟩ : DyadicInterval 40),(⟨762123381375,762123400704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4480,-3008⟩ : DyadicInterval 40),(⟨762123385120,762123405120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181951110315,182076414844⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168374904000,168374904064⟩ : DyadicInterval 40),(⟨-198904785600,-198904785536⟩ : DyadicInterval 40),(⟨746998947090,746998966420⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168482411648,168482411712⟩ : DyadicInterval 40),(⟨-199054948096,-199054948032⟩ : DyadicInterval 40),(⟨746978011448,746978030778⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30572536384,-30529881472⟩ : DyadicInterval 40),(⟨777388324352,777409671072⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168433471680,168531233536⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199123152128,-198986586240⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2708_ok : ecellOkT e2708 = true := by decide +kernel
theorem e2708_pos {a z : ℝ} (ha1 : ((27123/163840 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1356999/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2708 e2708_ok ha1 ha2 hz1 hz2 hz

-- box ['1356999/8192000', '169731/1024000', '3997/4000', '1599/1600']  interval_lower 71399181/274877906944
noncomputable def e2709 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281644950454,0,true,168531233472,168531233536⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917378305098,0,false,-199123152128,-199123152064⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281758901306,0,true,168628986496,168628986560⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917264354246,0,false,-199259734848,-199259734784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281508350461,0,true,168414039296,168414039360⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917514905091,0,false,-198959444160,-198959444096⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281644996761,0,true,168531273216,168531273280⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917378258791,0,false,-199123207616,-199123207552⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569698048,0,true,58068736,58068800⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453557504,0,false,-58071808,-58071744⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581358223,0,true,69728192,69728256⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441897329,0,false,-69732672,-69732608⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623353,0,false,-4480,-4416⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624710,0,false,-3072,-3008⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281576646209,0,true,168472634304,168472634368⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917446609343,0,false,-199041289984,-199041289920⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281701957865,0,true,168580138496,168580138560⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917321297687,0,false,-199191479680,-199191479616⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069322482395,0,false,-30611341184,-30611341120⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069363996683,0,false,-30568655680,-30568655616⟩
    { al := (1356999/8192000), au := (169731/1024000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨182133322678,182247273530⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168531233472,168531233536⟩ : DyadicInterval 40),(⟨-199123152128,-199123152064⟩ : DyadicInterval 40),(⟨746968498543,746968517872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168628986496,168628986560⟩ : DyadicInterval 40),(⟨-199259734848,-199259734784⟩ : DyadicInterval 40),(⟨746949441046,746949460376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168414039296,168414039360⟩ : DyadicInterval 40),(⟨-198959444160,-198959444096⟩ : DyadicInterval 40),(⟨746991327952,746991347282⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168531273216,168531273280⟩ : DyadicInterval 40),(⟨-199123207616,-199123207552⟩ : DyadicInterval 40),(⟨746968490785,746968510115⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨58070272,69730447⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58068736,58068800⟩ : DyadicInterval 40),(⟨-58071808,-58071744⟩ : DyadicInterval 40),(⟨762123382020,762123401350⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69728192,69728256⟩ : DyadicInterval 40),(⟨-69732672,-69732608⟩ : DyadicInterval 40),(⟨762123381369,762123400698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4480,-3008⟩ : DyadicInterval 40),(⟨762123385120,762123405120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182065018433,182190330089⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168472634304,168472634368⟩ : DyadicInterval 40),(⟨-199041289984,-199041289920⟩ : DyadicInterval 40),(⟨746979916128,746979935457⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168580138496,168580138560⟩ : DyadicInterval 40),(⟨-199191479680,-199191479616⟩ : DyadicInterval 40),(⟨746958965961,746958985290⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30611341184,-30568655616⟩ : DyadicInterval 40),(⟨777407711424,777429073472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168531233472,168628986560⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199259734848,-199123152064⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2709_ok : ecellOkT e2709 = true := by decide +kernel
theorem e2709_pos {a z : ℝ} (ha1 : ((1356999/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((169731/1024000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2709 e2709_ok ha1 ha2 hz1 hz2 hz

-- box ['27123/163840', '1356999/8192000', '1599/1600', '1999/2000']  interval_lower 142025453/549755813888
noncomputable def e2710 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281530999603,0,true,168433471680,168433471744⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917492255949,0,false,-198986586304,-198986586240⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281644950455,0,true,168531233472,168531233536⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917378305097,0,false,-199123152128,-199123152064⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281417237495,0,true,168335863232,168335863296⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917606018057,0,false,-198850263616,-198850263552⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281553883794,0,true,168453105408,168453105472⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917469371758,0,false,-199014010816,-199014010752⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558053811,0,true,46425024,46425088⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465201741,0,false,-46427072,-46427008⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569698860,0,true,58069504,58069568⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453556692,0,false,-58072640,-58072576⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624708,0,false,-3072,-3008⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625816,0,false,-1984,-1920⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281474114146,0,true,168384664768,168384664832⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917549141406,0,false,-198918417600,-198918417536⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281599425824,0,true,168492177600,168492177664⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917423829728,0,false,-199068590528,-199068590464⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069356452186,0,false,-30576412864,-30576412800⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069397943110,0,false,-30533752768,-30533752704⟩
    { al := (27123/163840), au := (1356999/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨182019371827,182133322679⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168433471680,168433471744⟩ : DyadicInterval 40),(⟨-198986586304,-198986586240⟩ : DyadicInterval 40),(⟨746987543913,746987563243⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168531233472,168531233536⟩ : DyadicInterval 40),(⟨-199123152128,-199123152064⟩ : DyadicInterval 40),(⟨746968498543,746968517872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168335863232,168335863296⟩ : DyadicInterval 40),(⟨-198850263616,-198850263552⟩ : DyadicInterval 40),(⟨747006545581,747006564910⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168453105408,168453105472⟩ : DyadicInterval 40),(⟨-199014010816,-199014010752⟩ : DyadicInterval 40),(⟨746983720106,746983739435⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨46426035,58071084⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46425024,46425088⟩ : DyadicInterval 40),(⟨-46427072,-46427008⟩ : DyadicInterval 40),(⟨762123382615,762123401944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58069504,58069568⟩ : DyadicInterval 40),(⟨-58072640,-58072576⟩ : DyadicInterval 40),(⟨762123382052,762123401382⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3072,-1920⟩ : DyadicInterval 40),(⟨762123384576,762123404416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181962486370,182087798048⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168384664768,168384664832⟩ : DyadicInterval 40),(⟨-198918417600,-198918417536⟩ : DyadicInterval 40),(⟨746997047003,746997066333⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168492177600,168492177664⟩ : DyadicInterval 40),(⟨-199068590528,-199068590464⟩ : DyadicInterval 40),(⟨746976108831,746976128161⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30576412864,-30533752704⟩ : DyadicInterval 40),(⟨777390259968,777411609312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168433471680,168531233536⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199123152128,-198986586240⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2710_ok : ecellOkT e2710 = true := by decide +kernel
theorem e2710_pos {a z : ℝ} (ha1 : ((27123/163840 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1356999/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2710 e2710_ok ha1 ha2 hz1 hz2 hz

-- box ['1356999/8192000', '169731/1024000', '1599/1600', '1999/2000']  interval_lower 142701669/549755813888
noncomputable def e2711 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281644950454,0,true,168531233472,168531233536⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917378305098,0,false,-199123152128,-199123152064⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281758901306,0,true,168628986496,168628986560⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917264354246,0,false,-199259734848,-199259734784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281531117127,0,true,168433572544,168433572608⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917492138425,0,false,-198986727168,-198986727104⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281667777670,0,true,168550816576,168550816640⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917355477882,0,false,-199150511680,-199150511616⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558084060,0,true,46455296,46455360⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465171492,0,false,-46457280,-46457216⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569736674,0,true,58107328,58107392⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453518878,0,false,-58110464,-58110400⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624704,0,false,-3136,-3072⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625814,0,false,-1984,-1920⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281588029385,0,true,168482400320,168482400384⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917435226167,0,false,-199054932224,-199054932160⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281713348193,0,true,168589909696,168589909760⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917309907359,0,false,-199205132352,-199205132288⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069318707497,0,false,-30615222656,-30615222592⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069360226750,0,false,-30572531904,-30572531840⟩
    { al := (1356999/8192000), au := (169731/1024000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨182133322678,182247273530⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168531233472,168531233536⟩ : DyadicInterval 40),(⟨-199123152128,-199123152064⟩ : DyadicInterval 40),(⟨746968498543,746968517872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168628986496,168628986560⟩ : DyadicInterval 40),(⟨-199259734848,-199259734784⟩ : DyadicInterval 40),(⟨746949441046,746949460376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168433572544,168433572608⟩ : DyadicInterval 40),(⟨-198986727168,-198986727104⟩ : DyadicInterval 40),(⟨746987524268,746987543598⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168550816576,168550816640⟩ : DyadicInterval 40),(⟨-199150511680,-199150511616⟩ : DyadicInterval 40),(⟨746964681792,746964701121⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨46456284,58108898⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46455296,46455360⟩ : DyadicInterval 40),(⟨-46457280,-46457216⟩ : DyadicInterval 40),(⟨762123382581,762123401910⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58107328,58107392⟩ : DyadicInterval 40),(⟨-58110464,-58110400⟩ : DyadicInterval 40),(⟨762123382048,762123401378⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3136,-1920⟩ : DyadicInterval 40),(⟨762123384576,762123404448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182076401609,182201720417⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168482400320,168482400384⟩ : DyadicInterval 40),(⟨-199054932224,-199054932160⟩ : DyadicInterval 40),(⟨746978013640,746978032970⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168589909696,168589909760⟩ : DyadicInterval 40),(⟨-199205132352,-199205132288⟩ : DyadicInterval 40),(⟨746957060939,746957080269⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30615222656,-30572531840⟩ : DyadicInterval 40),(⟨777409649536,777431014208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168531233472,168628986560⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199259734848,-199123152064⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2711_ok : ecellOkT e2711 = true := by decide +kernel
theorem e2711_pos {a z : ℝ} (ha1 : ((1356999/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((169731/1024000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2711 e2711_ok ha1 ha2 hz1 hz2 hz

-- box ['84441/512000', '270381/1638400', '1999/2000', '7997/8000']  interval_lower 34476339/137438953472
noncomputable def e2712 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280847294496,0,true,167846718592,167846718656⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918175961056,0,false,-198167547520,-198167547456⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280961245348,0,true,167944532544,167944532608⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918062010204,0,false,-198304011584,-198304011520⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280756626662,0,true,167768884288,167768884352⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918266628890,0,false,-198058978560,-198058978496⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280893201742,0,true,167886125824,167886125888⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918130053810,0,false,-198222522624,-198222522560⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546311245,0,true,34682880,34682944⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476944307,0,false,-34684032,-34683968⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557903355,0,true,46274560,46274624⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465352197,0,false,-46276608,-46276544⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625828,0,false,-1984,-1920⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626682,0,false,-1152,-1088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280801956061,0,true,167807798272,167807798336⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918221299491,0,false,-198113256256,-198113256192⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280927232147,0,true,167915336960,167915337024⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918096023405,0,false,-198263276672,-198263276608⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069578682386,0,false,-30347939648,-30347939584⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069620008353,0,false,-30305457984,-30305457920⟩
    { al := (84441/512000), au := (270381/1638400), zl := (1999/2000), zu := (7997/8000),
      A := ⟨181335666720,181449617572⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167846718592,167846718656⟩ : DyadicInterval 40),(⟨-198167547520,-198167547456⟩ : DyadicInterval 40),(⟨747101561058,747101580387⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167944532544,167944532608⟩ : DyadicInterval 40),(⟨-198304011584,-198304011520⟩ : DyadicInterval 40),(⟨747082588522,747082607852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167768884288,167768884352⟩ : DyadicInterval 40),(⟨-198058978560,-198058978496⟩ : DyadicInterval 40),(⟨747116648332,747116667662⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167886125824,167886125888⟩ : DyadicInterval 40),(⟨-198222522624,-198222522560⟩ : DyadicInterval 40),(⟨747093919089,747093938418⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34683469,46275579⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34682880,34682944⟩ : DyadicInterval 40),(⟨-34684032,-34683968⟩ : DyadicInterval 40),(⟨762123383033,762123402362⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46274560,46274624⟩ : DyadicInterval 40),(⟨-46276608,-46276544⟩ : DyadicInterval 40),(⟨762123382628,762123401957⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1984,-1088⟩ : DyadicInterval 40),(⟨762123384160,762123403872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181290328285,181415604371⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167807798272,167807798336⟩ : DyadicInterval 40),(⟨-198113256256,-198113256192⟩ : DyadicInterval 40),(⟨747109106381,747109125710⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167915336960,167915337024⟩ : DyadicInterval 40),(⟨-198263276672,-198263276608⟩ : DyadicInterval 40),(⟨747088252921,747088272250⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30347939648,-30305457920⟩ : DyadicInterval 40),(⟨777276112576,777297372704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167846718592,167944532608⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198304011584,-198167547456⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2712_ok : ecellOkT e2712 = true := by decide +kernel
theorem e2712_pos {a z : ℝ} (ha1 : ((84441/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((270381/1638400 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2712 e2712_ok ha1 ha2 hz1 hz2 hz

-- box ['270381/1638400', '676377/4096000', '1999/2000', '7997/8000']  interval_lower 138571977/549755813888
noncomputable def e2713 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280961245347,0,true,167944532544,167944532608⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918062010205,0,false,-198304011584,-198304011520⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281075196199,0,true,168042337728,168042337792⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917948059353,0,false,-198440492672,-198440492608⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280870520538,0,true,167866656256,167866656320⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918152735014,0,false,-198195360960,-198195360896⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281007109861,0,true,167983899584,167983899648⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918016145691,0,false,-198358942336,-198358942272⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546333921,0,true,34705536,34705600⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476921631,0,false,-34706752,-34706688⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557933593,0,true,46304832,46304896⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465321959,0,false,-46306816,-46306752⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625825,0,false,-1984,-1920⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626681,0,false,-1152,-1088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280915878426,0,true,167905591168,167905591232⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918107377126,0,false,-198249679552,-198249679488⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281041161629,0,true,168013126464,168013126528⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917982093923,0,false,-198399727040,-198399726976⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069541074642,0,false,-30386600576,-30386600512⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069582428919,0,false,-30344088320,-30344088256⟩
    { al := (270381/1638400), au := (676377/4096000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨181449617571,181563568423⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167944532544,167944532608⟩ : DyadicInterval 40),(⟨-198304011584,-198304011520⟩ : DyadicInterval 40),(⟨747082588523,747082607852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168042337728,168042337792⟩ : DyadicInterval 40),(⟨-198440492672,-198440492608⟩ : DyadicInterval 40),(⟨747063603922,747063623251⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167866656256,167866656320⟩ : DyadicInterval 40),(⟨-198195360960,-198195360896⟩ : DyadicInterval 40),(⟨747097694958,747097714287⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167983899584,167983899648⟩ : DyadicInterval 40),(⟨-198358942336,-198358942272⟩ : DyadicInterval 40),(⟨747074948789,747074968118⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34706145,46305817⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34705536,34705600⟩ : DyadicInterval 40),(⟨-34706752,-34706688⟩ : DyadicInterval 40),(⟨762123383064,762123402393⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46304832,46304896⟩ : DyadicInterval 40),(⟨-46306816,-46306752⟩ : DyadicInterval 40),(⟨762123382593,762123401922⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1984,-1088⟩ : DyadicInterval 40),(⟨762123384160,762123403872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181404250650,181529533853⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167905591168,167905591232⟩ : DyadicInterval 40),(⟨-198249679552,-198249679488⟩ : DyadicInterval 40),(⟨747090143493,747090162822⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168013126464,168013126528⟩ : DyadicInterval 40),(⟨-198399727040,-198399726976⟩ : DyadicInterval 40),(⟨747069275438,747069294768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30386600576,-30344088256⟩ : DyadicInterval 40),(⟨777295427744,777316703168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167944532544,168042337792⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198440492672,-198304011520⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2713_ok : ecellOkT e2713 = true := by decide +kernel
theorem e2713_pos {a z : ℝ} (ha1 : ((270381/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((676377/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2713 e2713_ok ha1 ha2 hz1 hz2 hz

-- box ['84441/512000', '270381/1638400', '7997/8000', '3999/4000']  interval_lower 275620017/1099511627776
noncomputable def e2714 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280847294496,0,true,167846718592,167846718656⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918175961056,0,false,-198167547520,-198167547456⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280961245348,0,true,167944532544,167944532608⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918062010204,0,false,-198304011584,-198304011520⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280779293620,0,true,167788343360,167788343424⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918243961932,0,false,-198086119744,-198086119680⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280915882944,0,true,167905595072,167905595136⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918107372608,0,false,-198249684928,-198249684864⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534750062,0,true,23121984,23122048⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488505490,0,false,-23122560,-23122496⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546334613,0,true,34706240,34706304⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476920939,0,false,-34707392,-34707328⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626680,0,false,-1152,-1088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627290,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280813289443,0,true,167817527424,167817527488⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918209966109,0,false,-198126827328,-198126827264⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280938572679,0,true,167925071296,167925071360⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918084682873,0,false,-198276858176,-198276858112⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069574939972,0,false,-30351786816,-30351786752⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069616270881,0,false,-30309299904,-30309299840⟩
    { al := (84441/512000), au := (270381/1638400), zl := (7997/8000), zu := (3999/4000),
      A := ⟨181335666720,181449617572⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167846718592,167846718656⟩ : DyadicInterval 40),(⟨-198167547520,-198167547456⟩ : DyadicInterval 40),(⟨747101561058,747101580387⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167944532544,167944532608⟩ : DyadicInterval 40),(⟨-198304011584,-198304011520⟩ : DyadicInterval 40),(⟨747082588522,747082607852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167788343360,167788343424⟩ : DyadicInterval 40),(⟨-198086119744,-198086119680⟩ : DyadicInterval 40),(⟨747112877225,747112896555⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167905595072,167905595136⟩ : DyadicInterval 40),(⟨-198249684928,-198249684864⟩ : DyadicInterval 40),(⟨747090142711,747090162041⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23122286,34706837⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23121984,23122048⟩ : DyadicInterval 40),(⟨-23122560,-23122496⟩ : DyadicInterval 40),(⟨762123383353,762123402682⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34706240,34706304⟩ : DyadicInterval 40),(⟨-34707392,-34707328⟩ : DyadicInterval 40),(⟨762123383032,762123402361⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1152,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181301661667,181426944903⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167817527424,167817527488⟩ : DyadicInterval 40),(⟨-198126827328,-198126827264⟩ : DyadicInterval 40),(⟨747107220427,747107239756⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167925071296,167925071360⟩ : DyadicInterval 40),(⟨-198276858176,-198276858112⟩ : DyadicInterval 40),(⟨747086364457,747086383786⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30351786816,-30309299840⟩ : DyadicInterval 40),(⟨777278033536,777299296288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167846718592,167944532608⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198304011584,-198167547456⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2714_ok : ecellOkT e2714 = true := by decide +kernel
theorem e2714_pos {a z : ℝ} (ha1 : ((84441/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((270381/1638400 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2714 e2714_ok ha1 ha2 hz1 hz2 hz

-- box ['270381/1638400', '676377/4096000', '7997/8000', '3999/4000']  interval_lower 276952983/1099511627776
noncomputable def e2715 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280961245347,0,true,167944532544,167944532608⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918062010205,0,false,-198304011584,-198304011520⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281075196199,0,true,168042337728,168042337792⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917948059353,0,false,-198440492672,-198440492608⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280893201740,0,true,167886125824,167886125888⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918130053812,0,false,-198222522624,-198222522560⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281029805308,0,true,168003379328,168003379392⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917993450244,0,false,-198386125120,-198386125056⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534765179,0,true,23137152,23137216⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488490373,0,false,-23137664,-23137600⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546357291,0,true,34728960,34729024⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476898261,0,false,-34730112,-34730048⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626679,0,false,-1152,-1088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627290,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280927218927,0,true,167915325568,167915325632⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918096036625,0,false,-198263260800,-198263260736⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281052509282,0,true,168022866048,168022866112⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917970746270,0,false,-198413318784,-198413318720⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069537327527,0,false,-30390452672,-30390452608⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069578686750,0,false,-30347935168,-30347935104⟩
    { al := (270381/1638400), au := (676377/4096000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨181449617571,181563568423⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167944532544,167944532608⟩ : DyadicInterval 40),(⟨-198304011584,-198304011520⟩ : DyadicInterval 40),(⟨747082588523,747082607852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168042337728,168042337792⟩ : DyadicInterval 40),(⟨-198440492672,-198440492608⟩ : DyadicInterval 40),(⟨747063603922,747063623251⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167886125824,167886125888⟩ : DyadicInterval 40),(⟨-198222522624,-198222522560⟩ : DyadicInterval 40),(⟨747093919089,747093938419⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168003379328,168003379392⟩ : DyadicInterval 40),(⟨-198386125120,-198386125056⟩ : DyadicInterval 40),(⟨747071167642,747071186971⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23137403,34729515⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23137152,23137216⟩ : DyadicInterval 40),(⟨-23137664,-23137600⟩ : DyadicInterval 40),(⟨762123383321,762123402650⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34728960,34729024⟩ : DyadicInterval 40),(⟨-34730112,-34730048⟩ : DyadicInterval 40),(⟨762123383031,762123402360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1152,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181415591151,181540881506⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167915325568,167915325632⟩ : DyadicInterval 40),(⟨-198263260800,-198263260736⟩ : DyadicInterval 40),(⟨747088255131,747088274461⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168022866048,168022866112⟩ : DyadicInterval 40),(⟨-198413318784,-198413318720⟩ : DyadicInterval 40),(⟨747067384589,747067403919⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30390452672,-30347935104⟩ : DyadicInterval 40),(⟨777297351168,777318629216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167944532544,168042337792⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198440492672,-198304011520⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2715_ok : ecellOkT e2715 = true := by decide +kernel
theorem e2715_pos {a z : ℝ} (ha1 : ((270381/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((676377/4096000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2715 e2715_ok ha1 ha2 hz1 hz2 hz

-- box ['676377/4096000', '1353603/8192000', '1999/2000', '7997/8000']  interval_lower 278480731/1099511627776
noncomputable def e2716 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281075196198,0,true,168042337728,168042337792⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917948059354,0,false,-198440492672,-198440492608⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281189147050,0,true,168140134272,168140134336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917834108502,0,false,-198576990656,-198576990592⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280984414413,0,true,167964419456,167964419520⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918038841139,0,false,-198331760256,-198331760192⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281121017981,0,true,168081664640,168081664704⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917902237571,0,false,-198495379008,-198495378944⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546356599,0,true,34728256,34728320⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476898953,0,false,-34729408,-34729344⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557963831,0,true,46335040,46335104⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465291721,0,false,-46337088,-46337024⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625823,0,false,-1984,-1920⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626680,0,false,-1152,-1088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281029800779,0,true,168003375424,168003375488⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917993454773,0,false,-198386119680,-198386119616⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281155091116,0,true,168110907200,168110907264⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917868164436,0,false,-198536194368,-198536194304⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069503443286,0,false,-30425287104,-30425287040⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069544825882,0,false,-30382744256,-30382744192⟩
    { al := (676377/4096000), au := (1353603/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨181563568422,181677519274⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168042337728,168042337792⟩ : DyadicInterval 40),(⟨-198440492672,-198440492608⟩ : DyadicInterval 40),(⟨747063603922,747063623251⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168140134272,168140134336⟩ : DyadicInterval 40),(⟨-198576990656,-198576990592⟩ : DyadicInterval 40),(⟨747044607126,747044626455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167964419456,167964419520⟩ : DyadicInterval 40),(⟨-198331760256,-198331760192⟩ : DyadicInterval 40),(⟨747078729490,747078748820⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168081664640,168081664704⟩ : DyadicInterval 40),(⟨-198495379008,-198495378944⟩ : DyadicInterval 40),(⟨747055966377,747055985706⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34728823,46336055⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34728256,34728320⟩ : DyadicInterval 40),(⟨-34729408,-34729344⟩ : DyadicInterval 40),(⟨762123383031,762123402360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46335040,46335104⟩ : DyadicInterval 40),(⟨-46337088,-46337024⟩ : DyadicInterval 40),(⟨762123382623,762123401952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1984,-1088⟩ : DyadicInterval 40),(⟨762123384160,762123403872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181518173003,181643463340⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168003375424,168003375488⟩ : DyadicInterval 40),(⟨-198386119680,-198386119616⟩ : DyadicInterval 40),(⟨747071168400,747071187729⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168110907200,168110907264⟩ : DyadicInterval 40),(⟨-198536194368,-198536194304⟩ : DyadicInterval 40),(⟨747050285871,747050305200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30425287104,-30382744192⟩ : DyadicInterval 40),(⟨777314755712,777336046432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168042337728,168140134336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198576990656,-198440492608⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2716_ok : ecellOkT e2716 = true := by decide +kernel
theorem e2716_pos {a z : ℝ} (ha1 : ((676377/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1353603/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2716 e2716_ok ha1 ha2 hz1 hz2 hz

-- box ['1353603/8192000', '338613/2048000', '1999/2000', '7997/8000']  interval_lower 2186095/8589934592
noncomputable def e2717 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281189147049,0,true,168140134272,168140134336⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917834108503,0,false,-198576990656,-198576990592⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281303097902,0,true,168237922112,168237922176⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917720157650,0,false,-198713505600,-198713505536⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281098308289,0,true,168062174080,168062174144⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917924947263,0,false,-198468176512,-198468176448⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281234926101,0,true,168179420992,168179421056⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917788329451,0,false,-198631832640,-198631832576⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546379278,0,true,34750912,34750976⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476876274,0,false,-34752064,-34752000⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557994074,0,true,46365312,46365376⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465261478,0,false,-46367296,-46367232⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625820,0,false,-1984,-1920⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626678,0,false,-1152,-1088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281143723145,0,true,168101150976,168101151040⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917879532407,0,false,-198522576832,-198522576768⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281269020601,0,true,168208679360,168208679424⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917754234951,0,false,-198672678656,-198672678592⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069465788321,0,false,-30463999296,-30463999232⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069507199233,0,false,-30421425792,-30421425728⟩
    { al := (1353603/8192000), au := (338613/2048000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨181677519273,181791470126⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168140134272,168140134336⟩ : DyadicInterval 40),(⟨-198576990656,-198576990592⟩ : DyadicInterval 40),(⟨747044607126,747044626455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168237922112,168237922176⟩ : DyadicInterval 40),(⟨-198713505600,-198713505536⟩ : DyadicInterval 40),(⟨747025598197,747025617527⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168062174080,168062174144⟩ : DyadicInterval 40),(⟨-198468176512,-198468176448⟩ : DyadicInterval 40),(⟨747059751842,747059771171⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168179420992,168179421056⟩ : DyadicInterval 40),(⟨-198631832640,-198631832576⟩ : DyadicInterval 40),(⟨747036971851,747036991180⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34751502,46366298⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34750912,34750976⟩ : DyadicInterval 40),(⟨-34752064,-34752000⟩ : DyadicInterval 40),(⟨762123383029,762123402358⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46365312,46365376⟩ : DyadicInterval 40),(⟨-46367296,-46367232⟩ : DyadicInterval 40),(⟨762123382588,762123401917⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1984,-1088⟩ : DyadicInterval 40),(⟨762123384160,762123403872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181632095369,181757392825⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168101150976,168101151040⟩ : DyadicInterval 40),(⟨-198522576832,-198522576768⟩ : DyadicInterval 40),(⟨747052181213,747052200542⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168208679360,168208679424⟩ : DyadicInterval 40),(⟨-198672678656,-198672678592⟩ : DyadicInterval 40),(⟨747031284106,747031303436⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30463999296,-30421425728⟩ : DyadicInterval 40),(⟨777334096480,777355402528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168140134272,168237922176⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198713505600,-198576990592⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2717_ok : ecellOkT e2717 = true := by decide +kernel
theorem e2717_pos {a z : ℝ} (ha1 : ((1353603/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((338613/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2717 e2717_ok ha1 ha2 hz1 hz2 hz

-- box ['676377/4096000', '1353603/8192000', '7997/8000', '3999/4000']  interval_lower 278289089/1099511627776
noncomputable def e2718 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281075196198,0,true,168042337728,168042337792⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917948059354,0,false,-198440492672,-198440492608⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281189147050,0,true,168140134272,168140134336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917834108502,0,false,-198576990656,-198576990592⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281007109859,0,true,167983899584,167983899648⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918016145693,0,false,-198358942336,-198358942272⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281143727671,0,true,168101154880,168101154944⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917879527881,0,false,-198522582208,-198522582144⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534780297,0,true,23152256,23152320⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488475255,0,false,-23152768,-23152704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546379970,0,true,34751616,34751680⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476875582,0,false,-34752768,-34752704⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626677,0,false,-1152,-1088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627289,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281041148407,0,true,168013115072,168013115136⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917982107145,0,false,-198399711232,-198399711168⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281166445891,0,true,168120652096,168120652160⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917856809661,0,false,-198549796288,-198549796224⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069499691466,0,false,-30429144192,-30429144128⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069541079009,0,false,-30386596096,-30386596032⟩
    { al := (676377/4096000), au := (1353603/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨181563568422,181677519274⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168042337728,168042337792⟩ : DyadicInterval 40),(⟨-198440492672,-198440492608⟩ : DyadicInterval 40),(⟨747063603922,747063623251⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168140134272,168140134336⟩ : DyadicInterval 40),(⟨-198576990656,-198576990592⟩ : DyadicInterval 40),(⟨747044607126,747044626455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167983899584,167983899648⟩ : DyadicInterval 40),(⟨-198358942336,-198358942272⟩ : DyadicInterval 40),(⟨747074948789,747074968118⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168101154880,168101154944⟩ : DyadicInterval 40),(⟨-198522582208,-198522582144⟩ : DyadicInterval 40),(⟨747052180428,747052199757⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23152521,34752194⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23152256,23152320⟩ : DyadicInterval 40),(⟨-23152768,-23152704⟩ : DyadicInterval 40),(⟨762123383320,762123402649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34751616,34751680⟩ : DyadicInterval 40),(⟨-34752768,-34752704⟩ : DyadicInterval 40),(⟨762123383029,762123402358⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1152,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181529520631,181654818115⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168013115072,168013115136⟩ : DyadicInterval 40),(⟨-198399711232,-198399711168⟩ : DyadicInterval 40),(⟨747069277678,747069297008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168120652096,168120652160⟩ : DyadicInterval 40),(⟨-198549796288,-198549796224⟩ : DyadicInterval 40),(⟨747048392569,747048411898⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30429144192,-30386596032⟩ : DyadicInterval 40),(⟨777316681632,777337974976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168042337728,168140134336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198576990656,-198440492608⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2718_ok : ecellOkT e2718 = true := by decide +kernel
theorem e2718_pos {a z : ℝ} (ha1 : ((676377/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1353603/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2718 e2718_ok ha1 ha2 hz1 hz2 hz

-- box ['1353603/8192000', '338613/2048000', '7997/8000', '3999/4000']  interval_lower 139814219/549755813888
noncomputable def e2719 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281189147049,0,true,168140134272,168140134336⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917834108503,0,false,-198576990656,-198576990592⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281303097902,0,true,168237922112,168237922176⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917720157650,0,false,-198713505600,-198713505536⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281121017979,0,true,168081664640,168081664704⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917902237573,0,false,-198495379008,-198495378944⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281257650035,0,true,168198921728,168198921792⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917765605517,0,false,-198659056256,-198659056192⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534795417,0,true,23167360,23167424⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488460135,0,false,-23167936,-23167872⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546402652,0,true,34774272,34774336⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476852900,0,false,-34775488,-34775424⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626676,0,false,-1152,-1088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627288,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281155077892,0,true,168110895872,168110895936⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917868177660,0,false,-198536178560,-198536178496⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281280382499,0,true,168218429440,168218429504⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917742873053,0,false,-198686290816,-198686290752⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069462031792,0,false,-30467861376,-30467861312⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069503447657,0,false,-30425282624,-30425282560⟩
    { al := (1353603/8192000), au := (338613/2048000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨181677519273,181791470126⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168140134272,168140134336⟩ : DyadicInterval 40),(⟨-198576990656,-198576990592⟩ : DyadicInterval 40),(⟨747044607126,747044626455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168237922112,168237922176⟩ : DyadicInterval 40),(⟨-198713505600,-198713505536⟩ : DyadicInterval 40),(⟨747025598197,747025617527⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168081664640,168081664704⟩ : DyadicInterval 40),(⟨-198495379008,-198495378944⟩ : DyadicInterval 40),(⟨747055966377,747055985706⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168198921728,168198921792⟩ : DyadicInterval 40),(⟨-198659056256,-198659056192⟩ : DyadicInterval 40),(⟨747033181094,747033200423⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23167641,34774876⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23167360,23167424⟩ : DyadicInterval 40),(⟨-23167936,-23167872⟩ : DyadicInterval 40),(⟨762123383351,762123402680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34774272,34774336⟩ : DyadicInterval 40),(⟨-34775488,-34775424⟩ : DyadicInterval 40),(⟨762123383060,762123402389⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1152,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181643450116,181768754723⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168110895872,168110895936⟩ : DyadicInterval 40),(⟨-198536178560,-198536178496⟩ : DyadicInterval 40),(⟨747050288077,747050307406⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168218429440,168218429504⟩ : DyadicInterval 40),(⟨-198686290816,-198686290752⟩ : DyadicInterval 40),(⟨747029388450,747029407780⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30467861376,-30425282560⟩ : DyadicInterval 40),(⟨777336024896,777357333568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168140134272,168237922176⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198713505600,-198576990592⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2719_ok : ecellOkT e2719 = true := by decide +kernel
theorem e2719_pos {a z : ℝ} (ha1 : ((1353603/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((338613/2048000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2719 e2719_ok ha1 ha2 hz1 hz2 hz

-- box ['84441/512000', '270381/1638400', '3999/4000', '7999/8000']  interval_lower 68857355/274877906944
noncomputable def e2720 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280847294496,0,true,167846718592,167846718656⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918175961056,0,false,-198167547520,-198167547456⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280961245348,0,true,167944532544,167944532608⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918062010204,0,false,-198304011584,-198304011520⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280801960579,0,true,167807802112,167807802176⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918221294973,0,false,-198113261696,-198113261632⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1280938564146,0,true,167925063936,167925064000⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨918084691406,0,false,-198276847936,-198276847872⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523188819,0,true,11560960,11561024⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500066733,0,false,-11561152,-11561088⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534765811,0,true,23137728,23137792⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488489741,0,false,-23138304,-23138240⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627289,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627655,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280824622850,0,true,167827256512,167827256576⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918198632702,0,false,-198140398656,-198140398592⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1280949913235,0,true,167934805568,167934805632⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨918073342317,0,false,-198290439872,-198290439808⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069571197316,0,false,-30355634240,-30355634176⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069612533167,0,false,-30313142080,-30313142016⟩
    { al := (84441/512000), au := (270381/1638400), zl := (3999/4000), zu := (7999/8000),
      A := ⟨181335666720,181449617572⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167846718592,167846718656⟩ : DyadicInterval 40),(⟨-198167547520,-198167547456⟩ : DyadicInterval 40),(⟨747101561058,747101580387⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167944532544,167944532608⟩ : DyadicInterval 40),(⟨-198304011584,-198304011520⟩ : DyadicInterval 40),(⟨747082588522,747082607852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167807802112,167807802176⟩ : DyadicInterval 40),(⟨-198113261696,-198113261632⟩ : DyadicInterval 40),(⟨747109105664,747109124993⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167925063936,167925064000⟩ : DyadicInterval 40),(⟨-198276847936,-198276847872⟩ : DyadicInterval 40),(⟨747086365890,747086385219⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11561043,23138035⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11560960,11561024⟩ : DyadicInterval 40),(⟨-11561152,-11561088⟩ : DyadicInterval 40),(⟨762123383526,762123402855⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23137728,23137792⟩ : DyadicInterval 40),(⟨-23138304,-23138240⟩ : DyadicInterval 40),(⟨762123383353,762123402682⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181312995074,181438285459⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167827256512,167827256576⟩ : DyadicInterval 40),(⟨-198140398656,-198140398592⟩ : DyadicInterval 40),(⟨747105334373,747105353702⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167934805568,167934805632⟩ : DyadicInterval 40),(⟨-198290439872,-198290439808⟩ : DyadicInterval 40),(⟨747084475866,747084495195⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30355634240,-30313142016⟩ : DyadicInterval 40),(⟨777279954624,777301220000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167846718592,167944532608⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198304011584,-198167547456⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2720_ok : ecellOkT e2720 = true := by decide +kernel
theorem e2720_pos {a z : ℝ} (ha1 : ((84441/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((270381/1638400 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2720 e2720_ok ha1 ha2 hz1 hz2 hz

-- box ['270381/1638400', '676377/4096000', '3999/4000', '7999/8000']  interval_lower 276762097/1099511627776
noncomputable def e2721 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280961245347,0,true,167944532544,167944532608⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918062010205,0,false,-198304011584,-198304011520⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281075196199,0,true,168042337728,168042337792⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917948059353,0,false,-198440492672,-198440492608⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280915882942,0,true,167905595072,167905595136⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918107372610,0,false,-198249684928,-198249684864⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281052500754,0,true,168022858688,168022858752⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917970754798,0,false,-198413308544,-198413308480⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523196378,0,true,11568512,11568576⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500059174,0,false,-11568704,-11568640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534780930,0,true,23152896,23152960⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488474622,0,false,-23153408,-23153344⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627288,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627655,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1280938559459,0,true,167925059968,167925060032⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨918084696093,0,false,-198276842304,-198276842240⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281063856961,0,true,168032605568,168032605632⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917959398591,0,false,-198426910656,-198426910592⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069533580168,0,false,-30394305088,-30394305024⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069574944336,0,false,-30351782336,-30351782272⟩
    { al := (270381/1638400), au := (676377/4096000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨181449617571,181563568423⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167944532544,167944532608⟩ : DyadicInterval 40),(⟨-198304011584,-198304011520⟩ : DyadicInterval 40),(⟨747082588523,747082607852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168042337728,168042337792⟩ : DyadicInterval 40),(⟨-198440492672,-198440492608⟩ : DyadicInterval 40),(⟨747063603922,747063623251⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167905595072,167905595136⟩ : DyadicInterval 40),(⟨-198249684928,-198249684864⟩ : DyadicInterval 40),(⟨747090142712,747090162041⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168022858688,168022858752⟩ : DyadicInterval 40),(⟨-198413308544,-198413308480⟩ : DyadicInterval 40),(⟨747067386023,747067405352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11568602,23153154⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11568512,11568576⟩ : DyadicInterval 40),(⟨-11568704,-11568640⟩ : DyadicInterval 40),(⟨762123383526,762123402855⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23152896,23152960⟩ : DyadicInterval 40),(⟨-23153408,-23153344⟩ : DyadicInterval 40),(⟨762123383320,762123402649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181426931683,181552229185⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167925059968,167925060032⟩ : DyadicInterval 40),(⟨-198276842304,-198276842240⟩ : DyadicInterval 40),(⟨747086366630,747086385960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168032605568,168032605632⟩ : DyadicInterval 40),(⟨-198426910656,-198426910592⟩ : DyadicInterval 40),(⟨747065493585,747065512915⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30394305088,-30351782272⟩ : DyadicInterval 40),(⟨777299274752,777320555424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨167944532544,168042337792⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198440492672,-198304011520⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2721_ok : ecellOkT e2721 = true := by decide +kernel
theorem e2721_pos {a z : ℝ} (ha1 : ((270381/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((676377/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2721 e2721_ok ha1 ha2 hz1 hz2 hz

-- box ['84441/512000', '270381/1638400', '7999/8000', '1']  interval_lower 17202437/68719476736
noncomputable def e2722 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280847294496,0,true,167846718592,167846718656⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918175961056,0,false,-198167547520,-198167547456⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1280961245348,0,true,167944532544,167944532608⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨918062010204,0,false,-198304011584,-198304011520⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280824627537,0,true,167827260544,167827260608⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918198628015,0,false,-198140404288,-198140404224⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523196952,0,true,11569088,11569152⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500058600,0,false,-11569280,-11569216⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627654,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1280835956287,0,true,167836985536,167836985600⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨918187299265,0,false,-198153970112,-198153970048⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1280961253827,0,true,167944539776,167944539840⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨918062001725,0,false,-198304021760,-198304021696⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1069567454415,0,false,-30359481920,-30359481856⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1069608795210,0,false,-30316984576,-30316984512⟩
    { al := (84441/512000), au := (270381/1638400), zl := (7999/8000), zu := 1,
      A := ⟨181335666720,181449617572⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167846718592,167846718656⟩ : DyadicInterval 40),(⟨-198167547520,-198167547456⟩ : DyadicInterval 40),(⟨747101561058,747101580387⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167944532544,167944532608⟩ : DyadicInterval 40),(⟨-198304011584,-198304011520⟩ : DyadicInterval 40),(⟨747082588522,747082607852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167827260544,167827260608⟩ : DyadicInterval 40),(⟨-198140404288,-198140404224⟩ : DyadicInterval 40),(⟨747105333596,747105352925⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167944532544,167944532608⟩ : DyadicInterval 40),(⟨-198304011584,-198304011520⟩ : DyadicInterval 40),(⟨747082588522,747082607852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11569176⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11569088,11569152⟩ : DyadicInterval 40),(⟨-11569280,-11569216⟩ : DyadicInterval 40),(⟨762123383526,762123402855⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨181324328511,181449626051⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167836985536,167836985600⟩ : DyadicInterval 40),(⟨-198153970112,-198153970048⟩ : DyadicInterval 40),(⟨747103448164,747103467493⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167944539776,167944539840⟩ : DyadicInterval 40),(⟨-198304021760,-198304021696⟩ : DyadicInterval 40),(⟨747082587146,747082606475⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30359481920,-30316984512⟩ : DyadicInterval 40),(⟨777281875872,777303143840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨167846718592,167944532608⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198304011584,-198167547456⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2722_ok : ecellOkT e2722 = true := by decide +kernel
theorem e2722_pos {a z : ℝ} (ha1 : ((84441/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((270381/1638400 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2722 e2722_ok ha1 ha2 hz1 hz2 hz

-- box ['270381/1638400', '676377/4096000', '7999/8000', '1']  interval_lower 69142815/274877906944
noncomputable def e2723 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1280961245347,0,true,167944532544,167944532608⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨918062010205,0,false,-198304011584,-198304011520⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281075196199,0,true,168042337728,168042337792⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917948059353,0,false,-198440492672,-198440492608⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1280938564144,0,true,167925063936,167925064000⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨918084691408,0,false,-198276847936,-198276847872⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523204512,0,true,11576640,11576704⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500051040,0,false,-11576832,-11576768⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627654,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1280949900016,0,true,167934794240,167934794304⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨918073355536,0,false,-198290424000,-198290423936⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1281075204667,0,true,168042345024,168042345088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨917948050885,0,false,-198440502784,-198440502720⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1069529832567,0,false,-30398157760,-30398157696⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1069571201680,0,false,-30355629760,-30355629696⟩
    { al := (270381/1638400), au := (676377/4096000), zl := (7999/8000), zu := 1,
      A := ⟨181449617571,181563568423⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167944532544,167944532608⟩ : DyadicInterval 40),(⟨-198304011584,-198304011520⟩ : DyadicInterval 40),(⟨747082588523,747082607852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168042337728,168042337792⟩ : DyadicInterval 40),(⟨-198440492672,-198440492608⟩ : DyadicInterval 40),(⟨747063603922,747063623251⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167925063936,167925064000⟩ : DyadicInterval 40),(⟨-198276847936,-198276847872⟩ : DyadicInterval 40),(⟨747086365890,747086385220⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168042337728,168042337792⟩ : DyadicInterval 40),(⟨-198440492672,-198440492608⟩ : DyadicInterval 40),(⟨747063603922,747063623251⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11576736⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11576640,11576704⟩ : DyadicInterval 40),(⟨-11576832,-11576768⟩ : DyadicInterval 40),(⟨762123383526,762123402855⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨181438272240,181563576891⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨167934794240,167934794304⟩ : DyadicInterval 40),(⟨-198290424000,-198290423936⟩ : DyadicInterval 40),(⟨747084478039,747084497369⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168042345024,168042345088⟩ : DyadicInterval 40),(⟨-198440502784,-198440502720⟩ : DyadicInterval 40),(⟨747063602481,747063621810⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30398157760,-30355629696⟩ : DyadicInterval 40),(⟨777301198464,777322481760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨167944532544,168042337792⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198440492672,-198304011520⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2723_ok : ecellOkT e2723 = true := by decide +kernel
theorem e2723_pos {a z : ℝ} (ha1 : ((270381/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((676377/4096000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2723 e2723_ok ha1 ha2 hz1 hz2 hz

-- box ['676377/4096000', '1353603/8192000', '3999/4000', '7999/8000']  interval_lower 69524427/274877906944
noncomputable def e2724 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281075196198,0,true,168042337728,168042337792⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917948059354,0,false,-198440492672,-198440492608⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281189147050,0,true,168140134272,168140134336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917834108502,0,false,-198576990656,-198576990592⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281029805305,0,true,168003379328,168003379392⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917993450247,0,false,-198386125120,-198386125056⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281166437361,0,true,168120644736,168120644800⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917856818191,0,false,-198549786112,-198549786048⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523203937,0,true,11576064,11576128⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500051615,0,false,-11576256,-11576192⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534796049,0,true,23168000,23168064⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488459503,0,false,-23168576,-23168512⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627287,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627655,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281052496059,0,true,168022854656,168022854720⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917970759493,0,false,-198413302912,-198413302848⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281177800690,0,true,168130396864,168130396928⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917845454862,0,false,-198563398464,-198563398400⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069495939403,0,false,-30433001600,-30433001536⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069537331894,0,false,-30390448192,-30390448128⟩
    { al := (676377/4096000), au := (1353603/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨181563568422,181677519274⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168042337728,168042337792⟩ : DyadicInterval 40),(⟨-198440492672,-198440492608⟩ : DyadicInterval 40),(⟨747063603922,747063623251⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168140134272,168140134336⟩ : DyadicInterval 40),(⟨-198576990656,-198576990592⟩ : DyadicInterval 40),(⟨747044607126,747044626455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168003379328,168003379392⟩ : DyadicInterval 40),(⟨-198386125120,-198386125056⟩ : DyadicInterval 40),(⟨747071167642,747071186972⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168120644736,168120644800⟩ : DyadicInterval 40),(⟨-198549786112,-198549786048⟩ : DyadicInterval 40),(⟨747048394032,747048413362⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11576161,23168273⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11576064,11576128⟩ : DyadicInterval 40),(⟨-11576256,-11576192⟩ : DyadicInterval 40),(⟨762123383526,762123402855⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23168000,23168064⟩ : DyadicInterval 40),(⟨-23168576,-23168512⟩ : DyadicInterval 40),(⟨762123383351,762123402680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181540868283,181666172914⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168022854656,168022854720⟩ : DyadicInterval 40),(⟨-198413302912,-198413302848⟩ : DyadicInterval 40),(⟨747067386803,747067406133⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168130396864,168130396928⟩ : DyadicInterval 40),(⟨-198563398464,-198563398400⟩ : DyadicInterval 40),(⟨747046499204,747046518533⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30433001600,-30390448128⟩ : DyadicInterval 40),(⟨777318607680,777339903680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168042337728,168140134336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198576990656,-198440492608⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2724_ok : ecellOkT e2724 = true := by decide +kernel
theorem e2724_pos {a z : ℝ} (ha1 : ((676377/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1353603/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2724 e2724_ok ha1 ha2 hz1 hz2 hz

-- box ['1353603/8192000', '338613/2048000', '3999/4000', '7999/8000']  interval_lower 279436519/1099511627776
noncomputable def e2725 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281189147049,0,true,168140134272,168140134336⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917834108503,0,false,-198576990656,-198576990592⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281303097902,0,true,168237922112,168237922176⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917720157650,0,false,-198713505600,-198713505536⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281143727669,0,true,168101154880,168101154944⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917879527883,0,false,-198522582208,-198522582144⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281280373969,0,true,168218422080,168218422144⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917742881583,0,false,-198686280576,-198686280512⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523211497,0,true,11583616,11583680⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500044055,0,false,-11583808,-11583744⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534811171,0,true,23183104,23183168⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488444381,0,false,-23183680,-23183616⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627287,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627654,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281166432667,0,true,168120640704,168120640768⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917856822885,0,false,-198549780480,-198549780416⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281291744422,0,true,168228179456,168228179520⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917731511130,0,false,-198699903168,-198699903104⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069458275020,0,false,-30471723712,-30471723648⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069499695837,0,false,-30429139712,-30429139648⟩
    { al := (1353603/8192000), au := (338613/2048000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨181677519273,181791470126⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168140134272,168140134336⟩ : DyadicInterval 40),(⟨-198576990656,-198576990592⟩ : DyadicInterval 40),(⟨747044607126,747044626455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168237922112,168237922176⟩ : DyadicInterval 40),(⟨-198713505600,-198713505536⟩ : DyadicInterval 40),(⟨747025598197,747025617527⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168101154880,168101154944⟩ : DyadicInterval 40),(⟨-198522582208,-198522582144⟩ : DyadicInterval 40),(⟨747052180428,747052199758⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168218422080,168218422144⟩ : DyadicInterval 40),(⟨-198686280576,-198686280512⟩ : DyadicInterval 40),(⟨747029389888,747029409218⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11583721,23183395⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11583616,11583680⟩ : DyadicInterval 40),(⟨-11583808,-11583744⟩ : DyadicInterval 40),(⟨762123383525,762123402854⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23183104,23183168⟩ : DyadicInterval 40),(⟨-23183680,-23183616⟩ : DyadicInterval 40),(⟨762123383351,762123402680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181654804891,181780116646⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168120640704,168120640768⟩ : DyadicInterval 40),(⟨-198549780480,-198549780416⟩ : DyadicInterval 40),(⟨747048394813,747048414142⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168228179456,168228179520⟩ : DyadicInterval 40),(⟨-198699903168,-198699903104⟩ : DyadicInterval 40),(⟨747027492666,747027511995⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30471723712,-30429139648⟩ : DyadicInterval 40),(⟨777337953440,777359264736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168140134272,168237922176⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198713505600,-198576990592⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2725_ok : ecellOkT e2725 = true := by decide +kernel
theorem e2725_pos {a z : ℝ} (ha1 : ((1353603/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((338613/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2725 e2725_ok ha1 ha2 hz1 hz2 hz

-- box ['676377/4096000', '1353603/8192000', '7999/8000', '1']  interval_lower 277906325/1099511627776
noncomputable def e2726 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281075196198,0,true,168042337728,168042337792⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917948059354,0,false,-198440492672,-198440492608⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281189147050,0,true,168140134272,168140134336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917834108502,0,false,-198576990656,-198576990592⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281052500751,0,true,168022858688,168022858752⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917970754801,0,false,-198413308544,-198413308480⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523212070,0,true,11584192,11584256⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500043482,0,false,-11584384,-11584320⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627653,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1281063843737,0,true,168032594176,168032594240⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨917959411815,0,false,-198426894848,-198426894784⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1281189155520,0,true,168140141568,168140141632⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨917834100032,0,false,-198577000768,-198577000704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1069492187095,0,false,-30436859200,-30436859136⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1069533584537,0,false,-30394300608,-30394300544⟩
    { al := (676377/4096000), au := (1353603/8192000), zl := (7999/8000), zu := 1,
      A := ⟨181563568422,181677519274⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168042337728,168042337792⟩ : DyadicInterval 40),(⟨-198440492672,-198440492608⟩ : DyadicInterval 40),(⟨747063603922,747063623251⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168140134272,168140134336⟩ : DyadicInterval 40),(⟨-198576990656,-198576990592⟩ : DyadicInterval 40),(⟨747044607126,747044626455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168022858688,168022858752⟩ : DyadicInterval 40),(⟨-198413308544,-198413308480⟩ : DyadicInterval 40),(⟨747067386023,747067405353⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168140134272,168140134336⟩ : DyadicInterval 40),(⟨-198576990656,-198576990592⟩ : DyadicInterval 40),(⟨747044607126,747044626455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11584294⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11584192,11584256⟩ : DyadicInterval 40),(⟨-11584384,-11584320⟩ : DyadicInterval 40),(⟨762123383525,762123402854⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨181552215961,181677527744⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168032594176,168032594240⟩ : DyadicInterval 40),(⟨-198426894848,-198426894784⟩ : DyadicInterval 40),(⟨747065495827,747065515157⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168140141568,168140141632⟩ : DyadicInterval 40),(⟨-198577000768,-198577000704⟩ : DyadicInterval 40),(⟨747044605683,747044625012⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30436859200,-30394300544⟩ : DyadicInterval 40),(⟨777320533888,777341832480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨168042337728,168140134336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198576990656,-198440492608⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2726_ok : ecellOkT e2726 = true := by decide +kernel
theorem e2726_pos {a z : ℝ} (ha1 : ((676377/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1353603/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2726 e2726_ok ha1 ha2 hz1 hz2 hz

-- box ['1353603/8192000', '338613/2048000', '7999/8000', '1']  interval_lower 34905583/137438953472
noncomputable def e2727 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281189147049,0,true,168140134272,168140134336⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917834108503,0,false,-198576990656,-198576990592⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281303097902,0,true,168237922112,168237922176⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917720157650,0,false,-198713505600,-198713505536⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281166437359,0,true,168120644736,168120644800⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917856818193,0,false,-198549786112,-198549786048⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523219631,0,true,11591744,11591808⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500035921,0,false,-11591936,-11591872⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627653,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1281177787465,0,true,168130385472,168130385536⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨917845468087,0,false,-198563382592,-198563382528⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1281303106372,0,true,168237929408,168237929472⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨917720149180,0,false,-198713515712,-198713515648⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1069454518005,0,false,-30475586304,-30475586240⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1069495943774,0,false,-30432997056,-30432996992⟩
    { al := (1353603/8192000), au := (338613/2048000), zl := (7999/8000), zu := 1,
      A := ⟨181677519273,181791470126⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168140134272,168140134336⟩ : DyadicInterval 40),(⟨-198576990656,-198576990592⟩ : DyadicInterval 40),(⟨747044607126,747044626455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168237922112,168237922176⟩ : DyadicInterval 40),(⟨-198713505600,-198713505536⟩ : DyadicInterval 40),(⟨747025598197,747025617527⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168120644736,168120644800⟩ : DyadicInterval 40),(⟨-198549786112,-198549786048⟩ : DyadicInterval 40),(⟨747048394032,747048413362⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168237922112,168237922176⟩ : DyadicInterval 40),(⟨-198713505600,-198713505536⟩ : DyadicInterval 40),(⟨747025598197,747025617527⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11591855⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11591744,11591808⟩ : DyadicInterval 40),(⟨-11591936,-11591872⟩ : DyadicInterval 40),(⟨762123383525,762123402854⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨181666159689,181791478596⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168130385472,168130385536⟩ : DyadicInterval 40),(⟨-198563382592,-198563382528⟩ : DyadicInterval 40),(⟨747046501422,747046520751⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168237929408,168237929472⟩ : DyadicInterval 40),(⟨-198713515712,-198713515648⟩ : DyadicInterval 40),(⟨747025596753,747025616082⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30475586304,-30432996992⟩ : DyadicInterval 40),(⟨777339882112,777361196032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨168140134272,168237922176⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198713505600,-198576990592⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2727_ok : ecellOkT e2727 = true := by decide +kernel
theorem e2727_pos {a z : ℝ} (ha1 : ((1353603/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((338613/2048000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2727 e2727_ok ha1 ha2 hz1 hz2 hz

-- box ['338613/2048000', '1355301/8192000', '1999/2000', '7997/8000']  interval_lower 281163069/1099511627776
noncomputable def e2728 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281303097901,0,true,168237922112,168237922176⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917720157651,0,false,-198713505600,-198713505536⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281417048753,0,true,168335701248,168335701312⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917606206799,0,false,-198850037440,-198850037376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281212202165,0,true,168159919936,168159920000⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917811053387,0,false,-198604609664,-198604609600⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281348834221,0,true,168277168640,168277168704⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917674421331,0,false,-198768303168,-198768303104⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546401959,0,true,34773632,34773696⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476853593,0,false,-34774784,-34774720⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558024318,0,true,46395520,46395584⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465231234,0,false,-46397568,-46397504⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625818,0,false,-1984,-1920⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626677,0,false,-1152,-1088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281257645507,0,true,168198917824,168198917888⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917765610045,0,false,-198659050880,-198659050816⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281382950087,0,true,168306442752,168306442816⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917640305465,0,false,-198809179840,-198809179776⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069428109745,0,false,-30502737088,-30502737024⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069469548978,0,false,-30460132992,-30460132928⟩
    { al := (338613/2048000), au := (1355301/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨181791470125,181905420977⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168237922112,168237922176⟩ : DyadicInterval 40),(⟨-198713505600,-198713505536⟩ : DyadicInterval 40),(⟨747025598197,747025617527⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168335701248,168335701312⟩ : DyadicInterval 40),(⟨-198850037440,-198850037376⟩ : DyadicInterval 40),(⟨747006577109,747006596439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168159919936,168159920000⟩ : DyadicInterval 40),(⟨-198604609664,-198604609600⟩ : DyadicInterval 40),(⟨747040762096,747040781426⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168277168640,168277168704⟩ : DyadicInterval 40),(⟨-198768303168,-198768303104⟩ : DyadicInterval 40),(⟨747017965184,747017984513⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34774183,46396542⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34773632,34773696⟩ : DyadicInterval 40),(⟨-34774784,-34774720⟩ : DyadicInterval 40),(⟨762123383028,762123402357⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46395520,46395584⟩ : DyadicInterval 40),(⟨-46397568,-46397504⟩ : DyadicInterval 40),(⟨762123382618,762123401947⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1984,-1088⟩ : DyadicInterval 40),(⟨762123384160,762123403872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181746017731,181871322311⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168198917824,168198917888⟩ : DyadicInterval 40),(⟨-198659050880,-198659050816⟩ : DyadicInterval 40),(⟨747033181880,747033201209⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168306442752,168306442816⟩ : DyadicInterval 40),(⟨-198809179840,-198809179776⟩ : DyadicInterval 40),(⟨747012270228,747012289558⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30502737088,-30460132928⟩ : DyadicInterval 40),(⟨777353450080,777374771424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168237922112,168335701312⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198850037440,-198713505536⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2728_ok : ecellOkT e2728 = true := by decide +kernel
theorem e2728_pos {a z : ℝ} (ha1 : ((338613/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1355301/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2728 e2728_ok ha1 ha2 hz1 hz2 hz

-- box ['1355301/8192000', '27123/163840', '1999/2000', '7997/8000']  interval_lower 282508693/1099511627776
noncomputable def e2729 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281417048752,0,true,168335701248,168335701312⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917606206800,0,false,-198850037440,-198850037376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281530999604,0,true,168433471744,168433471808⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917492255948,0,false,-198986586304,-198986586240⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281326096041,0,true,168257657088,168257657152⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917697159511,0,false,-198741059776,-198741059712⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281462742340,0,true,168374907648,168374907712⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917560513212,0,false,-198904790656,-198904790592⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546424643,0,true,34796288,34796352⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476830909,0,false,-34797440,-34797376⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558054563,0,true,46425792,46425856⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465200989,0,false,-46427776,-46427712⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625815,0,false,-1984,-1920⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626675,0,false,-1152,-1088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281371567867,0,true,168296675968,168296676032⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917651687685,0,false,-198795541824,-198795541760⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281496879577,0,true,168404197440,168404197504⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917526375975,0,false,-198945698048,-198945697984⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069390407557,0,false,-30541500544,-30541500480⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069431875117,0,false,-30498865792,-30498865728⟩
    { al := (1355301/8192000), au := (27123/163840), zl := (1999/2000), zu := (7997/8000),
      A := ⟨181905420976,182019371828⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168335701248,168335701312⟩ : DyadicInterval 40),(⟨-198850037440,-198850037376⟩ : DyadicInterval 40),(⟨747006577109,747006596439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168433471744,168433471808⟩ : DyadicInterval 40),(⟨-198986586304,-198986586240⟩ : DyadicInterval 40),(⟨746987543875,746987563205⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168257657088,168257657152⟩ : DyadicInterval 40),(⟨-198741059776,-198741059712⟩ : DyadicInterval 40),(⟨747021760243,747021779573⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168374907648,168374907712⟩ : DyadicInterval 40),(⟨-198904790656,-198904790592⟩ : DyadicInterval 40),(⟨746998946364,746998965694⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34796867,46426787⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34796288,34796352⟩ : DyadicInterval 40),(⟨-34797440,-34797376⟩ : DyadicInterval 40),(⟨762123383026,762123402355⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46425792,46425856⟩ : DyadicInterval 40),(⟨-46427776,-46427712⟩ : DyadicInterval 40),(⟨762123382583,762123401912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1984,-1088⟩ : DyadicInterval 40),(⟨762123384160,762123403872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181859940091,181985251801⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168296675968,168296676032⟩ : DyadicInterval 40),(⟨-198795541824,-198795541760⟩ : DyadicInterval 40),(⟨747014170400,747014189730⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168404197440,168404197504⟩ : DyadicInterval 40),(⟨-198945698048,-198945697984⟩ : DyadicInterval 40),(⟨746993244251,746993263580⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30541500544,-30498865728⟩ : DyadicInterval 40),(⟨777372816480,777394153152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168335701248,168433471808⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198986586304,-198850037376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2729_ok : ecellOkT e2729 = true := by decide +kernel
theorem e2729_pos {a z : ℝ} (ha1 : ((1355301/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((27123/163840 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2729 e2729_ok ha1 ha2 hz1 hz2 hz

-- box ['338613/2048000', '1355301/8192000', '7997/8000', '3999/4000']  interval_lower 140485369/549755813888
noncomputable def e2730 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281303097901,0,true,168237922112,168237922176⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917720157651,0,false,-198713505600,-198713505536⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281417048753,0,true,168335701248,168335701312⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917606206799,0,false,-198850037440,-198850037376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281234926099,0,true,168179420992,168179421056⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917788329453,0,false,-198631832640,-198631832576⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281371572398,0,true,168296679872,168296679936⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917651683154,0,false,-198795547264,-198795547200⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534810538,0,true,23182464,23182528⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488445014,0,false,-23183040,-23182976⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546425335,0,true,34796992,34797056⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476830217,0,false,-34798144,-34798080⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626674,0,false,-1152,-1088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627288,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281269007373,0,true,168208667968,168208668032⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917754248179,0,false,-198672662784,-198672662720⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281394319106,0,true,168316198080,168316198144⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917628936446,0,false,-198822802240,-198822802176⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069424348506,0,false,-30506604160,-30506604096⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069465792695,0,false,-30463994816,-30463994752⟩
    { al := (338613/2048000), au := (1355301/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨181791470125,181905420977⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168237922112,168237922176⟩ : DyadicInterval 40),(⟨-198713505600,-198713505536⟩ : DyadicInterval 40),(⟨747025598197,747025617527⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168335701248,168335701312⟩ : DyadicInterval 40),(⟨-198850037440,-198850037376⟩ : DyadicInterval 40),(⟨747006577109,747006596439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168179420992,168179421056⟩ : DyadicInterval 40),(⟨-198631832640,-198631832576⟩ : DyadicInterval 40),(⟨747036971851,747036991181⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168296679872,168296679936⟩ : DyadicInterval 40),(⟨-198795547264,-198795547200⟩ : DyadicInterval 40),(⟨747014169639,747014188968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23182762,34797559⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23182464,23182528⟩ : DyadicInterval 40),(⟨-23183040,-23182976⟩ : DyadicInterval 40),(⟨762123383351,762123402680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34796992,34797056⟩ : DyadicInterval 40),(⟨-34798144,-34798080⟩ : DyadicInterval 40),(⟨762123383026,762123402355⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1152,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181757379597,181882691330⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168208667968,168208668032⟩ : DyadicInterval 40),(⟨-198672662784,-198672662720⟩ : DyadicInterval 40),(⟨747031286327,747031305656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168316198080,168316198144⟩ : DyadicInterval 40),(⟨-198822802240,-198822802176⟩ : DyadicInterval 40),(⟨747010372177,747010391507⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30506604160,-30463994752⟩ : DyadicInterval 40),(⟨777355380992,777376704960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168237922112,168335701312⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198850037440,-198713505536⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2730_ok : ecellOkT e2730 = true := by decide +kernel
theorem e2730_pos {a z : ℝ} (ha1 : ((338613/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1355301/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2730 e2730_ok ha1 ha2 hz1 hz2 hz

-- box ['1355301/8192000', '27123/163840', '7997/8000', '3999/4000']  interval_lower 282315967/1099511627776
noncomputable def e2731 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281417048752,0,true,168335701248,168335701312⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917606206800,0,false,-198850037440,-198850037376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281530999604,0,true,168433471744,168433471808⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917492255948,0,false,-198986586304,-198986586240⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281348834219,0,true,168277168640,168277168704⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917674421333,0,false,-198768303168,-198768303104⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281485494762,0,true,168394429376,168394429440⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917537760790,0,false,-198932055232,-198932055168⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534825660,0,true,23197632,23197696⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488429892,0,false,-23198144,-23198080⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546448020,0,true,34819648,34819712⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476807532,0,false,-34820800,-34820736⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626673,0,false,-1152,-1088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627287,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281382936857,0,true,168306431360,168306431424⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917640318695,0,false,-198809164032,-198809163968⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281508255717,0,true,168413958016,168413958080⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917514999835,0,false,-198959330624,-198959330560⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069386641604,0,false,-30545372608,-30545372544⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069428114123,0,false,-30502732608,-30502732544⟩
    { al := (1355301/8192000), au := (27123/163840), zl := (7997/8000), zu := (3999/4000),
      A := ⟨181905420976,182019371828⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168335701248,168335701312⟩ : DyadicInterval 40),(⟨-198850037440,-198850037376⟩ : DyadicInterval 40),(⟨747006577109,747006596439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168433471744,168433471808⟩ : DyadicInterval 40),(⟨-198986586304,-198986586240⟩ : DyadicInterval 40),(⟨746987543875,746987563205⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168277168640,168277168704⟩ : DyadicInterval 40),(⟨-198768303168,-198768303104⟩ : DyadicInterval 40),(⟨747017965184,747017984514⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168394429376,168394429440⟩ : DyadicInterval 40),(⟨-198932055232,-198932055168⟩ : DyadicInterval 40),(⟨746995146024,746995165354⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23197884,34820244⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23197632,23197696⟩ : DyadicInterval 40),(⟨-23198144,-23198080⟩ : DyadicInterval 40),(⟨762123383318,762123402647⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34819648,34819712⟩ : DyadicInterval 40),(⟨-34820800,-34820736⟩ : DyadicInterval 40),(⟨762123383025,762123402354⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1152,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181871309081,181996627941⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168306431360,168306431424⟩ : DyadicInterval 40),(⟨-198809164032,-198809163968⟩ : DyadicInterval 40),(⟨747012272478,747012291808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168413958016,168413958080⟩ : DyadicInterval 40),(⟨-198959330624,-198959330560⟩ : DyadicInterval 40),(⟨746991343776,746991363105⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30545372608,-30502732544⟩ : DyadicInterval 40),(⟨777374749888,777396089184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168335701248,168433471808⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198986586304,-198850037376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2731_ok : ecellOkT e2731 = true := by decide +kernel
theorem e2731_pos {a z : ℝ} (ha1 : ((1355301/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((27123/163840 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2731 e2731_ok ha1 ha2 hz1 hz2 hz

-- box ['27123/163840', '1356999/8192000', '1999/2000', '7997/8000']  interval_lower 141928911/549755813888
noncomputable def e2732 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281530999603,0,true,168433471680,168433471744⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917492255949,0,false,-198986586304,-198986586240⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281644950455,0,true,168531233472,168531233536⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917378305097,0,false,-199123152128,-199123152064⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281439989917,0,true,168355385600,168355385664⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917583265635,0,false,-198877526784,-198877526720⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281576650460,0,true,168472637952,168472638016⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917446605092,0,false,-199041295104,-199041295040⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546447327,0,true,34818944,34819008⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476808225,0,false,-34820160,-34820096⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558084813,0,true,46456000,46456064⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465170739,0,false,-46458048,-46457984⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625813,0,false,-1984,-1920⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626674,0,false,-1152,-1088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281485490229,0,true,168394425472,168394425536⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917537765323,0,false,-198932049792,-198932049728⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281610809060,0,true,168501943488,168501943552⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917412446492,0,false,-199082233152,-199082233088⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069352681761,0,false,-30580289664,-30580289600⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069394177647,0,false,-30537624256,-30537624192⟩
    { al := (27123/163840), au := (1356999/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨182019371827,182133322679⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168433471680,168433471744⟩ : DyadicInterval 40),(⟨-198986586304,-198986586240⟩ : DyadicInterval 40),(⟨746987543913,746987563243⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168531233472,168531233536⟩ : DyadicInterval 40),(⟨-199123152128,-199123152064⟩ : DyadicInterval 40),(⟨746968498543,746968517872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168355385600,168355385664⟩ : DyadicInterval 40),(⟨-198877526784,-198877526720⟩ : DyadicInterval 40),(⟨747002746217,747002765546⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168472637952,168472638016⟩ : DyadicInterval 40),(⟨-199041295104,-199041295040⟩ : DyadicInterval 40),(⟨746979915427,746979934757⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34819551,46457037⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34818944,34819008⟩ : DyadicInterval 40),(⟨-34820160,-34820096⟩ : DyadicInterval 40),(⟨762123383057,762123402386⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46456000,46456064⟩ : DyadicInterval 40),(⟨-46458048,-46457984⟩ : DyadicInterval 40),(⟨762123382613,762123401942⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1984,-1088⟩ : DyadicInterval 40),(⟨762123384160,762123403872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181973862453,182099181284⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168394425472,168394425536⟩ : DyadicInterval 40),(⟨-198932049792,-198932049728⟩ : DyadicInterval 40),(⟨746995146787,746995166116⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168501943488,168501943552⟩ : DyadicInterval 40),(⟨-199082233152,-199082233088⟩ : DyadicInterval 40),(⟨746974206084,746974225414⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30580289664,-30537624192⟩ : DyadicInterval 40),(⟨777392195712,777413547712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168433471680,168531233536⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199123152128,-198986586240⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2732_ok : ecellOkT e2732 = true := by decide +kernel
theorem e2732_pos {a z : ℝ} (ha1 : ((27123/163840 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1356999/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2732 e2732_ok ha1 ha2 hz1 hz2 hz

-- box ['1356999/8192000', '169731/1024000', '1999/2000', '7997/8000']  interval_lower 71302517/274877906944
noncomputable def e2733 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281644950454,0,true,168531233472,168531233536⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917378305098,0,false,-199123152128,-199123152064⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281758901306,0,true,168628986496,168628986560⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917264354246,0,false,-199259734848,-199259734784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281553883792,0,true,168453105408,168453105472⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917469371760,0,false,-199014010816,-199014010752⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281690558579,0,true,168570359552,168570359616⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917332696973,0,false,-199177816512,-199177816448⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546470013,0,true,34841664,34841728⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476785539,0,false,-34842816,-34842752⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558115064,0,true,46486272,46486336⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465140488,0,false,-46488320,-46488256⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625810,0,false,-1984,-1920⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626672,0,false,-1152,-1088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281599412589,0,true,168492166272,168492166336⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917423842963,0,false,-199068574656,-199068574592⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281724738543,0,true,168599680832,168599680896⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917298517009,0,false,-199218785216,-199218785152⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069314932355,0,false,-30619104384,-30619104320⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069356456571,0,false,-30576408384,-30576408320⟩
    { al := (1356999/8192000), au := (169731/1024000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨182133322678,182247273530⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168531233472,168531233536⟩ : DyadicInterval 40),(⟨-199123152128,-199123152064⟩ : DyadicInterval 40),(⟨746968498543,746968517872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168628986496,168628986560⟩ : DyadicInterval 40),(⟨-199259734848,-199259734784⟩ : DyadicInterval 40),(⟨746949441046,746949460376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168453105408,168453105472⟩ : DyadicInterval 40),(⟨-199014010816,-199014010752⟩ : DyadicInterval 40),(⟨746983720106,746983739435⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168570359552,168570359616⟩ : DyadicInterval 40),(⟨-199177816512,-199177816448⟩ : DyadicInterval 40),(⟨746960872372,746960891702⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨34842237,46487288⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34841664,34841728⟩ : DyadicInterval 40),(⟨-34842816,-34842752⟩ : DyadicInterval 40),(⟨762123383023,762123402352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46486272,46486336⟩ : DyadicInterval 40),(⟨-46488320,-46488256⟩ : DyadicInterval 40),(⟨762123382610,762123401939⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1984,-1088⟩ : DyadicInterval 40),(⟨762123384160,762123403872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182087784813,182213110767⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168492166272,168492166336⟩ : DyadicInterval 40),(⟨-199068574656,-199068574592⟩ : DyadicInterval 40),(⟨746976111024,746976130353⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168599680832,168599680896⟩ : DyadicInterval 40),(⟨-199218785216,-199218785152⟩ : DyadicInterval 40),(⟨746955155789,746955175119⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30619104384,-30576408320⟩ : DyadicInterval 40),(⟨777411587776,777432955072⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168531233472,168628986560⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199259734848,-199123152064⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2733_ok : ecellOkT e2733 = true := by decide +kernel
theorem e2733_pos {a z : ℝ} (ha1 : ((1356999/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((169731/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2733 e2733_ok ha1 ha2 hz1 hz2 hz

-- box ['27123/163840', '1356999/8192000', '7997/8000', '3999/4000']  interval_lower 70916173/274877906944
noncomputable def e2734 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281530999603,0,true,168433471680,168433471744⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917492255949,0,false,-198986586304,-198986586240⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281644950455,0,true,168531233472,168531233536⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917378305097,0,false,-199123152128,-199123152064⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281462742338,0,true,168374907648,168374907712⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917560513214,0,false,-198904790656,-198904790592⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281599417125,0,true,168492170112,168492170176⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917423838427,0,false,-199068580096,-199068580032⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534840784,0,true,23212736,23212800⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488414768,0,false,-23213312,-23213248⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546470707,0,true,34842368,34842432⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476784845,0,false,-34843520,-34843456⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626671,0,false,-1152,-1088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627286,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281496866339,0,true,168404186112,168404186176⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917526389213,0,false,-198945682176,-198945682112⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281622192319,0,true,168511709312,168511709376⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917401063233,0,false,-199095875968,-199095875904⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069348911093,0,false,-30584166656,-30584166592⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069390411940,0,false,-30541496064,-30541496000⟩
    { al := (27123/163840), au := (1356999/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨182019371827,182133322679⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168433471680,168433471744⟩ : DyadicInterval 40),(⟨-198986586304,-198986586240⟩ : DyadicInterval 40),(⟨746987543913,746987563243⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168531233472,168531233536⟩ : DyadicInterval 40),(⟨-199123152128,-199123152064⟩ : DyadicInterval 40),(⟨746968498543,746968517872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168374907648,168374907712⟩ : DyadicInterval 40),(⟨-198904790656,-198904790592⟩ : DyadicInterval 40),(⟨746998946365,746998965694⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168492170112,168492170176⟩ : DyadicInterval 40),(⟨-199068580096,-199068580032⟩ : DyadicInterval 40),(⟨746976110297,746976129627⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23213008,34842931⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23212736,23212800⟩ : DyadicInterval 40),(⟨-23213312,-23213248⟩ : DyadicInterval 40),(⟨762123383349,762123402678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34842368,34842432⟩ : DyadicInterval 40),(⟨-34843520,-34843456⟩ : DyadicInterval 40),(⟨762123383023,762123402352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1152,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181985238563,182110564543⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168404186112,168404186176⟩ : DyadicInterval 40),(⟨-198945682176,-198945682112⟩ : DyadicInterval 40),(⟨746993246441,746993265771⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168511709312,168511709376⟩ : DyadicInterval 40),(⟨-199095875968,-199095875904⟩ : DyadicInterval 40),(⟨746972303208,746972322538⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30584166656,-30541496000⟩ : DyadicInterval 40),(⟨777394131616,777415486208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168433471680,168531233536⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199123152128,-198986586240⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2734_ok : ecellOkT e2734 = true := by decide +kernel
theorem e2734_pos {a z : ℝ} (ha1 : ((27123/163840 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1356999/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2734 e2734_ok ha1 ha2 hz1 hz2 hz

-- box ['1356999/8192000', '169731/1024000', '7997/8000', '3999/4000']  interval_lower 285016187/1099511627776
noncomputable def e2735 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281644950454,0,true,168531233472,168531233536⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917378305098,0,false,-199123152128,-199123152064⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281758901306,0,true,168628986496,168628986560⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917264354246,0,false,-199259734848,-199259734784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281576650457,0,true,168472637952,168472638016⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917446605095,0,false,-199041295104,-199041295040⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281713339488,0,true,168589902208,168589902272⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917309916064,0,false,-199205121920,-199205121856⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534855908,0,true,23227840,23227904⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488399644,0,false,-23228416,-23228352⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546493395,0,true,34865024,34865088⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476762157,0,false,-34866176,-34866112⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626670,0,false,-1152,-1088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627286,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281610795823,0,true,168501932096,168501932160⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917412459729,0,false,-199082217280,-199082217216⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281736128927,0,true,168609451840,168609451904⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917287126625,0,false,-199232438272,-199232438208⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069311156966,0,false,-30622986368,-30622986304⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069352686147,0,false,-30580285120,-30580285056⟩
    { al := (1356999/8192000), au := (169731/1024000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨182133322678,182247273530⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168531233472,168531233536⟩ : DyadicInterval 40),(⟨-199123152128,-199123152064⟩ : DyadicInterval 40),(⟨746968498543,746968517872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168628986496,168628986560⟩ : DyadicInterval 40),(⟨-199259734848,-199259734784⟩ : DyadicInterval 40),(⟨746949441046,746949460376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168472637952,168472638016⟩ : DyadicInterval 40),(⟨-199041295104,-199041295040⟩ : DyadicInterval 40),(⟨746979915428,746979934757⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168589902208,168589902272⟩ : DyadicInterval 40),(⟨-199205121920,-199205121856⟩ : DyadicInterval 40),(⟨746957062408,746957081737⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23228132,34865619⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23227840,23227904⟩ : DyadicInterval 40),(⟨-23228416,-23228352⟩ : DyadicInterval 40),(⟨762123383349,762123402678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34865024,34865088⟩ : DyadicInterval 40),(⟨-34866176,-34866112⟩ : DyadicInterval 40),(⟨762123383022,762123402351⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1152,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182099168047,182224501151⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168501932096,168501932160⟩ : DyadicInterval 40),(⟨-199082217280,-199082217216⟩ : DyadicInterval 40),(⟨746974208314,746974227644⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168609451840,168609451904⟩ : DyadicInterval 40),(⟨-199232438272,-199232438208⟩ : DyadicInterval 40),(⟨746953250546,746953269875⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30622986368,-30580285056⟩ : DyadicInterval 40),(⟨777413526144,777434896064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168531233472,168628986560⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199259734848,-199123152064⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2735_ok : ecellOkT e2735 = true := by decide +kernel
theorem e2735_pos {a z : ℝ} (ha1 : ((1356999/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((169731/1024000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2735 e2735_ok ha1 ha2 hz1 hz2 hz

-- box ['338613/2048000', '1355301/8192000', '3999/4000', '7999/8000']  interval_lower 280778377/1099511627776
noncomputable def e2736 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281303097901,0,true,168237922112,168237922176⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917720157651,0,false,-198713505600,-198713505536⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281417048753,0,true,168335701248,168335701312⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917606206799,0,false,-198850037440,-198850037376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281257650033,0,true,168198921728,168198921792⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917765605519,0,false,-198659056256,-198659056192⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281394310576,0,true,168316190720,168316190784⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917628944976,0,false,-198822792000,-198822791936⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523219057,0,true,11591168,11591232⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500036495,0,false,-11591360,-11591296⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534826293,0,true,23198272,23198336⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488429259,0,false,-23198784,-23198720⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627286,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627654,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281280369271,0,true,168218418048,168218418112⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917742886281,0,false,-198686274944,-198686274880⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281405688153,0,true,168325953344,168325953408⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917617567399,0,false,-198836424832,-198836424768⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069420587022,0,false,-30510471488,-30510471424⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069462036167,0,false,-30467856896,-30467856832⟩
    { al := (338613/2048000), au := (1355301/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨181791470125,181905420977⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168237922112,168237922176⟩ : DyadicInterval 40),(⟨-198713505600,-198713505536⟩ : DyadicInterval 40),(⟨747025598197,747025617527⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168335701248,168335701312⟩ : DyadicInterval 40),(⟨-198850037440,-198850037376⟩ : DyadicInterval 40),(⟨747006577109,747006596439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168198921728,168198921792⟩ : DyadicInterval 40),(⟨-198659056256,-198659056192⟩ : DyadicInterval 40),(⟨747033181094,747033200424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168316190720,168316190784⟩ : DyadicInterval 40),(⟨-198822792000,-198822791936⟩ : DyadicInterval 40),(⟨747010373617,747010392947⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11591281,23198517⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11591168,11591232⟩ : DyadicInterval 40),(⟨-11591360,-11591296⟩ : DyadicInterval 40),(⟨762123383525,762123402854⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23198272,23198336⟩ : DyadicInterval 40),(⟨-23198784,-23198720⟩ : DyadicInterval 40),(⟨762123383318,762123402647⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181768741495,181894060377⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168218418048,168218418112⟩ : DyadicInterval 40),(⟨-198686274944,-198686274880⟩ : DyadicInterval 40),(⟨747029390671,747029410000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168325953344,168325953408⟩ : DyadicInterval 40),(⟨-198836424832,-198836424768⟩ : DyadicInterval 40),(⟨747008473997,747008493327⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30510471488,-30467856832⟩ : DyadicInterval 40),(⟨777357312032,777378638624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168237922112,168335701312⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198850037440,-198713505536⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2736_ok : ecellOkT e2736 = true := by decide +kernel
theorem e2736_pos {a z : ℝ} (ha1 : ((338613/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1355301/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2736 e2736_ok ha1 ha2 hz1 hz2 hz

-- box ['1355301/8192000', '27123/163840', '3999/4000', '7999/8000']  interval_lower 282123325/1099511627776
noncomputable def e2737 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281417048752,0,true,168335701248,168335701312⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917606206800,0,false,-198850037440,-198850037376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281530999604,0,true,168433471744,168433471808⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917492255948,0,false,-198986586304,-198986586240⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281371572396,0,true,168296679872,168296679936⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917651683156,0,false,-198795547264,-198795547200⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281508247183,0,true,168413950720,168413950784⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917515008369,0,false,-198959320448,-198959320384⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523226619,0,true,11598720,11598784⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500028933,0,false,-11598912,-11598848⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534841417,0,true,23213376,23213440⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488414135,0,false,-23213888,-23213824⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627285,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627654,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281394305876,0,true,168316186688,168316186752⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917628949676,0,false,-198822786368,-198822786304⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281519631884,0,true,168423718528,168423718592⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917503623668,0,false,-198972963456,-198972963392⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069382875407,0,false,-30549244864,-30549244800⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069424352884,0,false,-30506599680,-30506599616⟩
    { al := (1355301/8192000), au := (27123/163840), zl := (3999/4000), zu := (7999/8000),
      A := ⟨181905420976,182019371828⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168335701248,168335701312⟩ : DyadicInterval 40),(⟨-198850037440,-198850037376⟩ : DyadicInterval 40),(⟨747006577109,747006596439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168433471744,168433471808⟩ : DyadicInterval 40),(⟨-198986586304,-198986586240⟩ : DyadicInterval 40),(⟨746987543875,746987563205⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168296679872,168296679936⟩ : DyadicInterval 40),(⟨-198795547264,-198795547200⟩ : DyadicInterval 40),(⟨747014169639,747014188969⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168413950720,168413950784⟩ : DyadicInterval 40),(⟨-198959320448,-198959320384⟩ : DyadicInterval 40),(⟨746991345207,746991364537⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11598843,23213641⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11598720,11598784⟩ : DyadicInterval 40),(⟨-11598912,-11598848⟩ : DyadicInterval 40),(⟨762123383525,762123402854⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23213376,23213440⟩ : DyadicInterval 40),(⟨-23213888,-23213824⟩ : DyadicInterval 40),(⟨762123383317,762123402646⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181882678100,182008004108⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168316186688,168316186752⟩ : DyadicInterval 40),(⟨-198822786368,-198822786304⟩ : DyadicInterval 40),(⟨747010374401,747010393731⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168423718528,168423718592⟩ : DyadicInterval 40),(⟨-198972963456,-198972963392⟩ : DyadicInterval 40),(⟨746989443198,746989462527⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30549244864,-30506599616⟩ : DyadicInterval 40),(⟨777376683424,777398025312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168335701248,168433471808⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198986586304,-198850037376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2737_ok : ecellOkT e2737 = true := by decide +kernel
theorem e2737_pos {a z : ℝ} (ha1 : ((1355301/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((27123/163840 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2737 e2737_ok ha1 ha2 hz1 hz2 hz

-- box ['338613/2048000', '1355301/8192000', '7999/8000', '1']  interval_lower 280586213/1099511627776
noncomputable def e2738 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281303097901,0,true,168237922112,168237922176⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917720157651,0,false,-198713505600,-198713505536⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281417048753,0,true,168335701248,168335701312⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917606206799,0,false,-198850037440,-198850037376⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281280373967,0,true,168218422080,168218422144⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917742881585,0,false,-198686280576,-198686280512⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523227193,0,true,11599296,11599360⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500028359,0,false,-11599488,-11599424⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627653,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1281291731193,0,true,168228168064,168228168128⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨917731524359,0,false,-198699887296,-198699887232⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1281417057227,0,true,168335708544,168335708608⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨917606198325,0,false,-198850047616,-198850047552⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1069416825294,0,false,-30514339072,-30514339008⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1069458279396,0,false,-30471719232,-30471719168⟩
    { al := (338613/2048000), au := (1355301/8192000), zl := (7999/8000), zu := 1,
      A := ⟨181791470125,181905420977⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168237922112,168237922176⟩ : DyadicInterval 40),(⟨-198713505600,-198713505536⟩ : DyadicInterval 40),(⟨747025598197,747025617527⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168335701248,168335701312⟩ : DyadicInterval 40),(⟨-198850037440,-198850037376⟩ : DyadicInterval 40),(⟨747006577109,747006596439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168218422080,168218422144⟩ : DyadicInterval 40),(⟨-198686280576,-198686280512⟩ : DyadicInterval 40),(⟨747029389888,747029409218⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168335701248,168335701312⟩ : DyadicInterval 40),(⟨-198850037440,-198850037376⟩ : DyadicInterval 40),(⟨747006577109,747006596439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11599417⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11599296,11599360⟩ : DyadicInterval 40),(⟨-11599488,-11599424⟩ : DyadicInterval 40),(⟨762123383525,762123402854⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨181780103417,181905429451⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168228168064,168228168128⟩ : DyadicInterval 40),(⟨-198699887296,-198699887232⟩ : DyadicInterval 40),(⟨747027494887,747027514217⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168335708544,168335708608⟩ : DyadicInterval 40),(⟨-198850047616,-198850047552⟩ : DyadicInterval 40),(⟨747006575689,747006595018⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30514339072,-30471719168⟩ : DyadicInterval 40),(⟨777359243200,777380572416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨168237922112,168335701312⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198850037440,-198713505536⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2738_ok : ecellOkT e2738 = true := by decide +kernel
theorem e2738_pos {a z : ℝ} (ha1 : ((338613/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1355301/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2738 e2738_ok ha1 ha2 hz1 hz2 hz

-- box ['1355301/8192000', '27123/163840', '7999/8000', '1']  interval_lower 281930443/1099511627776
noncomputable def e2739 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281417048752,0,true,168335701248,168335701312⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917606206800,0,false,-198850037440,-198850037376⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281530999604,0,true,168433471744,168433471808⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917492255948,0,false,-198986586304,-198986586240⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281394310574,0,true,168316190720,168316190784⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917628944978,0,false,-198822792000,-198822791936⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523234754,0,true,11606912,11606976⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500020798,0,false,-11607040,-11606976⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627653,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1281405674922,0,true,168325941952,168325942016⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨917617580630,0,false,-198836408960,-198836408896⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1281531008083,0,true,168433478976,168433479040⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨917492247469,0,false,-198986596480,-198986596416⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1069379108964,0,false,-30553117440,-30553117376⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1069420591401,0,false,-30510466944,-30510466880⟩
    { al := (1355301/8192000), au := (27123/163840), zl := (7999/8000), zu := 1,
      A := ⟨181905420976,182019371828⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168335701248,168335701312⟩ : DyadicInterval 40),(⟨-198850037440,-198850037376⟩ : DyadicInterval 40),(⟨747006577109,747006596439⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168433471744,168433471808⟩ : DyadicInterval 40),(⟨-198986586304,-198986586240⟩ : DyadicInterval 40),(⟨746987543875,746987563205⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168316190720,168316190784⟩ : DyadicInterval 40),(⟨-198822792000,-198822791936⟩ : DyadicInterval 40),(⟨747010373618,747010392947⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168433471744,168433471808⟩ : DyadicInterval 40),(⟨-198986586304,-198986586240⟩ : DyadicInterval 40),(⟨746987543875,746987563205⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11606978⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11606912,11606976⟩ : DyadicInterval 40),(⟨-11607040,-11606976⟩ : DyadicInterval 40),(⟨762123383493,762123402822⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨181894047146,182019380307⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168325941952,168325942016⟩ : DyadicInterval 40),(⟨-198836408960,-198836408896⟩ : DyadicInterval 40),(⟨747008476222,747008495551⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168433478976,168433479040⟩ : DyadicInterval 40),(⟨-198986596480,-198986596416⟩ : DyadicInterval 40),(⟨746987542490,746987561819⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30553117440,-30510466880⟩ : DyadicInterval 40),(⟨777378617056,777399961600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨168335701248,168433471808⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-198986586304,-198850037376⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2739_ok : ecellOkT e2739 = true := by decide +kernel
theorem e2739_pos {a z : ℝ} (ha1 : ((1355301/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((27123/163840 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2739 e2739_ok ha1 ha2 hz1 hz2 hz

-- box ['27123/163840', '1356999/8192000', '3999/4000', '7999/8000']  interval_lower 141735779/549755813888
noncomputable def e2740 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281530999603,0,true,168433471680,168433471744⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917492255949,0,false,-198986586304,-198986586240⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281644950455,0,true,168531233472,168531233536⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917378305097,0,false,-199123152128,-199123152064⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281485494760,0,true,168394429376,168394429440⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917537760792,0,false,-198932055232,-198932055168⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281622183790,0,true,168511701952,168511702016⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917401071762,0,false,-199095865792,-199095865728⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523234180,0,true,11606336,11606400⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500021372,0,false,-11606528,-11606464⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534856542,0,true,23228480,23228544⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488399010,0,false,-23229056,-23228992⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627285,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627654,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281508242479,0,true,168413946688,168413946752⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917515013073,0,false,-198959314752,-198959314688⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281633575609,0,true,168521475072,168521475136⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917389679943,0,false,-199109519040,-199109518976⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069345140178,0,false,-30588043968,-30588043904⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069386645988,0,false,-30545368064,-30545368000⟩
    { al := (27123/163840), au := (1356999/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨182019371827,182133322679⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168433471680,168433471744⟩ : DyadicInterval 40),(⟨-198986586304,-198986586240⟩ : DyadicInterval 40),(⟨746987543913,746987563243⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168531233472,168531233536⟩ : DyadicInterval 40),(⟨-199123152128,-199123152064⟩ : DyadicInterval 40),(⟨746968498543,746968517872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168394429376,168394429440⟩ : DyadicInterval 40),(⟨-198932055232,-198932055168⟩ : DyadicInterval 40),(⟨746995146024,746995165354⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168511701952,168511702016⟩ : DyadicInterval 40),(⟨-199095865792,-199095865728⟩ : DyadicInterval 40),(⟨746972304678,746972324007⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11606404,23228766⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11606336,11606400⟩ : DyadicInterval 40),(⟨-11606528,-11606464⟩ : DyadicInterval 40),(⟨762123383525,762123402854⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23228480,23228544⟩ : DyadicInterval 40),(⟨-23229056,-23228992⟩ : DyadicInterval 40),(⟨762123383349,762123402678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨181996614703,182121947833⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168413946688,168413946752⟩ : DyadicInterval 40),(⟨-198959314752,-198959314688⟩ : DyadicInterval 40),(⟨746991345966,746991365296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168521475072,168521475136⟩ : DyadicInterval 40),(⟨-199109519040,-199109518976⟩ : DyadicInterval 40),(⟨746970400228,746970419558⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30588043968,-30545368000⟩ : DyadicInterval 40),(⟨777396067616,777417424864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168433471680,168531233536⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199123152128,-198986586240⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2740_ok : ecellOkT e2740 = true := by decide +kernel
theorem e2740_pos {a z : ℝ} (ha1 : ((27123/163840 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1356999/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2740 e2740_ok ha1 ha2 hz1 hz2 hz

-- box ['1356999/8192000', '169731/1024000', '3999/4000', '7999/8000']  interval_lower 35602843/137438953472
noncomputable def e2741 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281644950454,0,true,168531233472,168531233536⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917378305098,0,false,-199123152128,-199123152064⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281758901306,0,true,168628986496,168628986560⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917264354246,0,false,-199259734848,-199259734784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281599417123,0,true,168492170112,168492170176⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917423838429,0,false,-199068580096,-199068580032⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281736120397,0,true,168609444544,168609444608⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917287135155,0,false,-199232428096,-199232428032⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523241743,0,true,11613888,11613952⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500013809,0,false,-11614080,-11614016⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534871668,0,true,23243584,23243648⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488383884,0,false,-23244160,-23244096⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627284,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627654,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281622179083,0,true,168511697920,168511697984⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917401076469,0,false,-199095860096,-199095860032⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281747519339,0,true,168619222848,168619222912⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917275736213,0,false,-199246091584,-199246091520⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069307381331,0,false,-30626868672,-30626868608⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069348915478,0,false,-30584162176,-30584162112⟩
    { al := (1356999/8192000), au := (169731/1024000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨182133322678,182247273530⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168531233472,168531233536⟩ : DyadicInterval 40),(⟨-199123152128,-199123152064⟩ : DyadicInterval 40),(⟨746968498543,746968517872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168628986496,168628986560⟩ : DyadicInterval 40),(⟨-199259734848,-199259734784⟩ : DyadicInterval 40),(⟨746949441046,746949460376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168492170112,168492170176⟩ : DyadicInterval 40),(⟨-199068580096,-199068580032⟩ : DyadicInterval 40),(⟨746976110298,746976129627⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168609444544,168609444608⟩ : DyadicInterval 40),(⟨-199232428096,-199232428032⟩ : DyadicInterval 40),(⟨746953251980,746953271310⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11613967,23243892⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11613888,11613952⟩ : DyadicInterval 40),(⟨-11614080,-11614016⟩ : DyadicInterval 40),(⟨762123383525,762123402854⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23243584,23243648⟩ : DyadicInterval 40),(⟨-23244160,-23244096⟩ : DyadicInterval 40),(⟨762123383348,762123402677⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182110551307,182235891563⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168511697920,168511697984⟩ : DyadicInterval 40),(⟨-199095860096,-199095860032⟩ : DyadicInterval 40),(⟨746972305439,746972324768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168619222848,168619222912⟩ : DyadicInterval 40),(⟨-199246091584,-199246091520⟩ : DyadicInterval 40),(⟨746951345162,746951364491⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30626868672,-30584162112⟩ : DyadicInterval 40),(⟨777415464672,777436837216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168531233472,168628986560⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199259734848,-199123152064⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2741_ok : ecellOkT e2741 = true := by decide +kernel
theorem e2741_pos {a z : ℝ} (ha1 : ((1356999/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((169731/1024000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2741 e2741_ok ha1 ha2 hz1 hz2 hz

-- box ['27123/163840', '1356999/8192000', '7999/8000', '1']  interval_lower 141639213/549755813888
noncomputable def e2742 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281530999603,0,true,168433471680,168433471744⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917492255949,0,false,-198986586304,-198986586240⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281644950455,0,true,168531233472,168531233536⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917378305097,0,false,-199123152128,-199123152064⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281508247181,0,true,168413950720,168413950784⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917515008371,0,false,-198959320448,-198959320384⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523242317,0,true,11614464,11614528⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500013235,0,false,-11614656,-11614592⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627653,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1281519618647,0,true,168423707200,168423707264⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨917503636905,0,false,-198972947584,-198972947520⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1281644958929,0,true,168531240704,168531240768⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨917378296623,0,false,-199123162240,-199123162176⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1069341369018,0,false,-30591921472,-30591921408⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1069382879791,0,false,-30549240384,-30549240320⟩
    { al := (27123/163840), au := (1356999/8192000), zl := (7999/8000), zu := 1,
      A := ⟨182019371827,182133322679⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168433471680,168433471744⟩ : DyadicInterval 40),(⟨-198986586304,-198986586240⟩ : DyadicInterval 40),(⟨746987543913,746987563243⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168531233472,168531233536⟩ : DyadicInterval 40),(⟨-199123152128,-199123152064⟩ : DyadicInterval 40),(⟨746968498543,746968517872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168413950720,168413950784⟩ : DyadicInterval 40),(⟨-198959320448,-198959320384⟩ : DyadicInterval 40),(⟨746991345208,746991364537⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168531233472,168531233536⟩ : DyadicInterval 40),(⟨-199123152128,-199123152064⟩ : DyadicInterval 40),(⟨746968498543,746968517872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11614541⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11614464,11614528⟩ : DyadicInterval 40),(⟨-11614656,-11614592⟩ : DyadicInterval 40),(⟨762123383525,762123402854⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨182007990871,182133331153⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168423707200,168423707264⟩ : DyadicInterval 40),(⟨-198972947584,-198972947520⟩ : DyadicInterval 40),(⟨746989445389,746989464718⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168531240704,168531240768⟩ : DyadicInterval 40),(⟨-199123162240,-199123162176⟩ : DyadicInterval 40),(⟨746968497130,746968516459⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30591921472,-30549240320⟩ : DyadicInterval 40),(⟨777398003776,777419363616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨168433471680,168531233536⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199123152128,-198986586240⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2742_ok : ecellOkT e2742 = true := by decide +kernel
theorem e2742_pos {a z : ℝ} (ha1 : ((27123/163840 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1356999/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2742 e2742_ok ha1 ha2 hz1 hz2 hz

-- box ['1356999/8192000', '169731/1024000', '7999/8000', '1']  interval_lower 284628993/1099511627776
noncomputable def e2743 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281644950454,0,true,168531233472,168531233536⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917378305098,0,false,-199123152128,-199123152064⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281758901306,0,true,168628986496,168628986560⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917264354246,0,false,-199259734848,-199259734784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281622183788,0,true,168511701952,168511702016⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917401071764,0,false,-199095865792,-199095865728⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523249880,0,true,11622016,11622080⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500005672,0,false,-11622208,-11622144⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627653,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1281633562373,0,true,168521463680,168521463744⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨917389693179,0,false,-199109503168,-199109503104⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1281758909780,0,true,168628993792,168628993856⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨917264345772,0,false,-199259745024,-199259744960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1069303605451,0,false,-30630751232,-30630751168⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1069345144564,0,false,-30588039424,-30588039360⟩
    { al := (1356999/8192000), au := (169731/1024000), zl := (7999/8000), zu := 1,
      A := ⟨182133322678,182247273530⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168531233472,168531233536⟩ : DyadicInterval 40),(⟨-199123152128,-199123152064⟩ : DyadicInterval 40),(⟨746968498543,746968517872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168628986496,168628986560⟩ : DyadicInterval 40),(⟨-199259734848,-199259734784⟩ : DyadicInterval 40),(⟨746949441046,746949460376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168511701952,168511702016⟩ : DyadicInterval 40),(⟨-199095865792,-199095865728⟩ : DyadicInterval 40),(⟨746972304678,746972324008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168628986496,168628986560⟩ : DyadicInterval 40),(⟨-199259734848,-199259734784⟩ : DyadicInterval 40),(⟨746949441046,746949460376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11622104⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11622016,11622080⟩ : DyadicInterval 40),(⟨-11622208,-11622144⟩ : DyadicInterval 40),(⟨762123383525,762123402854⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨182121934597,182247282004⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168521463680,168521463744⟩ : DyadicInterval 40),(⟨-199109503168,-199109503104⟩ : DyadicInterval 40),(⟨746970402459,746970421789⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168628993792,168628993856⟩ : DyadicInterval 40),(⟨-199259745024,-199259744960⟩ : DyadicInterval 40),(⟨746949439621,746949458950⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30630751232,-30588039360⟩ : DyadicInterval 40),(⟨777417403296,777438778496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨168531233472,168628986560⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199259734848,-199123152064⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2743_ok : ecellOkT e2743 = true := by decide +kernel
theorem e2743_pos {a z : ℝ} (ha1 : ((1356999/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((169731/1024000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2743 e2743_ok ha1 ha2 hz1 hz2 hz

-- box ['169731/1024000', '1358697/8192000', '999/1000', '7993/8000']  interval_lower 143670111/549755813888
noncomputable def e2744 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281758901305,0,true,168628986496,168628986560⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917264354247,0,false,-199259734848,-199259734784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281872852157,0,true,168726730880,168726730944⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917150403395,0,false,-199396334592,-199396334528⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281576654031,0,true,168472641024,168472641088⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917446601521,0,false,-199041299392,-199041299328⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281713286086,0,true,168589856448,168589856512⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917309969466,0,false,-199205057920,-199205057856⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592978783,0,true,81347968,81348032⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430276769,0,false,-81354048,-81353984⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099604661651,0,true,93029888,93029952⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099418593901,0,false,-93037824,-93037760⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619904,0,false,-7936,-7872⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621757,0,false,-6080,-6016⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281667773817,0,true,168550813248,168550813312⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917355481735,0,false,-199150507072,-199150507008⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281793078297,0,true,168658303680,168658303744⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917230177255,0,false,-199300703104,-199300703040⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069292277325,0,false,-30642399424,-30642399360⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069333810005,0,false,-30599693824,-30599693760⟩
    { al := (169731/1024000), au := (1358697/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨182247273529,182361224381⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168628986496,168628986560⟩ : DyadicInterval 40),(⟨-199259734848,-199259734784⟩ : DyadicInterval 40),(⟨746949441046,746949460376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168726730880,168726730944⟩ : DyadicInterval 40),(⟨-199396334592,-199396334528⟩ : DyadicInterval 40),(⟨746930371400,746930390730⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168472641024,168472641088⟩ : DyadicInterval 40),(⟨-199041299392,-199041299328⟩ : DyadicInterval 40),(⟨746979914829,746979934159⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168589856448,168589856512⟩ : DyadicInterval 40),(⟨-199205057920,-199205057856⟩ : DyadicInterval 40),(⟨746957071314,746957090643⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨81351007,93033875⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81347968,81348032⟩ : DyadicInterval 40),(⟨-81354048,-81353984⟩ : DyadicInterval 40),(⟨762123380572,762123399902⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨93029888,93029952⟩ : DyadicInterval 40),(⟨-93037824,-93037760⟩ : DyadicInterval 40),(⟨762123379647,762123398977⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7936,-6016⟩ : DyadicInterval 40),(⟨762123386624,762123406848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182156146041,182281450521⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168550813248,168550813312⟩ : DyadicInterval 40),(⟨-199150507072,-199150507008⟩ : DyadicInterval 40),(⟨746964682454,746964701783⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168658303680,168658303744⟩ : DyadicInterval 40),(⟨-199300703104,-199300703040⟩ : DyadicInterval 40),(⟨746943722793,746943742122⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30642399424,-30599693760⟩ : DyadicInterval 40),(⟨777423230496,777444602592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168628986496,168726730944⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199396334592,-199259734784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2744_ok : ecellOkT e2744 = true := by decide +kernel
theorem e2744_pos {a z : ℝ} (ha1 : ((169731/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1358697/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2744 e2744_ok ha1 ha2 hz1 hz2 hz

-- box ['1358697/8192000', '679773/4096000', '999/1000', '7993/8000']  interval_lower 72175069/274877906944
noncomputable def e2745 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281872852156,0,true,168726730880,168726730944⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917150403396,0,false,-199396334592,-199396334528⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281986803008,0,true,168824466560,168824466624⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917036452544,0,false,-199532951296,-199532951232⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281690490931,0,true,168570301504,168570301568⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917332764621,0,false,-199177735424,-199177735360⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281827137230,0,true,168687518720,168687518784⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917196118322,0,false,-199341531328,-199341531264⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593031724,0,true,81400896,81400960⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430223828,0,false,-81406976,-81406912⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099604722160,0,true,93090432,93090496⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099418533392,0,false,-93098368,-93098304⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619893,0,false,-7936,-7872⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621750,0,false,-6080,-6016⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281781667688,0,true,168648515712,168648515776⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917241587864,0,false,-199287024960,-199287024896⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281906979292,0,true,168756002688,168756002752⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917116276260,0,false,-199437248192,-199437248128⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069254499598,0,false,-30681245504,-30681245440⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069296060601,0,false,-30638509248,-30638509184⟩
    { al := (1358697/8192000), au := (679773/4096000), zl := (999/1000), zu := (7993/8000),
      A := ⟨182361224380,182475175232⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168726730880,168726730944⟩ : DyadicInterval 40),(⟨-199396334592,-199396334528⟩ : DyadicInterval 40),(⟨746930371400,746930390730⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168824466560,168824466624⟩ : DyadicInterval 40),(⟨-199532951296,-199532951232⟩ : DyadicInterval 40),(⟨746911289614,746911308944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168570301504,168570301568⟩ : DyadicInterval 40),(⟨-199177735424,-199177735360⟩ : DyadicInterval 40),(⟨746960883691,746960903021⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168687518720,168687518784⟩ : DyadicInterval 40),(⟨-199341531328,-199341531264⟩ : DyadicInterval 40),(⟨746938023247,746938042577⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨81403948,93094384⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81400896,81400960⟩ : DyadicInterval 40),(⟨-81406976,-81406912⟩ : DyadicInterval 40),(⟨762123380564,762123399894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨93090432,93090496⟩ : DyadicInterval 40),(⟨-93098368,-93098304⟩ : DyadicInterval 40),(⟨762123379637,762123398967⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7936,-6016⟩ : DyadicInterval 40),(⟨762123386624,762123406848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182270039912,182395351516⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168648515712,168648515776⟩ : DyadicInterval 40),(⟨-199287024960,-199287024896⟩ : DyadicInterval 40),(⟨746945632055,746945651385⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168756002688,168756002752⟩ : DyadicInterval 40),(⟨-199437248192,-199437248128⟩ : DyadicInterval 40),(⟨746924657867,746924677197⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30681245504,-30638509184⟩ : DyadicInterval 40),(⟨777442638208,777464025632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168726730880,168824466624⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199532951296,-199396334528⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2745_ok : ecellOkT e2745 = true := by decide +kernel
theorem e2745_pos {a z : ℝ} (ha1 : ((1358697/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((679773/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2745 e2745_ok ha1 ha2 hz1 hz2 hz

-- box ['169731/1024000', '1358697/8192000', '7993/8000', '3997/4000']  interval_lower 287146579/1099511627776
noncomputable def e2746 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281758901305,0,true,168628986496,168628986560⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917264354247,0,false,-199259734848,-199259734784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281872852157,0,true,168726730880,168726730944⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917150403395,0,false,-199396334592,-199396334528⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281599434940,0,true,168492185408,168492185472⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917423820612,0,false,-199068601472,-199068601408⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281736081239,0,true,168609410944,168609411008⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917287174313,0,false,-199232381120,-199232381056⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581357351,0,true,69727360,69727424⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441898201,0,false,-69731840,-69731776⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593032657,0,true,81401856,81401920⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430222895,0,false,-81407936,-81407872⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621749,0,false,-6080,-6016⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623354,0,false,-4480,-4416⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281679164056,0,true,168560584640,168560584704⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917344091496,0,false,-199164159104,-199164159040⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281804475685,0,true,168668080192,168668080256⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917218779867,0,false,-199314365568,-199314365504⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069288498198,0,false,-30646285376,-30646285312⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069330035844,0,false,-30603574464,-30603574400⟩
    { al := (169731/1024000), au := (1358697/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨182247273529,182361224381⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168628986496,168628986560⟩ : DyadicInterval 40),(⟨-199259734848,-199259734784⟩ : DyadicInterval 40),(⟨746949441046,746949460376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168726730880,168726730944⟩ : DyadicInterval 40),(⟨-199396334592,-199396334528⟩ : DyadicInterval 40),(⟨746930371400,746930390730⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168492185408,168492185472⟩ : DyadicInterval 40),(⟨-199068601472,-199068601408⟩ : DyadicInterval 40),(⟨746976107323,746976126652⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168609410944,168609411008⟩ : DyadicInterval 40),(⟨-199232381120,-199232381056⟩ : DyadicInterval 40),(⟨746953258520,746953277849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨69729575,81404881⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69727360,69727424⟩ : DyadicInterval 40),(⟨-69731840,-69731776⟩ : DyadicInterval 40),(⟨762123381369,762123400698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81401856,81401920⟩ : DyadicInterval 40),(⟨-81407936,-81407872⟩ : DyadicInterval 40),(⟨762123380564,762123399894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6080,-4416⟩ : DyadicInterval 40),(⟨762123385824,762123405920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182167536280,182292847909⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168560584640,168560584704⟩ : DyadicInterval 40),(⟨-199164159104,-199164159040⟩ : DyadicInterval 40),(⟨746962777797,746962797126⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168668080192,168668080256⟩ : DyadicInterval 40),(⟨-199314365568,-199314365504⟩ : DyadicInterval 40),(⟨746941815637,746941834967⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30646285376,-30603574400⟩ : DyadicInterval 40),(⟨777425170816,777446545568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168628986496,168726730944⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199396334592,-199259734784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2746_ok : ecellOkT e2746 = true := by decide +kernel
theorem e2746_pos {a z : ℝ} (ha1 : ((169731/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1358697/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2746 e2746_ok ha1 ha2 hz1 hz2 hz

-- box ['1358697/8192000', '679773/4096000', '7993/8000', '3997/4000']  interval_lower 288506085/1099511627776
noncomputable def e2747 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281872852156,0,true,168726730880,168726730944⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917150403396,0,false,-199396334592,-199396334528⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281986803008,0,true,168824466560,168824466624⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917036452544,0,false,-199532951296,-199532951232⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281713286084,0,true,168589856448,168589856512⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917309969468,0,false,-199205057920,-199205057856⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281849946627,0,true,168707083776,168707083840⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917173308925,0,false,-199368875008,-199368874944⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581402730,0,true,69772736,69772800⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441852822,0,false,-69777216,-69777152⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593085603,0,true,81454784,81454848⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430169949,0,false,-81460864,-81460800⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621741,0,false,-6080,-6016⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623349,0,false,-4480,-4416⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281793065057,0,true,168658292288,168658292352⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917230190495,0,false,-199300687232,-199300687168⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281918383808,0,true,168765784448,168765784512⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917104871744,0,false,-199450920896,-199450920832⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069250715744,0,false,-30685136384,-30685136320⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069292281716,0,false,-30642394880,-30642394816⟩
    { al := (1358697/8192000), au := (679773/4096000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨182361224380,182475175232⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168726730880,168726730944⟩ : DyadicInterval 40),(⟨-199396334592,-199396334528⟩ : DyadicInterval 40),(⟨746930371400,746930390730⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168824466560,168824466624⟩ : DyadicInterval 40),(⟨-199532951296,-199532951232⟩ : DyadicInterval 40),(⟨746911289614,746911308944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168589856448,168589856512⟩ : DyadicInterval 40),(⟨-199205057920,-199205057856⟩ : DyadicInterval 40),(⟨746957071314,746957090644⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168707083776,168707083840⟩ : DyadicInterval 40),(⟨-199368875008,-199368874944⟩ : DyadicInterval 40),(⟨746934205601,746934224930⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨69774954,81457827⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69772736,69772800⟩ : DyadicInterval 40),(⟨-69777216,-69777152⟩ : DyadicInterval 40),(⟨762123381363,762123400693⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81454784,81454848⟩ : DyadicInterval 40),(⟨-81460864,-81460800⟩ : DyadicInterval 40),(⟨762123380556,762123399886⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6080,-4416⟩ : DyadicInterval 40),(⟨762123385824,762123405920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182281437281,182406756032⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168658292288,168658292352⟩ : DyadicInterval 40),(⟨-199300687232,-199300687168⟩ : DyadicInterval 40),(⟨746943725028,746943744358⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168765784448,168765784512⟩ : DyadicInterval 40),(⟨-199450920896,-199450920832⟩ : DyadicInterval 40),(⟨746922748301,746922767631⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30685136384,-30642394816⟩ : DyadicInterval 40),(⟨777444581024,777465971072⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168726730880,168824466624⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199532951296,-199396334528⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2747_ok : ecellOkT e2747 = true := by decide +kernel
theorem e2747_pos {a z : ℝ} (ha1 : ((1358697/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((679773/4096000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2747 e2747_ok ha1 ha2 hz1 hz2 hz

-- box ['679773/4096000', '272079/1638400', '999/1000', '7993/8000']  interval_lower 72515853/274877906944
noncomputable def e2748 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281986803007,0,true,168824466560,168824466624⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917036452545,0,false,-199532951296,-199532951232⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282100753859,0,true,168922193600,168922193664⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916922501693,0,false,-199669585024,-199669584960⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281804327831,0,true,168667953344,168667953408⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917218927721,0,false,-199314188352,-199314188288⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281940988374,0,true,168785172416,168785172480⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917082267178,0,false,-199478021696,-199478021632⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593084670,0,true,81453824,81453888⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430170882,0,false,-81459968,-81459904⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099604782675,0,true,93150912,93150976⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099418472877,0,false,-93158848,-93158784⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619883,0,false,-7936,-7872⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621742,0,false,-6080,-6016⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281895561565,0,true,168746209472,168746209536⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917127693987,0,false,-199423559744,-199423559680⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282020880295,0,true,168853692992,168853693056⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917002375257,0,false,-199573810176,-199573810112⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069216698269,0,false,-30720117184,-30720117120⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069258287599,0,false,-30677350272,-30677350208⟩
    { al := (679773/4096000), au := (272079/1638400), zl := (999/1000), zu := (7993/8000),
      A := ⟨182475175231,182589126083⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168824466560,168824466624⟩ : DyadicInterval 40),(⟨-199532951296,-199532951232⟩ : DyadicInterval 40),(⟨746911289614,746911308944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168922193600,168922193664⟩ : DyadicInterval 40),(⟨-199669585024,-199669584960⟩ : DyadicInterval 40),(⟨746892195677,746892215006⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168667953344,168667953408⟩ : DyadicInterval 40),(⟨-199314188352,-199314188288⟩ : DyadicInterval 40),(⟨746941840401,746941859730⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168785172416,168785172480⟩ : DyadicInterval 40),(⟨-199478021696,-199478021632⟩ : DyadicInterval 40),(⟨746918963008,746918982338⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨81456894,93154899⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81453824,81453888⟩ : DyadicInterval 40),(⟨-81459968,-81459904⟩ : DyadicInterval 40),(⟨762123380589,762123399918⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨93150912,93150976⟩ : DyadicInterval 40),(⟨-93158848,-93158784⟩ : DyadicInterval 40),(⟨762123379627,762123398956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7936,-6016⟩ : DyadicInterval 40),(⟨762123386624,762123406848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182383933789,182509252519⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168746209472,168746209536⟩ : DyadicInterval 40),(⟨-199423559744,-199423559680⟩ : DyadicInterval 40),(⟨746926569514,746926588844⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168853692992,168853693056⟩ : DyadicInterval 40),(⟨-199573810176,-199573810112⟩ : DyadicInterval 40),(⟨746905580795,746905600124⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30720117184,-30677350208⟩ : DyadicInterval 40),(⟨777462058720,777483461472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168824466560,168922193664⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199669585024,-199532951232⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2748_ok : ecellOkT e2748 = true := by decide +kernel
theorem e2748_pos {a z : ℝ} (ha1 : ((679773/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((272079/1638400 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2748 e2748_ok ha1 ha2 hz1 hz2 hz

-- box ['272079/1638400', '340311/2048000', '999/1000', '7993/8000']  interval_lower 291429651/1099511627776
noncomputable def e2749 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282100753858,0,true,168922193600,168922193664⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916922501694,0,false,-199669585024,-199669584960⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282214704710,0,true,169019911872,169019911936⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916808550842,0,false,-199806235648,-199806235584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281918164731,0,true,168765596544,168765596608⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917105090821,0,false,-199450658240,-199450658176⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282054839518,0,true,168882817344,168882817408⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916968416034,0,false,-199614529024,-199614528960⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593137618,0,true,81506816,81506880⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430117934,0,false,-81512896,-81512832⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099604843193,0,true,93211456,93211520⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099418412359,0,false,-93219392,-93219328⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619873,0,false,-7936,-7872⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621734,0,false,-6080,-6016⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282009455442,0,true,168843894528,168843894592⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917013800110,0,false,-199560111552,-199560111488⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282134781289,0,true,168951374656,168951374720⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916888474263,0,false,-199710389184,-199710389120⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069178873345,0,false,-30759014528,-30759014464⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069220491001,0,false,-30716216960,-30716216896⟩
    { al := (272079/1638400), au := (340311/2048000), zl := (999/1000), zu := (7993/8000),
      A := ⟨182589126082,182703076934⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168922193600,168922193664⟩ : DyadicInterval 40),(⟨-199669585024,-199669584960⟩ : DyadicInterval 40),(⟨746892195677,746892215007⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169019911872,169019911936⟩ : DyadicInterval 40),(⟨-199806235648,-199806235584⟩ : DyadicInterval 40),(⟨746873089607,746873108937⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168765596544,168765596608⟩ : DyadicInterval 40),(⟨-199450658240,-199450658176⟩ : DyadicInterval 40),(⟨746922784982,746922804311⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168882817344,168882817408⟩ : DyadicInterval 40),(⟨-199614529024,-199614528960⟩ : DyadicInterval 40),(⟨746899890709,746899910038⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨81509842,93215417⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81506816,81506880⟩ : DyadicInterval 40),(⟨-81512896,-81512832⟩ : DyadicInterval 40),(⟨762123380549,762123399878⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨93211456,93211520⟩ : DyadicInterval 40),(⟨-93219392,-93219328⟩ : DyadicInterval 40),(⟨762123379616,762123398946⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7936,-6016⟩ : DyadicInterval 40),(⟨762123386624,762123406848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182497827666,182623153513⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168843894528,168843894592⟩ : DyadicInterval 40),(⟨-199560111552,-199560111488⟩ : DyadicInterval 40),(⟨746907494883,746907514213⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168951374656,168951374720⟩ : DyadicInterval 40),(⟨-199710389184,-199710389120⟩ : DyadicInterval 40),(⟨746886491593,746886510922⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30759014528,-30716216896⟩ : DyadicInterval 40),(⟨777481492064,777502910144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168922193600,169019911936⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199806235648,-199669584960⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2749_ok : ecellOkT e2749 = true := by decide +kernel
theorem e2749_pos {a z : ℝ} (ha1 : ((272079/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((340311/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2749 e2749_ok ha1 ha2 hz1 hz2 hz

-- box ['679773/4096000', '272079/1638400', '7993/8000', '3997/4000']  interval_lower 72467227/274877906944
noncomputable def e2750 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281986803007,0,true,168824466560,168824466624⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917036452545,0,false,-199532951296,-199532951232⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282100753859,0,true,168922193600,168922193664⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916922501693,0,false,-199669585024,-199669584960⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281827137228,0,true,168687518720,168687518784⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917196118324,0,false,-199341531328,-199341531264⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281963812015,0,true,168804747904,168804747968⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917059443537,0,false,-199505385856,-199505385792⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581448112,0,true,69818112,69818176⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441807440,0,false,-69822592,-69822528⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593138553,0,true,81507712,81507776⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430116999,0,false,-81513856,-81513792⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621733,0,false,-6080,-6016⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623343,0,false,-4480,-4416⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281906966050,0,true,168755991296,168755991360⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917116289502,0,false,-199437232320,-199437232256⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282032291929,0,true,168863480000,168863480064⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916990963623,0,false,-199587493120,-199587493056⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069212909689,0,false,-30724013120,-30724013056⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069254503992,0,false,-30681240960,-30681240896⟩
    { al := (679773/4096000), au := (272079/1638400), zl := (7993/8000), zu := (3997/4000),
      A := ⟨182475175231,182589126083⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168824466560,168824466624⟩ : DyadicInterval 40),(⟨-199532951296,-199532951232⟩ : DyadicInterval 40),(⟨746911289614,746911308944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168922193600,168922193664⟩ : DyadicInterval 40),(⟨-199669585024,-199669584960⟩ : DyadicInterval 40),(⟨746892195677,746892215006⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168687518720,168687518784⟩ : DyadicInterval 40),(⟨-199341531328,-199341531264⟩ : DyadicInterval 40),(⟨746938023247,746938042577⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168804747904,168804747968⟩ : DyadicInterval 40),(⟨-199505385856,-199505385792⟩ : DyadicInterval 40),(⟨746915140578,746915159908⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨69820336,81510777⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69818112,69818176⟩ : DyadicInterval 40),(⟨-69822592,-69822528⟩ : DyadicInterval 40),(⟨762123381358,762123400687⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81507712,81507776⟩ : DyadicInterval 40),(⟨-81513856,-81513792⟩ : DyadicInterval 40),(⟨762123380581,762123399910⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6080,-4416⟩ : DyadicInterval 40),(⟨762123385824,762123405920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182395338274,182520664153⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168755991296,168755991360⟩ : DyadicInterval 40),(⟨-199437232320,-199437232256⟩ : DyadicInterval 40),(⟨746924660106,746924679435⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168863480000,168863480064⟩ : DyadicInterval 40),(⟨-199587493120,-199587493056⟩ : DyadicInterval 40),(⟨746903668816,746903688146⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30724013120,-30681240896⟩ : DyadicInterval 40),(⟨777464004064,777485409440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168824466560,168922193664⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199669585024,-199532951232⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2750_ok : ecellOkT e2750 = true := by decide +kernel
theorem e2750_pos {a z : ℝ} (ha1 : ((679773/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((272079/1638400 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2750 e2750_ok ha1 ha2 hz1 hz2 hz

-- box ['272079/1638400', '340311/2048000', '7993/8000', '3997/4000']  interval_lower 145617333/549755813888
noncomputable def e2751 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282100753858,0,true,168922193600,168922193664⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916922501694,0,false,-199669585024,-199669584960⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282214704710,0,true,169019911872,169019911936⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916808550842,0,false,-199806235648,-199806235584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281940988372,0,true,168785172416,168785172480⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917082267180,0,false,-199478021696,-199478021632⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282077677403,0,true,168902403328,168902403392⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916945578149,0,false,-199641913600,-199641913536⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581493498,0,true,69863488,69863552⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441762054,0,false,-69867968,-69867904⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593191507,0,true,81560704,81560768⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430064045,0,false,-81566784,-81566720⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621725,0,false,-6080,-6016⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623337,0,false,-4480,-4416⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282020867050,0,true,168853681600,168853681664⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917002388502,0,false,-199573794304,-199573794240⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282146200048,0,true,168961166912,168961166976⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916877055504,0,false,-199724082368,-199724082304⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069175080033,0,false,-30762915456,-30762915392⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069216702667,0,false,-30720112640,-30720112576⟩
    { al := (272079/1638400), au := (340311/2048000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨182589126082,182703076934⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168922193600,168922193664⟩ : DyadicInterval 40),(⟨-199669585024,-199669584960⟩ : DyadicInterval 40),(⟨746892195677,746892215007⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169019911872,169019911936⟩ : DyadicInterval 40),(⟨-199806235648,-199806235584⟩ : DyadicInterval 40),(⟨746873089607,746873108937⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168785172416,168785172480⟩ : DyadicInterval 40),(⟨-199478021696,-199478021632⟩ : DyadicInterval 40),(⟨746918963009,746918982338⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168902403328,168902403392⟩ : DyadicInterval 40),(⟨-199641913600,-199641913536⟩ : DyadicInterval 40),(⟨746896063425,746896082754⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨69865722,81563731⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69863488,69863552⟩ : DyadicInterval 40),(⟨-69867968,-69867904⟩ : DyadicInterval 40),(⟨762123381352,762123400681⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81560704,81560768⟩ : DyadicInterval 40),(⟨-81566784,-81566720⟩ : DyadicInterval 40),(⟨762123380541,762123399870⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6080,-4416⟩ : DyadicInterval 40),(⟨762123385824,762123405920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182509239274,182634572272⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168853681600,168853681664⟩ : DyadicInterval 40),(⟨-199573794304,-199573794240⟩ : DyadicInterval 40),(⟨746905583036,746905602366⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168961166912,168961166976⟩ : DyadicInterval 40),(⟨-199724082368,-199724082304⟩ : DyadicInterval 40),(⟨746884577198,746884596528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30762915456,-30720112576⟩ : DyadicInterval 40),(⟨777483439904,777504860608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168922193600,169019911936⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199806235648,-199669584960⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2751_ok : ecellOkT e2751 = true := by decide +kernel
theorem e2751_pos {a z : ℝ} (ha1 : ((272079/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((340311/2048000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2751 e2751_ok ha1 ha2 hz1 hz2 hz

-- box ['169731/1024000', '1358697/8192000', '3997/4000', '1599/1600']  interval_lower 286952629/1099511627776
noncomputable def e2752 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281758901305,0,true,168628986496,168628986560⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917264354247,0,false,-199259734848,-199259734784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281872852157,0,true,168726730880,168726730944⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917150403395,0,false,-199396334592,-199396334528⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281622215849,0,true,168511729472,168511729536⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917401039703,0,false,-199095904192,-199095904128⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281758876392,0,true,168628965184,168628965248⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917264379160,0,false,-199259705024,-199259704960⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569735860,0,true,58106496,58106560⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453519692,0,false,-58109632,-58109568⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581403603,0,true,69773568,69773632⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441851949,0,false,-69778048,-69777984⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623347,0,false,-4480,-4416⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624706,0,false,-3072,-3008⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281690554327,0,true,168570355904,168570355968⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917332701225,0,false,-199177811392,-199177811328⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281815873108,0,true,168677856704,168677856768⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917207382444,0,false,-199328028288,-199328028224⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069284718822,0,false,-30650171584,-30650171520⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069326261437,0,false,-30607455424,-30607455360⟩
    { al := (169731/1024000), au := (1358697/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨182247273529,182361224381⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168628986496,168628986560⟩ : DyadicInterval 40),(⟨-199259734848,-199259734784⟩ : DyadicInterval 40),(⟨746949441046,746949460376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168726730880,168726730944⟩ : DyadicInterval 40),(⟨-199396334592,-199396334528⟩ : DyadicInterval 40),(⟨746930371400,746930390730⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168511729472,168511729536⟩ : DyadicInterval 40),(⟨-199095904192,-199095904128⟩ : DyadicInterval 40),(⟨746972299300,746972318629⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168628965184,168628965248⟩ : DyadicInterval 40),(⟨-199259705024,-199259704960⟩ : DyadicInterval 40),(⟨746949445196,746949464526⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨58108084,69775827⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58106496,58106560⟩ : DyadicInterval 40),(⟨-58109632,-58109568⟩ : DyadicInterval 40),(⟨762123382048,762123401378⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69773568,69773632⟩ : DyadicInterval 40),(⟨-69778048,-69777984⟩ : DyadicInterval 40),(⟨762123381363,762123400693⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4480,-3008⟩ : DyadicInterval 40),(⟨762123385120,762123405120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182178926551,182304245332⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168570355904,168570355968⟩ : DyadicInterval 40),(⟨-199177811392,-199177811328⟩ : DyadicInterval 40),(⟨746960873073,746960892403⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168677856704,168677856768⟩ : DyadicInterval 40),(⟨-199328028288,-199328028224⟩ : DyadicInterval 40),(⟨746939908339,746939927669⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30650171584,-30607455360⟩ : DyadicInterval 40),(⟨777427111296,777448488672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168628986496,168726730944⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199396334592,-199259734784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2752_ok : ecellOkT e2752 = true := by decide +kernel
theorem e2752_pos {a z : ℝ} (ha1 : ((169731/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1358697/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2752 e2752_ok ha1 ha2 hz1 hz2 hz

-- box ['1358697/8192000', '679773/4096000', '3997/4000', '1599/1600']  interval_lower 2252439/8589934592
noncomputable def e2753 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281872852156,0,true,168726730880,168726730944⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917150403396,0,false,-199396334592,-199396334528⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281986803008,0,true,168824466560,168824466624⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917036452544,0,false,-199532951296,-199532951232⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281736081237,0,true,168609410944,168609411008⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917287174315,0,false,-199232381120,-199232381056⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281872756024,0,true,168726648448,168726648512⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917150499528,0,false,-199396219392,-199396219328⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569773677,0,true,58144320,58144384⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453481875,0,false,-58147456,-58147392⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581448986,0,true,69818944,69819008⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441806566,0,false,-69823488,-69823424⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623342,0,false,-4480,-4416⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624702,0,false,-3136,-3072⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281804462445,0,true,168668068864,168668068928⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917218793107,0,false,-199314349696,-199314349632⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281929788348,0,true,168775566144,168775566208⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917093467204,0,false,-199464593792,-199464593728⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069246931645,0,false,-30689027584,-30689027520⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069288502589,0,false,-30646280832,-30646280768⟩
    { al := (1358697/8192000), au := (679773/4096000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨182361224380,182475175232⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168726730880,168726730944⟩ : DyadicInterval 40),(⟨-199396334592,-199396334528⟩ : DyadicInterval 40),(⟨746930371400,746930390730⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168824466560,168824466624⟩ : DyadicInterval 40),(⟨-199532951296,-199532951232⟩ : DyadicInterval 40),(⟨746911289614,746911308944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168609410944,168609411008⟩ : DyadicInterval 40),(⟨-199232381120,-199232381056⟩ : DyadicInterval 40),(⟨746953258520,746953277850⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168726648448,168726648512⟩ : DyadicInterval 40),(⟨-199396219392,-199396219328⟩ : DyadicInterval 40),(⟨746930387498,746930406828⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨58145901,69821210⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58144320,58144384⟩ : DyadicInterval 40),(⟨-58147456,-58147392⟩ : DyadicInterval 40),(⟨762123382044,762123401374⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69818944,69819008⟩ : DyadicInterval 40),(⟨-69823488,-69823424⟩ : DyadicInterval 40),(⟨762123381390,762123400719⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4480,-3072⟩ : DyadicInterval 40),(⟨762123385152,762123405120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182292834669,182418160572⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168668068864,168668068928⟩ : DyadicInterval 40),(⟨-199314349696,-199314349632⟩ : DyadicInterval 40),(⟨746941817835,746941837165⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168775566144,168775566208⟩ : DyadicInterval 40),(⟨-199464593792,-199464593728⟩ : DyadicInterval 40),(⟨746920838605,746920857935⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30689027584,-30646280768⟩ : DyadicInterval 40),(⟨777446524000,777467916672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168726730880,168824466624⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199532951296,-199396334528⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2753_ok : ecellOkT e2753 = true := by decide +kernel
theorem e2753_pos {a z : ℝ} (ha1 : ((1358697/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((679773/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2753 e2753_ok ha1 ha2 hz1 hz2 hz

-- box ['169731/1024000', '1358697/8192000', '1599/1600', '1999/2000']  interval_lower 286758865/1099511627776
noncomputable def e2754 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281758901305,0,true,168628986496,168628986560⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917264354247,0,false,-199259734848,-199259734784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281872852157,0,true,168726730880,168726730944⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917150403395,0,false,-199396334592,-199396334528⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281644996758,0,true,168531273216,168531273280⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917378258794,0,false,-199123207616,-199123207552⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281781671545,0,true,168648518976,168648519040⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917241584007,0,false,-199287029568,-199287029504⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558114311,0,true,46485504,46485568⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465141241,0,false,-46487552,-46487488⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569774489,0,true,58145152,58145216⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453481063,0,false,-58148288,-58148224⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624700,0,false,-3136,-3072⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625811,0,false,-1984,-1920⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281701944626,0,true,168580127168,168580127232⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917321310926,0,false,-199191463872,-199191463808⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281827270553,0,true,168687633088,168687633152⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917195984999,0,false,-199341691200,-199341691136⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069280939203,0,false,-30654058048,-30654057984⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069322486784,0,false,-30611336640,-30611336576⟩
    { al := (169731/1024000), au := (1358697/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨182247273529,182361224381⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168628986496,168628986560⟩ : DyadicInterval 40),(⟨-199259734848,-199259734784⟩ : DyadicInterval 40),(⟨746949441046,746949460376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168726730880,168726730944⟩ : DyadicInterval 40),(⟨-199396334592,-199396334528⟩ : DyadicInterval 40),(⟨746930371400,746930390730⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168531273216,168531273280⟩ : DyadicInterval 40),(⟨-199123207616,-199123207552⟩ : DyadicInterval 40),(⟨746968490786,746968510115⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168648518976,168648519040⟩ : DyadicInterval 40),(⟨-199287029568,-199287029504⟩ : DyadicInterval 40),(⟨746945631429,746945650759⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨46486535,58146713⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46485504,46485568⟩ : DyadicInterval 40),(⟨-46487552,-46487488⟩ : DyadicInterval 40),(⟨762123382610,762123401939⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58145152,58145216⟩ : DyadicInterval 40),(⟨-58148288,-58148224⟩ : DyadicInterval 40),(⟨762123382044,762123401374⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3136,-1920⟩ : DyadicInterval 40),(⟨762123384576,762123404448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182190316850,182315642777⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168580127168,168580127232⟩ : DyadicInterval 40),(⟨-199191463872,-199191463808⟩ : DyadicInterval 40),(⟨746958968183,746958987512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168687633088,168687633152⟩ : DyadicInterval 40),(⟨-199341691200,-199341691136⟩ : DyadicInterval 40),(⟨746938000950,746938020279⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30654058048,-30611336576⟩ : DyadicInterval 40),(⟨777429051904,777450431904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168628986496,168726730944⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199396334592,-199259734784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2754_ok : ecellOkT e2754 = true := by decide +kernel
theorem e2754_pos {a z : ℝ} (ha1 : ((169731/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1358697/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2754 e2754_ok ha1 ha2 hz1 hz2 hz

-- box ['1358697/8192000', '679773/4096000', '1599/1600', '1999/2000']  interval_lower 9003675/34359738368
noncomputable def e2755 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281872852156,0,true,168726730880,168726730944⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917150403396,0,false,-199396334592,-199396334528⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1281986803008,0,true,168824466560,168824466624⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨917036452544,0,false,-199532951296,-199532951232⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281758876390,0,true,168628965120,168628965184⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917264379162,0,false,-199259705024,-199259704960⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281895565421,0,true,168746212736,168746212800⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917127690131,0,false,-199423564416,-199423564352⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558144564,0,true,46515776,46515840⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465110988,0,false,-46517824,-46517760⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569812309,0,true,58182976,58183040⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453443243,0,false,-58186112,-58186048⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624696,0,false,-3136,-3072⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625809,0,false,-1984,-1920⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281815859863,0,true,168677845312,168677845376⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917207395689,0,false,-199328012416,-199328012352⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1281941192916,0,true,168785347840,168785347904⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨917082062636,0,false,-199478266944,-199478266880⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069243147301,0,false,-30692919040,-30692918976⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069284723215,0,false,-30650167040,-30650166976⟩
    { al := (1358697/8192000), au := (679773/4096000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨182361224380,182475175232⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168726730880,168726730944⟩ : DyadicInterval 40),(⟨-199396334592,-199396334528⟩ : DyadicInterval 40),(⟨746930371400,746930390730⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168824466560,168824466624⟩ : DyadicInterval 40),(⟨-199532951296,-199532951232⟩ : DyadicInterval 40),(⟨746911289614,746911308944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168628965120,168628965184⟩ : DyadicInterval 40),(⟨-199259705024,-199259704960⟩ : DyadicInterval 40),(⟨746949445234,746949464563⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168746212736,168746212800⟩ : DyadicInterval 40),(⟨-199423564416,-199423564352⟩ : DyadicInterval 40),(⟨746926568914,746926588244⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨46516788,58184533⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46515776,46515840⟩ : DyadicInterval 40),(⟨-46517824,-46517760⟩ : DyadicInterval 40),(⟨762123382607,762123401937⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58182976,58183040⟩ : DyadicInterval 40),(⟨-58186112,-58186048⟩ : DyadicInterval 40),(⟨762123382040,762123401370⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3136,-1920⟩ : DyadicInterval 40),(⟨762123384576,762123404448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182304232087,182429565140⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168677845312,168677845376⟩ : DyadicInterval 40),(⟨-199328012416,-199328012352⟩ : DyadicInterval 40),(⟨746939910576,746939929906⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168785347840,168785347904⟩ : DyadicInterval 40),(⟨-199478266944,-199478266880⟩ : DyadicInterval 40),(⟨746918928768,746918948098⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30692919040,-30650166976⟩ : DyadicInterval 40),(⟨777448467104,777469862400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168726730880,168824466624⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199532951296,-199396334528⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2755_ok : ecellOkT e2755 = true := by decide +kernel
theorem e2755_pos {a z : ℝ} (ha1 : ((1358697/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((679773/4096000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2755 e2755_ok ha1 ha2 hz1 hz2 hz

-- box ['679773/4096000', '272079/1638400', '3997/4000', '1599/1600']  interval_lower 72418611/274877906944
noncomputable def e2756 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281986803007,0,true,168824466560,168824466624⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917036452545,0,false,-199532951296,-199532951232⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282100753859,0,true,168922193600,168922193664⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916922501693,0,false,-199669585024,-199669584960⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281849946625,0,true,168707083776,168707083840⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917173308927,0,false,-199368875008,-199368874944⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1281986635656,0,true,168824323072,168824323136⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917036619896,0,false,-199532750656,-199532750592⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569811496,0,true,58182144,58182208⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453444056,0,false,-58185280,-58185216⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581494372,0,true,69864320,69864384⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441761180,0,false,-69868864,-69868800⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623336,0,false,-4480,-4416⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624698,0,false,-3136,-3072⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281918370565,0,true,168765773120,168765773184⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917104884987,0,false,-199450905024,-199450904960⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282043703594,0,true,168873267008,168873267072⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916979551958,0,false,-199601176320,-199601176256⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069209120862,0,false,-30727909312,-30727909248⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069250720139,0,false,-30685131904,-30685131840⟩
    { al := (679773/4096000), au := (272079/1638400), zl := (3997/4000), zu := (1599/1600),
      A := ⟨182475175231,182589126083⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168824466560,168824466624⟩ : DyadicInterval 40),(⟨-199532951296,-199532951232⟩ : DyadicInterval 40),(⟨746911289614,746911308944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168922193600,168922193664⟩ : DyadicInterval 40),(⟨-199669585024,-199669584960⟩ : DyadicInterval 40),(⟨746892195677,746892215006⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168707083776,168707083840⟩ : DyadicInterval 40),(⟨-199368875008,-199368874944⟩ : DyadicInterval 40),(⟨746934205601,746934224931⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168824323072,168824323136⟩ : DyadicInterval 40),(⟨-199532750656,-199532750592⟩ : DyadicInterval 40),(⟨746911317627,746911336957⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨58183720,69866596⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58182144,58182208⟩ : DyadicInterval 40),(⟨-58185280,-58185216⟩ : DyadicInterval 40),(⟨762123382040,762123401370⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69864320,69864384⟩ : DyadicInterval 40),(⟨-69868864,-69868800⟩ : DyadicInterval 40),(⟨762123381384,762123400713⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4480,-3072⟩ : DyadicInterval 40),(⟨762123385152,762123405120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182406742789,182532075818⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168765773120,168765773184⟩ : DyadicInterval 40),(⟨-199450905024,-199450904960⟩ : DyadicInterval 40),(⟨746922750503,746922769832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168873267008,168873267072⟩ : DyadicInterval 40),(⟨-199601176320,-199601176256⟩ : DyadicInterval 40),(⟨746901756696,746901776026⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30727909312,-30685131840⟩ : DyadicInterval 40),(⟨777465949536,777487357536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168824466560,168922193664⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199669585024,-199532951232⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2756_ok : ecellOkT e2756 = true := by decide +kernel
theorem e2756_pos {a z : ℝ} (ha1 : ((679773/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((272079/1638400 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2756 e2756_ok ha1 ha2 hz1 hz2 hz

-- box ['272079/1638400', '340311/2048000', '3997/4000', '1599/1600']  interval_lower 291039753/1099511627776
noncomputable def e2757 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282100753858,0,true,168922193600,168922193664⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916922501694,0,false,-199669585024,-199669584960⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282214704710,0,true,169019911872,169019911936⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916808550842,0,false,-199806235648,-199806235584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281963812013,0,true,168804747904,168804747968⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917059443539,0,false,-199505385856,-199505385792⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282100515287,0,true,168921988992,168921989056⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916922740265,0,false,-199669298944,-199669298880⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569849317,0,true,58219968,58220032⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453406235,0,false,-58223104,-58223040⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099581539761,0,true,69909760,69909824⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099441715791,0,false,-69914240,-69914176⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623330,0,false,-4480,-4416⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624694,0,false,-3136,-3072⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282032278682,0,true,168863468672,168863468736⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916990976870,0,false,-199587477248,-199587477184⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282157618833,0,true,168970959104,168970959168⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916865636719,0,false,-199737775744,-199737775680⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069171286476,0,false,-30766816640,-30766816576⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069212914088,0,false,-30724008576,-30724008512⟩
    { al := (272079/1638400), au := (340311/2048000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨182589126082,182703076934⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168922193600,168922193664⟩ : DyadicInterval 40),(⟨-199669585024,-199669584960⟩ : DyadicInterval 40),(⟨746892195677,746892215007⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169019911872,169019911936⟩ : DyadicInterval 40),(⟨-199806235648,-199806235584⟩ : DyadicInterval 40),(⟨746873089607,746873108937⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168804747904,168804747968⟩ : DyadicInterval 40),(⟨-199505385856,-199505385792⟩ : DyadicInterval 40),(⟨746915140579,746915159908⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168921988992,168921989056⟩ : DyadicInterval 40),(⟨-199669298944,-199669298880⟩ : DyadicInterval 40),(⟨746892235672,746892255001⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨58221541,69911985⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58219968,58220032⟩ : DyadicInterval 40),(⟨-58223104,-58223040⟩ : DyadicInterval 40),(⟨762123382036,762123401366⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨69909760,69909824⟩ : DyadicInterval 40),(⟨-69914240,-69914176⟩ : DyadicInterval 40),(⟨762123381346,762123400675⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4480,-3072⟩ : DyadicInterval 40),(⟨762123385152,762123405120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182520650906,182645991057⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168863468672,168863468736⟩ : DyadicInterval 40),(⟨-199587477248,-199587477184⟩ : DyadicInterval 40),(⟨746903671022,746903690351⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168970959104,168970959168⟩ : DyadicInterval 40),(⟨-199737775744,-199737775680⟩ : DyadicInterval 40),(⟨746882662673,746882682003⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30766816640,-30724008512⟩ : DyadicInterval 40),(⟨777485387872,777506811200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168922193600,169019911936⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199806235648,-199669584960⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2757_ok : ecellOkT e2757 = true := by decide +kernel
theorem e2757_pos {a z : ℝ} (ha1 : ((272079/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((340311/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2757 e2757_ok ha1 ha2 hz1 hz2 hz

-- box ['679773/4096000', '272079/1638400', '1599/1600', '1999/2000']  interval_lower 289479531/1099511627776
noncomputable def e2758 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1281986803007,0,true,168824466560,168824466624⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨917036452545,0,false,-199532951296,-199532951232⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282100753859,0,true,168922193600,168922193664⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916922501693,0,false,-199669585024,-199669584960⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281872756022,0,true,168726648448,168726648512⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917150499530,0,false,-199396219392,-199396219328⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282009459297,0,true,168843897856,168843897920⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨917013796255,0,false,-199560116160,-199560116096⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558174819,0,true,46546048,46546112⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465080733,0,false,-46548032,-46547968⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569850131,0,true,58220800,58220864⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453405421,0,false,-58223936,-58223872⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624692,0,false,-3136,-3072⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625806,0,false,-1984,-1920⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1281929775104,0,true,168775554816,168775554880⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨917093480448,0,false,-199464577920,-199464577856⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282055115285,0,true,168883053888,168883053952⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916968140267,0,false,-199614859648,-199614859584⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069205331789,0,false,-30731805760,-30731805696⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069246936041,0,false,-30689023104,-30689023040⟩
    { al := (679773/4096000), au := (272079/1638400), zl := (1599/1600), zu := (1999/2000),
      A := ⟨182475175231,182589126083⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168824466560,168824466624⟩ : DyadicInterval 40),(⟨-199532951296,-199532951232⟩ : DyadicInterval 40),(⟨746911289614,746911308944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168922193600,168922193664⟩ : DyadicInterval 40),(⟨-199669585024,-199669584960⟩ : DyadicInterval 40),(⟨746892195677,746892215006⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168726648448,168726648512⟩ : DyadicInterval 40),(⟨-199396219392,-199396219328⟩ : DyadicInterval 40),(⟨746930387499,746930406828⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168843897856,168843897920⟩ : DyadicInterval 40),(⟨-199560116160,-199560116096⟩ : DyadicInterval 40),(⟨746907494219,746907513549⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨46547043,58222355⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46546048,46546112⟩ : DyadicInterval 40),(⟨-46548032,-46547968⟩ : DyadicInterval 40),(⟨762123382573,762123401902⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58220800,58220864⟩ : DyadicInterval 40),(⟨-58223936,-58223872⟩ : DyadicInterval 40),(⟨762123382036,762123401366⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3136,-1920⟩ : DyadicInterval 40),(⟨762123384576,762123404448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182418147328,182543487509⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168775554816,168775554880⟩ : DyadicInterval 40),(⟨-199464577920,-199464577856⟩ : DyadicInterval 40),(⟨746920840807,746920860137⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168883053888,168883053952⟩ : DyadicInterval 40),(⟨-199614859648,-199614859584⟩ : DyadicInterval 40),(⟨746899844457,746899863786⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30731805760,-30689023040⟩ : DyadicInterval 40),(⟨777467895136,777489305760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168824466560,168922193664⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199669585024,-199532951232⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2758_ok : ecellOkT e2758 = true := by decide +kernel
theorem e2758_pos {a z : ℝ} (ha1 : ((679773/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((272079/1638400 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2758 e2758_ok ha1 ha2 hz1 hz2 hz

-- box ['272079/1638400', '340311/2048000', '1599/1600', '1999/2000']  interval_lower 290844451/1099511627776
noncomputable def e2759 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1282100753858,0,true,168922193600,168922193664⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨916922501694,0,false,-199669585024,-199669584960⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1282214704710,0,true,169019911872,169019911936⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨916808550842,0,false,-199806235648,-199806235584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1281986635654,0,true,168824323072,168824323136⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨917036619898,0,false,-199532750656,-199532750592⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1282123353172,0,true,168941574272,168941574336⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨916899902380,0,false,-199696684928,-199696684864⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558205076,0,true,46576256,46576320⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099465050476,0,false,-46578304,-46578240⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569887956,0,true,58258624,58258688⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453367596,0,false,-58261760,-58261696⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624688,0,false,-3136,-3072⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625803,0,false,-1984,-1920⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1282043690349,0,true,168873255616,168873255680⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨916979565203,0,false,-199601160448,-199601160384⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1282169037647,0,true,168980751232,168980751296⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨916854217905,0,false,-199751469376,-199751469312⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1069167492672,0,false,-30770718080,-30770718016⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1069209125260,0,false,-30727904768,-30727904704⟩
    { al := (272079/1638400), au := (340311/2048000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨182589126082,182703076934⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168922193600,168922193664⟩ : DyadicInterval 40),(⟨-199669585024,-199669584960⟩ : DyadicInterval 40),(⟨746892195677,746892215007⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨169019911872,169019911936⟩ : DyadicInterval 40),(⟨-199806235648,-199806235584⟩ : DyadicInterval 40),(⟨746873089607,746873108937⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168824323072,168824323136⟩ : DyadicInterval 40),(⟨-199532750656,-199532750592⟩ : DyadicInterval 40),(⟨746911317628,746911336957⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168941574272,168941574336⟩ : DyadicInterval 40),(⟨-199696684928,-199696684864⟩ : DyadicInterval 40),(⟨746888407434,746888426763⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨46577300,58260180⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46576256,46576320⟩ : DyadicInterval 40),(⟨-46578304,-46578240⟩ : DyadicInterval 40),(⟨762123382602,762123401931⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58258624,58258688⟩ : DyadicInterval 40),(⟨-58261760,-58261696⟩ : DyadicInterval 40),(⟨762123382032,762123401362⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3136,-1920⟩ : DyadicInterval 40),(⟨762123384576,762123404448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨182532062573,182657409871⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168873255616,168873255680⟩ : DyadicInterval 40),(⟨-199601160448,-199601160384⟩ : DyadicInterval 40),(⟨746901758939,746901778269⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨168980751232,168980751296⟩ : DyadicInterval 40),(⟨-199751469376,-199751469312⟩ : DyadicInterval 40),(⟨746880748043,746880767373⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-30770718080,-30727904704⟩ : DyadicInterval 40),(⟨777487335968,777508761920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨168922193600,169019911936⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-199806235648,-199669584960⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2759_ok : ecellOkT e2759 = true := by decide +kernel
theorem e2759_pos {a z : ℝ} (ha1 : ((272079/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((340311/2048000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2759 e2759_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B045

end


