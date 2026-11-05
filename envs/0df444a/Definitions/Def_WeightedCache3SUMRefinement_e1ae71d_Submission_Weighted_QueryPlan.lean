-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_QueryPlan
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_QueryPlan
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:48:13.152713+00:00
-- url     : https://prove2.me/theorems/26c4bd31-cac6-4264-a232-3b7c22aaaeca
-- title:
--   QueryPlan
-- statement:
--   Definitions and structural lemmas for QueryPlan, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/QueryPlan.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_WantedQuery
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearSetup
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
namespace ThreeSum.LightWeightedQueryPlan
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.TernaryEuler ThreeSum.TernaryCodeSemantics ThreeSum.LightWeightedNearPair
structure Resources (lim : Limits) {N : ℕ} (rows : ℕ) (c : Config)
    (source : TritWord N→ℤ) : Prop where
  homogeneous : ∀ A, source A≠0 → rank A=c.h
  division : ∀ current, c.h<current → current≤2*N → Light.Emod.Pre lim (current-c.h) c.V c.fr
  hw : (lim.space : ℤ)≤lim.word
  ha : c.a+rows≤c.ws
  hb : c.bank+c.nb≤c.ws
  hp : c.powers+(2*N+1)≤c.ws
  hactiveSpace : c.activeBase+N≤c.ws
  hbankVals : c.bv+c.nb≤c.ws
  hmetadataRanks : c.ws+2*N*rows+N≤c.rankBase
  hrankVals : c.rankBase+rows≤c.vals
  hvals : c.vals+rows≤c.fr
  hfr : c.fr≤lim.space
  hcount : c.vals+rows≤c.pcount
  hspace : c.pcount≤lim.space
  hword : ((c.nb+rows+2^(2*N+1)+2740*N+3000 : ℕ) : ℤ)≤lim.word
  hcontrols : ((c.T+N+32 : ℕ) : ℤ)≤lim.word
  hmemoWord : ((N+rows+2*N+c.h+20 : ℕ) : ℤ)≤lim.word
  hL : c.L≤2*N
  hnb : c.nb<2^c.L
  hnn : rows<2^c.L
  hnbpos : 0<c.nb
  hT : c.h≤2*N
  hh : 2740*c.h≤2*c.T
  hvalue : ∀ R, |binomialZeta source R|≤c.U
  hV : 2*(N+1)*c.U≤c.V
end ThreeSum.LightWeightedQueryPlan
end WeightedCache3SUMRefinement_e1ae71d


