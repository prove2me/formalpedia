-- Prove2me | Definitions.Def_Submission_Weighted_QueryPlan
-- name    : Submission_Weighted_QueryPlan
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:21:26.544836+00:00
-- url     : https://prove2.me/theorems/66a1178c-f90b-4463-b8ee-b969e30d5279
-- title:
--   Query Plan
-- statement:
--   Definitions and structural lemmas for Query Plan, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/QueryPlan.lean

import Definitions.Def_Submission_Weighted_WantedQuery
import Definitions.Def_Submission_Weighted_NearSetup
set_option autoImplicit false
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
  hword : ((c.nb+rows+2^(2*N+1)+1025*N+1100 : ℕ) : ℤ)≤lim.word
  hcontrols : ((c.T+N+32 : ℕ) : ℤ)≤lim.word
  hmemoWord : ((N+rows+2*N+c.h+20 : ℕ) : ℤ)≤lim.word
  hL : c.L≤2*N
  hnb : c.nb<2^c.L
  hnn : rows<2^c.L
  hnbpos : 0<c.nb
  hT : c.h≤2*N
  hh : 1025*c.h≤2*c.T
  hvalue : ∀ R, |binomialZeta source R|≤c.U
  hV : 2*(N+1)*c.U≤c.V
end ThreeSum.LightWeightedQueryPlan


