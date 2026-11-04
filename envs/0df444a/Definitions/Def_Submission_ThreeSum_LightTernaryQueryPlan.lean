-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryQueryPlan
-- name    : Submission_ThreeSum_LightTernaryQueryPlan
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:21:29.437498+00:00
-- url     : https://prove2.me/theorems/42200d94-c699-4789-997c-49334c979a94
-- title:
--   Light Ternary Query Plan
-- statement:
--   Definitions and structural lemmas for Light Ternary Query Plan, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryQueryPlan.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryWantedQuery
import Definitions.Def_Submission_ThreeSum_LightTernaryNearSetup
set_option autoImplicit false
namespace ThreeSum.LightTernaryQueryPlan
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryCodeSemantics ThreeSum.LightTernaryNearPair
structure Resources (lim : Limits) {N : ℕ} (rows : ℕ) (c : Config)
    (source : TritWord N→ℤ) : Prop where
  homogeneous : ∀ A, source A≠0 → rank A=c.h
  division : ∀ current, c.T<current → current≤2*N → Light.Emod.Pre lim (current-c.h) c.V c.fr
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
  hword : ((c.nb+rows+2^(2*N+1)+2*N+32 : ℕ) : ℤ)≤lim.word
  hcontrols : ((c.T+N+32 : ℕ) : ℤ)≤lim.word
  hmemoWord : ((N+rows+2*N+c.h+20 : ℕ) : ℤ)≤lim.word
  hL : c.L≤2*N
  hnb : c.nb<2^c.L
  hnn : rows<2^c.L
  hnbpos : 0<c.nb
  hT : c.T≤2*N
  hh : c.h≤c.T
  hvalue : ∀ R, |binomialZeta source R|≤c.U
  hV : 2*(N+1)*c.U≤c.V
end ThreeSum.LightTernaryQueryPlan


