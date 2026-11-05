-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_WantedRowDispatch
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_WantedRowDispatch
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:59:03.926605+00:00
-- url     : https://prove2.me/theorems/797935ed-87e5-4425-8ae4-f9d4335f6dbd
-- title:
--   WantedRowDispatch
-- statement:
--   Definitions and structural lemmas for WantedRowDispatch, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/WantedRowDispatch.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_PreparedWanted
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.LightWeightedWantedRowDispatch
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.WeightedBankStageModel
open ThreeSum.LightWeightedNearPair
set_option maxHeartbeats 6000000
set_option maxRecDepth 16000
variable {lim : Limits} {P : Program}
def sourceConfig (c : Config) (base stride tail group : ℕ) : Config :=
  {c with bv:=base+group*stride+tail}
def body (pPrepare : ℕ) : Stmt :=
  .set 46 (M (v 39 +' k 2)) ;;
  .set 47 (M (v 39 +' k 1)) ;;
  .call pPrepare [v 0,v 1,v 2,v 3,v 4,v 5,
    v 41 +' v 46 *' v 44 +' v 45,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 16,
    v 17,v 18,v 19,v 20,v 21,v 22,v 42 +' v 46 *' v 44 +' v 45,v 24,v 25,v 26,v 27,v 28,v 29,v 30,v 31,v 32,v 33,v 34,
    v 47,v 43 +' v 46 *' v 44,v 37,v 38] 48 ;;
  .store (v 40) (v 48)
def args {N : ℕ} (f g : Config) (Qstar : TritWord N)
    (out bankValues caps record dst fbase gbase hbase stride tail : ℕ) : List ℤ :=
  LightWeightedPreparedWanted.args out bankValues caps f g Qstar++
    [(record : ℤ),dst,fbase,gbase,hbase,stride,tail]
def time (t : ℕ) : ℕ :=t+500
end ThreeSum.LightWeightedWantedRowDispatch
end
end WeightedCache3SUMRefinement_e1ae71d


