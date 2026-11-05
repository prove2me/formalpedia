-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GroupBankStep
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GroupBankStep
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:14:18.029204+00:00
-- url     : https://prove2.me/theorems/6342867a-3a70-447c-94c0-41ced6a351be
-- title:
--   GroupBankStep
-- statement:
--   Definitions and structural lemmas for GroupBankStep, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/GroupBankStep.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankResources
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
namespace ThreeSum.LightWeightedGroupBankStep
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.LightWeightedBankSweep
set_option maxHeartbeats 5000000
variable {lim : Limits}
def body (pCopy : ℕ) : Stmt :=
  .call pCopy [v 6,v 8,v 2] 11 ;;
  .call pCopy [v 7,v 9,v 2] 11 ;;
  .call 0 [v 0,v 1,v 2,v 3,v 4,v 5,v 8,v 9,v 10] 11
def time (N L n : ℕ) : ℕ :=2*copyTime n+LightWeightedBankAssembly.time N L n+200
def Preserved (μ μ' : ℕ→ℤ) (keyBase n fbase gbase hbase N : ℕ) : Prop :=
  ∀ x, (x<keyBase ∨ keyBase+4*n≤x) →
    (x<fbase ∨ fbase+(N+1)*n≤x) →
    (x<gbase ∨ gbase+(N+1)*n≤x) →
    (x<hbase ∨ hbase+(N+1)*n≤x) → μ' x=μ x
def program : Program :=LightWeightedBankAssembly.program++[body 18,copyBody]
end ThreeSum.LightWeightedGroupBankStep
end WeightedCache3SUMRefinement_e1ae71d


