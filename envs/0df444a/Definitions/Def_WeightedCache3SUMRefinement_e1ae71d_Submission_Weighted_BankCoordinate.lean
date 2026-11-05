-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankCoordinate
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankCoordinate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:10:25.139262+00:00
-- url     : https://prove2.me/theorems/2c29d17a-b665-47b8-9824-147d74d3dce4
-- title:
--   BankCoordinate
-- statement:
--   Definitions and structural lemmas for BankCoordinate, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/BankCoordinate.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankStageModel
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
namespace ThreeSum.LightWeightedBankCoordinate
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryQuery
set_option maxHeartbeats 5000000
variable {lim : Limits} {P : Program}
def body (pMeta pPass : ℕ) : Stmt :=
  .call pMeta [k 2 *' v 0,v 1,v 2,v 3,v 4,v 5,v 7] 10 ;;
  .call pPass [v 3,v 4,v 5,v 6,v 7,v 8,v 9] 0
def time (N L n : ℕ) : ℕ :=LightTernaryMetadata.time (2*N) n+LightTernaryPass.time L n+100
def Preserved (μ μ' : ℕ→ℤ) (keyBase n dst : ℕ) : Prop :=
  ∀ x, (x<keyBase ∨ keyBase+4*n≤x) → (x<dst ∨ dst+n≤x) → μ' x=μ x
end ThreeSum.LightWeightedBankCoordinate
end WeightedCache3SUMRefinement_e1ae71d


