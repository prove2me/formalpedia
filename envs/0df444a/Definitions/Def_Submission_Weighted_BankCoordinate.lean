-- Prove2me | Definitions.Def_Submission_Weighted_BankCoordinate
-- name    : Submission_Weighted_BankCoordinate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:44:13.653204+00:00
-- url     : https://prove2.me/theorems/00cd58ad-8e86-4adf-8dba-7eefcef9f7e6
-- title:
--   Bank Coordinate
-- statement:
--   Definitions and structural lemmas for Bank Coordinate, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankCoordinate.lean

import Definitions.Def_Submission_Weighted_BankStageModel
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
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


