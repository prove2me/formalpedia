-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryGroupBankStep
-- name    : Submission_ThreeSum_LightTernaryGroupBankStep
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:01:06.942191+00:00
-- url     : https://prove2.me/theorems/e7bdf1ca-8b18-4c6e-a667-39990a4b8c9c
-- title:
--   Light Ternary Group Bank Step
-- statement:
--   Definitions and structural lemmas for Light Ternary Group Bank Step, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryGroupBankStep.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryBankResources
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightTernaryGroupBankStep
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.LightTernaryBankSweep
set_option maxHeartbeats 5000000
variable {lim : Limits}
def body (pCopy : ℕ) : Stmt :=
  .call pCopy [v 6,v 8,v 2] 11 ;;
  .call pCopy [v 7,v 9,v 2] 11 ;;
  .call 0 [v 0,v 1,v 2,v 3,v 4,v 5,v 8,v 9,v 10] 11
def time (N L n : ℕ) : ℕ :=2*copyTime n+LightTernaryBankAssembly.time N L n+200
def Preserved (μ μ' : ℕ→ℤ) (keyBase n fbase gbase hbase N : ℕ) : Prop :=
  ∀ x, (x<keyBase ∨ keyBase+4*n≤x) →
    (x<fbase ∨ fbase+(N+1)*n≤x) →
    (x<gbase ∨ gbase+(N+1)*n≤x) →
    (x<hbase ∨ hbase+(N+1)*n≤x) → μ' x=μ x
def program : Program :=LightTernaryBankAssembly.program++[body 18,copyBody]
end ThreeSum.LightTernaryGroupBankStep


