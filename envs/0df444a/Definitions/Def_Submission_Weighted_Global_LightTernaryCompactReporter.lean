-- Prove2me | Definitions.Def_Submission_Weighted_Global_LightTernaryCompactReporter
-- name    : Submission_Weighted_Global_LightTernaryCompactReporter
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T15:21:43.269207+00:00
-- url     : https://prove2.me/theorems/f385a1f8-4b87-4fa4-b824-dafb35c0482c
-- title:
--   Light Ternary Compact Reporter
-- statement:
--   Definitions and structural lemmas for Light Ternary Compact Reporter, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryCompactReporter.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryMomentReporter
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightWeightedGlobalCompactReporter
open Light TernaryMomentSchedule
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 500000
set_option maxRecDepth 24000
def body (pReporter : ℕ) : Stmt :=
  .set 12 (v 0) ;; .set 13 (M (v 2)) ;;
  .set 14 (v 3) ;; .set 15 (M (v 5)) ;;
  .set 31 (v 1) ;; .set 32 (M (v 2)) ;;
  .set 54 (v 4) ;; .set 55 (M (v 5)) ;;
  .call pReporter (LightWeightedSourceCountHost.callArgs 6 121) 0
def program {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (H : ℕ) : Program :=
  LightWeightedGlobalMomentReporter.program S H ++
    [body ((LightWeightedGlobalMomentReporter.driver S H).length+4)]
def zeroCounts {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) :
    WeightedSourceCountExecutionFactory.Setup N :=
  {S with left := {S.left with NL := 0}, right := {S.right with NL := 0}}
def args {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (originalA originalCount scratch valueB packedB lengthB valueC packedC lengthC matrix : ℕ) : List ℤ :=
  [(valueB : ℤ),packedB,lengthB,valueC,packedC,lengthC] ++
    LightWeightedGlobalMomentReporter.args (zeroCounts S) originalA originalCount scratch valueB valueC matrix
def time {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (H : ℕ) : ℕ :=
  LightWeightedGlobalMomentReporter.time S H+200
variable {lim : Limits}
end ThreeSum.LightWeightedGlobalCompactReporter


