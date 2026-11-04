-- Prove2me | Definitions.Def_Submission_ThreeSum_BudgetTime
-- name    : Submission_ThreeSum_BudgetTime
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:18:26.649915+00:00
-- url     : https://prove2.me/theorems/18005d56-7f4b-4cf7-a84f-87dc939116ae
-- title:
--   Budget Time
-- statement:
--   Definitions and structural lemmas for Budget Time, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BudgetTime.lean

import Definitions.Def_Submission_ThreeSum_UniformStageBounds
import Definitions.Def_Submission_EndStatement
set_option autoImplicit false
namespace ThreeSum.BudgetTime
open Filter Real ThreeSum.Parameters ThreeSum.StageBounds
  ThreeSum.UniformStageBounds
open scoped Topology
set_option maxHeartbeats 400000
def compiledBudget (a b C k n : ℕ) : ℕ := a * workBudget C k n + b
end ThreeSum.BudgetTime


