-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryColoredExecution
-- name    : Submission_Weighted_Global_TernaryColoredExecution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T04:31:34.266421+00:00
-- url     : https://prove2.me/theorems/fcaa1943-bcf7-4894-a3a3-16cfa62725bc
-- title:
--   Ternary Colored Execution
-- statement:
--   Definitions and structural lemmas for Ternary Colored Execution, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredExecution.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredNonemptyExecution
import Definitions.Def_Submission_Weighted_Global_TernaryProfilePreparation
import Definitions.Def_Submission_Weighted_Global_TernaryColoredExecutionTime
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalColoredExecution
open Light WeightedGlobalConcreteProfile WeightedGlobalColoredLoopSetup LightWeightedGlobalFastProgramProof
open WeightedGlobalLocalParameters LightWeightedGlobalColoredSolver
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {κ : ℕ}
end ThreeSum.WeightedGlobalColoredExecution


