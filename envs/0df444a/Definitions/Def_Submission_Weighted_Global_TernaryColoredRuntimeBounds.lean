-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryColoredRuntimeBounds
-- name    : Submission_Weighted_Global_TernaryColoredRuntimeBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T02:16:33.074321+00:00
-- url     : https://prove2.me/theorems/535c9d85-5014-4543-8676-90e3019e44dc
-- title:
--   Ternary Colored Runtime Bounds
-- statement:
--   Definitions and structural lemmas for Ternary Colored Runtime Bounds, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredRuntimeBounds.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryActualColoredRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryUniformQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedCollisions
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTimeMonotone
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalColoredRuntimeBounds
open WeightedGlobalConcreteProfile WeightedGlobalColoredLoopSetup WeightedGlobalArenaSourceSetup
open WeightedGlobalArenaSeedCandidate LightWeightedGlobalSeedScoreFactory WeightedGlobalLocalParameters
open WeightedGlobalActualColoredRuntime
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {κ : ℕ}
def zeroInput (I : Input) : Input := {I with queryTime:=0}
def coefficient (P : Profile κ) : ℕ :=256*(P.allocation.D+1)
end ThreeSum.WeightedGlobalColoredRuntimeBounds


