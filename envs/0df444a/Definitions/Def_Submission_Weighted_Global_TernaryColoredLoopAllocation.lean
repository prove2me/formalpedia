-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopAllocation
-- name    : Submission_Weighted_Global_TernaryColoredLoopAllocation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T02:06:03.874469+00:00
-- url     : https://prove2.me/theorems/25394d2d-436c-4fee-a9c5-a1ce664181e0
-- title:
--   Ternary Colored Loop Allocation
-- statement:
--   Definitions and structural lemmas for Ternary Colored Loop Allocation, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopAllocation.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopSetup
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalColoredLoopAllocation
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters WeightedGlobalColoredLoopSetup
open WeightedGlobalArenaPrefixFootprints
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {κ : ℕ}
end ThreeSum.WeightedGlobalColoredLoopAllocation


