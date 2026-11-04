-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopReady
-- name    : Submission_Weighted_Global_TernaryColoredLoopReady
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T02:19:52.402743+00:00
-- url     : https://prove2.me/theorems/72ae8faa-1b9f-4ae1-94f6-361e6d9f1245
-- title:
--   Ternary Colored Loop Ready
-- statement:
--   Definitions and structural lemmas for Ternary Colored Loop Ready, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopReady.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLoop
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalColoredLoopSetup
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters WeightedGlobalArenaSelectedSigned
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
variable {κ : ℕ}
end ThreeSum.WeightedGlobalColoredLoopSetup


