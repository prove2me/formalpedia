-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTime
-- name    : Submission_Weighted_Global_TernaryArenaQueryTime
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T16:42:55.811093+00:00
-- url     : https://prove2.me/theorems/a252d4db-d19d-43ca-8675-6f0809709e6f
-- title:
--   Ternary Arena Query Time
-- statement:
--   Definitions and structural lemmas for Ternary Arena Query Time, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaQueryTime.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCountReady
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaQueryTime
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup LightWeightedNearPair WeightedGlobalCountFrontendBudget
set_option maxHeartbeats 5000000
variable {p m F r : ℕ} [Fact p.Prime]
attribute [local instance] Classical.propDecidable
end ThreeSum.WeightedGlobalArenaQueryTime


