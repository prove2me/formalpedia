-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTimeMonotone
-- name    : Submission_Weighted_Global_TernaryArenaQueryTimeMonotone
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T17:35:33.754579+00:00
-- url     : https://prove2.me/theorems/8c01b6a4-9283-4d69-84df-ca73aa7f812c
-- title:
--   Ternary Arena Query Time Monotone
-- statement:
--   Definitions and structural lemmas for Ternary Arena Query Time Monotone, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaQueryTimeMonotone.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPostSelection
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaQueryTimeMonotone
open WeightedGlobalArenaSourceSetup WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters TernaryJointType
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
end ThreeSum.WeightedGlobalArenaQueryTimeMonotone


