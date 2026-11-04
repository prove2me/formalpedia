-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaFinalBounds
-- name    : Submission_Weighted_Global_TernaryArenaFinalBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:10:42.299556+00:00
-- url     : https://prove2.me/theorems/06b766c6-65ce-44d5-8099-15716a1a8ce2
-- title:
--   Ternary Arena Final Bounds
-- statement:
--   Definitions and structural lemmas for Ternary Arena Final Bounds, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFinalBounds.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFrontBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaArgumentBudget
import Definitions.Def_Submission_Weighted_Global_TernaryArenaAllocationResources
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaFinalBounds
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaPrefixFootprints
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters
set_option maxHeartbeats 8000000
variable {p m F r : ℕ} [Fact p.Prime]
end ThreeSum.WeightedGlobalArenaFinalBounds


