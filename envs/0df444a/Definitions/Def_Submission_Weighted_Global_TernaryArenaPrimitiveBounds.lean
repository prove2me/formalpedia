-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaPrimitiveBounds
-- name    : Submission_Weighted_Global_TernaryArenaPrimitiveBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T21:26:22.299461+00:00
-- url     : https://prove2.me/theorems/dd377c93-10bf-4368-8267-12996dce10a9
-- title:
--   Ternary Arena Primitive Bounds
-- statement:
--   Definitions and structural lemmas for Ternary Arena Primitive Bounds, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrimitiveBounds.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedPrimitiveGuards
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaPrimitiveBounds
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup WeightedGlobalArenaSourceBounds
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters WeightedGlobalNativeCompleteFrontend
open WeightedGlobalArenaSeedCandidate LightWeightedGlobalSeedScoreFactory
set_option maxHeartbeats 6000000
variable {p m F r : ℕ} [Fact p.Prime]
end ThreeSum.WeightedGlobalArenaPrimitiveBounds


