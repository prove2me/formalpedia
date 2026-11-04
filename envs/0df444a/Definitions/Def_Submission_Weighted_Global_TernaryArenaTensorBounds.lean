-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaTensorBounds
-- name    : Submission_Weighted_Global_TernaryArenaTensorBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T21:05:20.822996+00:00
-- url     : https://prove2.me/theorems/ff540afd-90b0-430e-a1b5-08474d79676c
-- title:
--   Ternary Arena Tensor Bounds
-- statement:
--   Definitions and structural lemmas for Ternary Arena Tensor Bounds, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaTensorBounds.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFrontBounds
import Definitions.Def_Submission_Weighted_Global_TernaryTensorWordResources
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaTensorBounds
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup WeightedGlobalArenaSourceBounds
open WeightedGlobalArenaFrontBounds WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters
open WeightedGlobalNativeCompleteFrontend WeightedGlobalNativeMomentBounds
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
end ThreeSum.WeightedGlobalArenaTensorBounds


