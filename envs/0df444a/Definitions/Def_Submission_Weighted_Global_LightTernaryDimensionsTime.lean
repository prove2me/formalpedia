-- Prove2me | Definitions.Def_Submission_Weighted_Global_LightTernaryDimensionsTime
-- name    : Submission_Weighted_Global_LightTernaryDimensionsTime
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:32:44.875236+00:00
-- url     : https://prove2.me/theorems/f3347272-bc82-4fbc-a32b-1335ad9d6e9b
-- title:
--   Light Ternary Dimensions Time
-- statement:
--   Definitions and structural lemmas for Light Ternary Dimensions Time, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryDimensionsTime.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryDimensions
import Definitions.Def_Submission_Weighted_Global_TernaryExtensionBudget
set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightWeightedGlobalDimensions
open WeightedGlobalSignedPadding TernaryExtensionEncoding WeightedGlobalCoverScale Filter Real
set_option maxHeartbeats 2000000
variable {p : ℕ} [Fact p.Prime]
end ThreeSum.LightWeightedGlobalDimensions


