-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryExtensionBudget
-- name    : Submission_Weighted_Global_TernaryExtensionBudget
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:22:15.513466+00:00
-- url     : https://prove2.me/theorems/13bf1dba-72c4-4b6b-a577-31973b9df0b2
-- title:
--   Ternary Extension Budget
-- statement:
--   Definitions and structural lemmas for Ternary Extension Budget, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryExtensionBudget.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryExtensionCandidates
import Definitions.Def_Submission_Weighted_Global_TernarySignedPreparationBudget
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalExtensionBudget
open ThreeSum.TernaryExtensionEncoding
open Filter Real WeightedGlobalSignedPadding WeightedGlobalCoverScale
open WeightedGlobalSignedPreparationBudget
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
end ThreeSum.WeightedGlobalExtensionBudget


