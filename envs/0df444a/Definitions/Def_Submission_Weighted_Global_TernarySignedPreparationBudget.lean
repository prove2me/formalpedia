-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernarySignedPreparationBudget
-- name    : Submission_Weighted_Global_TernarySignedPreparationBudget
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:14:49.716096+00:00
-- url     : https://prove2.me/theorems/456df923-a6b1-436f-8de1-1122bd27dd5a
-- title:
--   Ternary Signed Preparation Budget
-- statement:
--   Definitions and structural lemmas for Ternary Signed Preparation Budget, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySignedPreparationBudget.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernarySignedParameters
import Definitions.Def_Submission_ThreeSum_LightTernarySignedMatrix
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryCodes
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryApply
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalSignedPreparationBudget
open Filter Real Asymptotics WeightedGlobalSignedPadding WeightedGlobalCoverScale
open WeightedGlobalPrincipalDimensions WeightedGlobalLocalParameters WeightedGlobalParameters
open scoped Topology
def digitConstant (m b : ℕ) (κ : ℝ) : ℝ :=
  4+Real.log 5/Real.log (b : ℝ)+κ/Real.log (b : ℝ)+2/Real.log (outputSize m : ℝ)
def binaryConstant (κ : ℝ) : ℝ := 4+κ/Real.log 2
end ThreeSum.WeightedGlobalSignedPreparationBudget


