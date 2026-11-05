-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedPreparationBudget
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedPreparationBudget
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T11:20:42.676201+00:00
-- url     : https://prove2.me/theorems/45ce52f6-1ae2-402f-9c2c-d0da9d76ef76
-- title:
--   TernarySignedPreparationBudget
-- statement:
--   Definitions and structural lemmas for TernarySignedPreparationBudget, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernarySignedPreparationBudget.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedParameters
import Definitions.Def_Submission_ThreeSum_LightTernarySignedMatrix
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryCodes
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryApply
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalSignedPreparationBudget
open Filter Real Asymptotics WeightedGlobalSignedPadding WeightedGlobalCoverScale
open WeightedGlobalPrincipalDimensions WeightedGlobalLocalParameters WeightedGlobalParameters
open scoped Topology
def digitConstant (m b : ℕ) (κ : ℝ) : ℝ :=
  4+Real.log 5/Real.log (b : ℝ)+κ/Real.log (b : ℝ)+2/Real.log (outputSize m : ℝ)
def binaryConstant (κ : ℝ) : ℝ := 4+κ/Real.log 2
end ThreeSum.WeightedGlobalSignedPreparationBudget
end
end WeightedCache3SUMRefinement_e1ae71d


