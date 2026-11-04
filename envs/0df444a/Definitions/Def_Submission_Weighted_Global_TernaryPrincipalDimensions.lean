-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryPrincipalDimensions
-- name    : Submission_Weighted_Global_TernaryPrincipalDimensions
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:52:31.721206+00:00
-- url     : https://prove2.me/theorems/caa7cb43-e902-4b94-8c1d-4eb7c1585009
-- title:
--   Ternary Principal Dimensions
-- statement:
--   Definitions and structural lemmas for Ternary Principal Dimensions, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrincipalDimensions.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryFiniteLedger
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalPrincipalDimensions
open Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalDimensionBounds
open WeightedGlobalCoverScale WeightedGlobalLocalParameters WeightedGlobalFiniteLedger
def incidenceSlope (m : ℕ) : ℝ := Real.log (outputSize m : ℝ)-Real.log (prime m : ℝ)
def querySlope (m : ℕ) : ℝ := incidenceSlope m+(fixedLength m : ℝ)*Real.log 2*queryEntropy
end ThreeSum.WeightedGlobalPrincipalDimensions


