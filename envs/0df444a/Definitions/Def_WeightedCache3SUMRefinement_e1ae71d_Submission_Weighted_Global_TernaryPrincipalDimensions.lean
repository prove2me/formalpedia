-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPrincipalDimensions
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPrincipalDimensions
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T11:04:53.054371+00:00
-- url     : https://prove2.me/theorems/ae31311b-bea3-409c-8bd2-27e96adcdc6c
-- title:
--   TernaryPrincipalDimensions
-- statement:
--   Definitions and structural lemmas for TernaryPrincipalDimensions, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPrincipalDimensions.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryFiniteLedger
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalPrincipalDimensions
open Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalDimensionBounds
open WeightedGlobalCoverScale WeightedGlobalLocalParameters WeightedGlobalFiniteLedger
def incidenceSlope (m : ℕ) : ℝ := Real.log (outputSize m : ℝ)-Real.log (prime m : ℝ)
def querySlope (m : ℕ) : ℝ := incidenceSlope m+(fixedLength m : ℝ)*Real.log 2*queryEntropy
end ThreeSum.WeightedGlobalPrincipalDimensions
end
end WeightedCache3SUMRefinement_e1ae71d


