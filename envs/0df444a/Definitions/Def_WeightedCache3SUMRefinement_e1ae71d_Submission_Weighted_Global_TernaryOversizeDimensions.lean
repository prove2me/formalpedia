-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryOversizeDimensions
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryOversizeDimensions
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T11:11:51.761257+00:00
-- url     : https://prove2.me/theorems/e0910034-5db1-4a90-8bbc-0fc6c1c37872
-- title:
--   TernaryOversizeDimensions
-- statement:
--   Definitions and structural lemmas for TernaryOversizeDimensions, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryOversizeDimensions.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryOversizeOverhead
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalOversizeDimensions
open Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalPrincipalDimensions WeightedGlobalDimensionBounds TernaryJointType
def querySlope (K m : ℕ) : ℝ := Real.log (nativePrime K m : ℝ)-Real.log (partitionCap m : ℝ)+
  4*Real.log (inflation K m : ℝ)+(fixedLength m : ℝ)*Real.log 2*queryEntropy
def bankSlope (K m : ℕ) : ℝ := 4*Real.log (inflation K m : ℝ)+
  (fixedLength m : ℝ)*Real.log 2*bankEntropy
def tableSlope (K m t : ℕ) : ℝ := 4*Real.log (inflation K m : ℝ)+Real.log (t : ℝ)
def incidenceSlope (K m : ℕ) : ℝ := Real.log (nativePrime K m : ℝ)-Real.log (partitionCap m : ℝ)+
  4*Real.log (inflation K m : ℝ)
end ThreeSum.WeightedGlobalOversizeDimensions
end
end WeightedCache3SUMRefinement_e1ae71d


