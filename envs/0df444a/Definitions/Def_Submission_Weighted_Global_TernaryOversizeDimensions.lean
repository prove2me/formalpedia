-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryOversizeDimensions
-- name    : Submission_Weighted_Global_TernaryOversizeDimensions
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:03:20.607898+00:00
-- url     : https://prove2.me/theorems/fff2a08f-e215-410f-90b1-7cbf145a8f25
-- title:
--   Ternary Oversize Dimensions
-- statement:
--   Definitions and structural lemmas for Ternary Oversize Dimensions, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeDimensions.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeOverhead
set_option autoImplicit false
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


