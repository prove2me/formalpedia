-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryEntropyRates
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryEntropyRates
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:24:24.475009+00:00
-- url     : https://prove2.me/theorems/8448d181-6275-426e-b911-817e0bd6f191
-- title:
--   TernaryEntropyRates
-- statement:
--   Definitions and structural lemmas for TernaryEntropyRates, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryEntropyRates.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalParameters
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverScale
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalEntropyRates
open Filter Real
open scoped Topology
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters WeightedGlobalCoverScale
set_option maxRecDepth 10000
def typeCount (N r1 r2 m : ℕ) : ℕ :=
  (N*m).choose (r2*m)*((N-r2)*m).choose (r1*m)
def splitBits (N r1 r2 : ℕ) : ℝ :=
  ((N : ℝ)*ThreeSum.Parameters.entropy ((r2 : ℝ)/N)+
    ((N-r2 : ℕ) : ℝ)*ThreeSum.Parameters.entropy ((r1 : ℝ)/(N-r2 : ℕ)))/N
def endpointSize (m : ℕ) : ℕ := (vertices (fixedLength m) (fixedAlpha m)).card
def outputRate (m : ℕ) : ℝ := Real.log (outputSize m : ℝ)/((fixedLength m : ℝ)*Real.log 2)
def endpointRate (m : ℕ) : ℝ := Real.log (endpointSize m : ℝ)/((fixedLength m : ℝ)*Real.log 2)
def primeRate (m : ℕ) : ℝ := Real.log (prime m : ℝ)/((fixedLength m : ℝ)*Real.log 2)
def partitionCap (m : ℕ) : ℕ := 2^(fixedPi m 1)*3^(fixedPi m 2)
end ThreeSum.WeightedGlobalEntropyRates
end
end WeightedCache3SUMRefinement_e1ae71d


