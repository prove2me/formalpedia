-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryEntropyRates
-- name    : Submission_Weighted_Global_TernaryEntropyRates
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:35:05.141929+00:00
-- url     : https://prove2.me/theorems/e22b28b6-a6c1-4541-aabf-fd46734ab712
-- title:
--   Ternary Entropy Rates
-- statement:
--   Definitions and structural lemmas for Ternary Entropy Rates, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryEntropyRates.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_GlobalParameters
import Definitions.Def_Submission_Weighted_Global_TernaryCoverScale
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
set_option autoImplicit false
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


