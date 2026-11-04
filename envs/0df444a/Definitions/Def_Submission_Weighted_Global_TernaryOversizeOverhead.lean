-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryOversizeOverhead
-- name    : Submission_Weighted_Global_TernaryOversizeOverhead
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:59:35.303037+00:00
-- url     : https://prove2.me/theorems/cfccaa89-a06d-4110-a5be-c7bc188842e5
-- title:
--   Ternary Oversize Overhead
-- statement:
--   Definitions and structural lemmas for Ternary Oversize Overhead, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeOverhead.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeRates
import Definitions.Def_Submission_Weighted_Global_TernaryRadixOverhead
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalOversizeOverhead
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters TernaryCoverLocal WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalCoverFrequency WeightedGlobalCoverCapParameters
open scoped Topology
set_option maxHeartbeats 1000000
def baseFrequency (K m : ℕ) : ℕ := frequencyFactor m*(Nat.log2 (nativePrime K m^2)+1)
def baseFactor (K k c d m : ℕ) : ℕ :=
  (max 1 c)*(fixedLength m+1)^d*baseFrequency K m*
    rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) k
def rateUpper (k c d m : ℕ) : ℝ :=
  (Real.log (max 1 c : ℝ)+(361+45*(d : ℝ))*Real.log 2+
    (d+7 : ℕ)*Real.log (m+1 : ℝ))/((fixedLength m : ℝ)*Real.log 2)+
  20/(k : ℝ)+(8*(k : ℝ)^2+26+k)*Real.log 2/((k : ℝ)*((fixedLength m : ℝ)*Real.log 2))
def overheadCharge (k c d m : ℕ) : ℝ := 2*rateUpper k c d m/outputRate m
def selectedMoment (K : ℕ) : ℕ := 30000000000000*K^2
def microAllowance (K : ℕ) : ℝ := 1/(100*(K : ℝ)^2)
end ThreeSum.WeightedGlobalOversizeOverhead


