-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryOversizeRates
-- name    : Submission_Weighted_Global_TernaryOversizeRates
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:52:31.762596+00:00
-- url     : https://prove2.me/theorems/fbe2c527-8617-4f8d-bd9e-7e2f1671eb78
-- title:
--   Ternary Oversize Rates
-- statement:
--   Definitions and structural lemmas for Ternary Oversize Rates, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeRates.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizePrime
import Definitions.Def_Submission_Weighted_Global_TernaryFiniteLedger
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalOversizeRates
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters WeightedGlobalOversizePrime
open scoped Topology
set_option maxHeartbeats 1000000
def inflationRate (K m : ℕ) : ℝ := Real.log (inflation K m : ℝ)/((fixedLength m : ℝ)*Real.log 2)
def nativeRate (K m : ℕ) : ℝ := Real.log (nativePrime K m : ℝ)/((fixedLength m : ℝ)*Real.log 2)
def familyCharge (K m : ℕ) : ℝ := 8*inflationRate K m/outputRate m
def bankCharge (K m : ℕ) : ℝ := 2*bankEntropy/outputRate m+familyCharge K m
def queryCharge (K m : ℕ) : ℝ := 1+2*(nativeRate K m-partitionEntropy+queryEntropy)/outputRate m+familyCharge K m
def endpointCharge (K m : ℕ) : ℝ := 2*endpointRate m/outputRate m+familyCharge K m
def histogramCharge (K m : ℕ) : ℝ := 2*nativeRate K m/outputRate m+familyCharge K m
def incidenceCharge (K m : ℕ) : ℝ := 1+2*(nativeRate K m-partitionEntropy)/outputRate m+familyCharge K m
def softCertificate : ℝ := 2400349267/1250000000
def GoodBlock (K m : ℕ) : Prop := 0 < m ∧ bankCharge K m<softCertificate ∧
  queryCharge K m<softCertificate ∧ endpointCharge K m<softCertificate ∧
  histogramCharge K m<softCertificate ∧ incidenceCharge K m<softCertificate
end ThreeSum.WeightedGlobalOversizeRates


