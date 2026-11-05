-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryOversizeRates
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryOversizeRates
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T11:05:33.410768+00:00
-- url     : https://prove2.me/theorems/81116d1c-fcfc-4c41-a4e5-fa6e24a63637
-- title:
--   TernaryOversizeRates
-- statement:
--   Definitions and structural lemmas for TernaryOversizeRates, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryOversizeRates.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryOversizePrime
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryFiniteLedger
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
def softCertificate : ℝ := 48006985204621/25000000000000
def GoodBlock (K m : ℕ) : Prop := 0 < m ∧ bankCharge K m<softCertificate ∧
  queryCharge K m<softCertificate ∧ endpointCharge K m<softCertificate ∧
  histogramCharge K m<softCertificate ∧ incidenceCharge K m<softCertificate
end ThreeSum.WeightedGlobalOversizeRates
end
end WeightedCache3SUMRefinement_e1ae71d


