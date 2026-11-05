-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryFiniteLedger
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryFiniteLedger
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T11:03:07.204541+00:00
-- url     : https://prove2.me/theorems/8b6507f5-8516-496d-884d-1d7acbf5bdfb
-- title:
--   TernaryFiniteLedger
-- statement:
--   Definitions and structural lemmas for TernaryFiniteLedger, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryFiniteLedger.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryEntropyRates
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_DimensionBounds
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalFiniteLedger
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open scoped Topology
def bankCharge (m : ℕ) : ℝ := 2*bankEntropy/outputRate m
def queryCharge (m : ℕ) : ℝ := 1+2*(outputRate m-primeRate m+queryEntropy)/outputRate m
def endpointCharge (m : ℕ) : ℝ := 2*endpointRate m/outputRate m
def histogramCharge (m : ℕ) : ℝ := 2*primeRate m/outputRate m
def incidenceCharge (m : ℕ) : ℝ := 1+2*(outputRate m-primeRate m)/outputRate m
def GoodBlock (m : ℕ) : Prop :=
  0 < m ∧ bankCharge m<certificateExponent ∧ queryCharge m<certificateExponent ∧
    endpointCharge m<certificateExponent ∧ histogramCharge m<certificateExponent ∧
    incidenceCharge m<certificateExponent
end ThreeSum.WeightedGlobalFiniteLedger
end
end WeightedCache3SUMRefinement_e1ae71d


