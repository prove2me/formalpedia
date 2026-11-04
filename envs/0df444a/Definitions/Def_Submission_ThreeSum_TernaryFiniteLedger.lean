-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryFiniteLedger
-- name    : Submission_ThreeSum_TernaryFiniteLedger
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:38:37.760112+00:00
-- url     : https://prove2.me/theorems/8ec2ad06-1466-4dfc-806d-5e4fbf7c1120
-- title:
--   Ternary Finite Ledger
-- statement:
--   Definitions and structural lemmas for Ternary Finite Ledger, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFiniteLedger.lean

import Definitions.Def_Submission_ThreeSum_TernaryEntropyRates
import Definitions.Def_Submission_ThreeSum_TernaryDimensionBounds
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryFiniteLedger
open Filter Real TernaryParameters TernaryEntropyRates TernaryCoverScale
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
end ThreeSum.TernaryFiniteLedger


