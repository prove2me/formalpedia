-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryPrincipalDimensions
-- name    : Submission_ThreeSum_TernaryPrincipalDimensions
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:41:17.4503+00:00
-- url     : https://prove2.me/theorems/4800f34d-53c5-4649-ac4d-02c92e871cf1
-- title:
--   Ternary Principal Dimensions
-- statement:
--   Definitions and structural lemmas for Ternary Principal Dimensions, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPrincipalDimensions.lean

import Definitions.Def_Submission_ThreeSum_TernaryFiniteLedger
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryPrincipalDimensions
open Real TernaryParameters TernaryEntropyRates TernaryDimensionBounds
open TernaryCoverScale TernaryLocalParameters TernaryFiniteLedger
def incidenceSlope (m : ℕ) : ℝ := Real.log (outputSize m : ℝ)-Real.log (prime m : ℝ)
def querySlope (m : ℕ) : ℝ := incidenceSlope m+(fixedLength m : ℝ)*Real.log 2*queryEntropy
end ThreeSum.TernaryPrincipalDimensions


