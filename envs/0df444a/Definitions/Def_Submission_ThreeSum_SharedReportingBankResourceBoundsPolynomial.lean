-- Prove2me | Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBoundsPolynomial
-- name    : Submission_ThreeSum_SharedReportingBankResourceBoundsPolynomial
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T14:25:34.393198+00:00
-- url     : https://prove2.me/theorems/a295f9cc-14b6-42fa-9a55-5e0fb7bb9d54
-- title:
--   Shared Reporting Bank Resource Bounds Polynomial
-- statement:
--   Definitions and structural lemmas for Shared Reporting Bank Resource Bounds Polynomial, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankResourceBoundsPolynomial.lean

import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBoundsScales
set_option autoImplicit false
namespace ThreeSum.SharedReportingBankResourceBounds
open Scales StageBounds Filter Light
open scoped Topology
set_option maxHeartbeats 1200000
set_option maxRecDepth 14000
noncomputable section
def need (n _U : ℕ) : Light.Need := ⟨scaledWord n,scaledExtent n,scaledDepth n⟩
end
end ThreeSum.SharedReportingBankResourceBounds


