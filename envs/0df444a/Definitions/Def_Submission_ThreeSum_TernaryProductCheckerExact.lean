-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryProductCheckerExact
-- name    : Submission_ThreeSum_TernaryProductCheckerExact
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:12:58.25858+00:00
-- url     : https://prove2.me/theorems/21f4263f-0bb9-4638-a6dc-573a6af57378
-- title:
--   Ternary Product Checker Exact
-- statement:
--   Definitions and structural lemmas for Ternary Product Checker Exact, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryProductCheckerExact.lean

import Definitions.Def_Submission_ThreeSum_TernaryMonicCodes
import Definitions.Def_Submission_ThreeSum_LightPolynomialQuotientCheck
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
end ThreeSum.TernaryExtensionEncoding


