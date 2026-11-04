-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryExtensionCheckerSemantics
-- name    : Submission_ThreeSum_TernaryExtensionCheckerSemantics
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:17:07.594663+00:00
-- url     : https://prove2.me/theorems/74252a07-21a3-4a11-9969-10e1aeca92de
-- title:
--   Ternary Extension Checker Semantics
-- statement:
--   Definitions and structural lemmas for Ternary Extension Checker Semantics, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionCheckerSemantics.lean

import Definitions.Def_Submission_ThreeSum_TernaryProductCheckerExact
import Definitions.Def_Submission_ThreeSum_LightExtensionQuotientPredicate
import Definitions.Def_Submission_ThreeSum_LightExtensionFactorPredicate
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
def codeDigits (code k : ℕ) : ℕ := code/p^k%p
end ThreeSum.TernaryExtensionEncoding


