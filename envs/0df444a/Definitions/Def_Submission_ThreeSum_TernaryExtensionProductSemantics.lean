-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryExtensionProductSemantics
-- name    : Submission_ThreeSum_TernaryExtensionProductSemantics
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:02:43.755045+00:00
-- url     : https://prove2.me/theorems/45c6b7a2-6e92-47d7-8302-5a9202bacc31
-- title:
--   Ternary Extension Product Semantics
-- statement:
--   Definitions and structural lemmas for Ternary Extension Product Semantics, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionProductSemantics.lean

import Definitions.Def_Submission_ThreeSum_TernaryExtensionDecoded
import Definitions.Def_Submission_ThreeSum_LightPolynomialProductCheck
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
def arrayPolynomial (n : ℕ) (a : ℕ → ℕ) : (ZMod p)[X] :=
  ∑ i ∈ range n, monomial i (a i : ZMod p)
end ThreeSum.TernaryExtensionEncoding


