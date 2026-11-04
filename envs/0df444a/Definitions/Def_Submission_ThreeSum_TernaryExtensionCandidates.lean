-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryExtensionCandidates
-- name    : Submission_ThreeSum_TernaryExtensionCandidates
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:52:36.662964+00:00
-- url     : https://prove2.me/theorems/bfbafe2d-b86e-446a-945a-7eeb03712518
-- title:
--   Ternary Extension Candidates
-- statement:
--   Definitions and structural lemmas for Ternary Extension Candidates, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionCandidates.lean

import Definitions.Def_Submission_ThreeSum_TernaryExtensionEncoding
import Mathlib.Data.Nat.Log
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
set_option maxHeartbeats 3000000
variable {p : ℕ} [Fact p.Prime]
def vectorPolynomial {d : ℕ} (a : Fin d → ZMod p) : (ZMod p)[X] :=
  ∑ i : Fin d, monomial i.val (a i)
def monicCandidate {d : ℕ} (a : Fin d → ZMod p) : (ZMod p)[X] :=
  X^d+vectorPolynomial a
def menuDegree (p Λ K : ℕ) : ℕ := Nat.clog p (8*(Λ+1)*p^(4*K))
end ThreeSum.TernaryExtensionEncoding


