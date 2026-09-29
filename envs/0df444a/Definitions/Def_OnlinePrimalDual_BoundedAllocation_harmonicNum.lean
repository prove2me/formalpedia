-- Prove2me | Definitions.Def_OnlinePrimalDual_BoundedAllocation_harmonicNum
-- name    : OnlinePrimalDual_BoundedAllocation_harmonicNum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:05:53.574934+00:00
-- url     : https://prove2.me/theorems/b5718c5d-9832-41bf-819e-76a11c0f44a6
-- title:
--   The harmonic number H(n)
-- statement:
--   `harmonicNum n := H(n) = Σ_{i=1}^n 1/i`, `H(0) = 0`.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 244, Lemma 13.2

import Mathlib

namespace OnlinePrimalDual.BoundedAllocation

/-- The `n`-th harmonic number `H(n) = ∑_{i=1}^n 1/i` (Buchbinder & Naor, FnT TCS 2009,
Lemma 13.2, p. 244), `H(0) = 0` by the empty sum. -/
noncomputable def harmonicNum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, 1 / (i : ℝ)

end OnlinePrimalDual.BoundedAllocation


