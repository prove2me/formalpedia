-- Prove2me | Definitions.Def_OnlinePrimalDual_GeneralPacking_harmonicNum
-- name    : OnlinePrimalDual_GeneralPacking_harmonicNum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:09:08.592933+00:00
-- url     : https://prove2.me/theorems/361f818f-8333-43ae-bbbc-72df3f80425f
-- title:
--   The harmonic number H(n)
-- statement:
--   `harmonicNum n := H(n) = Σ_{i=1}^n 1/i`, `H(0) = 0`.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 251, Lemma 14.2

import Mathlib

namespace OnlinePrimalDual.GeneralPacking

/-- The `n`-th harmonic number `H(n) = ∑_{i=1}^n 1/i` (Buchbinder & Naor, FnT TCS 2009,
Lemma 14.2, p. 251), restated locally in this chunk's own sub-namespace since concurrent draft
missions in this series cannot import each other's definitions (`13-bounded-allocation` also
defines this quantity, for its own Lemma 13.2). -/
noncomputable def harmonicNum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, 1 / (i : ℝ)

end OnlinePrimalDual.GeneralPacking


