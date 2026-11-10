-- Prove2me | Definitions.Def_NashOrTriangle_payoffCol
-- name    : NashOrTriangle_payoffCol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:43:30.835824+00:00
-- url     : https://prove2.me/theorems/d7c61d45-58f2-4a0b-a5db-b0f72ed17d87
-- title:
--   Payoff $M(p,b)$ of a row mixture against a column
-- statement:
--   For a finitely supported row mixture $p$ and a pure column strategy $b$,
--   $$
--   M(p, b) = \sum_{a} p(a)\, M(a, b) .
--   $$
--
--   **Formalization Note** Payoffs are rational and are cast to real numbers.
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962…66f7), §1.1, p.3 (PDF p.4)

import Mathlib

namespace NashOrTriangle

/-- `M(p, b) = ∑_a p(a) M(a, b)`: the expected payoff to the row player when the finitely
supported row mixture `p` meets the pure column strategy `b`.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), §1.1, printed p. 3 (PDF p. 4).

**Formalization Note** Payoffs are rational and are cast to `ℝ`; the sum runs over the finite
support of `p`. -/
noncomputable def payoffCol {A B : Type*} (M : A → B → ℚ) (p : A →₀ ℚ) (b : B) : ℝ :=
  p.sum fun a w => (w : ℝ) * (M a b : ℝ)

end NashOrTriangle


