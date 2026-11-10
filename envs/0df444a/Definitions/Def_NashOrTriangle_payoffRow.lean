-- Prove2me | Definitions.Def_NashOrTriangle_payoffRow
-- name    : NashOrTriangle_payoffRow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:43:29.167197+00:00
-- url     : https://prove2.me/theorems/fd2a80a0-83a1-4805-8216-862ac1ee349c
-- title:
--   Payoff $M(a,q)$ of a row against a column mixture
-- statement:
--   For a pure row strategy $a$ and a finitely supported column mixture $q$, the payoff is extended by expectation:
--   $$
--   M(a, q) = \sum_{b} q(b)\, M(a, b) .
--   $$
--
--   **Formalization Note** Payoffs are rational and are cast to real numbers.
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962…66f7), §1.1, p.3 (PDF p.4)

import Mathlib

namespace NashOrTriangle

/-- `M(a, q) = ∑_b q(b) M(a, b)`: the expected payoff of the pure row strategy `a` against a
finitely supported column mixture `q` (the extension of `M` to mixed strategies "by taking
expectations").

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), §1.1, printed p. 3 (PDF p. 4).

**Formalization Note** Payoffs are rational and are cast to `ℝ`; the sum runs over the finite
support of `q`. -/
noncomputable def payoffRow {A B : Type*} (M : A → B → ℚ) (a : A) (q : B →₀ ℚ) : ℝ :=
  q.sum fun b w => (w : ℝ) * (M a b : ℝ)

end NashOrTriangle


