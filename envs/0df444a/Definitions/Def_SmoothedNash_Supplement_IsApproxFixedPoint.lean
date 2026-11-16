-- Prove2me | Definitions.Def_SmoothedNash_Supplement_IsApproxFixedPoint
-- name    : SmoothedNash_Supplement_IsApproxFixedPoint
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:57:23.52786+00:00
-- url     : https://prove2.me/theorems/6d4f55e9-e8a7-4409-8085-2ec8c02cb6d0
-- title:
--   $\varepsilon$-approximate fixed point (Definition 1.4)
-- statement:
--   Let $B_n = \{x \in \mathbb R^n : \|x\|_2 \le 1\}$ be the closed Euclidean unit ball and $F : B_n \to B_n$. A point $x$ is an **$\varepsilon$-approximate fixed point** of $F$ if
--   $$
--   x \in B_n \qquad\text{and}\qquad \|F(x) - x\|_2 \le \varepsilon .
--   $$
--   This is the output guarantee of Algorithm 3 (Theorem 3.3).
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` and $B_n$ is `Metric.closedBall 0 1`; membership of $x$ in the ball is part of the definition.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Definition 1.4, p.4

import Mathlib
open MeasureTheory

namespace SmoothedNash.Supplement

/-- **Definition 1.4 (Fixed Point problem)** (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), p.4): for `F : B_n(0,1) → B_n(0,1)`,
a point `x ∈ B_n(0,1)` is an `ε`-approximate fixed point if `‖F(x) − x‖₂ ≤ ε`.

**Formalization Note** `ℝ^n` with the Euclidean norm is `EuclideanSpace ℝ (Fin n)`, and
`B_n(0,1)` is `Metric.closedBall 0 1`. `F` is a function on the whole space; only its values on the
ball matter. Membership of `x` in the ball is part of the definition. -/
def IsApproxFixedPoint {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (ε : ℝ) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ∧ ‖F x - x‖ ≤ ε

end SmoothedNash.Supplement


