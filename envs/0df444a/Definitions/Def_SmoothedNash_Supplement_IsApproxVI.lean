-- Prove2me | Definitions.Def_SmoothedNash_Supplement_IsApproxVI
-- name    : SmoothedNash_Supplement_IsApproxVI
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:57:40.950202+00:00
-- url     : https://prove2.me/theorems/fa5c2b69-4743-4d3a-bab7-e8b29281d524
-- title:
--   $\varepsilon$-approximate variational inequality solution (Definition 1.5)
-- statement:
--   Let $F : B_n \to \mathbb R^n$. A point $x$ is an **$\varepsilon$-approximate solution to the variational inequality** for $F$ if $x \in B_n$ and
--   $$
--   \langle F(x), y - x \rangle \le \varepsilon \qquad\text{for all } y \in B_n .
--   $$
--   An exact solution either lies in the interior with $F(x) = 0$ or on the sphere with $F(x)$ pointing outward along $x$. This is the output guarantee of Algorithm 4 (Theorems 4.5, 4.17, 4.20).
--
--   **Formalization Note** The inner product is that of `EuclideanSpace ℝ (Fin n)`; membership of $x$ in the ball is part of the definition.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Definition 1.5, p.4

import Mathlib
open MeasureTheory

namespace SmoothedNash.Supplement

/-- **Definition 1.5 (Variational Inequality problem)** (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), p.4): for
`F : B_n(0,1) → ℝ^n`, a point `x ∈ B_n(0,1)` is an `ε`-approximate solution to the variational
inequality for `F` if `⟨F(x), y − x⟩ ≤ ε` for all `y ∈ B_n(0,1)`.

**Formalization Note** `ℝ^n` is `EuclideanSpace ℝ (Fin n)` with its standard inner product, and
`B_n(0,1)` is `Metric.closedBall 0 1`. Membership of `x` in the ball is part of the definition. -/
def IsApproxVI {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (ε : ℝ) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ∧
    ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, inner ℝ (F x) (y - x) ≤ ε

end SmoothedNash.Supplement


