-- Prove2me | Definitions.Def_FirstOrderOpt_ConvexTheory_normalCone
-- name    : FirstOrderOpt_ConvexTheory_normalCone
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T17:34:59.300969+00:00
-- url     : https://prove2.me/theorems/23749483-ef2d-4206-ba65-c1c6647f8e70
-- title:
--   Normal cone of a convex set
-- statement:
--   For a set $X \subseteq \mathbb{R}^n$ and a point $x$, the **normal cone** of $X$ at $x$ is
--   $$N_X(x) := \{w \in \mathbb{R}^n : \langle w, y - x\rangle \le 0 \text{ for all } y \in X\}.$$
--   Lan introduces this object as $\partial I_X(x)$, the subdifferential at $x$ of the indicator
--   function $I_X$ of $X$ (Eq. (2.2.14)): $I_X(x) = 0$ for $x \in X$ and $I_X(x) = \infty$
--   otherwise, so a subgradient of $I_X$ at $x \in X$ is exactly a vector making an obtuse (or
--   right) angle with every direction $y - x$ into $X$. When $X = \mathbb{R}^n$, $N_X(x) =
--   \{0\}$ for every $x$, recovering the unconstrained optimality condition $\nabla f(x) = 0$.
--
--   **Formalization Note.** Stated over `EuclideanSpace ℝ (Fin n)` with the real inner product,
--   matching the ambient space Lan works in throughout Chapter 2. This is the same object the
--   book calls `N∗_X(x)` in Theorem 2.8's stationarity condition (the star there is Lan's own
--   notation for the dual-space normal cone; in $\mathbb{R}^n$ with the identity embedding it
--   coincides with the primal-space normal cone defined here).
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 35, Eq. (2.2.14)

import Mathlib

namespace FirstOrderOpt.ConvexTheory

open scoped RealInnerProductSpace

/-- The normal cone of a set `X` at a point `x`: the vectors `w` with `⟪w, y - x⟫ ≤ 0`
for every `y ∈ X`. This is Lan's `N_X(x)`, defined via (2.2.14) as the subdifferential of the
indicator function of `X` at `x`. -/
def normalCone {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {w | ∀ y ∈ X, ⟪w, y - x⟫ ≤ 0}

end FirstOrderOpt.ConvexTheory


