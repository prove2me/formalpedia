-- Prove2me | Definitions.Def_ShorNonsmooth_AlmostDiff_IsSubgradient
-- name    : ShorNonsmooth_AlmostDiff_IsSubgradient
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T15:45:16.025697+00:00
-- url     : https://prove2.me/theorems/afeb6c48-f99e-43f6-b2c3-e78633b110d5
-- title:
--   Subgradient of a function on $E_n$ at a point
-- statement:
--   Let $f : E_n \to \mathbb{R}$ be a function on $n$-dimensional Euclidean space $E_n$ and let $x_0 \in E_n$. A vector $g \in E_n$ is a **subgradient** (generalized gradient) of $f$ at $x_0$ if
--
--   $$
--   f(x) - f(x_0) \ge (g,\, x - x_0) \qquad \text{for all } x \in E_n,
--   $$
--
--   where $(\cdot,\cdot)$ is the Euclidean inner product.
--
--   For a convex function the set of subgradients at $x_0$ is the subdifferential $G_f(x_0)$. The notion underlies the subgradient methods of Chapter 2 and the comparison with almost-gradients in Section 1.4.
--
--   **Formalization Note** The book defines subgradients for a convex $f$ with domain $M$ and $x_0$ interior to $M$; here the domain is all of $E_n$, which is the only case the missions of this series use, and convexity is a hypothesis of the theorems, not part of the definition. $E_n$ is `EuclideanSpace ℝ (Fin n)`.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 9, inequality (1.3) and Definition

import Mathlib

namespace ShorNonsmooth.AlmostDiff

/-- Shor (1985), p. 9, inequality (1.3) and the Definition following it, for a function whose
domain is the whole space `E_n`: a vector `g` is a **subgradient** of `f` at `x₀` if
`f x - f x₀ ≥ (g, x - x₀)` for every `x ∈ E_n`. -/
def IsSubgradient {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x₀ g : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ x : EuclideanSpace ℝ (Fin n), f x - f x₀ ≥ inner ℝ g (x - x₀)

end ShorNonsmooth.AlmostDiff


