-- Prove2me | Definitions.Def_FWIterates_Assumption23
-- name    : FWIterates_Assumption23
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:23:27.363656+00:00
-- url     : https://prove2.me/theorems/fc69d0f3-9c25-46df-86f5-10cea2e1a549
-- title:
--   Assumption 2.3, p.3 — standing assumptions of the Frank-Wolfe algorithm
-- statement:
--   Let $\mathcal C\subset\mathbb R^n$ be a nonempty compact convex set and $f:\mathcal D\to\mathbb R$ a convex function with $L$-Lipschitz-continuous gradient, where $L>0$ and $\mathcal D\subset\mathbb R^n$ is an open convex set containing $\mathcal C$. Explicitly, $f$ is differentiable on $\mathcal D$ and
--   $$
--   \|\nabla f(x)-\nabla f(y)\|\le L\,\|x-y\|\qquad\text{for all }x,y\in\mathcal D.
--   $$
--
--   These are the hypotheses under which the classical rates of Theorem 2.4 hold, and which the counterexamples of the paper satisfy.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`. The paper's $f:\mathcal D\to\mathbb R$ is a total function on $\mathbb R^n$ whose values outside $\mathcal D$ play no role: convexity, differentiability and the Lipschitz bound are all imposed on $\mathcal D$ only.
-- source:
--   Bolte, Combettes & Pauwels, The Iterates of the Frank-Wolfe Algorithm May Not Converge, arXiv:2202.08711v1, Assumption 2.3, p.3

import Mathlib

open scoped RealInnerProductSpace

namespace FWIterates

/-- **Assumption 2.3** (Bolte, Combettes & Pauwels, *The Iterates of the Frank-Wolfe Algorithm May
Not Converge*, arXiv:2202.08711v1, Assumption 2.3, p.3): `C ⊂ ℝⁿ` is a nonempty compact convex
set and `f : D → ℝ` is a convex function with `L`-Lipschitz-continuous gradient, where `L > 0` and
`D ⊂ ℝⁿ` is an open convex set containing `C`.

**Formalization Note** `ℝⁿ` is `EuclideanSpace ℝ (Fin n)`. The paper's `f : D → ℝ` is a total
function `f : ℝⁿ → ℝ` whose values outside `D` play no role: convexity, differentiability and the
Lipschitz bound are all required on `D` only. Since `D` is open, `gradient f x` at `x ∈ D` is the
true gradient. "With `L`-Lipschitz-continuous gradient" is split into differentiability on `D` and
`‖∇f(x) − ∇f(y)‖ ≤ L‖x − y‖` for `x, y ∈ D`. -/
structure Assumption23 {n : ℕ} (C D : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ) : Prop where
  nonempty : C.Nonempty
  isCompact : IsCompact C
  convex : Convex ℝ C
  isOpen_D : IsOpen D
  convex_D : Convex ℝ D
  subset_D : C ⊆ D
  convexOn : ConvexOn ℝ D f
  differentiableOn : DifferentiableOn ℝ f D
  lipschitz_gradient : ∀ x ∈ D, ∀ y ∈ D, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖
  pos_L : 0 < L

end FWIterates


