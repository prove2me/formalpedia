-- Prove2me | Definitions.Def_ConstrainedTrading_IsConvexRep
-- name    : ConstrainedTrading_IsConvexRep
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:18:48.014281+00:00
-- url     : https://prove2.me/theorems/c39a0527-bd95-4a07-a3b5-04cbef43307b
-- title:
--   Finite convex representation of a real point by integer points
-- statement:
--   A **convex representation** of $x\in\mathbb R^E$ by integer points is a finite set $S\subseteq\mathbb Z^E$ together with weights $\lambda_z>0$ ($z\in S$) such that
--   $$
--   \sum_{z\in S}\lambda_z=1,\qquad \sum_{z\in S}\lambda_z z=x .
--   $$
--   These are the feasible weight vectors of Definition 2.8 ($\sum_z\lambda_z z=x$, $0\le\lambda_z\le1$, $\sum_z\lambda_z=1$), with the points of weight $0$ left out.
--
--   **Formalization Note** Restricting to the strictly positive support changes no representation and makes the value $\sum_z\lambda_z f(z)$ well defined when $f=-\infty$ at points of weight $0$.
-- source:
--   Kizilkale, Vohra, Constrained Trading Networks, arXiv:2008.09757v1, Definition 2.8, p.5

import Mathlib

namespace ConstrainedTrading

/-- A **convex representation** of a real point `x ∈ ℝ^E` by integer points: a finite set
`S ⊆ ℤ^E` and weights `λ` with `λ_z > 0` for `z ∈ S`, `Σ_{z∈S} λ_z = 1` and
`Σ_{z∈S} λ_z z = x` (the feasible set of Definition 2.8, Kizilkale–Vohra, *Constrained Trading
Networks*, arXiv:2008.09757v1, p.5: `Σ_z λ_z z = x, 0 ≤ λ_z ≤ 1, Σ_z λ_z = 1`).

**Formalization Note** The page sums over all `z`; here the sum runs over the finite support
`S` of the weights, on which the weights are strictly positive (points of weight `0` are simply
left out of `S`). This makes the value `Σ λ_z f(z)` well defined when some `f(z) = −∞` lies
off the support. -/
def IsConvexRep {E : Type*} (x : E → ℝ) (S : Finset (E → ℤ)) (wt : (E → ℤ) → ℝ) : Prop :=
  (∀ z ∈ S, 0 < wt z) ∧ (∑ z ∈ S, wt z = 1) ∧ ∀ e, ∑ z ∈ S, wt z * (z e : ℝ) = x e

end ConstrainedTrading


