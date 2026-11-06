-- Prove2me | Definitions.Def_HOTrap_GradModelBounds
-- name    : HOTrap_GradModelBounds
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:46:06.647206+00:00
-- url     : https://prove2.me/theorems/b48372de-467f-41b5-b23a-bbfd6280e50b
-- title:
--   Conclusions (68), (69) of Corollary A.8
-- statement:
--   A scalar model $P$ of $f$ satisfies these bounds with constants $B_0,B_1$ if
--   $$
--   \|P-f+f(c)\|_{\infty,S}\le B_0,\qquad\|\nabla P-\nabla f\|_{\infty,S}\le B_1,
--   $$
--   for all $x,y\in S$
--   $$
--   |P(y)-P(x)-f(y)+f(x)|\le\min\{2B_0,\,B_1\|y-x\|_2\},
--   $$
--   and the term $2B_0$ can be replaced by $B_0$ when $x=c$.
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, Corollary A.8, Eqs. (68), (69), p.62

import Mathlib

namespace HOTrap

/-- **The conclusions (68) and (69) of Corollary A.8** for a scalar model `P` of `f`, with bounds `B₀, B₁`.
Zhou–Sugiyama–Suzuki, *Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, Corollary A.8, p.62: `∥P − f + f(c)∥_{∞,S} ≤ B₀`, `∥∇P − ∇f∥_{∞,S} ≤ B₁`; for all `x, y ∈ S`,
`|P(y) − P(x) − f(y) + f(x)| ≤ min{2B₀, B₁∥y − x∥₂}`; and `2B₀` can be replaced by `B₀` when `x = c`. -/
def GradModelBounds {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) (c : EuclideanSpace ℝ (Fin d)) (f P : EuclideanSpace ℝ (Fin d) → ℝ) (B₀ B₁ : ℝ) : Prop :=
  (∀ y ∈ S, |P y - f y + f c| ≤ B₀) ∧
    (∀ y ∈ S, ‖gradient P y - gradient f y‖ ≤ B₁) ∧
    (∀ x ∈ S, ∀ y ∈ S, |P y - P x - f y + f x| ≤ min (2 * B₀) (B₁ * ‖y - x‖)) ∧
    (∀ y ∈ S, |P y - P c - f y + f c| ≤ min B₀ (B₁ * ‖y - c‖))

end HOTrap


