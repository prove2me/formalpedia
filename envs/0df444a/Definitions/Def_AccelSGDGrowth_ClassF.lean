-- Prove2me | Definitions.Def_AccelSGDGrowth_ClassF
-- name    : AccelSGDGrowth_ClassF
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:29:24.304062+00:00
-- url     : https://prove2.me/theorems/5c73a846-3f61-43a2-a5eb-84e5c73211a1
-- title:
--   The class $\mathcal F(m,\mathcal L)$ of (1.2)
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$ and $m,\mathcal L\in\mathbb R$. We say $f\in\mathcal F(m,\mathcal L)$ if $f$ is continuously differentiable and, for all $x,y\in\mathbb R^d$,
--   $$
--   f(y)\le f(x)+\nabla f(x)^\top(y-x)+\frac{\mathcal L}{2}\|y-x\|^2,\qquad f(y)\ge f(x)+\nabla f(x)^\top(y-x)+\frac m2\|y-x\|^2 .
--   $$
--   These are the $\mathcal L$-smoothness and $m$-strong convexity inequalities (1.2). The class $\mathcal F(0,\mathcal L)$ of Lemma 2.2 is the case $m=0$ (convex and $\mathcal L$-smooth).
--
--   Every result of the mission is stated for $f\in\mathcal F(m,\mathcal L)$, the paper's standing assumption (§2).
--
--   **Formalization Note** The space is `EuclideanSpace ℝ (Fin d)` and $\nabla f$ is Mathlib's `gradient`. The page's "that is" makes (1.2) the definition, so the class is not built from `StrongConvexOn` and a Lipschitz gradient. Signs of $m,\mathcal L$ are imposed by the theorems.
-- source:
--   Chen, Na, Kolar, Convergence Analysis of Accelerated Stochastic Gradient Descent under the Growth Condition, arXiv:2006.06782v4 (preprint basis), https://arxiv.org/abs/2006.06782v4, (1.2), p.1, and §2, p.5

import Mathlib

namespace AccelSGDGrowth

/-- The function class $\mathcal F(m, \mathcal L)$ of Chen, Na, Kolar, arXiv:2006.06782v4, (1.2), p.1,
and §2, p.5: `f : ℝ^d → ℝ` is continuously differentiable and, for all `x y`,
`f y ≤ f x + ⟪∇f x, y - x⟫ + (L/2)‖y - x‖²` and `f y ≥ f x + ⟪∇f x, y - x⟫ + (m/2)‖y - x‖²`.

**Formalization Note.** The page's "that is" makes (1.2) the definition, so the class is the two
inequalities with Mathlib's `gradient`, not `StrongConvexOn` plus a Lipschitz hypothesis. The class
`F(0, L)` of Lemma 2.2 is `ClassF 0 L f`. No sign condition on `m`, `L` is built in; theorems carry
`0 < m ≤ L` (or `0 < L`) as binders. -/
def ClassF {d : ℕ} (m L : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ContDiff ℝ 1 f ∧
  (∀ x y : EuclideanSpace ℝ (Fin d),
      f y ≤ f x + inner ℝ (gradient f x) (y - x) + L / 2 * ‖y - x‖ ^ 2) ∧
  (∀ x y : EuclideanSpace ℝ (Fin d),
      f x + inner ℝ (gradient f x) (y - x) + m / 2 * ‖y - x‖ ^ 2 ≤ f y)

end AccelSGDGrowth


