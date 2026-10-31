-- Prove2me | Definitions.Def_AccelSGDGrowth_ClassFInf
-- name    : AccelSGDGrowth_ClassFInf
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:29:27.370254+00:00
-- url     : https://prove2.me/theorems/ac9d75d7-d64c-4ff6-9952-ce62037ac559
-- title:
--   The class $\mathcal F(m,\infty)$ of Lemma 2.1
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$ and $m\in\mathbb R$. We say $f\in\mathcal F(m,\infty)$ if $f$ is continuously differentiable and satisfies the strong-convexity half of (1.2): for all $x,y\in\mathbb R^d$,
--   $$
--   f(y)\ge f(x)+\nabla f(x)^\top(y-x)+\frac m2\|y-x\|^2 .
--   $$
--   No smoothness bound is imposed ($\mathcal L=\infty$). It is the hypothesis class of Lemma 2.1.
--
--   **Formalization Note** The space is `EuclideanSpace ℝ (Fin d)`; $\nabla f$ is Mathlib's `gradient`; the sign of $m$ is imposed by the theorem.
-- source:
--   Chen, Na, Kolar, Convergence Analysis of Accelerated Stochastic Gradient Descent under the Growth Condition, arXiv:2006.06782v4 (preprint basis), https://arxiv.org/abs/2006.06782v4, Lemma 2.1, p.5; (1.2), p.1

import Mathlib

namespace AccelSGDGrowth

/-- The function class $\mathcal F(m, \infty)$ of Chen, Na, Kolar, arXiv:2006.06782v4, Lemma 2.1, p.5:
`f : ℝ^d → ℝ` continuously differentiable with the lower inequality of (1.2), p.1, only:
`f y ≥ f x + ⟪∇f x, y - x⟫ + (m/2)‖y - x‖²` for all `x y` (no smoothness bound, i.e. `L = ∞`).

**Formalization Note.** Written with Mathlib's `gradient`; the sign of `m` is not built in. -/
def ClassFInf {d : ℕ} (m : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ContDiff ℝ 1 f ∧
  ∀ x y : EuclideanSpace ℝ (Fin d),
    f x + inner ℝ (gradient f x) (y - x) + m / 2 * ‖y - x‖ ^ 2 ≤ f y

end AccelSGDGrowth


