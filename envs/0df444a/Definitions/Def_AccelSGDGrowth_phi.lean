-- Prove2me | Definitions.Def_AccelSGDGrowth_phi
-- name    : AccelSGDGrowth_phi
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:29:39.190309+00:00
-- url     : https://prove2.me/theorems/7cb5f88e-1da4-4ee3-97e8-32264db03a29
-- title:
--   The regularizer $\phi_k(x)=\sum_{i=1}^k\frac{a_im}{2}\|x-x_i\|^2$
-- statement:
--   Given $m$, weights $a_1,\dots,a_k$ and points $x_1,\dots,x_k\in\mathbb R^d$, define
--   $$
--   \phi_k(x)=\sum_{i=1}^k\frac{a_i m}{2}\,\|x-x_i\|^2 .
--   $$
--   It is the quadratic model of DAM+ built from the past iterates (4.2); $\phi_0=0$.
--
--   **Formalization Note** Index 0 of the sequences is unused.
-- source:
--   Chen, Na, Kolar, Convergence Analysis of Accelerated Stochastic Gradient Descent under the Growth Condition, arXiv:2006.06782v4 (preprint basis), https://arxiv.org/abs/2006.06782v4, (4.2), p.14

import Mathlib

namespace AccelSGDGrowth

/-- The regularizer $\phi_k(u) = \sum_{i=1}^k \frac{a_i m}{2}\|u - x_i\|^2$ of Chen, Na, Kolar,
arXiv:2006.06782v4, (4.2), p.14, built from the iterates `x i` and weights `a i`, `1 ≤ i ≤ k`.

**Formalization Note.** Index 0 is unused; `phi m a x 0 = 0`. -/
noncomputable def phi {d : ℕ} (m : ℝ) (a : ℕ → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin d)) (k : ℕ)
    (u : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i ∈ Finset.Icc 1 k, a i * m / 2 * ‖u - x i‖ ^ 2

end AccelSGDGrowth


