-- Prove2me | Definitions.Def_AccelSGDGrowth_scheduleR
-- name    : AccelSGDGrowth_scheduleR
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:29:40.659171+00:00
-- url     : https://prove2.me/theorems/89f9df3c-02f7-4bc7-8635-80e8bb8bce7a
-- title:
--   The rate schedule $r_k$ of (5.4)
-- statement:
--   Given $\gamma_1,\gamma_4>0$ and a tuning parameter $\alpha>0$,
--   $$
--   r_k=\begin{cases}1/\gamma_4 & \text{if } \alpha k<\gamma_4,\\ 1/(\gamma_1k) & \text{otherwise.}\end{cases}
--   $$
--   A constant rate in the first phase, a decreasing one in the second. In Theorem 5.1, $\eta_k=r_k$ with $\gamma_1=\sqrt{m\mathcal L}$ and $\gamma_4=2\mathcal L(1+\delta)$.
--
--   **Formalization Note** The comparison $\alpha k<\gamma_4$ is in $\mathbb R$ with $k$ cast from $\mathbb N$.
-- source:
--   Chen, Na, Kolar, Convergence Analysis of Accelerated Stochastic Gradient Descent under the Growth Condition, arXiv:2006.06782v4 (preprint basis), https://arxiv.org/abs/2006.06782v4, (5.4), p.22

import Mathlib

namespace AccelSGDGrowth

/-- The rate schedule $r_k$ of Chen, Na, Kolar, arXiv:2006.06782v4, (5.4), p.22:
`r_k = 1/γ₄` if `α k < γ₄`, and `r_k = 1/(γ₁ k)` otherwise.

**Formalization Note.** The phase test `α * k < γ₄` is in `ℝ` with `k` cast from `ℕ`. Used for `k ≥ 1`. -/
noncomputable def scheduleR (γ₁ γ₄ α : ℝ) (k : ℕ) : ℝ :=
  if α * (k : ℝ) < γ₄ then 1 / γ₄ else 1 / (γ₁ * (k : ℝ))

end AccelSGDGrowth


