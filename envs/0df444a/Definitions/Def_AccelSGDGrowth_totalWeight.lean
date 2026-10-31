-- Prove2me | Definitions.Def_AccelSGDGrowth_totalWeight
-- name    : AccelSGDGrowth_totalWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:30:48.791864+00:00
-- url     : https://prove2.me/theorems/b7f19227-7f67-4a06-bf64-60b14bfe35e3
-- title:
--   The total weight $W_k=\sum_{t=1}^k w_{k,t}$
-- statement:
--   With the weights $w_{k,t}$ of (5.4),
--   $$
--   W_k=\sum_{t=1}^k w_{k,t}.
--   $$
--   For $k\ge1$ and $\gamma_4,\alpha>0$ it is positive: $w_{k,k}=1$ in both phases.
-- source:
--   Chen, Na, Kolar, Convergence Analysis of Accelerated Stochastic Gradient Descent under the Growth Condition, arXiv:2006.06782v4 (preprint basis), https://arxiv.org/abs/2006.06782v4, Proposition 5.1, p.23; Theorem 5.1, p.24

import Definitions.Def_AccelSGDGrowth_scheduleW

namespace AccelSGDGrowth

/-- The total averaging weight $W_k = \sum_{t=1}^k w_{k,t}$ of Chen, Na, Kolar, arXiv:2006.06782v4,
Proposition 5.1, p.23 and Theorem 5.1, p.24, with the weights of (5.4). -/
noncomputable def totalWeight (γ₄ α : ℝ) (k : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 k, scheduleW γ₄ α k t

end AccelSGDGrowth


