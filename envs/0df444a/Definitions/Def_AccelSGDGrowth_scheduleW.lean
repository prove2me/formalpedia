-- Prove2me | Definitions.Def_AccelSGDGrowth_scheduleW
-- name    : AccelSGDGrowth_scheduleW
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:29:50.639981+00:00
-- url     : https://prove2.me/theorems/6535199d-305c-4c5b-83a4-158fb568ec38
-- title:
--   The averaging weights $w_{k,t}$ of (5.4)
-- statement:
--   Given $\gamma_4>0$ and $\alpha>0$, for $1\le t\le k$:
--   $$
--   w_{k,t}=\begin{cases}0 & \alpha k<\gamma_4,\ t<k,\\ 1 & \alpha k<\gamma_4,\ t=k,\\ 0 & \alpha k\ge\gamma_4,\ \alpha t<\gamma_4,\\ 1 & \alpha k\ge\gamma_4,\ \alpha t\ge\gamma_4.\end{cases}
--   $$
--   In the first phase all weight sits on the current iterate; in the second phase the iterates from the first index $t$ with $\alpha t\ge\gamma_4$ onward are averaged uniformly.
--
--   **Formalization Note** Comparisons in $\mathbb R$ with $k,t$ cast from $\mathbb N$.
-- source:
--   Chen, Na, Kolar, Convergence Analysis of Accelerated Stochastic Gradient Descent under the Growth Condition, arXiv:2006.06782v4 (preprint basis), https://arxiv.org/abs/2006.06782v4, (5.4), p.22

import Mathlib

namespace AccelSGDGrowth

/-- The averaging weights $w_{k,t}$ of Chen, Na, Kolar, arXiv:2006.06782v4, (5.4), p.22:
if `α k < γ₄` then `w_{k,t} = 1` for `t = k` and `0` for `t < k`;
if `α k ≥ γ₄` then `w_{k,t} = 1` when `α t ≥ γ₄` and `0` when `α t < γ₄`.

**Formalization Note.** Used for `1 ≤ t ≤ k`; comparisons are in `ℝ` with `k`, `t` cast from `ℕ`. -/
noncomputable def scheduleW (γ₄ α : ℝ) (k t : ℕ) : ℝ :=
  if α * (k : ℝ) < γ₄ then (if t = k then 1 else 0)
  else (if γ₄ ≤ α * (t : ℝ) then 1 else 0)

end AccelSGDGrowth


