-- Prove2me | Definitions.Def_AccelSGDGrowth_tailAverage
-- name    : AccelSGDGrowth_tailAverage
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:31:55.737157+00:00
-- url     : https://prove2.me/theorems/788a077c-3de3-4c2b-a9f6-1c3041644dce
-- title:
--   The tail average $\bar x_k=\sum_{t=1}^k w_{k,t}x_t/W_k$
-- statement:
--   With the weights $w_{k,t}$ and $W_k$ of (5.4),
--   $$
--   \bar x_k=\frac{1}{W_k}\sum_{t=1}^k w_{k,t}\,x_t .
--   $$
--   This is the output of Theorem 5.1. It averages the iterates $x_t$ (not $y_t$): in the first phase $\bar x_k=x_k$, in the second phase it is the uniform average of the iterates of the second phase.
-- source:
--   Chen, Na, Kolar, Convergence Analysis of Accelerated Stochastic Gradient Descent under the Growth Condition, arXiv:2006.06782v4 (preprint basis), https://arxiv.org/abs/2006.06782v4, Theorem 5.1, p.24

import Definitions.Def_AccelSGDGrowth_totalWeight

namespace AccelSGDGrowth

/-- The tail average $\bar x_k = \sum_{t=1}^k w_{k,t} x_t / W_k$ of Chen, Na, Kolar,
arXiv:2006.06782v4, Theorem 5.1, p.24, with the weights $w_{k,t}$ of (5.4).

**Formalization Note.** `W_k > 0` for every `k ≥ 1` under (5.4) with `γ₄, α > 0` (the weight of
`t = k` is `1` in both phases), so the division is genuine there. It averages the iterates `x_t`, not
`y_t`. -/
noncomputable def tailAverage {d : ℕ} (γ₄ α : ℝ) (x : ℕ → EuclideanSpace ℝ (Fin d)) (k : ℕ) :
    EuclideanSpace ℝ (Fin d) :=
  (1 / totalWeight γ₄ α k) • ∑ t ∈ Finset.Icc 1 k, scheduleW γ₄ α k t • x t

end AccelSGDGrowth


