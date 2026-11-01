-- Prove2me | Definitions.Def_TightQLearning_weight
-- name    : TightQLearning_weight
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:30:26.591222+00:00
-- url     : https://prove2.me/theorems/34e8e2b3-ebe6-4e24-b93f-498e6738a154
-- title:
--   (36) — the weights $\eta_i^{(t)}$
-- statement:
--   The weights that arise from unrolling the recursion are
--   $$\eta_i^{(t)}:=\begin{cases}\prod_{j=1}^t(1-\eta_j),&i=0,\\ \eta_i\prod_{j=i+1}^t(1-\eta_j),&0<i<t,\\ \eta_t,&i=t.\end{cases}$$
--
--   **Formalization Note** The page's domain is $t\ge1$, $0\le i\le t$; at $t=0$ the first and third cases collide, and every statement of the mission that uses the weights has $t\ge1$. The value for $i>t$ is outside that domain.
-- source:
--   Li, Cai, Chen, Wei & Chi, Is Q-Learning Minimax Optimal? A Tight Sample Complexity Analysis, arXiv:2102.06548v4 (https://arxiv.org/abs/2102.06548v4), (36), p.13; (64), p.20

import Mathlib

namespace TightQLearning

/-- The weights `η_i^{(t)}` of (36) (arXiv:2102.06548v4, p.13; again (64), p.20):
`∏_{j=1}^t (1 − η_j)` if `i = 0`, `η_i ∏_{j=i+1}^t (1 − η_j)` if `0 < i < t`, and `η_t` if `i = t`.

**Formalization Note.** The page's domain is `t ≥ 1`, `0 ≤ i ≤ t`. At `t = 0` the cases `i = 0` and
`i = t` of the page collide; every statement that uses `weight` has `t ≥ 1`. The value `0` for
`i > t` is outside the page's domain and is never read. -/
noncomputable def weight (η : ℕ → ℝ) (t i : ℕ) : ℝ :=
  if i = 0 then ∏ j ∈ Finset.Icc 1 t, (1 - η j)
  else if i < t then η i * ∏ j ∈ Finset.Ioc i t, (1 - η j)
  else if i = t then η t
  else 0

end TightQLearning


