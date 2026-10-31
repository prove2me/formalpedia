-- Prove2me | Definitions.Def_AdaDiscRL_gap
-- name    : AdaDiscRL_gap
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:27:28.590377+00:00
-- url     : https://prove2.me/theorems/9bf96025-645f-4942-b719-3ae1149ef38d
-- title:
--   Sub-optimality gap $\mathrm{gap}_h(x,a)=V^\star_h(x)-Q^\star_h(x,a)$
-- statement:
--   For a state-action pair $(x,a)$ and a step $h$, the **stage dependent sub-optimality gap** is
--   $$
--   \mathrm{gap}_h(x,a)=V^\star_h(x)-Q^\star_h(x,a).
--   $$
--   It measures the regret incurred by taking $a$ in $x$ at step $h$ and then acting optimally; the near-optimal sets and the zooming dimension are defined through it.
--
--   **Formalization Note** `h : Fin H` is the paper's step $h+1$.
-- source:
--   Sinclair, Banerjee & Yu, Adaptive Discretization in Online Reinforcement Learning, arXiv:2110.15843v3, Definition 2.5, p.11

import Mathlib
import Definitions.Def_AdaDiscRL_optValue

namespace AdaDiscRL

/-- **Stage dependent sub-optimality gap** (arXiv:2110.15843v3, Definition 2.5, p.11):
`gap_h(x, a) = V⋆_h(x) − Q⋆_h(x, a)`, for `h : Fin H` (paper step `h + 1`). -/
noncomputable def gap {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] {H : ℕ}
    (M : EpisodicMDP S A H) (h : Fin H) (p : S × A) : ℝ :=
  optV M h p.1 - optQ M h p

end AdaDiscRL


