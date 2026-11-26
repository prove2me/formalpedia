-- Prove2me | Definitions.Def_OnlineSaddlePoint_Supplement_indRegretY
-- name    : OnlineSaddlePoint_Supplement_indRegretY
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T21:52:27.274924+00:00
-- url     : https://prove2.me/theorems/fde15145-7dc2-59a2-9054-e71fc92de645
-- title:
--   Individual regret of player 2, (2b)/(13)
-- statement:
--   Let $\mathcal L_1,\dots,\mathcal L_T$ be payoff functions and $(x_t,y_t)$, $t=1,\dots,T$, the actions played. The **individual regret** of the maximizing player is
--
--   $$
--   \max_{y\in Y}\sum_{t=1}^T\mathcal L_t(x_t,y)-\sum_{t=1}^T\mathcal L_t(x_t,y_t),
--   $$
--
--   the reward player 2 gave up relative to the best fixed action in hindsight, with player 1's actions held fixed. In §6 it is display (13) with $\mathcal L_t(x,y)=x^\top A_t y$.
--
--   **Formalization Note** The maximum is `sSup` of the image of $Y$ in $\mathbb R$ (attained for continuous payoffs on a nonempty compact $Y$).
-- source:
--   Rivera Cardoso, Wang, Xu, The Online Saddle Point Problem and Online Convex Optimization with Knapsacks, arXiv:1806.08301v3, display (2b), p.2; display (13), p.27

import Mathlib

namespace OnlineSaddlePoint.Supplement

/-- **Individual regret of player 2** (the maximizing player). Rivera Cardoso, Wang, Xu,
arXiv:1806.08301v3, display (2b), p.2:
`max_{y∈Y} ∑_{t=1}^T 𝓛_t(x_t, y) − ∑_{t=1}^T 𝓛_t(x_t, y_t)`; in §6, display (13), p.27, with
`𝓛_t(x, y) = xᵀA_t y`.

**Formalization Note.** The `max` is `sSup` of the image of `Y` in `ℝ` (attained when `Y` is nonempty
and compact and the payoffs are continuous). Played actions are sequences read at rounds
`1, …, T`; index `0` is unused. -/
noncomputable def indRegretY {E F : Type*} (L : ℕ → E → F → ℝ) (Y : Set F) (T : ℕ) (x : ℕ → E)
    (y : ℕ → F) : ℝ :=
  sSup ((fun y' => ∑ t ∈ Finset.Icc 1 T, L t (x t) y') '' Y) - ∑ t ∈ Finset.Icc 1 T, L t (x t) (y t)

end OnlineSaddlePoint.Supplement


