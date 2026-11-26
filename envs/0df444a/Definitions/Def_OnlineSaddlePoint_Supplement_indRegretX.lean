-- Prove2me | Definitions.Def_OnlineSaddlePoint_Supplement_indRegretX
-- name    : OnlineSaddlePoint_Supplement_indRegretX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T21:52:13.552688+00:00
-- url     : https://prove2.me/theorems/b996170d-c918-4c29-916f-a3ee068acfd6
-- title:
--   Individual regret of player 1, (2a)/(12)
-- statement:
--   Let $\mathcal L_1,\dots,\mathcal L_T$ be payoff functions and $(x_t,y_t)$, $t=1,\dots,T$, the actions played. The **individual regret** of the minimizing player is
--
--   $$
--   \sum_{t=1}^T\mathcal L_t(x_t,y_t)-\min_{x\in X}\sum_{t=1}^T\mathcal L_t(x,y_t),
--   $$
--
--   the loss of player 1 relative to the best fixed action in hindsight, with player 2's actions held fixed. In §6 it is display (12) with $\mathcal L_t(x,y)=x^\top A_t y$.
--
--   **Formalization Note** The minimum is `sInf` of the image of $X$ in $\mathbb R$ (attained for continuous payoffs on a nonempty compact $X$).
-- source:
--   Rivera Cardoso, Wang, Xu, The Online Saddle Point Problem and Online Convex Optimization with Knapsacks, arXiv:1806.08301v3, display (2a), p.2; display (12), p.27

import Mathlib

namespace OnlineSaddlePoint.Supplement

/-- **Individual regret of player 1** (the minimizing player). Rivera Cardoso, Wang, Xu,
arXiv:1806.08301v3, display (2a), p.2:
`∑_{t=1}^T 𝓛_t(x_t, y_t) − min_{x∈X} ∑_{t=1}^T 𝓛_t(x, y_t)`; in §6, display (12), p.27, with
`𝓛_t(x, y) = xᵀA_t y`.

**Formalization Note.** The `min` is `sInf` of the image of `X` in `ℝ` (attained when `X` is nonempty
and compact and the payoffs are continuous, e.g. bilinear on a simplex). Played actions are sequences
read at rounds `1, …, T`; index `0` is unused. -/
noncomputable def indRegretX {E F : Type*} (L : ℕ → E → F → ℝ) (X : Set E) (T : ℕ) (x : ℕ → E)
    (y : ℕ → F) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, L t (x t) (y t) - sInf ((fun x' => ∑ t ∈ Finset.Icc 1 T, L t x' (y t)) '' X)

end OnlineSaddlePoint.Supplement


