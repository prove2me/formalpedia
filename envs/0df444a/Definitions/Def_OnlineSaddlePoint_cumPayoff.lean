-- Prove2me | Definitions.Def_OnlineSaddlePoint_cumPayoff
-- name    : OnlineSaddlePoint_cumPayoff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:12:13.331907+00:00
-- url     : https://prove2.me/theorems/066a7fce-a912-42dd-a5ec-3d6bd0859509
-- title:
--   Cumulative payoff $\sum_{\tau=1}^t \mathcal L_\tau(x,y)$
-- statement:
--   Let $\mathcal L_1,\mathcal L_2,\dots$ be the payoff functions revealed in rounds $1,2,\dots$ of the online saddle point problem, each a function of the minimizing player's action $x$ and the maximizing player's action $y$. The **cumulative payoff** after $t$ rounds is
--
--   $$
--   \sum_{\tau=1}^{t}\mathcal L_\tau(x,y),
--   $$
--
--   the sum of the games observed so far. For $t=0$ it is the zero function.
--
--   It is the game that Saddle-Point Follow-the-Leader solves in every round, and the game whose min-max value defines the saddle-point regret.
--
--   **Formalization Note** The payoffs are a sequence `L : ℕ → E → F → ℝ` indexed from $1$ (index $0$ is unused); each $\mathcal L_\tau$ is given on all of $E\times F$, and only its values on $X\times Y$ are ever used.
-- source:
--   Rivera Cardoso, Wang, Xu, The Online Saddle Point Problem and Online Convex Optimization with Knapsacks, arXiv:1806.08301v3, Algorithm 1, p.6; display (1), p.2

import Mathlib

namespace OnlineSaddlePoint

/-- **Cumulative payoff** `∑_{τ=1}^t 𝓛_τ(x, y)`, the sum of the games observed in rounds
`1, …, t`. Rivera Cardoso, Wang, Xu, *The Online Saddle Point Problem and Online Convex
Optimization with Knapsacks*, arXiv:1806.08301v3, p.2, display (1), and Algorithm 1, p.6
("arg min_{x∈X} max_{y∈Y} ∑_{τ=1}^t 𝓛_τ(x, y)").

**Formalization Note.** The payoff sequence is `L : ℕ → E → F → ℝ`, with `L τ` the paper's `𝓛_τ`
for rounds `τ = 1, 2, …`; index `0` is never used. Each `𝓛_τ` is given on all of `E × F`, and only
its values on `X × Y` enter any statement. For `t = 0` the sum is empty and equals `0`. -/
def cumPayoff {E F : Type*} (L : ℕ → E → F → ℝ) (t : ℕ) (x : E) (y : F) : ℝ :=
  ∑ τ ∈ Finset.Icc 1 t, L τ x y

end OnlineSaddlePoint


