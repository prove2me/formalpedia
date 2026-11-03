-- Prove2me | Definitions.Def_OnlineSaddlePoint_spRegret
-- name    : OnlineSaddlePoint_spRegret
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:12:55.789098+00:00
-- url     : https://prove2.me/theorems/384f4853-1cc8-471a-a143-22979954a673
-- title:
--   Saddle-point regret $\mathrm{SP\text{-}Regret}(T)$
-- statement:
--   Let $(x_t,y_t)$, $t=1,\dots,T$, be the actions played by the two players in the online saddle point problem, with payoffs $\mathcal L_1,\dots,\mathcal L_T$ on $X\times Y$. The **saddle-point regret** is
--
--   $$
--   \mathrm{SP\text{-}Regret}(T)=\Big|\sum_{t=1}^{T}\mathcal L_t(x_t,y_t)-\min_{x\in X}\max_{y\in Y}\sum_{t=1}^{T}\mathcal L_t(x,y)\Big|.
--   $$
--
--   It measures the gap between the cumulative value achieved online and the value of the game, under the Nash equilibrium, that would be played if all payoffs were known in hindsight.
--
--   **Formalization Note** The actions are sequences indexed from $1$ (index $0$ is unused); the min-max term is the min-max value of the cumulative payoff after $T$ rounds.
-- source:
--   Rivera Cardoso, Wang, Xu, The Online Saddle Point Problem and Online Convex Optimization with Knapsacks, arXiv:1806.08301v3, display (1), p.2

import Mathlib
import Definitions.Def_OnlineSaddlePoint_cumPayoff
import Definitions.Def_OnlineSaddlePoint_minimaxValue

namespace OnlineSaddlePoint

/-- **Saddle-point regret** (SP-Regret). Rivera Cardoso, Wang, Xu, arXiv:1806.08301v3, p.2,
display (1):
`SP-Regret(T) = | ∑_{t=1}^T 𝓛_t(x_t, y_t) − min_{x∈X} max_{y∈Y} ∑_{t=1}^T 𝓛_t(x, y) |`.

**Formalization Note.** The played actions are sequences `x : ℕ → E`, `y : ℕ → F` read at rounds
`1, …, T` (index `0` is unused). The min-max term is `minimaxValue X Y (cumPayoff L T)`. -/
noncomputable def spRegret {E F : Type*} (L : ℕ → E → F → ℝ) (X : Set E) (Y : Set F) (T : ℕ)
    (x : ℕ → E) (y : ℕ → F) : ℝ :=
  |∑ t ∈ Finset.Icc 1 T, L t (x t) (y t) - minimaxValue X Y (cumPayoff L T)|

end OnlineSaddlePoint


