-- Prove2me | Definitions.Def_ImpulseGames_LinearGame_Equilibrium
-- name    : ImpulseGames_LinearGame_Equilibrium
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T01:27:56.973605+00:00
-- url     : https://prove2.me/theorems/fe142a50-8eb5-439d-8d4b-8df082c62f80
-- title:
--   The candidate equilibrium strategies $(]\bar x_1,+\infty[,\delta_1)$ and $(]-\infty,\bar x_2[,\delta_2)$ of Proposition 4.7
-- statement:
--   For $\xi$ and $\tilde s$ as in the candidates file, the strategies of Proposition 4.7 are
--   $$\varphi_1^*=(\mathcal C_1^*,\delta_1),\quad \mathcal C_1^*=]\bar x_1,+\infty[,\qquad \varphi_2^*=(\mathcal C_2^*,\delta_2),\quad \mathcal C_2^*=]-\infty,\bar x_2[,$$
--   with $\delta_1(y)=\max(x_1^*-y,0)$ and $\delta_2(y)=\min(x_2^*-y,0)$. The regions are open and the impulse maps are continuous with values in $Z_1=[0,\infty[$ and $Z_2=]-\infty,0]$, so these are strategies in the sense of Definition 2.1. Player 1 pushes the state up to $x_1^*$ whenever it is at or below $\bar x_1$, player 2 pushes it down to $x_2^*$ whenever it is at or above $\bar x_2$.
--
--   **Formalization Note.** The paper writes $\xi_1^*(y)=x_1^*-y$ and $\xi_2^*(y)=x_2^*-y$; these are not $Z_i$-valued on the whole line. They are replaced by $\delta_1,\delta_2$ of (4.23), which coincide with them where each player acts ($y\le\bar x_1<x_1^*$, resp. $y\ge\bar x_2>x_2^*$), so the controlled process is unchanged.
-- source:
--   Aïd et al. (2020), Math. Oper. Res. 45(1), accepted manuscript, Proposition 4.7 (p. 18) and (4.23) (p. 17)

import Mathlib
import Definitions.Def_ImpulseGames_LinearGame_Game
import Definitions.Def_ImpulseGames_LinearGame_Candidates

namespace ImpulseGames.LinearGame

/-- Player 1's candidate equilibrium strategy of Proposition 4.7: continuation region
`𝒞₁* = ]x̄₁, +∞[` and impulse `δ₁(y) = max(x₁* − y, 0)` (which equals `x₁* − y` wherever player 1
acts, i.e. on `]−∞, x̄₁] ⊆ ]−∞, x₁*]`). -/
noncomputable def eqStrat1 (M : Model) (ξ s : ℝ) : Strategy Z₁ where
  C := Set.Ioi (xbar M ξ s 1)
  isOpen_C := isOpen_Ioi
  ξ := delta1 M ξ s
  continuous_ξ := by unfold delta1; fun_prop
  mem_Z := fun _ => by simp only [Z₁, delta1, Set.mem_Ici]; exact le_max_right _ _

/-- Player 2's candidate equilibrium strategy of Proposition 4.7: continuation region
`𝒞₂* = ]−∞, x̄₂[` and impulse `δ₂(y) = min(x₂* − y, 0)` (which equals `x₂* − y` wherever player 2
acts, i.e. on `[x̄₂, +∞[ ⊆ [x₂*, +∞[`). -/
noncomputable def eqStrat2 (M : Model) (ξ s : ℝ) : Strategy Z₂ where
  C := Set.Iio (xbar M ξ s 2)
  isOpen_C := isOpen_Iio
  ξ := delta2 M ξ s
  continuous_ξ := by unfold delta2; fun_prop
  mem_Z := fun _ => by simp only [Z₂, delta2, Set.mem_Iic]; exact min_le_right _ _

end ImpulseGames.LinearGame


