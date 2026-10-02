-- Prove2me | Definitions.Def_TheoryOfGames_PerfectInfo_Values
-- name    : TheoryOfGames_PerfectInfo_Values
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T01:59:28.768162+00:00
-- url     : https://prove2.me/theorems/145f7d3e-5696-48ef-9748-cdc5a2199c39
-- title:
--   The quantities $v_1$, $v_2$ and strict determinateness (14.4.1–14.4.2)
-- statement:
--   Let $\Gamma$ be a finite game tree with normalized form $\mathcal H(\tau_1, \tau_2)$. Define
--   $$v_1 = \operatorname{Max}_{\tau_1} \operatorname{Min}_{\tau_2} \mathcal H(\tau_1, \tau_2), \qquad v_2 = \operatorname{Min}_{\tau_2} \operatorname{Max}_{\tau_1} \mathcal H(\tau_1, \tau_2),$$
--   the maxima and minima being taken over the finitely many pure strategies of each player, so they are attained. $v_1$ is what player 1 can secure when his strategy is "found out" by player 2, and $v_2$ what he obtains when he "finds out" player 2's strategy.
--
--   The game $\Gamma$ is **strictly determined** if $v_1 = v_2$, i.e.
--   $$\operatorname{Max}_{\tau_1} \operatorname{Min}_{\tau_2} \mathcal H(\tau_1, \tau_2) = \operatorname{Min}_{\tau_2} \operatorname{Max}_{\tau_1} \mathcal H(\tau_1, \tau_2).$$
--
--   These are the quantities whose equality is the main result of §15 for games with perfect information.
--
--   **Formalization Note** $\operatorname{Max}$ and $\operatorname{Min}$ are `Finset.sup'` and `Finset.inf'` over `Finset.univ`, which is nonempty because each player has a strategy; no junk value arises.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), pp. 105–106, 14.4.1, 14.4.2

import Mathlib
import Definitions.Def_TheoryOfGames_PerfectInfo_Strategy

namespace TheoryOfGames.PerfectInfo

namespace GameTree

/-- `v₁ = Max_{τ₁} Min_{τ₂} ℋ(τ₁, τ₂)` (14.4.1): the maximum over player 1's pure strategies of
the minimum over player 2's pure strategies of the normalized form. Both extrema are over
finite nonempty sets, hence attained. -/
noncomputable def v1 (t : GameTree) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun τ₁ : Strategy1 t =>
    Finset.univ.inf' Finset.univ_nonempty fun τ₂ : Strategy2 t => payoff t τ₁ τ₂

/-- `v₂ = Min_{τ₂} Max_{τ₁} ℋ(τ₁, τ₂)` (14.4.1). -/
noncomputable def v2 (t : GameTree) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun τ₂ : Strategy2 t =>
    Finset.univ.sup' Finset.univ_nonempty fun τ₁ : Strategy1 t => payoff t τ₁ τ₂

/-- The game is *strictly determined* (14.5.1) when `v₁ = v₂`. -/
def IsStrictlyDetermined (t : GameTree) : Prop := v1 t = v2 t

end GameTree

end TheoryOfGames.PerfectInfo


