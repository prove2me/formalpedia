-- Prove2me | Definitions.Def_TheoryOfGames_PerfectInfo_backwardValue
-- name    : TheoryOfGames_PerfectInfo_backwardValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T02:07:32.234157+00:00
-- url     : https://prove2.me/theorems/17ea073a-df2b-4548-9aff-97e0336fa3f8
-- title:
--   The value formula (15:12) built from the operations $M^{k}_{\sigma}$ of (15:8)
-- statement:
--   For a function $f(\sigma_1)$ of the alternatives $\sigma_1 = 1, \dots, \alpha_1$ of the first move $\mathfrak M_1$, of kind $k_1$, the operations of (15:8) are
--   $$M^{k_1}_{\sigma_1} f(\sigma_1) = \begin{cases} \sum_{\sigma_1=1}^{\alpha_1} p_1(\sigma_1) f(\sigma_1) & k_1 = 0 \text{ (chance move)},\\ \operatorname{Max}_{\sigma_1} f(\sigma_1) & k_1 = 1 \text{ (move of player 1)},\\ \operatorname{Min}_{\sigma_1} f(\sigma_1) & k_1 = 2 \text{ (move of player 2)}.\end{cases}$$
--   The **backward-induction value** of a game tree $\Gamma$ is the number obtained by applying these operations from the last move to the first, as in (15:12):
--   $$v = M^{k_1}_{\sigma_1} M^{k_2(\sigma_1)}_{\sigma_2} \cdots M^{k_\nu(\sigma_1, \dots, \sigma_{\nu-1})}_{\sigma_\nu} \mathfrak F_1(\pi(\sigma_1, \dots, \sigma_\nu)).$$
--   Recursively: at a leaf it is the payoff $w$; at a chance move it is $\sum_{\sigma} p(\sigma)\, v(\Gamma_\sigma)$; at a move of player 1 it is $\operatorname{Max}_\sigma v(\Gamma_\sigma)$; at a move of player 2, $\operatorname{Min}_\sigma v(\Gamma_\sigma)$.
--
--   This is the explicit formula for the value of a game with perfect information.
--
--   **Formalization Note** Defined by structural recursion on the tree; Max and Min over the $\alpha \geqq 1$ alternatives are `Finset.sup'`, `Finset.inf'`. Plays of different lengths are allowed (see the game-tree definition).
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 122, (15:8); p. 124, (15:10)–(15:12)

import Mathlib
import Definitions.Def_TheoryOfGames_PerfectInfo_GameTree

namespace TheoryOfGames.PerfectInfo

namespace GameTree

/-- The value given by the formula (15:12): the operations `M^{k}_{σ}` of (15:8) applied from the
last move back to the first — the expectation `∑ σ, p σ * f σ` at a chance move (`k = 0`),
`Max_σ f σ` at a personal move of player 1 (`k = 1`), `Min_σ f σ` at a personal move of
player 2 (`k = 2`) — and the payoff `𝔉₁(π)` of the play at a leaf. -/
noncomputable def backwardValue : GameTree → ℝ
  | leaf w => w
  | chance _ p next _ _ => ∑ σ, p σ * backwardValue (next σ)
  | move1 α hα next =>
      Finset.univ.sup' ⟨⟨0, hα⟩, Finset.mem_univ _⟩ fun σ : Fin α => backwardValue (next σ)
  | move2 α hα next =>
      Finset.univ.inf' ⟨⟨0, hα⟩, Finset.mem_univ _⟩ fun σ : Fin α => backwardValue (next σ)

end GameTree

end TheoryOfGames.PerfectInfo


