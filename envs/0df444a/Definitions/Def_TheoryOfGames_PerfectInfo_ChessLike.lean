-- Prove2me | Definitions.Def_TheoryOfGames_PerfectInfo_ChessLike
-- name    : TheoryOfGames_PerfectInfo_ChessLike
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T02:13:30.816242+00:00
-- url     : https://prove2.me/theorems/f2269fb0-895f-4c02-837f-8d0e56ab8ca9
-- title:
--   Games without chance moves and with outcomes win, tie, loss (15.7.1)
-- statement:
--   Two properties of a game tree $\Gamma$, used for the discussion of Chess in 15.7.1.
--
--   1. $\Gamma$ has **no chance moves**: every internal node is a personal move of player 1 or player 2.
--   2. Every play has **outcome win, tie or loss**: the payoff $\mathfrak F_1(\pi)$ to player 1 at every leaf is one of the numbers $1, 0, -1$ (player 2 then receives $-1, 0, 1$).
--
--   In a game with both properties, $\mathcal H(\tau_1, \tau_2)$ is the payoff of the single play determined by $\tau_1, \tau_2$, so it also takes only the values $1, 0, -1$.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 125, 15.7.1 and footnotes 1–3

import Mathlib
import Definitions.Def_TheoryOfGames_PerfectInfo_GameTree

namespace TheoryOfGames.PerfectInfo

namespace GameTree

/-- The game contains no chance moves (as in Chess, 15.7.1). -/
def NoChanceMoves : GameTree → Prop
  | leaf _ => True
  | chance _ _ _ _ _ => False
  | move1 _ _ next => ∀ σ, NoChanceMoves (next σ)
  | move2 _ _ next => ∀ σ, NoChanceMoves (next σ)

/-- Every play's payoff `𝔉₁(π)` to player 1 is one of `1, 0, -1` ("win", "tie", "loss";
15.7.1). -/
def OutcomesWinTieLoss : GameTree → Prop
  | leaf w => w = 1 ∨ w = 0 ∨ w = -1
  | chance _ _ next _ _ => ∀ σ, OutcomesWinTieLoss (next σ)
  | move1 _ _ next => ∀ σ, OutcomesWinTieLoss (next σ)
  | move2 _ _ next => ∀ σ, OutcomesWinTieLoss (next σ)

end GameTree

end TheoryOfGames.PerfectInfo


