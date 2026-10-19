-- Prove2me | Definitions.Def_CollabProject_TimeDep_Game
-- name    : CollabProject_TimeDep_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:24:28.047903+00:00
-- url     : https://prove2.me/theorems/e2538572-6a67-493b-8949-9a7098f9efc7
-- title:
--   Two-stage sequential game and subgame-perfect equilibrium
-- statement:
--   A **two-stage sequential game** has two action sets. Player 1 chooses an action first; player 0 observes it and then chooses an action. Each player has a real payoff for every action pair. A strategy for player 0 specifies an action after every possible first move.
--
--   Player 0's action is a best response when it maximizes that player's payoff at the observed first move. A **subgame-perfect equilibrium** consists of a first move and a complete second-stage strategy such that the strategy best-responds after either first move and player 1's first move maximizes payoff against that strategy.
--
--   This general interface is reusable for finite sequential games. The paper's particular supplier–manufacturer payoffs are defined separately.
-- source:
--   Song, Zhao & Xu, Incentives and Gaming in Collaborative Projects under Risk Sharing Partnerships, SSRN preprint (abstract 2980139, PDF of 2019-10-14; published in Manufacturing & Service Operations Management, 2020), p. 10 (PDF 10), §4 opening (sequence of moves); Appendix p. 1 (PDF 33), Figure 5b (extensive form)

import Mathlib

namespace CollabProject.TimeDep

/-- A two-stage perfect-information game: player 1 moves, then player 0 observes
that move and responds. -/
structure SequentialGame (A1 A0 : Type) where
  payoff1 : A1 → A0 → ℝ
  payoff0 : A1 → A0 → ℝ

/-- Player 0's best response at a specified player-1 action. -/
def SequentialGame.IsBR0 {A1 A0 : Type} (v0 : A1 → A0 → ℝ)
    (a1 : A1) (a0 : A0) : Prop :=
  ∀ b : A0, v0 a1 b ≤ v0 a1 a0

/-- Subgame-perfect equilibrium for the two-stage game. The follower's strategy
is specified at every possible first-stage action. -/
def SequentialGame.IsSPNE {A1 A0 : Type} (G : SequentialGame A1 A0)
    (a1 : A1) (σ0 : A1 → A0) : Prop :=
  (∀ a : A1, SequentialGame.IsBR0 G.payoff0 a (σ0 a)) ∧
    ∀ b : A1, G.payoff1 b (σ0 b) ≤ G.payoff1 a1 (σ0 a1)

end CollabProject.TimeDep


