-- Prove2me | Definitions.Def_MultitierCSR_Strategy_SequentialEffortGame
-- name    : MultitierCSR_Strategy_SequentialEffortGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:39.13697+00:00
-- url     : https://prove2.me/theorems/22f7ee00-cff6-4375-8875-0696ee82d678
-- title:
--   Sequential three-player effort game
-- statement:
--   A sequential effort game has three players, numbered 0, 1 and 2, whose efforts are nonnegative real numbers. Player 0 moves first, player 1 observes that choice, and player 2 observes both earlier choices. Each player has a real-valued profit function of all three efforts.
--
--   A strategy for player 2 is a best response when it maximizes player 2's profit after every feasible pair of earlier efforts. A strategy for player 1 is a best response when it maximizes player 1's profit after every feasible player 0 effort, anticipating player 2's strategy. Player 0 maximizes its resulting profit over all nonnegative efforts. If zero and a positive effort tie, the positive effort is selected.
--
--   This interface separates the sequential optimization problem from the supply chain's particular profit formula.
-- source:
--   Huang, Song & Swinney, Managing Social Responsibility in Multitier Supply Chains, SSRN 2837332 (version of October 2021), pp. 10–12 (PDF 10–12), §3.2 and the tie convention on p. 12

import Mathlib

namespace MultitierCSR.Strategy

/-- A three-player sequential game with nonnegative real efforts. Player 0 moves first,
player 1 observes that choice, and player 2 observes both earlier choices. -/
structure SequentialEffortGame where
  profit0 : ℝ → ℝ → ℝ → ℝ
  profit1 : ℝ → ℝ → ℝ → ℝ
  profit2 : ℝ → ℝ → ℝ → ℝ

/-- A strategy for the last mover maximizes its payoff after every feasible history. -/
def SequentialEffortGame.IsBestResponse2 (G : SequentialEffortGame)
    (σ2 : ℝ → ℝ → ℝ) : Prop :=
  ∀ x0 x1, 0 ≤ x0 → 0 ≤ x1 →
    0 ≤ σ2 x0 x1 ∧
    ∀ y, 0 ≤ y → G.profit2 x0 x1 y ≤ G.profit2 x0 x1 (σ2 x0 x1)

/-- Player 1 maximizes its payoff, anticipating the last mover's strategy. -/
def SequentialEffortGame.IsBestResponse1 (G : SequentialEffortGame)
    (σ2 : ℝ → ℝ → ℝ) (σ1 : ℝ → ℝ) : Prop :=
  ∀ x0, 0 ≤ x0 →
    0 ≤ σ1 x0 ∧
    ∀ y, 0 ≤ y →
      G.profit1 x0 y (σ2 x0 y) ≤
        G.profit1 x0 (σ1 x0) (σ2 x0 (σ1 x0))

/-- The first mover's payoff after the two subsequent strategies respond. -/
def SequentialEffortGame.buyerProfit (G : SequentialEffortGame)
    (σ2 : ℝ → ℝ → ℝ) (σ1 : ℝ → ℝ) (x0 : ℝ) : ℝ :=
  G.profit0 x0 (σ1 x0) (σ2 x0 (σ1 x0))

/-- A maximizing first move, with positive effort selected over zero on a tie. -/
def SequentialEffortGame.IsBuyerOptimal (G : SequentialEffortGame)
    (σ2 : ℝ → ℝ → ℝ) (σ1 : ℝ → ℝ) (x0 : ℝ) : Prop :=
  0 ≤ x0 ∧
    (∀ y, 0 ≤ y → G.buyerProfit σ2 σ1 y ≤ G.buyerProfit σ2 σ1 x0) ∧
    (x0 = 0 → ∀ y, 0 < y → G.buyerProfit σ2 σ1 y < G.buyerProfit σ2 σ1 0)

end MultitierCSR.Strategy


