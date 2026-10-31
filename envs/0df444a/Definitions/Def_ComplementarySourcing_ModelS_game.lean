-- Prove2me | Definitions.Def_ComplementarySourcing_ModelS_game
-- name    : ComplementarySourcing_ModelS_game
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:07:48.074016+00:00
-- url     : https://prove2.me/theorems/891b58b6-7995-4add-b68f-de6a97bb7c17
-- title:
--   Model (S): the supplier moves first
-- statement:
--   The Stackelberg game in which the supplier chooses $(x_s,w)$ with $x_s\ge0$ and $0\le w\le r$ before the market risk is known, the market risk $\epsilon\in\{\epsilon_0+\sigma,\epsilon_0-\sigma\}$ is realized, and the manufacturer, seeing both, chooses $x_m\ge0$ to maximize $(r-w)d-\tfrac12x_m^2$. The leader's payoff is the supplier's expected profit.
--
--   The game is defined directly, not by relabeling Model (M).
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), p.14

import Mathlib
import Definitions.Def_ComplementarySourcing_StackelbergGame
import Definitions.Def_ComplementarySourcing_manufacturerStageProfit
import Definitions.Def_ComplementarySourcing_ModelS_supplierProfit

namespace ComplementarySourcing

/-- Model (S), supplier moves first. The leader's move is `(x_s, w)` with `x_s ≥ 0` and
`0 ≤ w ≤ r`, the state is `ϵ ∈ {ϵ₀ + σ, ϵ₀ − σ}`, the follower's move is the manufacturer's effort
`x_m ≥ 0` with payoff `(r − w) d − ½ x_m²`, and the leader's payoff is `ModelS.supplierProfit`.
Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), p.14 (PDF 14). -/
noncomputable def ModelS.game (μ α r ε₀ σ : ℝ) : StackelbergGame (ℝ × ℝ) ℝ ℝ where
  leaderFeasible := {a | 0 ≤ a.1 ∧ 0 ≤ a.2 ∧ a.2 ≤ r}
  followerFeasible := Set.Ici 0
  states := {ε₀ + σ, ε₀ - σ}
  followerPayoff a ε := manufacturerStageProfit μ α r a.1 a.2 ε
  leaderPayoff a f := ModelS.supplierProfit μ α ε₀ σ a.1 a.2 f

end ComplementarySourcing


