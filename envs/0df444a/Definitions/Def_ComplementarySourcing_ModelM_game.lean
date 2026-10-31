-- Prove2me | Definitions.Def_ComplementarySourcing_ModelM_game
-- name    : ComplementarySourcing_ModelM_game
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:07:42.340607+00:00
-- url     : https://prove2.me/theorems/67f5db41-b0ed-4db2-b86b-bd9a36763c73
-- title:
--   Model (M): the manufacturer moves first
-- statement:
--   The Stackelberg game in which the manufacturer chooses $(x_m,w)$ with $x_m\ge0$ and $0\le w\le r$ before the market risk is known, the market risk $\epsilon\in\{\epsilon_0+\sigma,\epsilon_0-\sigma\}$ is realized, and the supplier, seeing both, chooses $x_s\ge0$ to maximize the objective of (2). The leader's payoff is the manufacturer's expected profit.
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), p.8, eqs. (1)–(2), and p.13

import Mathlib
import Definitions.Def_ComplementarySourcing_StackelbergGame
import Definitions.Def_ComplementarySourcing_supplierStageProfit
import Definitions.Def_ComplementarySourcing_ModelM_manufacturerProfit

namespace ComplementarySourcing

/-- Model (M), manufacturer moves first. The leader's move is `(x_m, w)` with `x_m ≥ 0` and
`0 ≤ w ≤ r`, the state is `ϵ ∈ {ϵ₀ + σ, ϵ₀ − σ}`, the follower's move is the supplier's effort
`x_s ≥ 0`, its payoff is the objective of (2), and the leader's payoff is
`ModelM.manufacturerProfit`. Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), eqs. (1)–(2), p.8 (PDF 8), and
p.13 (PDF 13). -/
noncomputable def ModelM.game (μ α r ε₀ σ : ℝ) : StackelbergGame (ℝ × ℝ) ℝ ℝ where
  leaderFeasible := {a | 0 ≤ a.1 ∧ 0 ≤ a.2 ∧ a.2 ≤ r}
  followerFeasible := Set.Ici 0
  states := {ε₀ + σ, ε₀ - σ}
  followerPayoff a ε := supplierStageProfit μ α a.1 a.2 ε
  leaderPayoff a f := ModelM.manufacturerProfit μ α r ε₀ σ a.1 a.2 f

end ComplementarySourcing


