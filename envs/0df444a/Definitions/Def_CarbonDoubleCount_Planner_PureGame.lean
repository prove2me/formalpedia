-- Prove2me | Definitions.Def_CarbonDoubleCount_Planner_PureGame
-- name    : CarbonDoubleCount_Planner_PureGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:46:05.265771+00:00
-- url     : https://prove2.me/theorems/01c3b620-3355-4910-915e-b536a9d68ba4
-- title:
--   Equation (4), p. 11 — pure Nash equilibrium with feasible unilateral deviations
-- statement:
--   Consider finitely many players, each with a strategy space and a feasible subset, and a real payoff for each player at every strategy profile. A **pure Nash equilibrium** is a feasible profile $s$ such that for every player $n$ and every feasible alternative $x_n$,
--   $$
--   u_n(x_n,s_{-n})\le u_n(s).
--   $$
--   The definition allows each player's strategy type to differ. It is the reusable game-theoretic relation behind the paper's decentralized effort condition (4); the paper-specific payoff and effort boxes are supplied by the following setting definition.
-- source:
--   Caro, Corbett, Tan and Zuidwijk, Double-Counting in Supply Chain Carbon Footprinting, working paper dated December 21, 2012, p. 11, equation (4); https://www.anderson.ucla.edu/documents/areas/fac/dotm/bio/pdf_FC16.pdf

import Mathlib

namespace CarbonDoubleCount.Planner

/-- A feasible pure-strategy Nash equilibrium for a dependent family of strategy spaces. -/
def IsPureNash {ι : Type} [DecidableEq ι] {strategy : ι → Type}
    (feasible : (n : ι) → Set (strategy n))
    (payoff : ι → ((n : ι) → strategy n) → ℝ)
    (s : (n : ι) → strategy n) : Prop :=
  (∀ n, s n ∈ feasible n) ∧
    ∀ n, ∀ x ∈ feasible n,
      payoff n (Function.update s n x) ≤ payoff n s

end CarbonDoubleCount.Planner


