-- Prove2me | Definitions.Def_UniformPatrol_Star_ZeroSum
-- name    : UniformPatrol_Star_ZeroSum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:13:20.699534+00:00
-- url     : https://prove2.me/theorems/7390a875-b1d5-4583-ad63-a8abc60ca6d2
-- title:
--   Pure saddle point of a real two-player payoff
-- statement:
--   For any two pure-strategy sets $P$ and $A$ and real payoff $G:P\times A\to\mathbb R$, a pair $(x,a)$ is a **saddle point** when
--
--   $$G(x',a)\leq G(x,a)\leq G(x,a')\qquad\text{for all }x'\in P,\ a'\in A.$$
--
--   The first player maximizes and the second minimizes. This generic predicate supplies the optimality convention for the patrolling game and can be reused for other zero-sum games.
-- source:
--   Alpern, Chleboun, Katsikas, The Uniformed Patroller Game, arXiv:1908.07366v2, p. 10 (PDF 11), proof of Theorem 1

import Mathlib

namespace UniformPatrol.Star

/-- A pure saddle point for a real payoff, maximized by the first player and minimized by the second. -/
def PureSaddle {P A : Type} (payoff : P → A → ℝ) (x : P) (a : A) : Prop :=
  (∀ x' : P, payoff x' a ≤ payoff x a) ∧
  (∀ a' : A, payoff x a ≤ payoff x a')

end UniformPatrol.Star


