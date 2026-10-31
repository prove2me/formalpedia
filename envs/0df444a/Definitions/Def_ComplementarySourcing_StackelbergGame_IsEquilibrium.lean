-- Prove2me | Definitions.Def_ComplementarySourcing_StackelbergGame_IsEquilibrium
-- name    : ComplementarySourcing_StackelbergGame_IsEquilibrium
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:07:29.588408+00:00
-- url     : https://prove2.me/theorems/995c02f0-d63a-4283-a667-7bafe6279d60
-- title:
--   Subgame-perfect equilibrium of a Stackelberg game
-- statement:
--   A pair $(s,a)$ is an equilibrium when $s$ is a follower strategy, $a$ is feasible, and $u_L(a',s(a',\cdot))\le u_L(a,s(a,\cdot))$ for every feasible leader move $a'$.
--
--   This is the solution concept of problems (1)–(2): the leader optimizes against the follower's best responses.
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), p.8, eqs. (1)–(2)

import Mathlib
import Definitions.Def_ComplementarySourcing_StackelbergGame_IsFollowerStrategy

namespace ComplementarySourcing

/-- A subgame-perfect equilibrium `(s, a)`: `s` is a follower strategy best-responding everywhere,
and `a` is feasible and maximizes the leader's payoff anticipating `s`. Problems (1)–(2) of
Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), p.8 (PDF 8). -/
def StackelbergGame.IsEquilibrium {L F Ω : Type*} (G : StackelbergGame L F Ω)
    (s : L → Ω → F) (a : L) : Prop :=
  G.IsFollowerStrategy s ∧ a ∈ G.leaderFeasible ∧
    ∀ a' ∈ G.leaderFeasible, G.leaderPayoff a' (s a') ≤ G.leaderPayoff a (s a)

end ComplementarySourcing


