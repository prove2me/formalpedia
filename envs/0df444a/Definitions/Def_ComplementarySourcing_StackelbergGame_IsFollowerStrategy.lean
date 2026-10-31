-- Prove2me | Definitions.Def_ComplementarySourcing_StackelbergGame_IsFollowerStrategy
-- name    : ComplementarySourcing_StackelbergGame_IsFollowerStrategy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:06:32.891994+00:00
-- url     : https://prove2.me/theorems/1056f20d-200a-4f0a-b216-4b262f17aca6
-- title:
--   Follower strategy: best response in every subgame
-- statement:
--   A map $s$ from leader moves and states to follower moves is a follower strategy when $s(a,\omega)$ is a best response to $(a,\omega)$ for every feasible leader move $a$ and every state $\omega$, on and off the equilibrium path.
--
--   This is the meaning of the leader anticipating the follower's best response.
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), p.13

import Mathlib
import Definitions.Def_ComplementarySourcing_StackelbergGame
import Definitions.Def_ComplementarySourcing_IsBestResponse

namespace ComplementarySourcing

/-- `s` best-responds at every feasible leader move and every state, on and off the equilibrium
path: subgame perfection, which is what "anticipating the supplier's best response" means in
Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), p.13 (PDF 13). -/
def StackelbergGame.IsFollowerStrategy {L F Ω : Type*} (G : StackelbergGame L F Ω)
    (s : L → Ω → F) : Prop :=
  ∀ a ∈ G.leaderFeasible, ∀ ω ∈ G.states,
    IsBestResponse G.followerFeasible (G.followerPayoff a ω) (s a ω)

end ComplementarySourcing


