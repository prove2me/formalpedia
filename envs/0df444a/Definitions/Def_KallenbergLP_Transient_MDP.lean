-- Prove2me | Definitions.Def_KallenbergLP_Transient_MDP
-- name    : KallenbergLP_Transient_MDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T09:42:14.127161+00:00
-- url     : https://prove2.me/theorems/e4c7762c-5897-417e-8cd0-6ac8192482fd
-- title:
--   Finite substochastic Markov decision system
-- statement:
--   A finite state space $E$ has $N>0$ states. Each state $i$ has a nonempty finite set $A(i)$ of admissible actions. The transition numbers satisfy
--
--   $$p_{iaj}\ge 0,\qquad \sum_{j\in E}p_{iaj}\le 1\quad(a\in A(i)).$$
--
--   Missing probability mass represents termination of the process. This dynamics-only object is shared by the total reward and transience criteria in the chapter; rewards are supplied separately when needed.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 20, Section 2.2

import Mathlib
set_option autoImplicit false

namespace KallenbergLP.Transient

/-- The finite substochastic Markov decision system of §2.2, without a reward criterion. -/
structure MDP (N : ℕ) (α : Type) [Fintype α] [DecidableEq α] where
  states_nonempty : 0 < N
  actions : Fin N → Finset α
  actions_nonempty : ∀ i, (actions i).Nonempty
  transition : Fin N → α → Fin N → ℝ
  transition_nonneg : ∀ i a j, a ∈ actions i → 0 ≤ transition i a j
  transition_subprob : ∀ i a, a ∈ actions i →
    (∑ j : Fin N, transition i a j) ≤ 1

end KallenbergLP.Transient


