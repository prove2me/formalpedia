-- Prove2me | Definitions.Def_KallenbergLP_Positive_MDP
-- name    : KallenbergLP_Positive_MDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T10:15:27.491904+00:00
-- url     : https://prove2.me/theorems/38b7388a-7336-49b0-b321-0f37ce9c673e
-- title:
--   Section 2.2 — finite substochastic Markov decision system
-- statement:
--   A **finite Markov decision system** has a nonempty finite state space $E=\{1,\ldots,N\}$ and a finite, nonempty set $A(i)$ of actions in each state $i$. Choosing $a\in A(i)$ earns a real reward $r_{ia}$ and moves to state $j$ with probability $p_{iaj}\ge0$. The row sum satisfies
--   $$
--   \sum_{j\in E}p_{iaj}\le1.
--   $$
--   Missing probability represents termination of the process. Rewards have no sign restriction in this general system; the positive reward condition is imposed in the statements from Section 3.5.
--
--   This system supplies the common state, action, transition and reward data for the policy values and linear program.
--
--   **Formalization Note** States are `Fin N` with $N>0$, and $A(i)$ is a nonempty finite subset of a finite action type; different states may have different action sets. Transition conditions apply only to admissible actions.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, pp. 19–20 (PDF pp. 27–28), Section 2.2

import Mathlib

namespace KallenbergLP.Positive

/-- The finite substochastic Markov decision system of §2.2. Rewards are real;
the positive-reward restriction of §3.5 is imposed on the theorems. -/
structure MDP (N : ℕ) (α : Type) [Fintype α] [DecidableEq α] where
  states_nonempty : 0 < N
  actions : Fin N → Finset α
  actions_nonempty : ∀ i, (actions i).Nonempty
  transition : Fin N → α → Fin N → ℝ
  transition_nonneg : ∀ i a j, a ∈ actions i → 0 ≤ transition i a j
  transition_subprob : ∀ i a, a ∈ actions i →
    (∑ j : Fin N, transition i a j) ≤ 1
  reward : Fin N → α → ℝ

end KallenbergLP.Positive


