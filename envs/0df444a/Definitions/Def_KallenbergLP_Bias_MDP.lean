-- Prove2me | Definitions.Def_KallenbergLP_Bias_MDP
-- name    : KallenbergLP_Bias_MDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T10:15:22.999884+00:00
-- url     : https://prove2.me/theorems/74cefac5-8721-4715-a1a1-75c1423c445d
-- title:
--   The finite stochastic Markov decision model of Chapters 2 and 5
-- statement:
--   A **finite Markov decision model** has a nonempty finite state set $E=\{1,\ldots,N\}$, a finite nonempty admissible action set $A(i)$ at each state $i$, a transition probability $p_{iaj}$ from state $i$ to state $j$ after action $a\in A(i)$, and a real immediate reward $r_{ia}$. The probabilities satisfy
--
--   $$
--   p_{iaj}\ge 0,\qquad \sum_{j\in E}p_{iaj}=1\quad(i\in E,\ a\in A(i)).
--   $$
--
--   This is the stochastic-row convention imposed at the start of §5.2. It permits different action sets in different states and makes no sign assumption on rewards.
--
--   **Formalization Note** States are `Fin N` with $N>0$; actions come from one finite type and are restricted by a state-dependent `Finset`. The transition and reward functions have arbitrary values on inadmissible state-action pairs, which no admissible policy uses.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, pp. 19–20, Section 2.2; p. 162, Section 5.2 standing assumption; https://ir.cwi.nl/pub/13008

import Mathlib

namespace KallenbergLP.Bias

/-- The finite stochastic Markov decision model of §2.2 and the standing assumption of §5.2. -/
structure MDP (N : ℕ) (α : Type) [Fintype α] [DecidableEq α] where
  states_nonempty : 0 < N
  actions : Fin N → Finset α
  actions_nonempty : ∀ i, (actions i).Nonempty
  transition : Fin N → α → Fin N → ℝ
  transition_nonneg : ∀ i a j, a ∈ actions i → 0 ≤ transition i a j
  transition_sum_one : ∀ i a, a ∈ actions i →
    (∑ j : Fin N, transition i a j) = 1
  reward : Fin N → α → ℝ

end KallenbergLP.Bias


