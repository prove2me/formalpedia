-- Prove2me | Definitions.Def_KallenbergLP_OptTransient_FiniteMDP
-- name    : KallenbergLP_OptTransient_FiniteMDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T09:57:22.891033+00:00
-- url     : https://prove2.me/theorems/28cf2744-6d02-42fe-9425-077af8c11250
-- title:
--   Finite substochastic Markov decision model
-- statement:
--   A finite Markov decision model has a nonempty state set $E=\{1,\ldots,N\}$ and, for each state $i$, a finite nonempty action set $A(i)$. Choosing $a\in A(i)$ earns a real reward $r_{ia}$ and moves to state $j$ with probability $p_{iaj}\ge0$. The transition row may lose mass, representing termination:
--
--   $$
--   \sum_{j\in E}p_{iaj}\le1.
--   $$
--
--   This general model supplies the state, action, transition and reward data used throughout the chapter. Action sets may differ by state. **Formalization Note** States are `Fin N`; the model requires $N>0$, and a state-action pair is a dependent pair carrying a proof that its action is available.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, pp. 19–20, Section 2.2; https://ir.cwi.nl/pub/13008

import Mathlib

namespace KallenbergLP.OptTransient

/-- A finite Markov decision model with termination: transition rows may have mass below one. -/
structure FiniteSubstochasticMDP (n : ℕ) (α : Type) [Fintype α] [DecidableEq α] where
  n_pos : 0 < n
  actions : Fin n → Finset α
  actions_nonempty : ∀ i, (actions i).Nonempty
  transition : Fin n → α → Fin n → ℝ
  transition_nonneg : ∀ i a j, a ∈ actions i → 0 ≤ transition i a j
  transition_sum_le_one : ∀ i a, a ∈ actions i → ∑ j, transition i a j ≤ 1
  reward : Fin n → α → ℝ

/-- Feasible state-action pairs of a finite decision model. -/
abbrev StateAction {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (m : FiniteSubstochasticMDP n α) : Type :=
  Σ i : Fin n, {a : α // a ∈ m.actions i}

end KallenbergLP.OptTransient


