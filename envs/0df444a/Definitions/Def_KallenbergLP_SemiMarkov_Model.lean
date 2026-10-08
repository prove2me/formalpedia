-- Prove2me | Definitions.Def_KallenbergLP_SemiMarkov_Model
-- name    : KallenbergLP_SemiMarkov_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T10:35:46.125142+00:00
-- url     : https://prove2.me/theorems/1c00f1b9-cfde-4a20-8d7e-aac44b6e0e86
-- title:
--   Chapter 7 finite semi-Markov decision model
-- statement:
--   Let $E$ be a nonempty finite state set and $A(i)$ a finite nonempty action set at each state $i$. Choosing $a\in A(i)$ sends the process to $j$ with probability $p_{iaj}$, where $p_{iaj}\geq0$ and $\sum_j p_{iaj}=1$. Conditional on that next state, the nonnegative sojourn time has distribution $F_{iaj}$. The epoch earns a lump reward $r_{ia}$ and a reward rate $s_{ia}$ until the next decision.
--
--   This is the general semi-Markov decision model for Chapter 7. It permits different action sets by state and arbitrary nonnegative holding-time distributions, including atoms at zero.
--
--   **Formalization Note** The state and action carriers are finite types. Each $F_{iaj}$ is a probability measure on $\mathbb R$ with no mass on negative times.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, pp. 210–211, Section 7.1, https://ir.cwi.nl/pub/13008

import Mathlib

namespace KallenbergLP.SemiMarkov

open MeasureTheory

/-- The finite semi-Markov decision model of Chapter 7, before a reward criterion is chosen.
Actions can depend on the current state. The holding-time law is conditional on both the
chosen action and the next state and may have an atom at zero. -/
structure Model (S U : Type*) [Fintype S] [Nonempty S] [Fintype U] where
  actions : S → Finset U
  actions_nonempty : ∀ i, (actions i).Nonempty
  p : S → U → S → ℝ
  p_nonneg : ∀ i a j, a ∈ actions i → 0 ≤ p i a j
  p_sum : ∀ i a, a ∈ actions i → ∑ j, p i a j = 1
  F : S → U → S → Measure ℝ
  F_prob : ∀ i a j, a ∈ actions i → IsProbabilityMeasure (F i a j)
  F_nonneg : ∀ i a j, a ∈ actions i → F i a j (Set.Iio 0) = 0
  r : S → U → ℝ
  s : S → U → ℝ

end KallenbergLP.SemiMarkov


