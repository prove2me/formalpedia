-- Prove2me | Definitions.Def_MarkovEntanglementExact_IsFeasibleKernel
-- name    : MarkovEntanglementExact_IsFeasibleKernel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:20:06.887044+00:00
-- url     : https://prove2.me/theorems/0f4222ef-3382-43c7-9d49-6a86b3f84b57
-- title:
--   Transition kernel of a finite MDP with feasible action sets
-- statement:
--   Let $S$ be a finite state set and, for each state $s$, let $\mathcal A(s)$ be the set of actions feasible at $s$. A **transition kernel** assigns to each state $s$, feasible action $a\in\mathcal A(s)$ and next state $s'$ a number $P(s'\mid s,a)$ with
--   $$P(s'\mid s,a)\ge 0,\qquad \sum_{s'}P(s'\mid s,a)=1.$$
--
--   This is the dynamics of the two-agent MDP of the paper, with $S=S_A\times S_B$ and $\mathcal A(s)=\mathcal A_A(s_A)\times\mathcal A_B(s_B)$. Feasible sets depending on the state are what footnote 1 of the paper uses to remove pairs that are never played.
--
--   **Formalization Note** The action sets are a family `A : S → Type*`. The constant action set of the paper is the case `A := fun _ => A₀`.
-- source:
--   Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, §2, pp.6–7, and footnote 1, p.8

import Mathlib

open scoped BigOperators

namespace MarkovEntanglementExact

/-- A transition kernel of a finite MDP with feasible action sets: `kernel s a s'` is
`P(s' | s, a)` for a state `s`, a feasible action `a : A s` and a next state `s'`. Each entry is
nonnegative and each row `(s, a)` sums to one.

Source: Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, §2, pp.6–7, with the
feasible action set `𝒜(s_A)` of footnote 1, p.8.

**Formalization Note.** Actions are a family `A : S → Type*`, not one type, because footnote 1
restricts the action set at each state. The paper's constant action set is `A := fun _ => A₀`. -/
def IsFeasibleKernel {S : Type*} {A : S → Type*} [Fintype S]
    (kernel : (s : S) → A s → S → ℝ) : Prop :=
  (∀ s a s', 0 ≤ kernel s a s') ∧ ∀ s a, ∑ s', kernel s a s' = 1

end MarkovEntanglementExact


