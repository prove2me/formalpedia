-- Prove2me | Definitions.Def_MarkovEntanglementExact_IsFeasiblePolicy
-- name    : MarkovEntanglementExact_IsFeasiblePolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:20:09.546461+00:00
-- url     : https://prove2.me/theorems/ed36bd9f-2cec-446b-9331-7e896283a7b3
-- title:
--   Stationary randomized policy on feasible action sets
-- statement:
--   A **stationary randomized policy** on feasible action sets $\mathcal A(s)$ assigns to each state $s$ a probability distribution $\pi(\cdot\mid s)$ on $\mathcal A(s)$:
--   $$\pi(a\mid s)\ge 0,\qquad \sum_{a\in\mathcal A(s)}\pi(a\mid s)=1.$$
--
--   In the paper this is the global policy $\pi:\mathcal S\to\Delta(\mathcal A)$, which may correlate the agents' actions.
-- source:
--   Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, §2, p.7, and footnote 1, p.8

import Mathlib

open scoped BigOperators

namespace MarkovEntanglementExact

/-- A stationary randomized policy on feasible action sets: `π s a` is `π(a | s)`, nonnegative,
and summing to one over the feasible actions at every state.

Source: Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, §2, p.7
("any global policy π : 𝒮 → Δ(𝒜)"), with the feasible action sets of footnote 1, p.8. -/
def IsFeasiblePolicy {S : Type*} {A : S → Type*} [∀ s, Fintype (A s)]
    (π : (s : S) → A s → ℝ) : Prop :=
  (∀ s a, 0 ≤ π s a) ∧ ∀ s, ∑ a, π s a = 1

end MarkovEntanglementExact


