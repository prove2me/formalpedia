-- Prove2me | Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
-- name    : FoundationsML_ReinforcementLearning_IsTransitionKernel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-20T04:30:17.885105+00:00
-- url     : https://prove2.me/theorems/33dee61c-a01a-4761-9eb9-c00334b91285
-- title:
--   MDP transition kernel (Definition 17.1)
-- statement:
--   **Definition 17.1 (MDPs, transition-probability clause), p. 380, PDF p. 397.** A Markov
--   decision process is defined in part by a transition probability $P[s'\mid s,a]$: a
--   distribution over destination states $s'$, for every state $s\in S$ and action $a\in A$.
--
--   This predicate is the finite-state, finite-action specialization used throughout the
--   chapter (the book allows possibly infinite $S,A$ in general, but §17.2 onward and every
--   theorem cited here work with finite MDPs).
--
--   **Formalization Note.** `P : S → A → S → ℝ` with `IsTransitionKernel P` asserting that
--   `P s a` is a probability distribution over the finite type `S`, for every `(s,a)`.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 380, Definition 17.1 (PDF p. 397)

import Mathlib

namespace FoundationsML.ReinforcementLearning

/-- Definition 17.1 (MDP transition probability; Mohri, Rostamizadeh & Talwalkar, *Foundations
of Machine Learning*, 2nd ed., MIT Press 2018, p. 380, PDF p. 397): `P[s'|s,a]`, a distribution
over destination states `s'`, for every `(s,a) ∈ S × A`.

**Formalization Note.** `P : S → A → S → ℝ` with `IsTransitionKernel P` asserting `P s a` is a
probability distribution over the finite type `S`, for every `(s,a)`. -/
def IsTransitionKernel {S A : Type*} [Fintype S] (P : S → A → S → ℝ) : Prop :=
  ∀ (s : S) (a : A), (∀ s' : S, 0 ≤ P s a s') ∧ ∑ s' : S, P s a s' = 1

end FoundationsML.ReinforcementLearning


