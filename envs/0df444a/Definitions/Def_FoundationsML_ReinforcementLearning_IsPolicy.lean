-- Prove2me | Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
-- name    : FoundationsML_ReinforcementLearning_IsPolicy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-20T04:30:38.214905+00:00
-- url     : https://prove2.me/theorems/174640f1-9609-4286-8628-c2c3ef1976d2
-- title:
--   Stationary policy (Definition 17.2)
-- statement:
--   **Definition 17.2 (Policy), p. 381, PDF p. 398.** A policy is a mapping $\pi:S\to\Delta(A)$,
--   where $\Delta(A)$ is the set of probability distributions over $A$. A policy $\pi$ is
--   deterministic if for any $s$ there exists a unique $a\in A$ with $\pi(s)(a)=1$; this
--   formalization targets the stationary case (p. 382): the distribution of actions does not
--   depend on time.
--
--   **Formalization Note.** `π : S → A → ℝ` with `IsPolicy π` asserting `π s` is a probability
--   distribution over the finite type `A`, for every `s` — matches Theorem 17.7's own
--   quantification "for any pair `(s,a)` with `π(s)(a) > 0`" directly, rather than a `PMF`-valued
--   function. Deterministic policies are the special case `π(s)(a) = 1` for a unique `a`.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 381, Definition 17.2 (PDF p. 398)

import Mathlib

namespace FoundationsML.ReinforcementLearning

/-- Definition 17.2 (Policy; Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine
Learning*, 2nd ed., MIT Press 2018, p. 381, PDF p. 398). A (stationary) policy is a mapping
`π : S → Δ(A)`, a probability distribution over actions at each state.

**Formalization Note.** `π : S → A → ℝ` with `IsPolicy π` asserting `π s` is a probability
distribution over the finite type `A`, for every `s`, rather than a `PMF`-valued function —
matches Theorem 17.7's own quantification "for any pair `(s,a)` with `π(s)(a) > 0`" directly. -/
def IsPolicy {S A : Type*} [Fintype A] (π : S → A → ℝ) : Prop :=
  ∀ s : S, (∀ a : A, 0 ≤ π s a) ∧ ∑ a : A, π s a = 1

end FoundationsML.ReinforcementLearning


