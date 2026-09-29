-- Prove2me | Definitions.Def_FoundationsML_ReinforcementLearning_InducedTransition
-- name    : FoundationsML_ReinforcementLearning_InducedTransition
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-20T04:31:20.622468+00:00
-- url     : https://prove2.me/theorems/81153875-49b9-4410-9449-cabd0fc3e6ac
-- title:
--   Transition matrix induced by a fixed policy
-- statement:
--   **Notation used in Proposition 17.9 and Theorem 17.10, p. 385-386, PDF p. 402-403.** For a
--   fixed (possibly stochastic) policy $\pi$, the transition-probability matrix it induces is
--   $P_{s,s'} = P[s'\mid s,\pi(s)] = \sum_{a} \pi(s)(a)\,P[s'\mid s,a]$: the transition
--   probability marginalized over the mixed action distribution $\pi(s)$ at state $s$. Not
--   itself a book-numbered definition; it is the object the book calls "$P$" once a policy has
--   been fixed (distinct from the raw MDP kernel $P[s'\mid s,a]$, which is still indexed by an
--   unfixed action).
--
--   **Formalization Note.** `InducedTransition π P s s' = ∑ a, π s a * P s a s'`, the mixed-action
--   marginalization used directly in the goal theorem's `(I − γP)` and in Proposition 17.9's
--   right-hand side.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 385-386, notation preceding (17.6) (PDF p. 402-403)

import Mathlib

namespace FoundationsML.ReinforcementLearning

/-- The transition-probability matrix induced by a (possibly stochastic) policy `π`
(Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018,
p. 385-386, PDF p. 402-403, notation `P_{s,s'} = P[s'|s,π(s)]` used in Proposition 17.9 and
Theorem 17.10): `P_{s,s'} = ∑_{a} π(s)(a) P[s'|s,a]`, the transition probability marginalized
over the mixed action distribution `π(s)`. -/
noncomputable def InducedTransition {S A : Type*} [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ) (s s' : S) : ℝ :=
  ∑ a : A, π s a * P s a s'

end FoundationsML.ReinforcementLearning


