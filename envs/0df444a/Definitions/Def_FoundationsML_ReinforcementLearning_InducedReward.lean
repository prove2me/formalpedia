-- Prove2me | Definitions.Def_FoundationsML_ReinforcementLearning_InducedReward
-- name    : FoundationsML_ReinforcementLearning_InducedReward
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-20T04:32:42.123797+00:00
-- url     : https://prove2.me/theorems/4e9b7c9c-9792-46ba-9ab6-0d4c154bf5f6
-- title:
--   Expected reward induced by a fixed policy
-- statement:
--   **Notation used in Proposition 17.9 and Theorem 17.10, p. 386, PDF p. 403.** For a fixed
--   (possibly stochastic) policy $\pi$, the expected-reward vector it induces is
--   $R_s = \mathbb E[r(s,\pi(s))] = \sum_a \pi(s)(a)\,\mathbb E[r(s,a)]$: the expected reward
--   marginalized over the mixed action distribution $\pi(s)$. Not itself a book-numbered
--   definition; it is the object the book calls "$R$" in (17.6)/(17.7).
--
--   **Formalization Note.** `InducedReward π Er s = ∑ a, π s a * Er s a`, where `Er s a` is the
--   expected reward $\mathbb E[r(s,a)]$ of taking action $a$ at state $s$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 386, notation preceding (17.6) (PDF p. 403)

import Mathlib

namespace FoundationsML.ReinforcementLearning

/-- The expected reward vector induced by a (possibly stochastic) policy `π` (Mohri,
Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 386,
PDF p. 403, notation `R_s = E[r(s,π(s))]` used in Proposition 17.9 and Theorem 17.10):
`R_s = ∑_a π(s)(a) E[r(s,a)]`, the expected reward marginalized over the mixed action
distribution `π(s)`. -/
noncomputable def InducedReward {S A : Type*} [Fintype A]
    (π : S → A → ℝ) (Er : S → A → ℝ) (s : S) : ℝ :=
  ∑ a : A, π s a * Er s a

end FoundationsML.ReinforcementLearning


