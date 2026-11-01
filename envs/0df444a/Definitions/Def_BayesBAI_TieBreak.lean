-- Prove2me | Definitions.Def_BayesBAI_TieBreak
-- name    : BayesBAI_TieBreak
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:52:53.180462+00:00
-- url     : https://prove2.me/theorems/a133c17f-168c-4cc6-8d02-543ea380a2d2
-- title:
--   A tie-break rule for the arg max of Algorithm 1
-- statement:
--   A **tie-break rule** assigns to every nonempty set $A$ of arms and values $v:[K]\to\mathbb R$ an element of $A$ at which $v$ attains its maximum over $A$.
--
--   The paper says that ties are broken arbitrarily (footnote 1, p.1). All statements of the mission hold for every rule, uniformly.
--
--   **Formalization Note.** A rule sees the candidate set and the observed values only, never the means. A rule using extra independent randomness is a mixture of these rules.
-- source:
--   Komiyama, Ariu, Kato, Qin, Rate-optimal Bayesian Simple Regret in Best Arm Identification, arXiv:2111.09885v3, Algorithm 1, p.6, and footnote 1, p.1

import Mathlib

namespace BayesBAI

/-- A tie-break rule for the `arg max` of Algorithm 1, Komiyama, Ariu, Kato, Qin,
arXiv:2111.09885v3, p.6. For a nonempty set `A` of arms and values `v`, `sel A v` is a maximizer of
`v` on `A`.

**Formalization Note.** The paper says ties are broken arbitrarily (footnote 1). A rule sees only the
candidate set and the observed values, never the means. Every statement quantifies over all rules. A
rule using extra independent randomness is a mixture of these. -/
structure TieBreak (K : ℕ) where
  /-- The selected arm. -/
  sel : Finset (Fin K) → (Fin K → ℝ) → Fin K
  /-- The selected arm is in the set. -/
  sel_mem : ∀ (A : Finset (Fin K)) (v : Fin K → ℝ), A.Nonempty → sel A v ∈ A
  /-- The selected arm maximizes the values on the set. -/
  sel_max : ∀ (A : Finset (Fin K)) (v : Fin K → ℝ), A.Nonempty → ∀ i ∈ A, v i ≤ v (sel A v)

end BayesBAI


