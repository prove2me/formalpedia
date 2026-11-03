-- Prove2me | Definitions.Def_RiskAverseConsistency_IsMeasurableSetValued
-- name    : RiskAverseConsistency_IsMeasurableSetValued
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:21:26.047349+00:00
-- url     : https://prove2.me/theorems/2e30a39e-6148-4b0d-bb5c-fbdef900cd28
-- title:
--   Measurable set-valued map
-- statement:
--   A set-valued map $\Gamma:\Omega'\rightrightarrows Z$ from a measurable space to a topological space is **measurable** if
--
--   $$
--   \{\omega'\in\Omega':\ \Gamma(\omega')\cap U\neq\emptyset\}\in\mathcal F'
--   $$
--
--   for every open $U\subseteq Z$.
--
--   **Formalization Note** The paper does not define the notion; Corollary 14 (c) uses it with reference to [5] (Aubin and Frankowska, *Set-Valued Analysis*, Def. 8.1.1), whose definition is the one above.
-- source:
--   Milz, Surowiec, Asymptotic consistency for nonconvex risk-averse stochastic optimization with infinite dimensional decision spaces, arXiv:2207.14756v2, Corollary 14 (c), p.10, with reference [5]

import Mathlib

namespace RiskAverseConsistency

/-- A set-valued map `Γ : Ω′ ⇉ Z` is **measurable**: `{ω′ : Γ(ω′) ∩ U ≠ ∅}` is measurable for every
open `U ⊂ Z`.

Milz, Surowiec, arXiv:2207.14756v2, Corollary 14 (c), p.10 ("Ŝ^r_N are measurable"), in the sense
of the reference [5] cited there (Aubin–Frankowska, *Set-Valued Analysis*, Def. 8.1.1). -/
def IsMeasurableSetValued {Ω' Z : Type*} [MeasurableSpace Ω'] [TopologicalSpace Z]
    (Γ : Ω' → Set Z) : Prop :=
  ∀ U : Set Z, IsOpen U → MeasurableSet {ω' | (Γ ω' ∩ U).Nonempty}

end RiskAverseConsistency


