-- Prove2me | Definitions.Def_RiskBargaining_Instance_Commensurable
-- name    : RiskBargaining_Instance_Commensurable
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:27:08.773996+00:00
-- url     : https://prove2.me/theorems/20d7dad5-0768-4ad4-b1fa-26ed4aa7286a
-- title:
--   Pairwise commensurable values
-- statement:
--   The values of an instance are **commensurable** if there is a real $c>0$ such that every $v_i$ is a natural multiple of $c$.
--
--   Every instance with all $v_i\in\mathbb Q$ has this property, with $c$ the inverse of a common denominator. Commensurability is the domain on which Axioms 1–3 alone determine the rule.
-- source:
--   Gutjahr, Kovacevic, Wozabal, Risk-Averse Bargaining in a Stochastic Optimization Context, manuscript, Appendix A.3, p.36 (generalizes the case $v_i\in\mathbb Q$)

import Mathlib
import Definitions.Def_RiskBargaining_Instance_v

open MeasureTheory
open scoped ENNReal

namespace RiskBargaining

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {X : Type*} [TopologicalSpace X] [CompactSpace X] {ι : Type*}

/-- **Pairwise commensurable values**: all `v i` are natural multiples of one positive real `c`.
Generalizes the case `v_i ∈ ℚ` of Gutjahr, Kovacevic, Wozabal, *Risk-Averse Bargaining in a Stochastic Optimization Context*, manuscript, Appendix A.3, p.36, where `v_i = p_i / q` and `c = 1 / q`. -/
def Instance.Commensurable (I : Instance μ p X ι) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ i, ∃ q : ℕ, I.v i = q * c

end RiskBargaining


