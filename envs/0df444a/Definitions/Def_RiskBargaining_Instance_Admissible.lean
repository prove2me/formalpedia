-- Prove2me | Definitions.Def_RiskBargaining_Instance_Admissible
-- name    : RiskBargaining_Instance_Admissible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:29:09.012532+00:00
-- url     : https://prove2.me/theorems/4d8e7054-458c-4abf-a777-3155bf531f15
-- title:
--   Admissible instance: positive values, and the max in (8) exists
-- statement:
--   An instance is **admissible** if $v_i>0$ for every player and the $\max$ in (8) exists.
--
--   The paper assumes the positivity and restricts to feasible instances. Attainment is the one condition added by the correction of Theorem 1. It implies feasibility, so feasibility is not repeated. Assumption 1 is part of the notion of instance. All axioms and characterizations of the mission range over this class.
-- source:
--   Gutjahr, Kovacevic, Wozabal, Risk-Averse Bargaining in a Stochastic Optimization Context, manuscript, §2.2, p.8

import Mathlib
import Definitions.Def_RiskBargaining_Instance_Attained

open MeasureTheory
open scoped ENNReal

namespace RiskBargaining

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {X : Type*} [TopologicalSpace X] [CompactSpace X] {ι : Type*}

/-- **Admissible instance**: the class on which Theorem 1 is stated.
Gutjahr, Kovacevic, Wozabal, *Risk-Averse Bargaining in a Stochastic Optimization Context*, manuscript, §2.2, p.8: "We assume that the values vi := 𝒜i(Ri) ... are always strictly positive"; "We
restrict ourselves to feasible instances".

**Formalization Note.** Strict positivity is the first clause. Feasibility is implied by the second
clause, `Attained`, whose `IsGreatest` contains a witness, so it is not repeated. `Attained` is the
only condition beyond the paper's class (correction to Theorem 1). Assumption 1 is part of
`RiskBargaining.Instance`. -/
def Instance.Admissible [Fintype ι] (I : Instance μ p X ι) : Prop :=
  (∀ i, 0 < I.v i) ∧ I.Attained

end RiskBargaining


