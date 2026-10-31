-- Prove2me | Definitions.Def_RiskBargaining_Instance_Feasible
-- name    : RiskBargaining_Instance_Feasible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:27:50.990742+00:00
-- url     : https://prove2.me/theorems/7858c127-008a-40b5-a892-90805565aceb
-- title:
--   Feasible instance
-- statement:
--   The instance $(R,M,\mathcal A)$ is **feasible** if the set $\mathcal U(R,M,\mathcal A)$ is nonempty, that is, if cooperation has a non-negative value for the players.
-- source:
--   Gutjahr, Kovacevic, Wozabal, Risk-Averse Bargaining in a Stochastic Optimization Context, manuscript, §2.2, p.8

import Mathlib
import Definitions.Def_RiskBargaining_Instance_U

open MeasureTheory
open scoped ENNReal

namespace RiskBargaining

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {X : Type*} [TopologicalSpace X] [CompactSpace X] {ι : Type*}

/-- **Feasible instance.**
Gutjahr, Kovacevic, Wozabal, *Risk-Averse Bargaining in a Stochastic Optimization Context*, manuscript, §2.2, p.8: "The instance (R,M,𝒜) is called feasible if the set 𝒰(R,M,𝒜) is non-empty". -/
def Instance.Feasible [Fintype ι] (I : Instance μ p X ι) : Prop :=
  I.U.Nonempty

end RiskBargaining


