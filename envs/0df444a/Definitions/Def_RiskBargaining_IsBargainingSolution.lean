-- Prove2me | Definitions.Def_RiskBargaining_IsBargainingSolution
-- name    : RiskBargaining_IsBargainingSolution
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:30:10.280843+00:00
-- url     : https://prove2.me/theorems/05823cec-9be4-4540-99e6-902a0259253c
-- title:
--   Bargaining solution
-- statement:
--   A **bargaining solution** is a rule $F$ with $F(R,M,\mathcal A)\in\mathcal U(R,M,\mathcal A)$ for each admissible instance.
--
--   **Formalization Note** The paper says "each feasible instance". The requirement ranges over the admissible class, since at a feasible instance whose max in (8) fails no rule can satisfy Axiom 1. Values off the class are unconstrained.
-- source:
--   Gutjahr, Kovacevic, Wozabal, Risk-Averse Bargaining in a Stochastic Optimization Context, manuscript, Definition 3, p.8

import Mathlib
import Definitions.Def_RiskBargaining_Rule
import Definitions.Def_RiskBargaining_Instance_U
import Definitions.Def_RiskBargaining_Instance_Admissible

open MeasureTheory
open scoped ENNReal

namespace RiskBargaining

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- **Bargaining solution.**
Gutjahr, Kovacevic, Wozabal, *Risk-Averse Bargaining in a Stochastic Optimization Context*, manuscript, Definition 3, p.8: a mapping that assigns a vector in `𝒰(R, M, 𝒜)` to each feasible instance.

**Formalization Note.** The requirement ranges over admissible instances (correction to Theorem 1):
on a feasible instance where the max in (8) fails, no rule satisfies PAR. Values off the class are
unconstrained. -/
def IsBargainingSolution (F : Rule μ p X) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (I : Instance μ p X ι),
    I.Admissible → F ι I ∈ I.U

end RiskBargaining


