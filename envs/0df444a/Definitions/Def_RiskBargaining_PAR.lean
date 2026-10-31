-- Prove2me | Definitions.Def_RiskBargaining_PAR
-- name    : RiskBargaining_PAR
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:29:54.514416+00:00
-- url     : https://prove2.me/theorems/87fa6835-c901-4701-a20f-1d83cd8ed681
-- title:
--   Axiom 1 (PAR): Pareto optimality
-- statement:
--   A rule $F$ satisfies **PAR** if, for every admissible instance with $u^*=F(R,M,\mathcal A)$ and every $u\in\mathcal U(R,M,\mathcal A)$,
--   $$
--   \exists i\in N: u_i>u^*_i\ \Rightarrow\ \exists j\in N: u_j<u^*_j.
--   $$
--   This is the efficiency requirement of the characterization.
-- source:
--   Gutjahr, Kovacevic, Wozabal, Risk-Averse Bargaining in a Stochastic Optimization Context, manuscript, Axiom 1, p.8

import Mathlib
import Definitions.Def_RiskBargaining_Rule
import Definitions.Def_RiskBargaining_Instance_U
import Definitions.Def_RiskBargaining_Instance_Admissible

open MeasureTheory
open scoped ENNReal

namespace RiskBargaining

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- **Axiom 1 (PAR).**
Gutjahr, Kovacevic, Wozabal, *Risk-Averse Bargaining in a Stochastic Optimization Context*, manuscript, Axiom 1, p.8: if `u ∈ 𝒰(R, M, 𝒜)`, then `∃ i, u i > u* i` implies `∃ j, u j < u* j`, where
`u* = F(R, M, 𝒜)`. -/
def PAR (F : Rule μ p X) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (I : Instance μ p X ι),
    I.Admissible → ∀ u ∈ I.U, (∃ i, F ι I i < u i) → ∃ j, u j < F ι I j

end RiskBargaining


