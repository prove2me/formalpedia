-- Prove2me | Definitions.Def_RiskBargaining_Instance_Attained
-- name    : RiskBargaining_Instance_Attained
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:27:58.584534+00:00
-- url     : https://prove2.me/theorems/b9ab1ead-0655-484b-90d4-4fd48822c9ae
-- title:
--   The max in (8) exists
-- statement:
--   An instance is **attained** if the value set of problem (8) has a greatest element, so that the $\max$ printed in (8) exists.
--
--   The paper writes this $\max$ for every feasible instance, but it need not exist, so this condition enters the corrected statements. It implies feasibility.
-- source:
--   Gutjahr, Kovacevic, Wozabal, Risk-Averse Bargaining in a Stochastic Optimization Context, manuscript, equation (8), p.9 (the condition itself is not in the paper)

import Mathlib
import Definitions.Def_RiskBargaining_Instance_totals

open MeasureTheory
open scoped ENNReal

namespace RiskBargaining

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {X : Type*} [TopologicalSpace X] [CompactSpace X] {ι : Type*}

/-- **The max in (8) exists.**
Gutjahr, Kovacevic, Wozabal, *Risk-Averse Bargaining in a Stochastic Optimization Context*, manuscript, equation (8), p.9; the condition itself is **not** in the paper. It is the correction to
Propositions 1–2 and to the formula of Theorem 1: (8) is printed as a `max` on every feasible instance,
but the max need not exist (`RiskBargaining.proposition_1_counterexample`). `IsGreatest` contains
membership, so an attained instance is feasible. -/
def Instance.Attained [Fintype ι] (I : Instance μ p X ι) : Prop :=
  ∃ z, IsGreatest I.totals z

end RiskBargaining


