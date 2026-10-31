-- Prove2me | Definitions.Def_RiskBargaining_Instance_totals
-- name    : RiskBargaining_Instance_totals
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:26:57.307161+00:00
-- url     : https://prove2.me/theorems/58d21917-48be-4c63-a528-6881958da716
-- title:
--   The value set of problem (8)
-- statement:
--   For an instance $(R,M,\mathcal A)$, this is the set
--   $$
--   \Big\{\sum_{i=1}^n u_i \;\Big|\; \sum_{i=1}^n L_i=M_x,\ \mathcal A_i(R_i)\le u_i\le\mathcal A_i(L_i)\ \forall i\in N,\ x\in\mathcal X\Big\}
--   $$
--   over which problem (8) maximizes. The value $z$ and the condition that the maximum exists are both read off it.
-- source:
--   Gutjahr, Kovacevic, Wozabal, Risk-Averse Bargaining in a Stochastic Optimization Context, manuscript, equation (8), p.9

import Mathlib
import Definitions.Def_RiskBargaining_Instance_v

open MeasureTheory
open scoped ENNReal

namespace RiskBargaining

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {X : Type*} [TopologicalSpace X] [CompactSpace X] {ι : Type*}

/-- **The value set of problem (8)**: every `∑ i, u i` over the constraints of (8).
Gutjahr, Kovacevic, Wozabal, *Risk-Averse Bargaining in a Stochastic Optimization Context*, manuscript, equation (8), p.9.

**Formalization Note.** This is the set in braces in (8); `Instance.z` is its supremum and
`Instance.Attained` says that the printed `max` exists. -/
def Instance.totals [Fintype ι] (I : Instance μ p X ι) : Set ℝ :=
  {t | ∃ (u : ι → ℝ) (L : ι → Lp ℝ p μ) (x : X),
      t = ∑ i, u i ∧ ∑ i, L i = I.M x ∧ ∀ i, I.v i ≤ u i ∧ u i ≤ I.A i (L i)}

end RiskBargaining


