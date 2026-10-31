-- Prove2me | Definitions.Def_RiskBargaining_ContScaling
-- name    : RiskBargaining_ContScaling
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:30:37.327186+00:00
-- url     : https://prove2.me/theorems/911f96dc-28b1-46e8-b8fe-4b3114b4cb27
-- title:
--   CONT: continuity along scalings of the endowments
-- statement:
--   A rule $F$ satisfies **CONT** if, for every admissible instance $(R,M,\mathcal A)$ and every sequence of positive scalars $c^k_i\to 1$ ($k\to\infty$, $i\in N$) such that the instances $((c^k_iR_i)_i,M,\mathcal A)$ are admissible,
--   $$
--   F\big((c^k_iR_i)_i,M,\mathcal A\big)\ \longrightarrow\ F(R,M,\mathcal A).
--   $$
--
--   This axiom is not in the paper. It is the continuity that the printed proof of Theorem 1 tacitly uses at irrational values, in its weakest useful form. Continuity of $F$ in $R$ with respect to the $L^p$ norm implies it.
-- source:
--   Gutjahr, Kovacevic, Wozabal, Risk-Averse Bargaining in a Stochastic Optimization Context, manuscript, Appendix A.3, p.37 (the axiom is not in the paper)

import Mathlib
import Definitions.Def_RiskBargaining_Rule
import Definitions.Def_RiskBargaining_Instance_Admissible
import Definitions.Def_RiskBargaining_Instance_scale

open MeasureTheory
open scoped ENNReal

namespace RiskBargaining

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- **CONT: continuity along scalings of the endowments.** Not in the paper. It is the correction to the
"only if" of Theorem 1: Gutjahr, Kovacevic, Wozabal, *Risk-Averse Bargaining in a Stochastic Optimization Context*, manuscript, Appendix A.3, p.37, passes from rational to irrational values by the
continuity of the right-hand side of (9), which says nothing about `F`, and the claim fails without an
axiom (`RiskBargaining.str_does_not_force_nash_rule`).

`F` at `I.scale (c k)` converges to `F` at `I` in the product topology whenever the positive scalars
`c k i` tend to `1` and the scaled instances are admissible. `L^p`-continuity of `F` in `R` implies this.

**Formalization Note.** This is the weakest form that the proof needs: `M` and `𝒜` stay fixed, and only
sequences of positive scalars are tested. -/
def ContScaling (F : Rule μ p X) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (I : Instance μ p X ι),
    I.Admissible → ∀ c : ℕ → ι → ℝ, (∀ k i, 0 < c k i) →
      (∀ i, Filter.Tendsto (fun k => c k i) Filter.atTop (nhds 1)) →
      (∀ k, (I.scale (c k)).Admissible) →
      Filter.Tendsto (fun k => F ι (I.scale (c k))) Filter.atTop (nhds (F ι I))

end RiskBargaining


