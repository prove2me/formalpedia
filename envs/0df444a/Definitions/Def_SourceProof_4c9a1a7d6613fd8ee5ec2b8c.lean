-- Prove2me | Definitions.Def_SourceProof_4c9a1a7d6613fd8ee5ec2b8c
-- name    : SourceProof_4c9a1a7d6613fd8ee5ec2b8c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T12:25:17.123181+00:00
-- url     : https://prove2.me/theorems/d3dc441e-2450-46fb-9d2a-6f42f64bce02
-- title:
--   LevyStochCalc source module: SourceProof_4c9a1a7d6613fd8ee5ec2b8c
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.MarkStep.integral_p_eq` comes from the `LevyStochCalc.Poisson.MarkStepWeight` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_MarkStepIsometry_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Sums, negations and weightings of mark-step integrands

Two mark-step integrands on a common time grid are added by concatenating their mark
families (`MarkStep.append`), and a mark-step integrand is negated coefficientwise
(`MarkStep.neg`); both operations act additively on the compensated integral and on the
integrand, so the `L²` isometry applies to differences. Multiplying the coefficients from a
given piece on by a bounded measurable weight `w`, and zeroing the earlier ones
(`MarkStep.weight`), yields the isometry for the weighted increment of the integral over a
grid interval.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

namespace MarkStep

section Append

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid}

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ :
  IsPoissonFiltration N ℱ) (G G' : MarkStep Ω E ν g)

end Append

section Weight

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid}

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ :
  IsPoissonFiltration N ℱ) (G : MarkStep Ω E ν g) {w : Ω → ℝ}
  (hw : ∃ C : ℝ, ∀ ω, |w ω| ≤ C) (hwm : Measurable w)


theorem _root_.Prove2MeSourceProof.h_4c9a1a7d6613fd8ee5ec2b8c (b : ℕ) (hb : b ≤ g.N₀) (ω : Ω) :
    G.integral N (g.p b) ω = ∑ i ∈ Finset.range b, ∑ k, G.ξ i k ω
      * N.compensated (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k) ω := by
  unfold LevyStochCalc.Poisson.Compensated.MarkStep.integral
  refine (Finset.sum_subset (Finset.range_subset.2 fun i hi =>
    Finset.mem_range.2 (lt_of_lt_of_le hi hb)) ?_).symm.trans
    (Finset.sum_congr rfl fun i hi => ?_)
  · intro i hi hni
    rw [Finset.mem_range] at hi hni
    have hti : g.p b ≤ g.p i := g.p_mono (not_lt.1 hni) hi.le
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [min_eq_right hti, min_eq_right (hti.trans (g.p_mono (Nat.le_succ i) hi)),
      LevyStochCalc.Poisson.Compensated.MarkStep.compensated_Ioc_self, mul_zero]
  · rw [Finset.mem_range] at hi
    rw [min_eq_left (g.p_mono hi.le hb), min_eq_left (g.p_mono hi hb)]
end Weight

end MarkStep

end LevyStochCalc.Poisson.Compensated


