-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_MarkStepIncrement_F003
-- name    : LevyStochCalc_Poisson_MarkStepIncrement_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T12:35:06.331146+00:00
-- url     : https://prove2.me/theorems/9ba1dca2-3a6c-458f-b041-d6aed2c070f6
-- title:
--   Source declarations: LevyStochCalc.Poisson.MarkStepIncrement
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.MarkStepIncrement. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_MarkStepIncrement_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Dyadic mark-step integrands and their weighted increments

On the dyadic grids `TimeGrid.dyadic T hT n` of `[0, T]`, a mark-step integrand of level
`n` is re-expressed on any finer level `m ≥ n` (`MarkStep.dyadicRefine`), each fine piece
inheriting the coefficients of the coarse piece containing it, and is restricted to a
horizon `T'` with `T = T' * 2 ^ d` (`MarkStep.dyadicRestrict`); both leave the compensated
integral and the integrand unchanged. The increment of a mark-step integrand over `(s, t]`,
weighted by a bounded measurable `w`, is itself a mark-step integrand on the increment grid
`TimeGrid.incr` (`MarkStep.incr`), which gives the `L²` isometry for such increments.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

namespace MarkStep

section Dyadic

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]

variable {T : ℝ} {hT : 0 < T} {n m : ℕ}

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ :
  IsPoissonFiltration N ℱ) (G : MarkStep Ω E ν (TimeGrid.dyadic T hT n))
  (hnm : n ≤ m)

end Dyadic

section Increment

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid}

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ :
  IsPoissonFiltration N ℱ) (G : MarkStep Ω E ν g) {w : Ω → ℝ}
  (hw : ∃ C : ℝ, ∀ ω, |w ω| ≤ C) (hwm : Measurable w) {s t : ℝ} (hs : 0 < s) (hst : s < t)

/-- The integral of the weighted increment over its horizon, as a sum over the pieces
meeting `(s, t]`. -/
lemma full_incr_eq (ω : Ω) :
    (G.incr w hw hwm s t hs hst).full N ω
      = ∑ j ∈ Finset.range (g.clampIndex t - g.startIndex s),
        ∑ k, (w ω * G.ξ (g.startIndex s + j) k ω)
          * N.compensated (Set.Ioc (min (max (g.p (g.startIndex s + j)) s) t)
            (min (max (g.p (g.startIndex s + (j + 1))) s) t) ×ˢ G.B k) ω := by
  unfold full
  change ∑ i ∈ Finset.range (g.clampIndex t - g.startIndex s + 1),
      ∑ k, (if i = 0 then (0 : ℝ) else w ω * G.ξ (g.startIndex s + (i - 1)) k ω)
        * N.compensated (Set.Ioc ((g.incr s t hs hst).p i) ((g.incr s t hs hst).p (i + 1))
          ×ˢ G.B k) ω = _
  rw [Finset.sum_range_succ']
  simp only [if_true, zero_mul, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [g.incr_p_succ, g.incr_p_succ]
  simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
end Increment

end MarkStep

end LevyStochCalc.Poisson.Compensated


