-- Prove2me | Definitions.Def_SourceProof_8b57cd5261008e75b4f880d6
-- name    : SourceProof_8b57cd5261008e75b4f880d6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T16:04:07.177608+00:00
-- url     : https://prove2.me/theorems/731ae80e-dfde-4972-8bcc-6c1849788bc3
-- title:
--   LevyStochCalc source module: SourceProof_8b57cd5261008e75b4f880d6
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.MarkStep.eval_dyadicRestrict` comes from the `LevyStochCalc.Poisson.MarkStepIncrement` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_MarkStepIncrement_F001

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

theorem _root_.Prove2MeSourceProof.h_8b57cd5261008e75b4f880d6 {ℓ d : ℕ} (G : MarkStep Ω E ν (TimeGrid.dyadic T hT ℓ)) {T' : ℝ}
    (hT' : 0 < T') (hd : d ≤ ℓ) (h : T = T' * 2 ^ d) {s : ℝ} (hs : s ≤ T') (e : E) (ω : Ω) :
    (G.dyadicRestrict hT' hd h).eval s e ω = G.eval s e ω := by
  unfold LevyStochCalc.Poisson.Compensated.MarkStep.eval
  simp_rw [LevyStochCalc.Poisson.Compensated.MarkStep.dyadic_p_restrict (hT := hT) hT' hd h]
  refine Finset.sum_subset (Finset.range_subset.2 fun i hi =>
    Finset.mem_range.2 (lt_of_lt_of_le hi (Nat.pow_le_pow_right two_pos (Nat.sub_le ℓ d)))) ?_
  intro i hi hni
  rw [Finset.mem_range] at hi hni
  rw [Set.indicator_of_notMem, zero_mul]
  intro hs'
  have : (LevyStochCalc.Poisson.Compensated.TimeGrid.dyadic T hT ℓ).p (2 ^ (ℓ - d)) ≤ (LevyStochCalc.Poisson.Compensated.TimeGrid.dyadic T hT ℓ).p i :=
    (LevyStochCalc.Poisson.Compensated.TimeGrid.dyadic T hT ℓ).p_mono (not_lt.1 hni) hi.le
  rw [LevyStochCalc.Poisson.Compensated.MarkStep.dyadic_p_pow (hT := hT) hd h] at this
  exact absurd (hs.trans this) (not_le.2 hs'.1)
end Dyadic

section Increment

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid}

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ :
  IsPoissonFiltration N ℱ) (G : MarkStep Ω E ν g) {w : Ω → ℝ}
  (hw : ∃ C : ℝ, ∀ ω, |w ω| ≤ C) (hwm : Measurable w) {s t : ℝ} (hs : 0 < s) (hst : s < t)

end Increment

end MarkStep

end LevyStochCalc.Poisson.Compensated


