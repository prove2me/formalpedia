-- Prove2me | Definitions.Def_LevyStochCalc_Driver_CellConditionalIsometryPoisson_F000
-- name    : LevyStochCalc_Driver_CellConditionalIsometryPoisson_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:54:40.872651+00:00
-- url     : https://prove2.me/theorems/18731a8a-4936-47e7-be1a-dad60e48cf46
-- title:
--   Source declarations: LevyStochCalc.Driver.CellConditionalIsometryPoisson
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.CellConditionalIsometryPoisson. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_CellConditionalIsometry_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Conditional cell isometries against the compensated Poisson random measure

Over a cell `(a, b]` with `0 ≤ a < b` and a mark set `A` of finite intensity, the increment of a
compensated integral across `(a, b]` pairs with the compensated count `Ñ((a, b] × A)` to the
integral of the integrand over the cell and over `A`, and the pairing survives conditioning at
the left endpoint. The compensated count is the compensated integral of the indicator integrand
of the rectangle `(a, b] × A`, restricting the integrand to the cell turns the increment into the
integral at the horizon `b`, a bounded weight measurable at `a` passes inside, and the horizon
isometry then evaluates the pairing.

## Main statements

* `stochasticIntegral_cellMarkIndicator_ae_eq` — the compensated count of `(a, b] × A` is the
  compensated integral of the indicator integrand of that rectangle.
* `condExp_compensated_cell_mul_compensated_count` — the conditional Itô–Lévy isometry over a
  cell, against the compensated count of `(a, b] × A`.
* `condExp_brownian_cell_mul_compensated_count_eq_zero` — a Brownian cell increment is
  conditionally orthogonal to the compensated count of `(a, b] × A`.

## References

* Karatzas and Shreve, *Brownian Motion and Stochastic Calculus*, 1991, §3.2.
* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §4.2.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

open LevyStochCalc.Brownian.Ito (indIoc)

variable {D : LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section CompensatedCell

variable {φ : Ω → ℝ → E → ℝ} {A : Set E}

/-- The indicator integrand of the space-time rectangle `(a, b] × A`. -/
noncomputable def cellMarkIndicator (Ω) [MeasurableSpace Ω] (a b : ℝ) (A : Set E) :
    Ω → ℝ → E → ℝ :=
  fun _ s e => (Set.Ioc a b ×ˢ A).indicator (fun _ => (1 : ℝ)) (s, e)
omit [MeasurableSpace E] [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The indicator integrand of `(a, b] × A` vanishes off the mark set `A`. -/
theorem cellMarkIndicator_eq_zero_of_notMem {a b : ℝ} (ω : Ω) (s : ℝ) {e : E} (he : e ∉ A) :
    cellMarkIndicator Ω a b A ω s e = 0 :=
  Set.indicator_of_notMem (fun hm => he (Set.mem_prod.mp hm).2) _
omit [MeasurableSpace E] [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The indicator integrand of `(a, b] × A` vanishes off the cell `(a, b]`. -/
theorem cellMarkIndicator_eq_zero_of_notMem_Ioc {a b : ℝ} (ω : Ω) {s : ℝ}
    (hs : s ∉ Set.Ioc a b) (e : E) : cellMarkIndicator Ω a b A ω s e = 0 :=
  Set.indicator_of_notMem (fun hm => hs (Set.mem_prod.mp hm).1) _
omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The indicator integrand of `(a, b] × A` is jointly measurable. -/
theorem measurable_cellMarkIndicator (hA : MeasurableSet A) (a b : ℝ) :
    Measurable fun p : Ω × ℝ × E => cellMarkIndicator Ω a b A p.1 p.2.1 p.2.2 :=
  (measurable_const.indicator (measurableSet_Ioc.prod hA)).comp measurable_snd
omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The indicator integrand of `(a, b] × A` is predictable when `A` has finite intensity. -/
theorem markedPredictable_cellMarkIndicator {a b : ℝ} (ha : 0 ≤ a) (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤) : Probability.MarkedPredictable ℱ ν (cellMarkIndicator Ω a b A) :=
  _root_.Prove2MeSourceProof.h_fdeeab164202d120da06e07d ha hA hAν
    (c := fun _ : Ω => (1 : ℝ)) measurable_const
omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The indicator integrand of `(a, b] × A` is marked progressively measurable when `A` has
finite intensity. -/
theorem markedProgressivelyMeasurable_cellMarkIndicator {a b : ℝ} (ha : 0 ≤ a)
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) :
    Probability.MarkedProgressivelyMeasurable ℱ (cellMarkIndicator Ω a b A) :=
  (_root_.Prove2MeSourceProof.h_6bebe70af91e345e56c64c09 (markedPredictable_cellMarkIndicator (ℱ := ℱ) ha hA hAν))
end CompensatedCell

end LevyDriver

end LevyStochCalc.Driver


