-- Prove2me | Definitions.Def_LevyStochCalc_Driver_CellConditionalIsometryPoisson_F002
-- name    : LevyStochCalc_Driver_CellConditionalIsometryPoisson_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:55:54.993207+00:00
-- url     : https://prove2.me/theorems/be7419c2-a620-465e-b2a0-77cf7264afa8
-- title:
--   LevyStochCalc source module: LevyStochCalc.Driver.CellConditionalIsometryPoisson
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.Driver.CellConditionalIsometryPoisson in the pinned LevyStochCalc project.
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

/-- An integrand restricted to the cell `(a, b]`, as a marked horizon integrand at `b`. -/
noncomputable def cellIntegrand (P) [IsProbabilityMeasure P] (ν) [SigmaFinite ν]
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {φ : Ω → ℝ → E → ℝ}
    (hφm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hφp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hφs : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    Poisson.Compensated.MarkedHorizonIntegrand P ν ℱ b where
  toFun := fun ω s e => indIoc Ω a b ω s * φ ω s e
  measurable_uncurry := Poisson.Compensated.measurable_indIoc_mul hφm a b
  progressive := Poisson.Compensated.markedProgressivelyMeasurable_indIoc_mul hφp a b
  vanishing := fun ω s e hs => by
    have hnot : s ∉ Set.Ioc a b := fun hmem => hs ⟨ha.trans hmem.1.le, hmem.2⟩
    simp [Brownian.Ito.indIoc, Set.indicator_of_notMem hnot]
  energy_ne_top :=
    (Poisson.Compensated.sq_int_global_indIoc_mul hφs a b b (ha.trans_lt hab)).ne
end CompensatedCell

end LevyDriver

end LevyStochCalc.Driver


