-- Prove2me | Definitions.Def_LevyStochCalc_Driver_CellConditionalIsometryPoisson_F001
-- name    : LevyStochCalc_Driver_CellConditionalIsometryPoisson_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:58:59.700846+00:00
-- url     : https://prove2.me/theorems/1db0ceb5-633e-4d6b-9f5d-298fe549585d
-- title:
--   Source declarations: LevyStochCalc.Driver.CellConditionalIsometryPoisson
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.CellConditionalIsometryPoisson. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_CellConditionalIsometryPoisson_F000

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

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The rectangle indicator on `(a, b] × A` reduces the horizon double integral of a marked
integrand to its integral over the cell and the mark set. -/
theorem setIntegral_Icc_mul_cellMarkIndicator {a b : ℝ} (ha : 0 ≤ a) (hA : MeasurableSet A)
    (F : ℝ → E → ℝ) (ω : Ω) :
    ∫ s in Set.Icc (0 : ℝ) b, ∫ e, F s e * cellMarkIndicator Ω a b A ω s e ∂ν ∂volume
      = ∫ s in Set.Ioc a b, ∫ e in A, F s e ∂ν ∂volume := by
  have hpt : ∀ s : ℝ, (∫ e, F s e * cellMarkIndicator Ω a b A ω s e ∂ν)
      = (Set.Ioc a b).indicator (fun u => ∫ e in A, F u e ∂ν) s := by
    intro s
    by_cases hs : s ∈ Set.Ioc a b
    · rw [Set.indicator_of_mem hs]
      have hinner : ∀ e : E, F s e * cellMarkIndicator Ω a b A ω s e
          = A.indicator (fun u => F s u) e := by
        intro e
        by_cases he : e ∈ A
        · rw [Set.indicator_of_mem he]
          simp [cellMarkIndicator, Set.indicator_of_mem (Set.mk_mem_prod hs he)]
        · rw [Set.indicator_of_notMem he,
            cellMarkIndicator_eq_zero_of_notMem (a := a) (b := b) ω s he]
          ring
      simp_rw [hinner]
      exact integral_indicator hA
    · rw [Set.indicator_of_notMem hs]
      have hinner : ∀ e : E, F s e * cellMarkIndicator Ω a b A ω s e = 0 := by
        intro e
        rw [cellMarkIndicator_eq_zero_of_notMem_Ioc (A := A) ω hs e]
        ring
      simp_rw [hinner]
      exact integral_zero E ℝ
  simp_rw [hpt]
  exact setIntegral_Icc_indicator_Ioc ha _
end CompensatedCell

end LevyDriver

end LevyStochCalc.Driver


