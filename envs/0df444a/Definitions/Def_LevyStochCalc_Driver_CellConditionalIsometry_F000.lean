-- Prove2me | Definitions.Def_LevyStochCalc_Driver_CellConditionalIsometry_F000
-- name    : LevyStochCalc_Driver_CellConditionalIsometry_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:48:04.986544+00:00
-- url     : https://prove2.me/theorems/006288bf-bd6d-4efb-97ab-74ef31a9a6a6
-- title:
--   Source declarations: LevyStochCalc.Driver.CellConditionalIsometry
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.CellConditionalIsometry. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_CellOrthogonality_F000
import Definitions.Def_LevyStochCalc_Ito_SecondMomentQuadratic_F000
import Definitions.Def_LevyStochCalc_Ito_SecondMomentQuadratic_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Conditional cell isometries for a Lévy driver

Over a cell `(a, b]` with `0 ≤ a < b` the increment of a Brownian Itô integral pairs with a
second such increment to the time integral of the product of the integrands over the cell, and
the pairing survives conditioning at the left endpoint: the conditional expectation at `ℱ a` of
the increment against the Brownian increment `W_b − W_a` is the conditional cell average of the
integrand. Restricting the integrand to the cell turns the increment into the integral at the
horizon `b`, a bounded weight measurable at `a` passes inside, and the horizon isometry then
evaluates the pairing.

## Main statements

* `integral_brownian_cell_mul_brownian_cell` — the polarised Itô isometry over a cell.
* `condExp_brownian_cell_mul_increment` — the conditional Itô isometry over a cell, against the
  Brownian increment.
* `condExp_brownian_cell_mul_brownian_increment_eq_zero` — the increment against one coordinate
  is conditionally orthogonal to the increment of another coordinate.

## References

* Karatzas and Shreve, *Brownian Motion and Stochastic Calculus*, 1991, §3.2.
* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §4.2.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The window indicator `1_{(a, b]}` is progressively measurable for `0 ≤ a < b`. -/
theorem progressivelyMeasurable_indIoc_of_nonneg (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b) := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · exact progressivelyMeasurable_indIoc₀ ℱ hab
  · exact progressivelyMeasurable_indIoc ℱ ha' hab
/-- An integrand weighted by a weight bounded by one and by the window indicator has pointwise
square at most the square of the integrand. -/
theorem nnnorm_sq_mul_indIoc_mul_le {H V : Ω → ℝ → ℝ} (hVb : ∀ ω s, |V ω s| ≤ 1) (a b : ℝ)
    (ω : Ω) (s : ℝ) :
    (‖V ω s * indIoc Ω a b ω s * H ω s‖₊ : ℝ≥0∞) ^ 2 ≤ (‖H ω s‖₊ : ℝ≥0∞) ^ 2 := by
  have hprod : |V ω s| * |indIoc Ω a b ω s| ≤ 1 := by
    have := mul_le_mul (hVb ω s) (indIoc_le_one a b ω s) (abs_nonneg _) zero_le_one
    simpa using this
  have hnorm : ‖V ω s * indIoc Ω a b ω s * H ω s‖ ≤ ‖H ω s‖ := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
    simpa using mul_le_mul_of_nonneg_right hprod (abs_nonneg (H ω s))
  have hnn : (‖V ω s * indIoc Ω a b ω s * H ω s‖₊ : ℝ≥0∞) ≤ (‖H ω s‖₊ : ℝ≥0∞) := by
    exact_mod_cast hnorm
  exact pow_le_pow_left' hnn 2
end LevyStochCalc.Brownian.Ito

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

open LevyStochCalc.Brownian.Ito (indIoc)

variable {D : LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section BrownianCell

variable {H K : Ω → ℝ → ℝ}

omit [MeasurableSpace Ω] [MeasurableSpace E] [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- For `0 ≤ a` the integral over the horizon `[0, b]` of a function extended by zero off
`(a, b]` is its integral over `(a, b]`. -/
theorem setIntegral_Icc_indicator_Ioc {a b : ℝ} (ha : 0 ≤ a) (f : ℝ → ℝ) :
    ∫ s in Set.Icc (0 : ℝ) b, (Set.Ioc a b).indicator f s ∂volume
      = ∫ s in Set.Ioc a b, f s ∂volume := by
  have hsub : Set.Ioc a b ⊆ Set.Icc (0 : ℝ) b := fun s hs => ⟨ha.trans hs.1.le, hs.2⟩
  rw [setIntegral_indicator measurableSet_Ioc, Set.inter_eq_right.mpr hsub]
omit [MeasurableSpace E] [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The product of two integrands restricted to `(a, b]` integrates over the horizon `[0, b]` to
the integral of the product of the integrands over `(a, b]`. -/
theorem setIntegral_Icc_indIoc_mul_mul {a b : ℝ} (ha : 0 ≤ a) (ω : Ω) :
    ∫ s in Set.Icc (0 : ℝ) b,
        (indIoc Ω a b ω s * H ω s) * (indIoc Ω a b ω s * K ω s) ∂volume
      = ∫ s in Set.Ioc a b, H ω s * K ω s ∂volume := by
  have hpt : ∀ s : ℝ, (indIoc Ω a b ω s * H ω s) * (indIoc Ω a b ω s * K ω s)
      = (Set.Ioc a b).indicator (fun u => H ω u * K ω u) s := by
    intro s
    by_cases hs : s ∈ Set.Ioc a b
    · rw [Set.indicator_of_mem hs]
      simp [Brownian.Ito.indIoc, Set.indicator_of_mem hs]
    · rw [Set.indicator_of_notMem hs]
      simp [Brownian.Ito.indIoc, Set.indicator_of_notMem hs]
  simp_rw [hpt]
  exact setIntegral_Icc_indicator_Ioc ha _
omit [MeasurableSpace E] [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- An integrand restricted to `(a, b]` integrates over the horizon `[0, b]` to its integral
over `(a, b]`. -/
theorem setIntegral_Icc_indIoc_mul {a b : ℝ} (ha : 0 ≤ a) (ω : Ω) :
    ∫ s in Set.Icc (0 : ℝ) b, indIoc Ω a b ω s * H ω s ∂volume
      = ∫ s in Set.Ioc a b, H ω s ∂volume := by
  have hpt : ∀ s : ℝ, indIoc Ω a b ω s * H ω s = (Set.Ioc a b).indicator (H ω) s := by
    intro s
    by_cases hs : s ∈ Set.Ioc a b
    · rw [Set.indicator_of_mem hs]
      simp [Brownian.Ito.indIoc, Set.indicator_of_mem hs]
    · rw [Set.indicator_of_notMem hs]
      simp [Brownian.Ito.indIoc, Set.indicator_of_notMem hs]
  simp_rw [hpt]
  exact setIntegral_Icc_indicator_Ioc ha _
omit [MeasurableSpace E] [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- A weighted integrand restricted to `(a, b]`, paired with the window indicator, integrates
over the horizon `[0, b]` to the weight times the integral of the integrand over `(a, b]`. -/
theorem setIntegral_Icc_mul_indIoc_mul {V : Ω → ℝ} {a b : ℝ} (ha : 0 ≤ a) (ω : Ω) :
    ∫ s in Set.Icc (0 : ℝ) b,
        (V ω * indIoc Ω a b ω s * H ω s) * indIoc Ω a b ω s ∂volume
      = V ω * ∫ s in Set.Ioc a b, H ω s ∂volume := by
  have hpt : ∀ s : ℝ, (V ω * indIoc Ω a b ω s * H ω s) * indIoc Ω a b ω s
      = (Set.Ioc a b).indicator (fun u => V ω * H ω u) s := by
    intro s
    by_cases hs : s ∈ Set.Ioc a b
    · rw [Set.indicator_of_mem hs]
      simp [Brownian.Ito.indIoc, Set.indicator_of_mem hs]
    · rw [Set.indicator_of_notMem hs]
      simp [Brownian.Ito.indIoc, Set.indicator_of_notMem hs]
  simp_rw [hpt]
  rw [setIntegral_Icc_indicator_Ioc ha _, integral_const_mul]
end BrownianCell

end LevyDriver

end LevyStochCalc.Driver


