-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoTimeRiemann_F000
-- name    : LevyStochCalc_Brownian_ItoTimeRiemann_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:31:43.93389+00:00
-- url     : https://prove2.me/theorems/3adb7eae-b4ec-4482-8301-964521d2a793
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoTimeRiemann
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoTimeRiemann. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFormulaGrid_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Frozen-weight Riemann sums of the Itô formula

Freezing a Lipschitz function of a continuous Itô process at the left endpoints of a uniform
grid and pairing it with the cell integrals of a bounded time density gives a Riemann sum for
`∫_0^T φ(X_s)·w_s ds`, with an `L¹` error of order `√(T/m)`. Both the process's own drift and
the squared diffusion coefficient are admissible densities.

## Main statements

* `LevyStochCalc.Brownian.Ito.sum_setIntegral_unifGrid` — the cells of the uniform grid
  partition the time integral.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_frozenRiemann_sub_le` — the `L¹` error
  of a frozen-weight Riemann sum.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The absolute value of a difference is at most the sum of the absolute values. -/
theorem abs_sub_le_abs_add_abs (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [sub_eq_add_neg]
  simpa using abs_add_le a (-b)
/-- A bounded measurable function is interval integrable on every interval. -/
theorem intervalIntegrable_of_bounded {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ}
    (hgM : ∀ s, |g s| ≤ M) (a b : ℝ) : IntervalIntegrable g volume a b :=
  intervalIntegrable_iff.mpr
    (integrableOn_of_bounded_of_measurable hg hgM (by simp [Set.uIoc_eq_union]))
/-- **The uniform grid partitions the time integral.** -/
theorem sum_setIntegral_unifGrid {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) {g : ℝ → ℝ}
    (hg : Measurable g) {M : ℝ} (hgM : ∀ s, |g s| ≤ M) :
    ∑ i ∈ Finset.range m, ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
        g s ∂volume
      = ∫ s in Set.Ioc (0 : ℝ) T, g s ∂volume := by
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := unifGrid T m) (f := g) (μ := volume) (n := m)
    (fun k _ => intervalIntegrable_of_bounded hg hgM _ _)
  rw [unifGrid_zero, unifGrid_self hm0] at hsum
  rw [← intervalIntegral.integral_of_le hT.le, ← hsum]
  exact Finset.sum_congr rfl fun i _ =>
    (intervalIntegral.integral_of_le (unifGrid_lt_succ hT hm0 i).le).symm
section Riemann

variable {P : Measure Ω} [IsProbabilityMeasure P] {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}
  {H : Ω → ℝ → ℝ} {hm : Measurable (Function.uncurry H)}
  {hp : Probability.ProgressivelyMeasurable ℱ H}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → ℝ} {bdrift : Ω → ℝ → ℝ} {X : ℝ → Ω → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

end Riemann

end LevyStochCalc.Brownian.Ito


