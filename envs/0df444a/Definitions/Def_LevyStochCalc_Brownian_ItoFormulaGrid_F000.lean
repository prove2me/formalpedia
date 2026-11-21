-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoFormulaGrid_F000
-- name    : LevyStochCalc_Brownian_ItoFormulaGrid_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:19:10.076939+00:00
-- url     : https://prove2.me/theorems/47e56faf-d4cc-480e-a342-26e0956e6ba0
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoFormulaGrid
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoFormulaGrid. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoProcess_F000
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The uniform grid and the third-moment remainder

The uniform partition of `[0, T]` into `m` cells, and the bound it gives for the sum of third
absolute moments of the increments of an Itô process — the size of the Taylor remainder in
Itô's formula.

## Main statements

* `LevyStochCalc.Brownian.Ito.unifGrid` — the uniform grid on `[0, T]`.
* `LevyStochCalc.Brownian.Ito.SimplePredictable.ofUnifGrid` — the simple integrand carried by
  the uniform grid.
* `LevyStochCalc.Brownian.Ito.sum_integral_abs_sub_pow_three_le` — the sum of third absolute
  moments of the Itô-integral increments across the grid, of order `m^{-1/2}`.
* `LevyStochCalc.Brownian.Ito.sum_integral_abs_itoIncrement_pow_three_le` — the same for the
  increments of a full Itô process, drift included.
* `LevyStochCalc.Brownian.Ito.tendsto_riemann_weighted_unifGrid` — the Riemann sums of a
  continuous weight against a bounded density converge as the grid refines.
* `LevyStochCalc.Brownian.Ito.exists_unifGrid_cell` — every time in `(0, T]` lies in a cell.
* `LevyStochCalc.Brownian.Ito.abs_ofUnifGrid_eval_sub_le` — the grid step weight is within the
  weight's modulus of continuity at the mesh.
* `LevyStochCalc.Brownian.Ito.lintegral_sq_sub_le_of_bound` — a uniform pathwise bound on
  `(0, T]` gives the `L²` distance over the window.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The uniform grid on `[0, T]` with `m` cells. -/
noncomputable def unifGrid (T : ℝ) (m : ℕ) (i : ℕ) : ℝ := (i : ℝ) * T / (m : ℝ)
@[simp] theorem unifGrid_zero (T : ℝ) (m : ℕ) : unifGrid T m 0 = 0 := by simp [unifGrid]
theorem unifGrid_self {T : ℝ} {m : ℕ} (hm : m ≠ 0) : unifGrid T m m = T := by
  rw [unifGrid]
  field_simp
theorem unifGrid_succ_sub {T : ℝ} {m : ℕ} (hm : m ≠ 0) (i : ℕ) :
    unifGrid T m (i + 1) - unifGrid T m i = T / (m : ℝ) := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [unifGrid, unifGrid]
  push_cast
  field_simp
  ring
theorem unifGrid_nonneg {T : ℝ} (hT : 0 ≤ T) (m i : ℕ) : 0 ≤ unifGrid T m i := by
  rw [unifGrid]
  positivity
theorem unifGrid_lt_succ {T : ℝ} (hT : 0 < T) {m : ℕ} (hm : m ≠ 0) (i : ℕ) :
    unifGrid T m i < unifGrid T m (i + 1) := by
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
  have h := unifGrid_succ_sub (T := T) hm i
  have : 0 < T / (m : ℝ) := div_pos hT hm'
  linarith
theorem unifGrid_le {T : ℝ} (hT : 0 ≤ T) {m i : ℕ} (hi : i ≤ m) (hm : m ≠ 0) :
    unifGrid T m i ≤ T := by
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
  rw [unifGrid, div_le_iff₀ hm']
  have : (i : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hi
  nlinarith
section ThirdMomentSum

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

end ThirdMomentSum

section RiemannLimit

end RiemannLimit

section ItoIncrement

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

end ItoIncrement

end LevyStochCalc.Brownian.Ito


