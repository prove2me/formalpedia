-- Prove2me | Definitions.Def_SourceProof_5f044d421aced7bf9f1cdb5e
-- name    : SourceProof_5f044d421aced7bf9f1cdb5e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T09:31:23.334383+00:00
-- url     : https://prove2.me/theorems/e082268f-0dbd-4d23-bc0f-c2870e8cf7b2
-- title:
--   LevyStochCalc source module: SourceProof_5f044d421aced7bf9f1cdb5e
-- statement:
--   The original source theorem `LevyStochCalc.Examples.Nonvacuity.abs_expWeightClamp_sub_le` comes from the `NonvacuityBSDEJRate` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_NonvacuityBSDEJRate_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The cell-average rate for the backward equation with the identity generator

For the scalar backward equation

  `Y_t = W_1 + ∫_t^1 Y_s ds − ∫_t^1 Z_s dW_s − ∫_t^1 ∫_ℝ U_s(e) Ñ(ds, de)`

of `NonvacuityBSDEJExp`, the Brownian integrand of every solution triple agrees `P ⊗ dt`-almost
everywhere on `Ω × [0, 1]` with the windowed weight `e^{1-s} 1_{(0, 1]}(s)`, hence with the
globally Lipschitz clamped weight `s ↦ e^{1 - max s 0}`. Transporting the deterministic bound
`LevyStochCalc.BSDEJ.PathRegularity.energy_sub_cellTimeAverage_le_of_lipschitz` along that
agreement gives, for every solution triple and every strictly monotone partition of `[0, 1]` of
mesh at most `δ`, the energy bound `(e δ) ^ 2` for the difference between the integrand and its
pathwise cell average.

The average subtracted here is the pathwise cell average `cellTimeAverage_Z`, not the
`ℱ_{t_n}`-conditional projection; the equation is the single equation with generator
`f(s, y, z, u) = y`, terminal datum `W_1` and horizon `1`.

## Main statements

* `abs_expWeightClamp_sub_le` — the clamped weight `s ↦ e^{1 - max s 0}` is Lipschitz with
  constant `e`.
* `ae_eq_expZ_of_solvesBSDEJ` — the Brownian integrand of a solution triple agrees with `expZ`
  almost everywhere for `P ⊗ dt` on `Ω × [0, 1]`.
* `energy_sub_cellAverage_le_of_solvesBSDEJ` — the cell-average error of the Brownian integrand
  of a solution triple has energy at most `(e δ) ^ 2` on the horizon.
* `exists_solvesBSDEJ_cellAverage_rate` — on a probability space carrying such a driver the
  equation has a solution triple and every solution triple obeys that bound.

## References

* Bouchard, B. & Elie, R., *Discrete-time approximation of decoupled Forward-Backward SDE with
  jumps*, Stochastic Processes Appl. **118(1)**, 2008, pp. 53–75.
* Delong, Ł., *BSDEs with Jumps and their Actuarial and Financial Applications*, Springer 2013,
  §4.1.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Examples.Nonvacuity

open LevyStochCalc.BSDEJ.Solves
open LevyStochCalc.BSDEJ.PathRegularity
open LevyStochCalc.Driver (LevyDriver)

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### The clamped exponential weight -/


theorem _root_.Prove2MeSourceProof.h_5f044d421aced7bf9f1cdb5e (s t : ℝ) :
    |expWeightClamp s - expWeightClamp t| ≤ Real.exp 1 * |s - t| := by
  have key : ∀ x y : ℝ, x ≤ y → LevyStochCalc.Examples.Nonvacuity.expWeightClamp x - LevyStochCalc.Examples.Nonvacuity.expWeightClamp y ≤ Real.exp 1 * (y - x) := by
    intro x y hxy
    have hx : (0 : ℝ) ≤ max x 0 := le_max_right _ _
    have hxy' : max x 0 ≤ max y 0 := max_le_max hxy le_rfl
    have hdiff : max y 0 - max x 0 ≤ y - x := by
      have h1 : y ≤ max x 0 + (y - x) := by
        have hml := le_max_left x (0 : ℝ)
        linarith
      have h2 : (0 : ℝ) ≤ max x 0 + (y - x) := by
        have hmr := le_max_right x (0 : ℝ)
        linarith
      have h3 := max_le h1 h2
      linarith
    have hE : Real.exp (1 - max x 0) - Real.exp (1 - max y 0)
        ≤ Real.exp 1 * (max y 0 - max x 0) := LevyStochCalc.Examples.Nonvacuity.exp_sub_exp_le_of_le hx hxy'
    show Real.exp (1 - max x 0) - Real.exp (1 - max y 0) ≤ Real.exp 1 * (y - x)
    exact hE.trans (mul_le_mul_of_nonneg_left hdiff (Real.exp_pos 1).le)
  rcases le_total s t with h | h
  · have hmon : LevyStochCalc.Examples.Nonvacuity.expWeightClamp t ≤ LevyStochCalc.Examples.Nonvacuity.expWeightClamp s := by
      show Real.exp (1 - max t 0) ≤ Real.exp (1 - max s 0)
      have hst : max s 0 ≤ max t 0 := max_le_max h le_rfl
      exact Real.exp_le_exp.mpr (by linarith)
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ expWeightClamp s - expWeightClamp t),
      abs_of_nonpos (by linarith : s - t ≤ 0), neg_sub]
    exact key s t h
  · have hmon : LevyStochCalc.Examples.Nonvacuity.expWeightClamp s ≤ LevyStochCalc.Examples.Nonvacuity.expWeightClamp t := by
      show Real.exp (1 - max s 0) ≤ Real.exp (1 - max t 0)
      have hst : max t 0 ≤ max s 0 := max_le_max h le_rfl
      exact Real.exp_le_exp.mpr (by linarith)
    rw [abs_of_nonpos (by linarith : expWeightClamp s - expWeightClamp t ≤ 0),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ s - t), neg_sub]
    exact key t s h
/-! ### The Brownian integrand of a solution -/

/-! ### The pathwise cell average of a solution -/

/-! ### The rate -/

/-! ### The witness -/

/-! ### The uniform partition -/

variable {M : ℕ}

/-! ### The rate along the uniform partitions -/

end LevyStochCalc.Examples.Nonvacuity


