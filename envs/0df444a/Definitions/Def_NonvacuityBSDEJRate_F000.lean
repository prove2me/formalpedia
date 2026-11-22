-- Prove2me | Definitions.Def_NonvacuityBSDEJRate_F000
-- name    : NonvacuityBSDEJRate_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T09:26:06.568553+00:00
-- url     : https://prove2.me/theorems/87efaafb-0ed7-4e00-87e5-925cf35b8250
-- title:
--   Source declarations: NonvacuityBSDEJRate
-- statement:
--   Source-preserving extracted declarations from NonvacuityBSDEJRate. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_PathRegularity_F000
import Definitions.Def_NonvacuityBSDEJExp_F002

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

/-- The exponential weight `e^{1-s}` clamped at the origin, `s ↦ e^{1 - max s 0}`. -/
noncomputable def expWeightClamp : ℝ → ℝ := fun s => Real.exp (1 - max s 0)
/-- At a nonnegative time the clamped weight is the exponential weight. -/
theorem expWeightClamp_of_nonneg {s : ℝ} (hs : 0 ≤ s) :
    expWeightClamp s = Real.exp (1 - s) := by
  show Real.exp (1 - max s 0) = Real.exp (1 - s)
  rw [max_eq_left hs]
/-- On `[0, ∞)` the decrements of `s ↦ e^{1-s}` are at most `e` times the increments of `s`. -/
theorem exp_sub_exp_le_of_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Real.exp (1 - a) - Real.exp (1 - b) ≤ Real.exp 1 * (b - a) := by
  have hexp : Real.exp (1 - a) * Real.exp (a - b) = Real.exp (1 - b) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hfac : Real.exp (1 - a) - Real.exp (1 - b)
      = Real.exp (1 - a) * (1 - Real.exp (a - b)) := by
    rw [mul_sub, mul_one, hexp]
  have hone : 1 - Real.exp (a - b) ≤ b - a := by
    have h := Real.add_one_le_exp (a - b)
    linarith
  have hnn : 0 ≤ 1 - Real.exp (a - b) := by
    have h : Real.exp (a - b) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_zero] at h
    linarith
  have hle : Real.exp (1 - a) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith)
  rw [hfac]
  exact mul_le_mul hle hone hnn (Real.exp_pos 1).le
/-! ### The Brownian integrand of a solution -/

/-! ### The pathwise cell average of a solution -/

/-! ### The rate -/

/-! ### The witness -/

/-! ### The uniform partition -/

variable {M : ℕ}

/-! ### The rate along the uniform partitions -/

end LevyStochCalc.Examples.Nonvacuity


