-- Prove2me | Definitions.Def_LevyStochCalc_Probability_CharacterL2_F000
-- name    : LevyStochCalc_Probability_CharacterL2_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:01:19.711726+00:00
-- url     : https://prove2.me/theorems/bb6bfc89-5d87-4858-935d-893e0d1c7271
-- title:
--   Source declarations: LevyStochCalc.Probability.CharacterL2
-- statement:
--   Source-preserving Lean declaration bundle from LevyStochCalc.Probability.CharacterL2, retaining definitions, helper results, proofs and elaboration context where present.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.L2Space

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Characters of real variables in `L²`

For a real frequency `u` the character `x ↦ e^{iux}` has modulus one and is `|u|`-Lipschitz, and
`e^{iux} − 1` is bounded by `|u| |x|` and by two. So along `L²` convergence of real variables
`Y_n → Y` the characters `e^{iuY_n}` converge in `L²`, and a square-integrable `Y` gives a
square-integrable `e^{iuY} − 1` on any measure and a square-integrable `e^{iuY}` on a finite one.
The complex pairing `∫ F G` is the `L²` inner product of `F̄` and `G`, so it is continuous along
`L²` convergence in each argument.

## Main statements

* `LevyStochCalc.Probability.norm_exp_I_mul_sub_one_le_two` — `‖e^{it} − 1‖ ≤ 2`.
* `LevyStochCalc.Probability.integrable_exp_I_mul_mul` — a character times an integrable
  variable is integrable.
* `LevyStochCalc.Probability.memLp_exp_I_mul`, `LevyStochCalc.Probability.memLp_exp_I_mul_sub_one`
  — square integrability of `e^{iuY}` and of `e^{iuY} − 1`.
* `LevyStochCalc.Probability.memLp_mul_of_norm_le` — a bounded multiple of a square-integrable
  variable is square integrable.
* `LevyStochCalc.Probability.tendsto_integral_mul_of_tendsto_eLpNorm` — continuity of the complex
  pairing along `L²` convergence.
* `LevyStochCalc.Probability.tendsto_eLpNorm_ofReal_sub`,
  `LevyStochCalc.Probability.tendsto_eLpNorm_exp_I_mul_sub`,
  `LevyStochCalc.Probability.tendsto_eLpNorm_mul_sub_mul` — `L²` convergence passes to the complex
  embedding, to the characters and to bounded multiples.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace LevyStochCalc.Probability

/-- For real `t`, `‖e^{it} − 1‖ ≤ 2`. -/
theorem norm_exp_I_mul_sub_one_le_two (t : ℝ) :
    ‖Complex.exp (Complex.I * (t : ℂ)) - 1‖ ≤ 2 := by
  refine (norm_sub_le _ _).trans (le_of_eq ?_)
  rw [Complex.norm_exp_I_mul_ofReal, norm_one]
  norm_num
/-- The product of an integrable complex function with the character `e^{iuY}` of a real
function `Y` is integrable. -/
theorem integrable_exp_I_mul_mul {α : Type*} [MeasurableSpace α] {m : Measure α} (u : ℝ)
    {Y : α → ℝ} (hY : AEStronglyMeasurable Y m) {X : α → ℂ} (hX : Integrable X m) :
    Integrable (fun x => Complex.exp (Complex.I * ((u * Y x : ℝ) : ℂ)) * X x) m := by
  refine hX.norm.mono' (((by fun_prop : Continuous fun t : ℝ =>
    Complex.exp (Complex.I * ((u * t : ℝ) : ℂ))).comp_aestronglyMeasurable hY).mul hX.1)
    (Eventually.of_forall fun x => ?_)
  rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
/-- On a finite measure the character `e^{iuY}` of a real function `Y` is square integrable. -/
theorem memLp_exp_I_mul {α : Type*} [MeasurableSpace α] {m : Measure α} [IsFiniteMeasure m]
    (u : ℝ) {Y : α → ℝ} (hY : AEStronglyMeasurable Y m) :
    MemLp (fun x => Complex.exp (Complex.I * ((u * Y x : ℝ) : ℂ))) 2 m :=
  MemLp.of_bound ((by fun_prop : Continuous fun t : ℝ =>
    Complex.exp (Complex.I * ((u * t : ℝ) : ℂ))).comp_aestronglyMeasurable hY) 1
    (Eventually.of_forall fun x => le_of_eq (Complex.norm_exp_I_mul_ofReal _))
/-- For a square-integrable real function `Y`, `e^{iuY} − 1` is square integrable. -/
theorem memLp_exp_I_mul_sub_one {α : Type*} [MeasurableSpace α] {m : Measure α} (u : ℝ)
    {Y : α → ℝ} (hY : MemLp Y 2 m) :
    MemLp (fun x => Complex.exp (Complex.I * ((u * Y x : ℝ) : ℂ)) - 1) 2 m :=
  hY.of_le_mul (c := |u|) (((by fun_prop : Continuous fun t : ℝ =>
    Complex.exp (Complex.I * ((u * t : ℝ) : ℂ)) - 1).comp_aestronglyMeasurable hY.1))
    (Eventually.of_forall fun x => by
      refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans (le_of_eq ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul])
/-- The product of a bounded complex function with a square-integrable one is square
integrable. -/
theorem memLp_mul_of_norm_le {α : Type*} [MeasurableSpace α] {m : Measure α}
    {Z X : α → ℂ} (hZ : AEStronglyMeasurable Z m) {C : ℝ} (hZC : ∀ x, ‖Z x‖ ≤ C)
    (hX : MemLp X 2 m) : MemLp (fun x => Z x * X x) 2 m :=
  hX.of_le_mul (c := C) (hZ.mul hX.1) (Eventually.of_forall fun x => by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hZC x) (norm_nonneg _))
end LevyStochCalc.Probability


