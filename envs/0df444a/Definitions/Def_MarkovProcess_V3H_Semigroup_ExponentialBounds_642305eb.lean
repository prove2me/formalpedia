-- Prove2me | Definitions.Def_MarkovProcess_V3H_Semigroup_ExponentialBounds_642305eb
-- name    : MarkovProcess_V3H_Semigroup_ExponentialBounds_642305eb
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:16:31.586882+00:00
-- url     : https://prove2.me/theorems/bd920637-2c62-4804-b1c7-66e199527482
-- title:
--   MarkovProcess: MarkovProcess_V3H_Semigroup_ExponentialBounds_642305eb
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Norm bounds for Banach-algebra exponentials

This file records elementary estimates for the exponential in a real Banach algebra.  The
contraction estimate is tailored to exponentials of bounded Yosida-type generators.
-/

namespace MarkovProcess.Semigroup

open NormedSpace

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/- `NormedSpace.exp_add_of_commute`'s continuity lemma is now stated for a `ℚ`-normed algebra
(the field argument was dropped); this restricts the existing `NormedAlgebra ℝ A` instance
along `ℚ ↪ ℝ` so it can be found on `A`. -/
private noncomputable instance cacheNormedAlgebraRatA : NormedAlgebra ℚ A :=
  NormedAlgebra.restrictScalars ℚ ℝ A

/-- The norm of a Banach-algebra exponential is bounded by the scalar exponential of the norm
when the multiplicative identity has norm at most one. -/
theorem p2m_embedded_d16afa0707dac45f (hOne : ‖(1 : A)‖ ≤ 1) (a : A) :
    ‖exp a‖ ≤ Real.exp ‖a‖ := by
  have hscalar : HasSum (fun n : ℕ ↦ (Nat.factorial n : ℝ)⁻¹ * ‖a‖ ^ n)
      (Real.exp ‖a‖) := by
    rw [Real.exp_eq_exp_ℝ]
    simpa only [smul_eq_mul] using!
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (𝔸 := ℝ) ‖a‖)
  rw [exp_eq_tsum ℝ]
  calc
    ‖∑' n : ℕ, (Nat.factorial n : ℝ)⁻¹ • a ^ n‖ ≤
        ∑' n : ℕ, ‖(Nat.factorial n : ℝ)⁻¹ • a ^ n‖ :=
      norm_tsum_le_tsum_norm (norm_expSeries_summable' a)
    _ ≤ ∑' n : ℕ, (Nat.factorial n : ℝ)⁻¹ * ‖a‖ ^ n := by
      exact (norm_expSeries_summable' a).tsum_le_tsum (fun n ↦ by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (Nat.cast_nonneg _))
        cases n with
        | zero => simpa only [pow_zero] using hOne
        | succ n => exact norm_pow_le' a (Nat.succ_pos n))
        hscalar.summable
    _ = Real.exp ‖a‖ := hscalar.tsum_eq



/-- If `Q` is a contraction and `c` is nonnegative, then `exp (c (Q - 1))` is a contraction. -/
theorem p2m_embedded_966fc3c68f77e5f8 [CompleteSpace A]
    (hOne : ‖(1 : A)‖ ≤ 1) {c : ℝ} (hc : 0 ≤ c) {Q : A} (hQ : ‖Q‖ ≤ 1) :
    ‖exp (c • (Q - 1))‖ ≤ 1 := by
  have hsplit : c • (Q - 1) = c • Q + (-c) • (1 : A) := by module
  have hcomm : Commute (c • Q) ((-c) • (1 : A)) := by
    exact (Commute.one_right Q).smul_left c |>.smul_right (-c)
  have hexp_scalar : exp ((-c) • (1 : A)) = algebraMap ℝ A (Real.exp (-c)) := by
    have harg : (-c) • (1 : A) = algebraMap ℝ A (-c) := by
      rw [Algebra.smul_def, mul_one]
    rw [harg, Real.exp_eq_exp_ℝ]
    exact (algebraMap_exp_comm (-c)).symm
  calc
    ‖exp (c • (Q - 1))‖ =
        ‖exp (c • Q) * exp ((-c) • (1 : A))‖ := by
      rw [hsplit, exp_add_of_commute hcomm]
    _ ≤ ‖exp (c • Q)‖ * ‖exp ((-c) • (1 : A))‖ := norm_mul_le _ _
    _ ≤
        Real.exp ‖c • Q‖ * ‖exp ((-c) • (1 : A))‖ :=
      mul_le_mul_of_nonneg_right
        (_root_.MarkovProcess.Semigroup.p2m_embedded_d16afa0707dac45f hOne (c • Q)) (norm_nonneg _)
    _ ≤ Real.exp c * ‖exp ((-c) • (1 : A))‖ := by
      refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
      exact mul_le_of_le_one_right hc hQ
    _ ≤ Real.exp c * Real.exp (-c) := by
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos c).le
      rw [hexp_scalar, norm_algebraMap, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (Real.exp_pos (-c)).le hOne
    _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]



/-- Exponentiating a nonnegative multiple of a contractive endomorphism minus the identity gives
a contractive endomorphism.  This includes the trivial ambient space. -/
theorem norm_exp_continuousLinearMap_smul_sub_id_le_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {c : ℝ} (hc : 0 ≤ c) {Q : E →L[ℝ] E} (hQ : ‖Q‖ ≤ 1) :
    ‖exp (c • (Q - ContinuousLinearMap.id ℝ E))‖ ≤ 1 :=
  _root_.MarkovProcess.Semigroup.p2m_embedded_966fc3c68f77e5f8 ContinuousLinearMap.norm_id_le hc hQ

end MarkovProcess.Semigroup


