-- Prove2me | Definitions.Def_MarkovProcess_V3H_Semigroup_Duhamel_d67aa5ca
-- name    : MarkovProcess_V3H_Semigroup_Duhamel_d67aa5ca
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:16:31.930359+00:00
-- url     : https://prove2.me/theorems/e15fcb0c-2f40-4f90-97a7-d56713b61b96
-- title:
--   MarkovProcess: MarkovProcess_V3H_Semigroup_Duhamel_d67aa5ca
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Duhamel estimates for bounded generators

This file gives the variation identity and contraction bounds needed to compare
exponentials of commuting bounded generators.  The identity is oriented as
`exp (t B) - exp (t A)`, so its integrand acts on `(B - A) x` and the resulting
estimate is immediately applicable to Yosida approximants.
-/

open MeasureTheory NormedSpace Set

namespace MarkovProcess.Semigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/- Head-class caches: the repeated closed instance searches in this file are all
rooted at the operator type `E →L[ℝ] E`; resolving each once here keeps the
normed-hierarchy walk on `E` from being replayed at every `•` and `exp`. -/
private instance cacheSMulCLM : SMul ℝ (E →L[ℝ] E) := inferInstance
private instance cacheAlgebraCLM : Algebra ℝ (E →L[ℝ] E) := inferInstance
private instance cacheIsTopologicalRingCLM : IsTopologicalRing (E →L[ℝ] E) := inferInstance
private instance cacheCompleteSpaceCLM : CompleteSpace (E →L[ℝ] E) := inferInstance
/- `NormedSpace.exp`'s continuity lemma is now stated for a `ℚ`-normed algebra (the field
argument was dropped); this restricts the existing `NormedAlgebra ℝ (E →L[ℝ] E)` instance
along `ℚ ↪ ℝ` so `exp_continuous`/`fun_prop` can find it on `E →L[ℝ] E`. -/
private noncomputable instance cacheNormedAlgebraRatCLM : NormedAlgebra ℚ (E →L[ℝ] E) :=
  NormedAlgebra.restrictScalars ℚ ℝ (E →L[ℝ] E)

/-- Duhamel's identity for two commuting bounded generators, applied to a vector. -/
theorem p2m_embedded_845c3b1ff191bf83 (A B : E →L[ℝ] E) (hAB : Commute A B)
    (t : ℝ) (x : E) :
    exp (t • B) x - exp (t • A) x =
      ∫ s in 0..t, exp ((t - s) • A) (exp (s • B) ((B - A) x)) := by
  let F : ℝ → E := fun s ↦ exp ((t - s) • A) (exp (s • B) x)
  let F' : ℝ → E :=
    fun s ↦ exp ((t - s) • A) (exp (s • B) ((B - A) x))
  have hderiv : ∀ s : ℝ,
      HasDerivAt F (exp ((t - s) • A) (exp (s • B) ((B - A) x))) s := by
    intro s
    have haffine : HasDerivAt (fun u : ℝ ↦ t - u) (-1) s :=
      by simpa only [Pi.sub_apply, id_eq, zero_sub] using!
        (hasDerivAt_const s t).sub (hasDerivAt_id s)
    have hleft := HasDerivAt.scomp (𝕜 := ℝ) s
      (hasDerivAt_exp_smul_const A (t - s)) haffine
    have hright := HasDerivAt.clm_apply (hasDerivAt_exp_smul_const B s)
      (hasDerivAt_const s x)
    have hproduct := HasDerivAt.clm_apply hleft hright
    have hmove : A (exp (s • B) x) = exp (s • B) (A x) := by
      have hscaled : Commute A (s • B) := by
        calc
          A * (s • B) = s • (A * B) := Algebra.mul_smul_comm s A B
          _ = s • (B * A) := congrArg (fun C : E →L[ℝ] E ↦ s • C) hAB.eq
          _ = (s • B) * A := (Algebra.smul_mul_assoc s B A).symm
      have heq : A * exp (s • B) = exp (s • B) * A := hscaled.exp_right
      exact DFunLike.congr_fun heq x
    refine hproduct.congr_deriv ?_
    simp only [one_smul, neg_smul, ContinuousLinearMap.map_zero, add_zero,
      neg_apply, mul_apply_eq_comp, Function.comp_apply, sub_apply, hmove, map_sub]
    abel
  have hint : IntervalIntegrable F' volume 0 t :=
    (by fun_prop : Continuous F').intervalIntegrable 0 t
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ ↦ hderiv s) hint
  dsimp only [F] at hFTC
  simpa only [sub_zero, sub_self, zero_smul, exp_zero, one_apply_eq_self]
    using hFTC.symm

/-- Duhamel's contraction estimate for two commuting bounded generators. -/
theorem p2m_embedded_cfdd32977de215ab (A B : E →L[ℝ] E) (hAB : Commute A B)
    {t : ℝ} (ht : 0 ≤ t)
    (hA : ∀ s ∈ Icc (0 : ℝ) t, ‖exp (s • A)‖ ≤ 1)
    (hB : ∀ s ∈ Icc (0 : ℝ) t, ‖exp (s • B)‖ ≤ 1) (x : E) :
    ‖exp (t • B) x - exp (t • A) x‖ ≤ t * ‖(B - A) x‖ := by
  rw [_root_.MarkovProcess.Semigroup.p2m_embedded_845c3b1ff191bf83 A B hAB t x]
  calc
    ‖∫ s in 0..t, exp ((t - s) • A) (exp (s • B) ((B - A) x))‖
        ≤ ‖(B - A) x‖ * |t - 0| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs ↦ ?_
      rw [uIoc_of_le ht] at hs
      have hsIcc : s ∈ Icc (0 : ℝ) t := ⟨hs.1.le, hs.2⟩
      have hts : t - s ∈ Icc (0 : ℝ) t :=
        ⟨sub_nonneg.mpr hs.2, sub_le_self t hs.1.le⟩
      calc
        ‖exp ((t - s) • A) (exp (s • B) ((B - A) x))‖
            ≤ ‖exp ((t - s) • A)‖ * ‖exp (s • B) ((B - A) x)‖ :=
          (exp ((t - s) • A)).le_opNorm _
        _ ≤ 1 * ‖exp (s • B) ((B - A) x)‖ :=
          mul_le_mul_of_nonneg_right (hA (t - s) hts) (norm_nonneg _)
        _ = ‖exp (s • B) ((B - A) x)‖ := one_mul _
        _ ≤ ‖exp (s • B)‖ * ‖(B - A) x‖ :=
          (exp (s • B)).le_opNorm _
        _ ≤ 1 * ‖(B - A) x‖ :=
          mul_le_mul_of_nonneg_right (hB s hsIcc) (norm_nonneg _)
        _ = ‖(B - A) x‖ := one_mul _
    _ = t * ‖(B - A) x‖ := by rw [sub_zero, abs_of_nonneg ht, mul_comm]

/-- A contractive bounded exponential moves a vector by at most time times the
norm of its generator applied to that vector. -/
theorem norm_exp_apply_sub_le (A : E →L[ℝ] E) {t : ℝ} (ht : 0 ≤ t)
    (hA : ∀ s ∈ Icc (0 : ℝ) t, ‖exp (s • A)‖ ≤ 1) (x : E) :
    ‖exp (t • A) x - x‖ ≤ t * ‖A x‖ := by
  have hzero : ∀ s ∈ Icc (0 : ℝ) t,
      ‖exp (s • (0 : E →L[ℝ] E))‖ ≤ 1 := by
    intro s hs
    simpa only [smul_zero, exp_zero] using! ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E)
  have h := _root_.MarkovProcess.Semigroup.p2m_embedded_cfdd32977de215ab (0 : E →L[ℝ] E) A
    (Commute.zero_left A) ht hzero hA x
  simpa only [smul_zero, exp_zero, one_apply_eq_self, sub_zero] using h

end MarkovProcess.Semigroup


