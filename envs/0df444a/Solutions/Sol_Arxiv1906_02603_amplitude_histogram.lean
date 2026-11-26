-- Prove2me | solution 1 for Arxiv1906_02603.amplitude_histogram
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T04:35:20.228801+00:00
-- url     : https://prove2.me/submissions/b541344f-6f10-41dc-a046-1adb6d893150

import Mathlib
import Definitions.Def_Arxiv1906_02603_Basic

set_option autoImplicit false

open MeasureTheory Set Filter Topology

open Arxiv1906_02603 in
theorem solution (N0 A0 amin b : ℝ) (hN0 : 0 < N0) (hA0 : 0 < A0) (hamin : 0 ≤ amin) :
    (∀ a : ℝ, amin < a →
      vesselDensity N0 b a / deriv (amplitudeOfRadius A0 amin) a =
        ampHist N0 A0 amin b (amplitudeOfRadius A0 amin a)) ∧
    (∀ A : ℝ, 0 < A → amin < (A / A0) ^ 2 + amin ∧
      amplitudeOfRadius A0 amin ((A / A0) ^ 2 + amin) = A) ∧
    Measure.map (amplitudeOfRadius A0 amin)
        ((volume.restrict (Ioi amin)).withDensity
          (fun a => ENNReal.ofReal (vesselDensity N0 b a))) =
      (volume.restrict (Ioi 0)).withDensity (fun A => ENNReal.ofReal (ampHist N0 A0 amin b A)) := by
  have inv : ∀ A : ℝ, 0 < A → amin < (A / A0) ^ 2 + amin ∧
      amplitudeOfRadius A0 amin ((A / A0) ^ 2 + amin) = A := by
    intro A hA
    refine ⟨by have : 0 < (A / A0) ^ 2 := by positivity
               linarith, ?_⟩
    simp only [amplitudeOfRadius, add_sub_cancel_right, Real.sqrt_sq (div_pos hA hA0).le]
    field_simp
  refine ⟨?_, inv, ?_⟩
  · intro a ha
    have hs : 0 < Real.sqrt (a - amin) := Real.sqrt_pos.2 (by linarith)
    have hd : deriv (amplitudeOfRadius A0 amin) a = A0 / (2 * Real.sqrt (a - amin)) := by
      have := ((((hasDerivAt_id' a).sub_const amin).sqrt (by simp; linarith)).const_mul A0)
      unfold amplitudeOfRadius
      rw [this.deriv]; field_simp
    rw [hd]
    have ha0 : 0 < a := by linarith
    simp only [ampHist, vesselDensity, amplitudeOfRadius]
    rw [mul_div_cancel_left₀ _ hA0.ne', Real.sq_sqrt (by linarith), sub_add_cancel,
      Real.rpow_neg ha0.le]
    have h2 : 0 < a ^ b := Real.rpow_pos_of_pos ha0 b
    field_simp
  · have hfm : Measurable (amplitudeOfRadius A0 amin) := by
      unfold amplitudeOfRadius; fun_prop
    obtain ⟨ψ, hψ⟩ : ∃ ψ : ℝ → ℝ, ψ = fun A => (A / A0) ^ 2 + amin := ⟨_, rfl⟩
    ext t ht
    rw [Measure.map_apply hfm ht, withDensity_apply _ (hfm ht), withDensity_apply _ ht,
      Measure.restrict_restrict (hfm ht), Measure.restrict_restrict ht]
    have hmeas : MeasurableSet (t ∩ Ioi 0) := ht.inter measurableSet_Ioi
    have himg : amplitudeOfRadius A0 amin ⁻¹' t ∩ Ioi amin = ψ '' (t ∩ Ioi 0) := by
      ext a; simp only [mem_inter_iff, mem_preimage, mem_Ioi, mem_image, hψ]
      constructor
      · rintro ⟨h1, h2⟩
        have hs : 0 < Real.sqrt (a - amin) := Real.sqrt_pos.2 (by linarith)
        refine ⟨A0 * Real.sqrt (a - amin), ⟨h1, mul_pos hA0 hs⟩, ?_⟩
        rw [mul_div_cancel_left₀ _ hA0.ne', Real.sq_sqrt (by linarith)]; ring
      · rintro ⟨A, ⟨h1, h2⟩, rfl⟩
        obtain ⟨i1, i2⟩ := inv A h2
        exact ⟨by rw [i2]; exact h1, i1⟩
    rw [himg, lintegral_image_eq_lintegral_abs_deriv_mul hmeas (f' := fun A => 2 * A / A0 ^ 2)]
    · refine setLIntegral_congr_fun hmeas ?_
      intro A hA
      have hA' : 0 < A := hA.2
      have hp : 0 < (A / A0) ^ 2 := by positivity
      have hψ0 : 0 < ψ A := by rw [hψ]; positivity
      simp only [vesselDensity, ampHist, abs_of_pos (show 0 < 2 * A / A0 ^ 2 by positivity)]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have hq : (A / A0) ^ 2 + amin = ψ A := by rw [hψ]
      rw [hq, Real.rpow_neg hψ0.le]
      have h2 : 0 < ψ A ^ b := Real.rpow_pos_of_pos hψ0 b
      field_simp
    · intro x _
      rw [hψ]
      refine (((hasDerivAt_id x).div_const A0 |>.pow 2 |>.add_const amin).hasDerivWithinAt).congr_deriv ?_
      simp; field_simp
    · intro x hx y hy hxy
      simp only [hψ, add_left_inj] at hxy
      have := (pow_left_inj₀ (div_pos hx.2 hA0).le (div_pos hy.2 hA0).le two_ne_zero).1 hxy
      field_simp at this; linarith
