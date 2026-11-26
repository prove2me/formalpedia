-- Prove2me | solution 1 for Arxiv1906_02603.appendix_envelope_histogram
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T04:37:27.119951+00:00
-- url     : https://prove2.me/submissions/2ee39e98-e3bb-4e2f-a5ac-4b1b1b8a9c52

import Mathlib
import Definitions.Def_Arxiv1906_02603_Basic

set_option autoImplicit false

open MeasureTheory Set Filter Topology

open Arxiv1906_02603 in
theorem solution (A1 : ℝ) (hA1 : 0 < A1) :
    (∀ x ∈ Ioo (0 : ℝ) 1, |deriv (appendixEnvelope A1) x| = A1 * (2 * x)) ∧
    (∀ y ∈ Ioo (0 : ℝ) A1, Real.sqrt (1 - y / A1) ∈ Ioo (0 : ℝ) 1 ∧
      appendixEnvelope A1 (Real.sqrt (1 - y / A1)) = y) ∧
    Measure.map (appendixEnvelope A1) (volume.restrict (Ioo (0 : ℝ) 1)) =
      (volume.restrict (Ioo (0 : ℝ) A1)).withDensity (fun y => ENNReal.ofReal (appendixHist A1 y)) ∧
    Tendsto (appendixHist A1) (𝓝[<] A1) atTop := by
  have p2 : ∀ y ∈ Ioo (0 : ℝ) A1, Real.sqrt (1 - y / A1) ∈ Ioo (0 : ℝ) 1 ∧
      appendixEnvelope A1 (Real.sqrt (1 - y / A1)) = y := by
    intro y ⟨h1, h2⟩
    have hq : y / A1 < 1 := (div_lt_one hA1).2 h2
    have hq0 : 0 < y / A1 := div_pos h1 hA1
    refine ⟨⟨Real.sqrt_pos.2 (by linarith), ?_⟩, ?_⟩
    · rw [Real.sqrt_lt' one_pos]; linarith
    · simp only [appendixEnvelope]; rw [Real.sq_sqrt (by linarith)]; field_simp; ring
  refine ⟨?_, p2, ?_, ?_⟩
  · intro x hx
    have hd : HasDerivAt (appendixEnvelope A1) (A1 * (-(2 * x))) x := by
      unfold appendixEnvelope
      have := ((hasDerivAt_pow 2 x).const_sub 1).const_mul A1
      refine this.congr_deriv ?_; simp
    rw [hd.deriv, mul_neg, abs_neg, abs_of_pos (mul_pos hA1 (by linarith [hx.1]))]
  · have hfm : Measurable (appendixEnvelope A1) := by unfold appendixEnvelope; fun_prop
    obtain ⟨ψ, hψ⟩ : ∃ ψ : ℝ → ℝ, ψ = fun y => Real.sqrt (1 - y / A1) := ⟨_, rfl⟩
    ext t ht
    rw [Measure.map_apply hfm ht, withDensity_apply _ ht, Measure.restrict_apply (hfm ht),
      Measure.restrict_restrict ht]
    have hmeas : MeasurableSet (t ∩ Ioo 0 A1) := ht.inter measurableSet_Ioo
    have himg : appendixEnvelope A1 ⁻¹' t ∩ Ioo 0 1 = ψ '' (t ∩ Ioo 0 A1) := by
      ext x; simp only [mem_inter_iff, mem_preimage, mem_image, hψ]
      constructor
      · rintro ⟨h1, h2⟩
        have hx2 : x ^ 2 < 1 := by nlinarith [h2.1, h2.2]
        have hy : appendixEnvelope A1 x ∈ Ioo 0 A1 := by
          simp only [appendixEnvelope, mem_Ioo]
          constructor
          · exact mul_pos hA1 (by linarith)
          · have : 0 < x ^ 2 := by have := h2.1; positivity
            nlinarith
        refine ⟨appendixEnvelope A1 x, ⟨h1, hy⟩, ?_⟩
        simp only [appendixEnvelope]
        rw [show 1 - A1 * (1 - x ^ 2) / A1 = x ^ 2 by field_simp; ring, Real.sqrt_sq h2.1.le]
      · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
        obtain ⟨a, b⟩ := p2 y h2
        exact ⟨by rw [b]; exact h1, a⟩
    rw [himg, ← setLIntegral_one, lintegral_image_eq_lintegral_abs_deriv_mul hmeas
      (f' := fun y => -(1 / A1) / (2 * Real.sqrt (1 - y / A1)))]
    · refine setLIntegral_congr_fun hmeas ?_
      intro y hy
      have hs : 0 < Real.sqrt (1 - y / A1) := (p2 y hy.2).1.1
      simp only [mul_one, appendixHist]
      congr 1
      rw [neg_div, abs_neg, abs_of_pos (by positivity)]
      field_simp
    · intro y hy
      have hs : 1 - y / A1 ≠ 0 := ne_of_gt (by
        have := (div_lt_one hA1).2 hy.2.2; linarith)
      rw [hψ]
      refine (((hasDerivAt_id' y).div_const A1).const_sub 1 |>.sqrt hs |>.hasDerivWithinAt).congr_deriv ?_
      ring
    · intro x hx y hy hxy
      simp only [hψ] at hxy
      have hx1 : 0 ≤ 1 - x / A1 := by have := (div_lt_one hA1).2 hx.2.2; linarith
      have hy1 : 0 ≤ 1 - y / A1 := by have := (div_lt_one hA1).2 hy.2.2; linarith
      have := (Real.sqrt_inj hx1 hy1).1 hxy
      field_simp at this; linarith
  · have hg : Tendsto (fun y => 2 * A1 * Real.sqrt (1 - y / A1)) (𝓝[<] A1) (𝓝[>] 0) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have : Continuous (fun y => 2 * A1 * Real.sqrt (1 - y / A1)) := by fun_prop
        have h := this.tendsto A1
        rw [div_self hA1.ne', sub_self, Real.sqrt_zero, mul_zero] at h
        exact h.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with y hy
        have := (div_lt_one hA1).2 (show y < A1 from hy)
        exact mul_pos (by linarith) (Real.sqrt_pos.2 (by linarith))
    have := tendsto_inv_nhdsGT_zero.comp hg
    refine this.congr ?_
    intro y; simp [appendixHist, Function.comp]
