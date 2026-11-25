-- Prove2me | solution 1 for Arxiv2105_07250.emission_time_formula
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T20:36:20.6919+00:00
-- url     : https://prove2.me/submissions/408ff969-7958-4882-b8ae-946fed75a956

import Mathlib
import Definitions.Def_Arxiv2105_07250_Basic

open MeasureTheory Filter Topology

open Arxiv2105_07250 in
theorem solution (c : ℝ) (hc : 0 < c) (v : Plane) (hv : ‖v‖ < c) (x : Plane) (t : ℝ) :
    0 ≤ q2 c t x v ∧
    c * (t - emissionTime c t x v) = ‖x - emissionTime c t x v • v‖ ∧
    (∀ t' : ℝ, c * (t - t') = ‖x - t' • v‖ ↔ t' = emissionTime c t x v) ∧
    (∀ t' : ℝ, heaviside (t - t' - ‖x - t' • v‖ / c) =
      if t' ≤ emissionTime c t x v then 1 else 0) := by
  have hv0 : 0 ≤ ‖v‖ := norm_nonneg v
  set a := c ^ 2 - ‖v‖ ^ 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; nlinarith
  have hns : ∀ s : ℝ, ‖x - s • v‖ ^ 2 = ‖x‖ ^ 2 - 2 * s * inner ℝ x v + s ^ 2 * ‖v‖ ^ 2 := by
    intro s
    rw [norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]; ring
  -- quadratic identity
  have hQ : ∀ s : ℝ, c ^ 2 * (t - s) ^ 2 - ‖x - s • v‖ ^ 2 = a * ((s - q1 c t x v) ^ 2 - q2 c t x v) := by
    intro s
    rw [hns, q2, q1]
    rw [← ha_def]
    field_simp
    ring
  have hq2 : 0 ≤ q2 c t x v := by
    have key : a ^ 2 * q2 c t x v = a * ‖x - t • v‖ ^ 2 + (inner ℝ x v - t * ‖v‖ ^ 2) ^ 2 := by
      rw [hns, q2, q1, ← ha_def]
      field_simp
      rw [ha_def]; ring
    have : 0 ≤ a ^ 2 * q2 c t x v := by rw [key]; positivity
    by_contra hneg
    have : a ^ 2 * q2 c t x v < 0 := mul_neg_of_pos_of_neg (by positivity) (lt_of_not_ge hneg)
    linarith
  set e := emissionTime c t x v with he_def
  have hsq := Real.sq_sqrt hq2
  have hsn := Real.sqrt_nonneg (q2 c t x v)
  have hQe : c ^ 2 * (t - e) ^ 2 - ‖x - e • v‖ ^ 2 = 0 := by
    rw [hQ, he_def, emissionTime]; rw [show q1 c t x v - Real.sqrt (q2 c t x v) - q1 c t x v
      = -Real.sqrt (q2 c t x v) by ring, neg_sq, hsq]; ring
  have het : e ≤ t := by
    have h1 := hQ t
    have h2 : a * ((t - q1 c t x v) ^ 2 - q2 c t x v) ≤ 0 := by
      rw [← h1]; simp only [sub_self]; nlinarith [sq_nonneg ‖x - t • v‖]
    have h3 : (t - q1 c t x v) ^ 2 ≤ Real.sqrt (q2 c t x v) ^ 2 := by
      rw [hsq]; by_contra h; push Not at h; nlinarith
    have h4 := abs_le_of_sq_le_sq' h3 hsn
    rw [he_def, emissionTime]
    linarith [h4.1]
  have hfe : c * (t - e) = ‖x - e • v‖ := by
    have h0 : 0 ≤ c * (t - e) := mul_nonneg hc.le (by linarith)
    have : (c * (t - e)) ^ 2 = ‖x - e • v‖ ^ 2 := by nlinarith
    exact (sq_eq_sq₀ h0 (norm_nonneg _)).1 this
  -- f strictly decreasing
  have hanti : StrictAnti (fun s : ℝ => c * (t - s) - ‖x - s • v‖) := by
    intro s u hsu
    simp only
    have h1 : ‖x - s • v‖ - ‖x - u • v‖ ≤ ‖(x - s • v) - (x - u • v)‖ := norm_sub_norm_le _ _
    have h2 : ‖(x - s • v) - (x - u • v)‖ = (u - s) * ‖v‖ := by
      rw [show (x - s • v) - (x - u • v) = (u - s) • v by rw [sub_smul]; abel, norm_smul,
        Real.norm_eq_abs, abs_of_pos (by linarith)]
    nlinarith
  have hfe0 : c * (t - e) - ‖x - e • v‖ = 0 := by rw [hfe]; ring
  refine ⟨hq2, hfe, fun t' => ?_, fun t' => ?_⟩
  · constructor
    · intro h
      have : c * (t - t') - ‖x - t' • v‖ = c * (t - e) - ‖x - e • v‖ := by rw [h, hfe0]; ring
      exact hanti.injective this
    · rintro rfl; exact hfe
  · unfold heaviside
    have hiff : 0 ≤ t - t' - ‖x - t' • v‖ / c ↔ t' ≤ e := by
      have : t - t' - ‖x - t' • v‖ / c = (c * (t - t') - ‖x - t' • v‖) / c := by field_simp
      rw [this, div_nonneg_iff]
      constructor
      · rintro (⟨h, -⟩ | ⟨-, h⟩)
        · by_contra hlt; push Not at hlt
          have := hanti hlt; simp only at this; linarith
        · linarith
      · intro h
        left; refine ⟨?_, hc.le⟩
        rcases h.lt_or_eq with h | h
        · have := hanti h; simp only at this; linarith
        · rw [h]; linarith
    by_cases h : t' ≤ e
    · rw [if_pos (hiff.2 h), if_pos h]
    · rw [if_neg (mt hiff.1 h), if_neg h]
