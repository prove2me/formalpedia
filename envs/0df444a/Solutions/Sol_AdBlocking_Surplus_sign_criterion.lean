-- Prove2me | solution 1 for AdBlocking.Surplus.sign_criterion
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:46:50.791447+00:00
-- url     : https://prove2.me/submissions/a607f1ee-4541-4c44-87df-5220f052f01f

import Mathlib
set_option autoImplicit false
open Filter Topology

lemma sc_hform (a G C D k : ℝ) (ha : 0 < a) (hG : 0 < G) (hk : 0 < k) :
    (a + G / k)⁻¹ * C + ((a + G / k)⁻¹) ^ 2 * D / k
      = k * (C * a * k + C * G + D) / (a * k + G) ^ 2 := by
  have h1 : a * k + G ≠ 0 := by positivity
  have hk' : k ≠ 0 := hk.ne'
  have h2 : a + G / k = (a * k + G) / k := by field_simp
  rw [h2]; field_simp

lemma sc_diff (a G C D k l : ℝ) (ha : 0 < a) (hG : 0 < G) (hk : 0 < k) (hl : 0 < l) :
    l * (C * a * l + C * G + D) / (a * l + G) ^ 2 - k * (C * a * k + C * G + D) / (a * k + G) ^ 2
      = (l - k) * ((G * (C * G + D) - a * (D - C * G) * l) * (a * k + G) + a * G * D * (l - k))
          / ((a * k + G) ^ 2 * (a * l + G) ^ 2) := by
  have h1 : a * k + G ≠ 0 := by positivity
  have h2 : a * l + G ≠ 0 := by positivity
  field_simp
  ring

lemma sc_sub (a G C D k : ℝ) (ha : 0 < a) (hG : 0 < G) (hk : 0 < k) :
    k * (C * a * k + C * G + D) / (a * k + G) ^ 2 - C / a
      = ((D - C * G) * a * k - C * G ^ 2) / (a * (a * k + G) ^ 2) := by
  have h1 : a * k + G ≠ 0 := by positivity
  have h2 : a ≠ 0 := ha.ne'
  field_simp
  ring

theorem solution
    (a G C₀ CΔ : ℝ) (ha : 0 < a) (hG : 0 < G) (hC₀ : 0 < C₀) (hCΔ : 0 < CΔ) :
    let h : ℝ → ℝ := fun κbar =>
      (a + G / κbar)⁻¹ * C₀ + ((a + G / κbar)⁻¹) ^ 2 * CΔ / κbar
    Tendsto h atTop (𝓝 (C₀ / a)) ∧
      (CΔ ≤ C₀ * G →
        StrictMonoOn h (Set.Ioi 0) ∧
        ∀ κbar : ℝ, 0 < κbar → h κbar < C₀ / a) ∧
      (C₀ * G < CΔ →
        ∃ κ₀ : ℝ, 0 < κ₀ ∧
          StrictMonoOn h (Set.Ioc 0 κ₀) ∧
          StrictAntiOn h (Set.Ici κ₀) ∧
          ∃ K : ℝ, 0 < K ∧ ∀ κbar : ℝ, K ≤ κbar → C₀ / a < h κbar) := by
  intro h
  have hF : ∀ k : ℝ, 0 < k →
      h k = k * (C₀ * a * k + C₀ * G + CΔ) / (a * k + G) ^ 2 :=
    fun k hk => sc_hform a G C₀ CΔ k ha hG hk
  have hden : ∀ k l : ℝ, 0 < k → 0 < l →
      0 < (a * k + G) ^ 2 * (a * l + G) ^ 2 := fun k l hk hl => by positivity
  refine ⟨?_, ?_, ?_⟩
  · -- limit
    have h1 : Tendsto (fun κ : ℝ => G / κ) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds tendsto_id
    have h2 : Tendsto (fun κ : ℝ => (a + G / κ)⁻¹) atTop (𝓝 ((a + 0)⁻¹)) :=
      (tendsto_const_nhds.add h1).inv₀ (by simpa using ha.ne')
    have h3 : Tendsto h atTop (𝓝 ((a + 0)⁻¹ * C₀ + ((a + 0)⁻¹) ^ 2 * CΔ * 0)) := by
      have h4 : Tendsto (fun κ : ℝ => κ⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
      have h5 : Tendsto (fun κ : ℝ => (a + G / κ)⁻¹ * C₀
          + ((a + G / κ)⁻¹) ^ 2 * CΔ * κ⁻¹) atTop
          (𝓝 ((a + 0)⁻¹ * C₀ + ((a + 0)⁻¹) ^ 2 * CΔ * 0)) :=
        (h2.mul_const _).add (((h2.pow 2).mul_const _).mul h4)
      refine h5.congr (fun κ => ?_)
      simp only [h, div_eq_mul_inv]
    have : (a + 0)⁻¹ * C₀ + ((a + 0)⁻¹) ^ 2 * CΔ * 0 = C₀ / a := by
      simp [div_eq_inv_mul]
    rwa [this] at h3
  · intro hle
    refine ⟨?_, ?_⟩
    · intro k hk l hl hkl
      have hk : 0 < k := hk
      have hl : 0 < l := hl
      rw [hF k hk, hF l hl]
      have := sc_diff a G C₀ CΔ k l ha hG hk hl
      have hP : 0 < (G * (C₀ * G + CΔ) - a * (CΔ - C₀ * G) * l) * (a * k + G)
          + a * G * CΔ * (l - k) := by
        have h1 : 0 < G * (C₀ * G + CΔ) - a * (CΔ - C₀ * G) * l := by
          nlinarith [mul_nonneg ha.le (mul_nonneg (sub_nonneg.2 hle) hl.le), mul_pos hG hC₀, mul_pos hG hCΔ]
        have h2 : 0 < a * k + G := by positivity
        have h3 : 0 < a * G * CΔ * (l - k) := by
          have := sub_pos.2 hkl
          positivity
        nlinarith [mul_pos h1 h2]
      have : 0 < l * (C₀ * a * l + C₀ * G + CΔ) / (a * l + G) ^ 2
          - k * (C₀ * a * k + C₀ * G + CΔ) / (a * k + G) ^ 2 := by
        rw [this]
        have := sub_pos.2 hkl
        have := hden k l hk hl
        positivity
      linarith
    · intro k hk
      rw [hF k hk, ← sub_neg, sc_sub a G C₀ CΔ k ha hG hk]
      have h1 : (CΔ - C₀ * G) * a * k - C₀ * G ^ 2 < 0 := by
        have : (CΔ - C₀ * G) * a * k ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonpos_of_nonneg (by linarith) ha.le) hk.le
        nlinarith [mul_pos hC₀ (pow_pos hG 2)]
      exact div_neg_of_neg_of_pos h1 (by positivity)
  · intro hlt
    have hE : 0 < CΔ - C₀ * G := by linarith
    have hB : 0 < C₀ * G + CΔ := by positivity
    set κ₀ := G * (C₀ * G + CΔ) / (a * (CΔ - C₀ * G)) with hκ₀
    have hκ₀pos : 0 < κ₀ := by positivity
    have hrel : a * (CΔ - C₀ * G) * κ₀ = G * (C₀ * G + CΔ) := by
      rw [hκ₀]; field_simp
    refine ⟨κ₀, hκ₀pos, ?_, ?_, C₀ * G ^ 2 / (a * (CΔ - C₀ * G)) + 1, by positivity, ?_⟩
    · intro k hk l hl hkl
      have hk : 0 < k := hk.1
      have hl' : 0 < l := hl.1
      have hlκ : l ≤ κ₀ := hl.2
      rw [hF k hk, hF l hl']
      have := sc_diff a G C₀ CΔ k l ha hG hk hl'
      have hP : 0 < (G * (C₀ * G + CΔ) - a * (CΔ - C₀ * G) * l) * (a * k + G)
          + a * G * CΔ * (l - k) := by
        have h1 : 0 ≤ G * (C₀ * G + CΔ) - a * (CΔ - C₀ * G) * l := by
          have : a * (CΔ - C₀ * G) * l ≤ a * (CΔ - C₀ * G) * κ₀ := mul_le_mul_of_nonneg_left hlκ (by positivity)
          linarith
        have h2 : 0 < a * k + G := by positivity
        have h3 : 0 < a * G * CΔ * (l - k) := by
          have := sub_pos.2 hkl
          positivity
        nlinarith [mul_nonneg h1 h2.le]
      have : 0 < l * (C₀ * a * l + C₀ * G + CΔ) / (a * l + G) ^ 2
          - k * (C₀ * a * k + C₀ * G + CΔ) / (a * k + G) ^ 2 := by
        rw [this]
        have := sub_pos.2 hkl
        have := hden k l hk hl'
        positivity
      linarith
    · intro k hk l hl hkl
      have hk' : κ₀ ≤ k := hk
      have hk0 : 0 < k := lt_of_lt_of_le hκ₀pos hk'
      have hl0 : 0 < l := lt_trans hk0 hkl
      rw [hF k hk0, hF l hl0]
      have := sc_diff a G C₀ CΔ l k ha hG hl0 hk0
      -- use symmetric form: roles of k, l swapped
      have hP : (G * (C₀ * G + CΔ) - a * (CΔ - C₀ * G) * k) * (a * l + G)
          + a * G * CΔ * (k - l) < 0 := by
        have h1 : G * (C₀ * G + CΔ) - a * (CΔ - C₀ * G) * k ≤ 0 := by
          have : a * (CΔ - C₀ * G) * κ₀ ≤ a * (CΔ - C₀ * G) * k := mul_le_mul_of_nonneg_left hk' (by positivity)
          linarith
        have h2 : 0 < a * l + G := by positivity
        have h3 : a * G * CΔ * (k - l) < 0 := by
          have := sub_neg.2 hkl
          have : 0 < a * G * CΔ := by positivity
          nlinarith
        nlinarith [mul_nonpos_of_nonpos_of_nonneg h1 h2.le]
      have hneg : 0 < k * (C₀ * a * k + C₀ * G + CΔ) / (a * k + G) ^ 2
          - l * (C₀ * a * l + C₀ * G + CΔ) / (a * l + G) ^ 2 := by
        rw [this]
        have := sub_neg.2 hkl
        have := hden l k hl0 hk0
        exact div_pos (mul_pos_of_neg_of_neg (by linarith) hP) this
      linarith
    · intro k hk
      have hk0 : 0 < k := by
        have : 0 < C₀ * G ^ 2 / (a * (CΔ - C₀ * G)) := by positivity
        linarith
      rw [hF k hk0, ← sub_pos, sc_sub a G C₀ CΔ k ha hG hk0]
      have h1 : 0 < (CΔ - C₀ * G) * a * k - C₀ * G ^ 2 := by
        have h2 : C₀ * G ^ 2 / (a * (CΔ - C₀ * G)) < k := by linarith
        rw [div_lt_iff₀ (by positivity)] at h2
        nlinarith
      exact div_pos h1 (by positivity)
