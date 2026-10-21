-- Prove2me | solution 1 for AmbDiversify.Smooth.smoothCE_raise_upper_le
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T18:01:45.008213+00:00
-- url     : https://prove2.me/submissions/c1c911e4-6fed-4469-a15d-891624b9f2cf

import Mathlib
import Definitions.Def_AmbDiversify_Smooth_Model

set_option autoImplicit false
open AmbDiversify.Smooth

theorem ce_spec (φ : ℝ → ℝ) (hc : Continuous φ) (μ a b : ℝ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    φ (smoothCE φ μ a b) = μ * φ a + (1 - μ) * φ b := by
  have hex : ∃ c, φ c = μ * φ a + (1 - μ) * φ b := by
    have hmem : μ * φ a + (1 - μ) * φ b ∈ Set.uIcc (φ a) (φ b) := by
      rw [Set.mem_uIcc]
      rcases le_total (φ a) (φ b) with h | h
      · left; constructor <;> nlinarith
      · right; constructor <;> nlinarith
    obtain ⟨c, _, hc'⟩ := intermediate_value_uIcc (a := a) (b := b) hc.continuousOn hmem
    exact ⟨c, hc'⟩
  exact Function.invFun_eq hex

theorem raise_le (φ : ℝ → ℝ) (hφ : IsAmbiguityFunction φ)
    (μ x1 x2 d : ℝ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hx : x1 ≤ x2) (hd : 0 ≤ d) :
    smoothCE φ μ x1 (x2 + d) ≤ smoothCE φ μ x1 x2 + (1 - μ) * d := by
  obtain ⟨h2, h1, hconc⟩ := hφ
  have hs : StrictMono φ := strictMono_of_deriv_pos h1
  have hcont : Continuous φ := h2.continuous
  have hc : φ (smoothCE φ μ x1 x2) = μ * φ x1 + (1 - μ) * φ x2 := ce_spec φ hcont μ _ _ hμ0 hμ1
  have hc' : φ (smoothCE φ μ x1 (x2 + d)) = μ * φ x1 + (1 - μ) * φ (x2 + d) :=
    ce_spec φ hcont μ _ _ hμ0 hμ1
  generalize smoothCE φ μ x1 x2 = c at hc ⊢
  generalize smoothCE φ μ x1 (x2 + d) = c' at hc' ⊢
  have hμ' : 0 ≤ 1 - μ := by linarith
  have hcx2 : c ≤ x2 := by
    apply hs.le_iff_le.1
    rw [hc]
    have := hs.monotone hx
    nlinarith
  -- increments of a concave function decrease
  have hinc : φ (x2 + d) + φ c ≤ φ (c + d) + φ x2 := by
    rcases eq_or_lt_of_le (show 0 ≤ x2 - c + d by linarith) with h0 | hpos
    · have hd0 : d = 0 := by linarith
      have hx0 : x2 = c := by linarith
      subst hd0; subst hx0; linarith
    · have hs0 : 0 ≤ d / (x2 - c + d) := div_nonneg hd hpos.le
      have hs1 : 0 ≤ 1 - d / (x2 - c + d) := by
        rw [sub_nonneg, div_le_one hpos]; linarith
      have e1 := @hconc.2 c (Set.mem_univ _) (x2 + d) (Set.mem_univ _)
        (1 - d / (x2 - c + d)) (d / (x2 - c + d)) hs1 hs0 (by ring)
      have e2 := @hconc.2 c (Set.mem_univ _) (x2 + d) (Set.mem_univ _)
        (d / (x2 - c + d)) (1 - d / (x2 - c + d)) hs0 hs1 (by ring)
      have q1 : (1 - d / (x2 - c + d)) • c + (d / (x2 - c + d)) • (x2 + d) = c + d := by
        simp only [smul_eq_mul]; field_simp; ring
      have q2 : (d / (x2 - c + d)) • c + (1 - d / (x2 - c + d)) • (x2 + d) = x2 := by
        simp only [smul_eq_mul]; field_simp; ring
      rw [q1] at e1
      rw [q2] at e2
      simp only [smul_eq_mul] at e1 e2
      linarith
  have hconc2 : (1 - μ) * φ (c + d) + μ * φ c ≤ φ (c + (1 - μ) * d) := by
    have := @hconc.2 c (Set.mem_univ _) (c + d) (Set.mem_univ _) μ (1 - μ) hμ0 hμ' (by ring)
    simp only [smul_eq_mul] at this
    have e : μ * c + (1 - μ) * (c + d) = c + (1 - μ) * d := by ring
    rw [e] at this
    linarith
  have hm := mul_le_mul_of_nonneg_left hinc hμ'
  have : φ c' ≤ φ (c + (1 - μ) * d) := by
    rw [hc']
    nlinarith
  have := hs.le_iff_le.1 this
  linarith

theorem solution (φ : ℝ → ℝ) (hφ : IsAmbiguityFunction φ)
    (μ x1 x2 d : ℝ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hx : x1 ≤ x2) (hd : 0 ≤ d) :
    smoothCE φ μ x1 (x2 + d) ≤ smoothCE φ μ x1 x2 + (1 - μ) * d :=
  raise_le φ hφ μ x1 x2 d hμ0 hμ1 hx hd
