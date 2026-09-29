-- Prove2me | solution 1 for AnalyticGeometry.exists_poly_unique_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T20:32:14.324095+00:00
-- url     : https://prove2.me/submissions/0893eaa9-159a-4f42-95c7-8cf97fa94674

import Mathlib
import Definitions.Def_AnalyticGeometry_ZLaurentGT

set_option autoImplicit false

open Polynomial

theorem p5c16_pow_step (a : ℝ) (m : ℕ) : ∀ K : ℕ, ∃ s : Polynomial ℝ,
    (1 - C a * X ^ m) ^ K = 1 - C ((K : ℝ) * a) * X ^ m + X ^ (2 * m) * s := by
  intro K
  induction K with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨s, hs⟩ := ih
    refine ⟨C ((k : ℝ) * a * a) + s * (1 - C a * X ^ m), ?_⟩
    rw [pow_succ, hs]
    have h2 : (X : Polynomial ℝ) ^ (2 * m) = X ^ m * X ^ m := by rw [two_mul, pow_add]
    rw [h2]
    push_cast
    simp only [map_mul, map_add, map_one, map_natCast]
    ring

theorem p5c16_main (r x : ℝ) (hr0 : 0 < r) (hx0 : 0 < x) (hxr : x ≤ r) :
    ∀ m : ℕ, ∃ g : Polynomial ℝ, X ^ (m + 1) ∣ g - 1 ∧
      ∀ y : ℂ, ‖y‖ ≤ r → (aeval y g = 0 ↔ y = (x : ℂ)) := by
  intro m
  induction m with
  | zero =>
    refine ⟨1 - C x⁻¹ * X, ⟨-C x⁻¹, by ring⟩, ?_⟩
    intro y _
    have hx : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
    simp only [map_sub, map_one, map_mul, aeval_C, aeval_X, Complex.coe_algebraMap,
      Complex.ofReal_inv]
    constructor
    · intro h
      field_simp at h
      linear_combination -h
    · intro h
      rw [h]
      field_simp
      ring
  | succ k ih =>
    obtain ⟨g, hdvd, hz⟩ := ih
    obtain ⟨q, hq⟩ := hdvd
    set c := q.coeff 0 with hc
    obtain ⟨K, hK⟩ := exists_nat_gt (|c| * r ^ (k + 1))
    have hKpos : (0 : ℝ) < K := lt_of_le_of_lt (by positivity) hK
    set a := c / K with ha
    obtain ⟨s, hs⟩ := p5c16_pow_step a (k + 1) K
    refine ⟨g * (1 - C a * X ^ (k + 1)) ^ K, ?_, ?_⟩
    · have hKa : (K : ℝ) * a = c := by
        rw [ha]; field_simp
      rw [hs, hKa]
      have hg : g = 1 + X ^ (k + 1) * q := by rw [← hq]; ring
      have hX : X ∣ q - C c := by
        rw [X_dvd_iff]; simp [hc]
      obtain ⟨t, ht⟩ := hX
      have hq' : q = C c + X * t := by rw [← ht]; ring
      rw [hg, hq']
      refine ⟨t + X ^ k * (s - (C c + X * t) * C c + X ^ (k + 1) * (C c + X * t) * s), ?_⟩
      ring
    · intro y hy
      have hp : aeval y ((1 - C a * X ^ (k + 1)) ^ K) ≠ 0 := by
        simp only [map_pow, map_sub, map_one, map_mul, aeval_C, aeval_X]
        apply pow_ne_zero
        intro h0
        have h1 : algebraMap ℝ ℂ a * y ^ (k + 1) = 1 := by linear_combination -h0
        have h2 := congrArg norm h1
        rw [norm_mul, norm_pow, norm_one] at h2
        have ha' : ‖algebraMap ℝ ℂ a‖ = |a| := by
          rw [Complex.coe_algebraMap, Complex.norm_real, Real.norm_eq_abs]
        rw [ha'] at h2
        have h3 : |a| * ‖y‖ ^ (k + 1) ≤ |a| * r ^ (k + 1) := by gcongr
        have h4 : |a| * r ^ (k + 1) < 1 := by
          rw [ha, abs_div, abs_of_pos hKpos, div_mul_eq_mul_div, div_lt_one hKpos]
          exact hK
        linarith
      rw [map_mul, mul_eq_zero, hz y hy]
      constructor
      · rintro (h | h)
        · exact h
        · exact absurd h hp
      · intro h
        exact Or.inl h

open AnalyticGeometry in
theorem solution (r x : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (hx0 : 0 < x)
    (hxr : x ≤ r) (n : ℕ) :
    ∃ g : Polynomial ℝ, g.coeff 0 = 1 ∧ (∀ i : ℕ, 0 < i → i < n → g.coeff i = 0) ∧
      ∀ y : ℂ, 0 < ‖y‖ → ‖y‖ ≤ r →
        (Polynomial.aeval y g = 0 ↔ y = (x : ℂ)) := by
  obtain ⟨g, hdvd, hz⟩ := p5c16_main r x hr0 hx0 hxr n
  rw [X_pow_dvd_iff] at hdvd
  refine ⟨g, ?_, ?_, fun y _ hy => hz y hy⟩
  · have h0 := hdvd 0 (by omega)
    rw [coeff_sub, coeff_one_zero, sub_eq_zero] at h0
    exact h0
  · intro i hi hin
    have h0 := hdvd i (by omega)
    rw [coeff_sub, coeff_one, if_neg (by omega), sub_zero] at h0
    exact h0
