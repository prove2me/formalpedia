-- Prove2me | solution 1 for Arxiv2606_14486.reciprocity_implications
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T23:50:29.980413+00:00
-- url     : https://prove2.me/submissions/7ff53764-2955-48c7-8142-1783787a621b

import Mathlib
import Definitions.Def_Arxiv2606_14486_Basic

set_option autoImplicit false

namespace S73IP
open Arxiv2606_14486

lemma exp_eq_iff (a b : ℝ) :
    Complex.exp ((a : ℂ) * Complex.I) = Complex.exp ((b : ℂ) * Complex.I) ↔
      ∃ m : ℤ, a = b + 2 * m * Real.pi := by
  rw [Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have := congrArg Complex.im hm
    simp at this
    linarith
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    rw [hm]; push_cast; ring

lemma inphase_iff {n : ℕ} (r θ : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    InPhase (fun i => (r i : ℂ) * Complex.exp ((θ i : ℂ) * Complex.I)) ↔
      ∃ φ : ℝ, ∀ i, ∃ m : ℤ, θ i = φ + 2 * m * Real.pi := by
  have hn : ∀ i, ‖(r i : ℂ) * Complex.exp ((θ i : ℂ) * Complex.I)‖ = r i := by
    intro i
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hr i)]
  unfold InPhase
  simp only [hn]
  have hc : ∀ i (φ : ℝ), (r i : ℂ) * Complex.exp ((θ i : ℂ) * Complex.I) =
      (r i : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) ↔ ∃ m : ℤ, θ i = φ + 2 * m * Real.pi := by
    intro i φ
    rw [← exp_eq_iff]
    constructor
    · intro h
      exact mul_left_cancel₀ (by exact_mod_cast (hr i).ne') h
    · intro h; rw [h]
  simp only [hc]

lemma wf_eq {n : ℕ} (k d α β : ℝ) (R ψ : Fin n → ℝ) (i : Fin n) :
    wavefront n k d α β (reflCoeffs R ψ) i =
      (R i : ℂ) * Complex.exp (((((i : ℕ) : ℝ) * k * d * (Real.sin α + Real.sin β) + ψ i : ℝ) : ℂ)
        * Complex.I) := by
  unfold wavefront steering reflCoeffs
  rw [show (((((i : ℕ) : ℝ) * k * d * (Real.sin α + Real.sin β) + ψ i : ℝ) : ℂ) * Complex.I) =
      ((((i : ℕ) : ℝ) * k * d * Real.sin α : ℝ) : ℂ) * Complex.I + (ψ i : ℂ) * Complex.I +
        ((((i : ℕ) : ℝ) * k * d * Real.sin β : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.exp_add, Complex.exp_add]
  ring

lemma wf_fun {n : ℕ} (k d α β : ℝ) (R ψ : Fin n → ℝ) :
    wavefront n k d α β (reflCoeffs R ψ) = fun i =>
      (R i : ℂ) * Complex.exp (((fun j : Fin n => (((j : ℕ) : ℝ) * k * d * (Real.sin α + Real.sin β) + ψ j)) i : ℂ)
        * Complex.I) := by
  funext i; exact wf_eq k d α β R ψ i

end S73IP
namespace S73IP
open Arxiv2606_14486

lemma lin_inphase {n : ℕ} (hn : 2 ≤ n) (R : Fin n → ℝ) (hR : ∀ i, 0 < R i) (X : ℝ) :
    InPhase (fun i : Fin n => (R i : ℂ) * Complex.exp (((((i : ℕ) : ℝ) * X : ℝ) : ℂ) * Complex.I)) ↔
      ∃ m : ℤ, X = 2 * m * Real.pi := by
  rw [inphase_iff (fun i : Fin n => R i) (fun i : Fin n => ((i : ℕ) : ℝ) * X) hR]
  constructor
  · rintro ⟨φ, h⟩
    obtain ⟨m0, h0⟩ := h ⟨0, by omega⟩
    obtain ⟨m1, h1⟩ := h ⟨1, by omega⟩
    simp only [Nat.cast_zero, zero_mul, Nat.cast_one, one_mul] at h0 h1
    refine ⟨m1 - m0, ?_⟩
    push_cast
    linarith
  · rintro ⟨m, hm⟩
    refine ⟨0, fun i => ⟨(i : ℕ) * m, ?_⟩⟩
    rw [hm]; push_cast; ring

lemma wf_lin {n : ℕ} (k d θ₂ θ₃ : ℝ) (R' : Fin n → ℝ) (dpsi' : ℝ) :
    wavefront n k d (-θ₃) θ₂ (reflCoeffs R' (linearPhases n 0 dpsi')) = fun i =>
      (R' i : ℂ) * Complex.exp
        (((((i : ℕ) : ℝ) * (k * d * (Real.sin θ₂ - Real.sin θ₃) + dpsi') : ℝ) : ℂ) * Complex.I) := by
  funext i
  rw [wf_eq]
  unfold linearPhases
  congr 3
  rw [Real.sin_neg]; ring

end S73IP

open Arxiv2606_14486 S73IP in
theorem solution {n : ℕ} (k d θ₁ θ₂ : ℝ) (hk : 0 < k) (hd : 0 < d)
    (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (hθ₁₂ : θ₂ ≠ θ₁)
    (R' : Fin n → ℝ) (hR' : ∀ i, 0 < R' i) (dpsi' : ℝ) :
    (dpsi' = phaseStep k d θ₁ θ₂ →
      InPhase (wavefront n k d (-θ₁) θ₂ (reflCoeffs R' (linearPhases n 0 dpsi')))) ∧
    (dpsi' = phaseStep k d θ₁ θ₂ → 2 ≤ n → k * d ≤ 2 * Real.pi → θ₁ < Real.pi / 2 →
      ∀ θ₃ : ℝ, 0 < θ₃ → θ₃ < Real.pi / 2 →
        InPhase (wavefront n k d (-θ₃) θ₂ (reflCoeffs R' (linearPhases n 0 dpsi'))) →
          θ₃ = θ₁) ∧
    (2 ≤ n →
      (InPhase (wavefront n k d (-θ₁) θ₂ (reflCoeffs R' (linearPhases n 0 dpsi'))) ↔
        ∃ m : ℤ, dpsi' - phaseStep k d θ₁ θ₂ = 2 * m * Real.pi)) := by
  have hkd : 0 < k * d := mul_pos hk hd
  refine ⟨fun hd' => ?_, fun hd' hn hkd2 h1 θ₃ h3 h3' h => ?_, fun hn => ?_⟩
  · rw [wf_lin, inphase_iff _ _ hR']
    refine ⟨0, fun i => ⟨0, ?_⟩⟩
    rw [hd']; unfold phaseStep; push_cast; ring
  · rw [wf_lin, lin_inphase hn R' hR'] at h
    obtain ⟨m, hm⟩ := h
    rw [hd'] at hm
    unfold phaseStep at hm
    have e : k * d * (Real.sin θ₁ - Real.sin θ₃) = 2 * m * Real.pi := by linarith
    have s1 := Real.sin_pos_of_pos_of_lt_pi hθ₁ (by linarith [Real.pi_pos])
    have s3 := Real.sin_pos_of_pos_of_lt_pi h3 (by linarith [Real.pi_pos])
    have hp := Real.pi_pos
    have u1 : Real.sin θ₁ < 1 := by
      have := Real.sin_lt_sin_of_lt_of_le_pi_div_two (x := θ₁) (y := Real.pi / 2) (by linarith) le_rfl h1
      rwa [Real.sin_pi_div_two] at this
    have u3 : Real.sin θ₃ < 1 := by
      have := Real.sin_lt_sin_of_lt_of_le_pi_div_two (x := θ₃) (y := Real.pi / 2) (by linarith) le_rfl h3'
      rwa [Real.sin_pi_div_two] at this
    have hm0 : m = 0 := by
      rcases lt_trichotomy m 0 with hlt | heq | hgt
      · have : (m : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hlt
        nlinarith
      · exact heq
      · have : (1 : ℝ) ≤ m := by exact_mod_cast hgt
        nlinarith
    rw [hm0] at e
    simp only [Int.cast_zero, mul_zero, zero_mul] at e
    have hs : Real.sin θ₃ = Real.sin θ₁ := by
      have := (mul_eq_zero.1 e).resolve_left hkd.ne'
      linarith
    exact Real.injOn_sin ⟨by linarith, h3'.le⟩ ⟨by linarith, h1.le⟩ hs
  · rw [wf_lin, lin_inphase hn R' hR']
    unfold phaseStep
    constructor
    · rintro ⟨m, hm⟩; exact ⟨m, by linarith⟩
    · rintro ⟨m, hm⟩; exact ⟨m, by linarith⟩
