-- Prove2me | solution 1 for Arxiv2606_14486.reverse_beam_direction
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T23:49:50.913883+00:00
-- url     : https://prove2.me/submissions/118e32a9-7504-4328-be5e-d930e29b0106

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
theorem solution {n : ℕ} (k d θ₁ θ₂ θ₃ : ℝ) (hk : 0 < k) (hd : 0 < d)
    (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (hθ₃ : 0 < θ₃) (hθ₁₂ : θ₂ ≠ θ₁)
    (R' : Fin n → ℝ) (hR' : ∀ i, 0 < R' i) (dpsi' : ℝ) :
    (∀ i : Fin n, wavefront n k d (-θ₃) θ₂ (reflCoeffs R' (linearPhases n 0 dpsi')) i =
      (R' i : ℂ) * Complex.exp
        ((((i : ℕ) : ℝ) * (k * d * (Real.sin θ₂ - Real.sin θ₃) + dpsi') : ℝ) * Complex.I)) ∧
    (2 ≤ n → InPhase (wavefront n k d (-θ₃) θ₂ (reflCoeffs R' (linearPhases n 0 dpsi'))) →
      ∃ m : ℤ, Real.sin θ₃ =
        Real.sin θ₁ + ((dpsi' - phaseStep k d θ₁ θ₂) - 2 * m * Real.pi) / (k * d)) := by
  refine ⟨fun i => by rw [wf_lin], fun hn h => ?_⟩
  rw [wf_lin, lin_inphase hn R' hR'] at h
  obtain ⟨m, hm⟩ := h
  refine ⟨m, ?_⟩
  unfold phaseStep
  have hkd : 0 < k * d := mul_pos hk hd
  field_simp
  linarith
