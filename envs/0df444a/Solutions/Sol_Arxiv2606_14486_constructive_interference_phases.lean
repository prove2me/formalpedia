-- Prove2me | solution 1 for Arxiv2606_14486.constructive_interference_phases
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T23:48:42.933036+00:00
-- url     : https://prove2.me/submissions/1a350434-968a-4539-af0a-2345d59e19f0

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

open Arxiv2606_14486 S73IP in
theorem solution {n : ℕ} (k d θ₁ θ₂ : ℝ) (hk : 0 < k) (hd : 0 < d)
    (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (R ψ : Fin n → ℝ) (hR : ∀ i, 0 < R i) :
    InPhase (wavefront n k d θ₂ (-θ₁) (reflCoeffs R ψ)) ↔
      ∃ c : ℝ, ∀ i : Fin n, ∃ m : ℤ,
        ψ i = linearPhases n c (phaseStep k d θ₁ θ₂) i + 2 * m * Real.pi := by
  rw [wf_fun, inphase_iff _ _ hR]
  unfold linearPhases phaseStep
  simp only [Real.sin_neg]
  constructor
  · rintro ⟨φ, h⟩
    refine ⟨φ, fun i => ?_⟩
    obtain ⟨m, hm⟩ := h i
    exact ⟨m, by linarith⟩
  · rintro ⟨c, h⟩
    refine ⟨c, fun i => ?_⟩
    obtain ⟨m, hm⟩ := h i
    exact ⟨m, by linarith⟩
