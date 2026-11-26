-- Prove2me | solution 1 for Arxiv2606_14486.uniform_phase_rotation
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T23:51:13.6343+00:00
-- url     : https://prove2.me/submissions/7fa9eac7-aac7-4e69-a3d4-3b2deeddd996

import Mathlib
import Definitions.Def_Arxiv2606_14486_Basic

set_option autoImplicit false

namespace S73UP
open Arxiv2606_14486

lemma af_swap {n : ℕ} (k d α β : ℝ) (w : Fin n → ℂ) :
    arrayFactor n k d α β w = arrayFactor n k d β α w := by
  unfold arrayFactor
  congr 1; funext i; rw [add_comm (Real.sin α)]

lemma af_smul {n : ℕ} (k d α β : ℝ) (c : ℂ) (w τ : Fin n → ℂ) (h : ∀ i, τ i = c * w i) :
    arrayFactor n k d α β τ = c * arrayFactor n k d α β w := by
  unfold arrayFactor
  rw [Finset.mul_sum]
  congr 1; funext i; rw [h i]; ring

end S73UP

open Arxiv2606_14486 S73UP in
theorem solution {n : ℕ} (B : Finset ℂ) (k d θ₁ θ₂ : ℝ) (hk : 0 < k) (hd : 0 < d)
    (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (wt : Fin n → ℂ)
    (hopt : IsOptimalWeights B n k d (-θ₁) θ₂ wt) (κ : ℝ) (τ : Fin n → ℂ)
    (hτ : ∀ i, τ i = Complex.exp ((κ : ℂ) * Complex.I) * wt i) :
    arrayFactor n k d θ₂ (-θ₁) τ =
        Complex.exp ((κ : ℂ) * Complex.I) * arrayFactor n k d (-θ₁) θ₂ wt ∧
      ‖arrayFactor n k d θ₂ (-θ₁) τ‖ = ‖arrayFactor n k d (-θ₁) θ₂ wt‖ ∧
      (∀ w : Fin n → ℂ, (∀ i, w i ∈ B) →
        ‖arrayFactor n k d θ₂ (-θ₁) w‖ ≤ ‖arrayFactor n k d θ₂ (-θ₁) τ‖) ∧
      (arrayFactor n k d (-θ₁) θ₂ wt ≠ 0 →
        (arrayFactor n k d θ₂ (-θ₁) τ = arrayFactor n k d (-θ₁) θ₂ wt ↔
          ∃ m : ℤ, κ = 2 * m * Real.pi)) := by
  have h1 : arrayFactor n k d θ₂ (-θ₁) τ =
      Complex.exp ((κ : ℂ) * Complex.I) * arrayFactor n k d (-θ₁) θ₂ wt := by
    rw [af_smul k d θ₂ (-θ₁) _ wt τ hτ, af_swap k d θ₂ (-θ₁)]
  have h2 : ‖arrayFactor n k d θ₂ (-θ₁) τ‖ = ‖arrayFactor n k d (-θ₁) θ₂ wt‖ := by
    rw [h1, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  refine ⟨h1, h2, fun w hw => ?_, fun hne => ?_⟩
  · rw [h2, af_swap k d θ₂ (-θ₁)]
    exact hopt.2 w hw
  · rw [h1]
    constructor
    · intro h
      have : Complex.exp ((κ : ℂ) * Complex.I) = 1 := by
        have := mul_right_cancel₀ hne (h.trans (one_mul _).symm)
        exact this
      obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 this
      refine ⟨m, ?_⟩
      have := congrArg Complex.im hm
      simp at this
      linarith
    · rintro ⟨m, hm⟩
      have : Complex.exp ((κ : ℂ) * Complex.I) = 1 := by
        rw [Complex.exp_eq_one_iff]
        exact ⟨m, by rw [hm]; push_cast; ring⟩
      rw [this, one_mul]
