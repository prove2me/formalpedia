-- Prove2me | solution 1 for AkhmedovNeutrino.common_phase_irrelevant
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T03:43:52.218401+00:00
-- url     : https://prove2.me/submissions/5699e3be-2c14-4fbb-b61d-ef9a5637c109

import Mathlib
import Definitions.Def_AkhmedovNeutrino_MSW

set_option autoImplicit false

open AkhmedovNeutrino in
theorem solution (H : Matrix (Fin 2) (Fin 2) ℂ) (c : ℝ)
    (ψ : ℝ → Fin 2 → ℂ)
    (hψ : ∀ t : ℝ, HasDerivAt ψ
      (-(Complex.I • (H + (c : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).mulVec (ψ t))) t) :
    (∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (Complex.I * c * s) • ψ s)
      (-(Complex.I • H.mulVec (Complex.exp (Complex.I * c * t) • ψ t))) t) ∧
    ∀ (t : ℝ) (k : Fin 2),
      Complex.normSq ((Complex.exp (Complex.I * c * t) • ψ t) k) = Complex.normSq (ψ t k) := by
  refine ⟨fun t => ?_, fun t k => ?_⟩
  · have h1 : HasDerivAt (fun s : ℝ => Complex.I * c * (s : ℂ)) (Complex.I * c * 1) t := by
      have := ((hasDerivAt_id t).ofReal_comp).const_mul (Complex.I * (c : ℂ))
      simpa using this
    have hg : HasDerivAt (fun s : ℝ => Complex.exp (Complex.I * c * s))
        (Complex.exp (Complex.I * c * t) * (Complex.I * c * 1)) t := h1.cexp
    have hprod := hg.smul (hψ t)
    have key : Complex.exp (Complex.I * c * t) •
          -(Complex.I • (H + (c : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).mulVec (ψ t)) +
        (Complex.exp (Complex.I * c * t) * (Complex.I * c * 1)) • ψ t
        = -(Complex.I • H.mulVec (Complex.exp (Complex.I * c * t) • ψ t)) := by
      ext k
      simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_smul,
        Pi.neg_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    exact hprod.congr_deriv key
  · have he : Complex.normSq (Complex.exp (Complex.I * c * t)) = 1 := by
      have hx : Complex.I * c * t = ((c * t : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      rw [hx, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
      norm_num
    rw [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, he, one_mul]
#print axioms solution
