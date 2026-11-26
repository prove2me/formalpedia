-- Prove2me | solution 1 for Arxiv2405_15536.kappa_influence_function
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T23:57:57.77612+00:00
-- url     : https://prove2.me/submissions/3041d838-d1bb-4078-9cb9-6acdacc19292

import Mathlib
import Definitions.Def_Arxiv2405_15536_Basic

set_option autoImplicit false

open MeasureTheory Filter

namespace S73KF
open Arxiv2405_15536

lemma loss_eq (κ : ℝ) (hκ : κ ≠ 0) :
    lossKappa κ = fun ε => -(1 / κ) * Real.arsinh (κ * (-betaKappa κ * ε ^ 2)) := by
  funext ε
  unfold lossKappa expKappa
  rw [if_neg hκ]
  set y := -betaKappa κ * ε ^ 2
  have hb : 0 < Real.sqrt (1 + κ ^ 2 * y ^ 2) + κ * y := by
    have h1 : |κ * y| < Real.sqrt (1 + κ ^ 2 * y ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]
      apply Real.sqrt_lt_sqrt (sq_nonneg _)
      nlinarith
    have := neg_abs_le (κ * y)
    linarith
  rw [Real.log_rpow hb, Real.arsinh]
  congr 2
  rw [add_comm]; congr 2; ring

end S73KF

open Arxiv2405_15536 S73KF in
theorem solution :
    (∀ κ : ℝ, 0 < κ → κ < 2 / 3 → ∀ ε : ℝ, HasDerivAt (lossKappa κ)
      (2 * betaKappa κ * ε / Real.sqrt (1 + κ ^ 2 * betaKappa κ ^ 2 * ε ^ 4)) ε) ∧
    (∀ ε : ℝ, HasDerivAt (lossKappa 0) ε ε) := by
  constructor
  · intro κ hκ _ ε
    rw [loss_eq κ hκ.ne']
    set b := betaKappa κ
    have h1 : HasDerivAt (fun ε : ℝ => κ * (-b * ε ^ 2)) (κ * (-b * (2 * ε))) ε := by
      have := ((hasDerivAt_pow 2 ε).const_mul (-b)).const_mul κ
      simpa using this
    have h2 := (h1.arsinh).const_mul (-(1 / κ))
    refine h2.congr_deriv ?_
    have e : 1 + (κ * (-b * ε ^ 2)) ^ 2 = 1 + κ ^ 2 * b ^ 2 * ε ^ 4 := by ring
    rw [e, smul_eq_mul]
    have hs : 0 < Real.sqrt (1 + κ ^ 2 * b ^ 2 * ε ^ 4) := Real.sqrt_pos.2 (by positivity)
    field_simp
  · intro ε
    have hl : lossKappa 0 = fun ε => (1 / 2) * ε ^ 2 := by
      funext ε
      unfold lossKappa expKappa betaKappa
      simp only [if_true, Real.log_exp]
      ring
    rw [hl]
    have := (hasDerivAt_pow 2 ε).const_mul (1 / 2 : ℝ)
    refine this.congr_deriv ?_
    push_cast; ring
