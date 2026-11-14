-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendreErrorAssembly
-- name    : row23_rh_supp_RHLegendreErrorAssembly
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:16:39.685334+00:00
-- url     : https://prove2.me/theorems/25b4d49c-cbc0-4b9d-b38f-fab130ccb957
-- title:
--   Row 23 RH support: RHLegendreErrorAssembly
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreZeroSeries
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace DusartLegendreSmoothing

/-- Sublinear powers give a uniform relative bound above a positive lower endpoint. -/
lemma rpow_relative_bound (A y a : ℝ) (hA : 0 < A) (hy : A ≤ y) (ha : a ≤ 1) :
    y^a ≤ A^(a-1)*y := by
  have hy0 := hA.trans_le hy
  have h := Real.rpow_le_rpow_of_nonpos hA hy (sub_nonpos.mpr ha)
  rw [Real.rpow_sub hy0,Real.rpow_one] at h
  exact (div_le_iff₀ hy0).mp h

lemma average_error_from_formula (m : ℕ) (f : ℝ → ℝ) (y δ U V : ℝ) (Z R : ℂ)
    (hformula : ((average m f y δ-y*(1+δ/2):ℝ):ℂ) = -Z+R)
    (hZ : ‖Z‖ ≤ U) (hR : ‖R‖ ≤ V) :
    |average m f y δ-y*(1+δ/2)| ≤ U+V := by
  calc
    _ = ‖((average m f y δ-y*(1+δ/2):ℝ):ℂ)‖ := by
      rw [Complex.norm_real,Real.norm_eq_abs]
    _ = ‖-Z+R‖ := congrArg norm hformula
    _ ≤ ‖Z‖+‖R‖ := by simpa only [norm_neg] using norm_add_le (-Z) R
    _ ≤ _ := add_le_add hZ hR

/-- Turns the zero series and constant/trivial-zero terms into one relative error. -/
theorem average_relative_error (m : ℕ) (f : ℝ → ℝ)
    (A y δ σ C₁ C₂ L Q : ℝ) (Z R : ℂ)
    (hA : 0 < A) (hy : A ≤ y) (hσ : σ ≤ 1)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hL : 0 ≤ L) (hQ : 0 ≤ Q)
    (hformula : ((average m f y δ-y*(1+δ/2):ℝ):ℂ) = -Z+R)
    (hZ : ‖Z‖ ≤ C₁*y^(1/2:ℝ)+C₂*y^σ)
    (hR : ‖R‖ ≤ L+Q*y^(-2:ℝ)) :
    |average m f y δ-y*(1+δ/2)| ≤
      (C₁*A^((1/2:ℝ)-1)+C₂*A^(σ-1)+L*A^(-1:ℝ)+Q*A^(-3:ℝ))*y := by
  have h₁ := mul_le_mul_of_nonneg_left
    (rpow_relative_bound A y (1/2) hA hy (by norm_num)) hC₁
  have h₂ := mul_le_mul_of_nonneg_left (rpow_relative_bound A y σ hA hy hσ) hC₂
  have h₀ := mul_le_mul_of_nonneg_left
    (rpow_relative_bound A y 0 hA hy (by norm_num)) hL
  have h₃ := mul_le_mul_of_nonneg_left
    (rpow_relative_bound A y (-2) hA hy (by norm_num)) hQ
  norm_num only [sub_zero,zero_sub,zero_sub,zero_sub,Real.rpow_zero,mul_one] at h₀
  norm_num only at h₃
  have h := average_error_from_formula m f y δ _ _ Z R hformula hZ hR
  nlinarith

/-- The final desmoothing step, with the lower endpoint required by both averages. -/
theorem desmoothing_from_series_majorants (m : ℕ) (f : ℝ → ℝ) (hf : Monotone f)
    (A x δ σ C₁ C₂ L Q : ℝ) (Z R : ℝ → ℂ)
    (hA : 0 < A) (hx : 0 ≤ x) (hd : 0 ≤ δ) (hσ : σ ≤ 1)
    (hAx : A ≤ x/(1+δ)) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hL : 0 ≤ L) (hQ : 0 ≤ Q)
    (hformula : ∀ y, A ≤ y → ((average m f y δ-y*(1+δ/2):ℝ):ℂ) = -Z y+R y)
    (hZ : ∀ y, A ≤ y → ‖Z y‖ ≤ C₁*y^(1/2:ℝ)+C₂*y^σ)
    (hR : ∀ y, A ≤ y → ‖R y‖ ≤ L+Q*y^(-2:ℝ)) :
    |f x-x| ≤ (δ/2+C₁*A^((1/2:ℝ)-1)+C₂*A^(σ-1)+
      L*A^(-1:ℝ)+Q*A^(-3:ℝ))*x := by
  let E := C₁*A^((1/2:ℝ)-1)+C₂*A^(σ-1)+L*A^(-1:ℝ)+Q*A^(-3:ℝ)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hbase : x/(1+δ) ≤ x :=
    (div_le_iff₀ (by linarith : 0 < 1+δ)).mpr (by nlinarith [mul_nonneg hx hd])
  have havg (y : ℝ) (hy : A ≤ y) : |average m f y δ-y*(1+δ/2)| ≤ E*y :=
    average_relative_error m f A y δ σ C₁ C₂ L Q (Z y) (R y)
      hA hy hσ hC₁ hC₂ hL hQ (hformula y hy) (hZ y hy) (hR y hy)
  have h := desmoothing m f hf x δ E hx hd hE
    (havg x (hAx.trans hbase)) (havg (x/(1+δ)) hAx)
  convert h using 1 <;> dsimp [E] <;> ring

end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.rpow_relative_bound
#print axioms DusartLegendreSmoothing.average_error_from_formula
#print axioms DusartLegendreSmoothing.average_relative_error
#print axioms DusartLegendreSmoothing.desmoothing_from_series_majorants


