-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendrePowerErrorAssembly
-- name    : row23_rh_supp_RHLegendrePowerErrorAssembly
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:17:39.091731+00:00
-- url     : https://prove2.me/theorems/4d804e30-a464-4534-9b35-b20a104507a6
-- title:
--   Row 23 RH support: RHLegendrePowerErrorAssembly
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreErrorAssembly
set_option autoImplicit false
namespace DusartLegendreSmoothing
 theorem average_relative_power_remainder (m : ℕ) (f : ℝ → ℝ)
    (A y δ σ a C₁ C₂ L Q : ℝ) (Z R : ℂ)
    (hA : 0 < A) (hy : A ≤ y) (hσ : σ ≤ 1) (ha : a ≤ 1)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hL : 0 ≤ L) (hQ : 0 ≤ Q)
    (hformula : ((average m f y δ-y*(1+δ/2):ℝ):ℂ) = -Z+R)
    (hZ : ‖Z‖ ≤ C₁*y^(1/2:ℝ)+C₂*y^σ) (hR : ‖R‖ ≤ L+Q*y^a) :
    |average m f y δ-y*(1+δ/2)| ≤
      (C₁*A^((1/2:ℝ)-1)+C₂*A^(σ-1)+L*A^(-1:ℝ)+Q*A^(a-1))*y := by
  have h₁ := mul_le_mul_of_nonneg_left
    (rpow_relative_bound A y (1/2) hA hy (by norm_num)) hC₁
  have h₂ := mul_le_mul_of_nonneg_left (rpow_relative_bound A y σ hA hy hσ) hC₂
  have h₀ := mul_le_mul_of_nonneg_left
    (rpow_relative_bound A y 0 hA hy (by norm_num)) hL
  have h₃ := mul_le_mul_of_nonneg_left (rpow_relative_bound A y a hA hy ha) hQ
  norm_num only [sub_zero,zero_sub,Real.rpow_zero,mul_one] at h₀
  have h := average_error_from_formula m f y δ _ _ Z R hformula hZ hR
  nlinarith
 theorem desmoothing_power_remainder (m : ℕ) (f : ℝ → ℝ) (hf : Monotone f)
    (A x δ σ a C₁ C₂ L Q : ℝ) (Z R : ℝ → ℂ)
    (hA : 0 < A) (hx : 0 ≤ x) (hd : 0 ≤ δ) (hσ : σ ≤ 1) (ha : a ≤ 1)
    (hAx : A ≤ x/(1+δ)) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hL : 0 ≤ L) (hQ : 0 ≤ Q)
    (hformula : ∀ y, A ≤ y → ((average m f y δ-y*(1+δ/2):ℝ):ℂ) = -Z y+R y)
    (hZ : ∀ y, A ≤ y → ‖Z y‖ ≤ C₁*y^(1/2:ℝ)+C₂*y^σ)
    (hR : ∀ y, A ≤ y → ‖R y‖ ≤ L+Q*y^a) :
    |f x-x| ≤ (δ/2+C₁*A^((1/2:ℝ)-1)+C₂*A^(σ-1)+L*A^(-1:ℝ)+Q*A^(a-1))*x := by
  let E := C₁*A^((1/2:ℝ)-1)+C₂*A^(σ-1)+L*A^(-1:ℝ)+Q*A^(a-1)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hbase : x/(1+δ) ≤ x :=
    (div_le_iff₀ (by linarith : 0 < 1+δ)).mpr (by nlinarith [mul_nonneg hx hd])
  have havg (y : ℝ) (hy : A ≤ y) : |average m f y δ-y*(1+δ/2)| ≤ E*y :=
    average_relative_power_remainder m f A y δ σ a C₁ C₂ L Q (Z y) (R y)
      hA hy hσ ha hC₁ hC₂ hL hQ (hformula y hy) (hZ y hy) (hR y hy)
  have h := desmoothing m f hf x δ E hx hd hE
    (havg x (hAx.trans hbase)) (havg (x/(1+δ)) hAx)
  convert h using 1 <;> dsimp [E] <;> ring
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.average_relative_power_remainder
#print axioms DusartLegendreSmoothing.desmoothing_power_remainder


