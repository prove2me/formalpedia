-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendreLeftKernel
-- name    : row23_rh_supp_RHLegendreLeftKernel
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:15:54.745652+00:00
-- url     : https://prove2.me/theorems/8b5b2c32-3fa2-4766-9282-2ceee51d5e55
-- title:
--   Row 23 RH support: RHLegendreLeftKernel
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreSecondKernel
import Definitions.Def_row23_rh_supp_RHLegendreSecondDerivative
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace DusartLegendreSmoothing
open Complex MeasureTheory intervalIntegral
 theorem zeroKernel_nonpositive_low (m : ℕ) (ρ : ℂ) (δ : ℝ)
    (hd : 0 ≤ δ) (hβ : ρ.re ≤ 0) :
    ‖zeroKernel m ρ δ‖ ≤ 1/‖ρ‖ := by
  have hp (t : ℝ) (ht : t ∈ Set.Ioc (0:ℝ) 1) :
      ‖(weight m t:ℂ)*((1+δ*t:ℝ):ℂ)^ρ/ρ‖ ≤ weight m t/‖ρ‖ := by
    have hw := weight_nonneg m t ⟨ht.1.le,ht.2⟩
    have hb : 1 ≤ 1+δ*t := by nlinarith [mul_nonneg hd ht.1.le]
    have hr : (1+δ*t)^ρ.re ≤ 1 := by
      simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hb hβ
    rw [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hw,
      Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < 1+δ*t)]
    exact div_le_div_of_nonneg_right (by nlinarith) (norm_nonneg _)
  have hi := intervalIntegral.norm_integral_le_of_norm_le (by norm_num : (0:ℝ) ≤ 1)
    (Filter.Eventually.of_forall hp) ((weight_continuous m).intervalIntegrable (μ:=volume) (a:=(0:ℝ)) (b:=1) |>.div_const ‖ρ‖)
  simpa only [zeroKernel,intervalIntegral.integral_div,integral_weight] using hi
 theorem zeroKernel_second_high (m : ℕ) (hm : 2 ≤ m) (ρ : ℂ) (δ : ℝ)
    (hd : 0 < δ) (hβ : ρ.re ≤ -(1/2:ℝ)) (hi : 0 < |ρ.im|) :
    ‖zeroKernel m ρ δ‖ ≤
      (8*(m:ℝ)*(2*m+1))*(1+δ)^(3/2:ℝ)/(δ^2*|ρ.im|^3) := by
  let D : ℝ := (1+δ)^(3/2:ℝ)/(δ^2*|ρ.im|^3)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hp (t : ℝ) (ht : t ∈ Set.Ioc (0:ℝ) 1) :
      ‖((iteratedDeriv 2 (weight m) t:ℝ):ℂ)*normalizedPrimitive 2 ρ δ t‖ ≤
        D*|iteratedDeriv 2 (weight m) t| := by
    have hb : 1 ≤ 1+δ*t := by nlinarith [mul_nonneg hd.le ht.1.le]
    have hb' : 1+δ*t ≤ 1+δ := by nlinarith [mul_le_mul_of_nonneg_left ht.2 hd.le]
    have hpow : (1+δ*t)^(ρ.re+(2:ℝ)) ≤ (1+δ)^(3/2:ℝ) :=
      (Real.rpow_le_rpow_of_exponent_le hb (by linarith)).trans
        (Real.rpow_le_rpow (by linarith) hb' (by norm_num))
    have hn : ‖normalizedPrimitive 2 ρ δ t‖ ≤ D := by
      apply (normalizedPrimitive_norm 2 ρ δ t hd hi (by linarith)).trans
      simpa only [Nat.cast_ofNat] using
        div_le_div_of_nonneg_right hpow (by positivity : 0 ≤ δ^2*|ρ.im|^3)
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left hn (abs_nonneg _)).trans_eq (mul_comm _ _)
  have ha := ((iterated_weight_continuous m 2).abs.intervalIntegrable (μ:=volume) (a:=(0:ℝ)) (b:=1)).const_mul D
  have hn := intervalIntegral.norm_integral_le_of_norm_le (by norm_num : (0:ℝ) ≤ 1)
    (Filter.Eventually.of_forall hp) ha
  rw [←zeroKernel_second_derivative_integral m hm ρ δ hd (abs_pos.mp hi),
    intervalIntegral.integral_const_mul] at hn
  exact (hn.trans (mul_le_mul_of_nonneg_left (integral_abs_second_derivative m hm) hD)).trans_eq (by dsimp [D]; ring)
 theorem zeroKernel_left_uniform (m : ℕ) (δ v : ℝ) (hd : 0 ≤ δ) :
    ‖zeroKernel m (-(1/2:ℂ)+v*I) δ‖ ≤ 2 := by
  have h := zeroKernel_nonpositive_low m (-(1/2:ℂ)+v*I) δ hd (by norm_num)
  have hn : (1/2:ℝ) ≤ ‖-(1/2:ℂ)+v*I‖ := by
    simpa using Complex.abs_re_le_norm (-(1/2:ℂ)+v*I)
  exact h.trans ((div_le_iff₀ (by linarith : 0 < ‖-(1/2:ℂ)+v*I‖)).2 (by linarith))
 theorem zeroKernel_left_inverse (m : ℕ) (δ v : ℝ) (hd : 0 ≤ δ) (hv : v ≠ 0) :
    ‖zeroKernel m (-(1/2:ℂ)+v*I) δ‖ ≤ 1/|v| := by
  have h := zeroKernel_nonpositive_low m (-(1/2:ℂ)+v*I) δ hd (by norm_num)
  have hn : |v| ≤ ‖-(1/2:ℂ)+v*I‖ := by
    simpa using Complex.abs_im_le_norm (-(1/2:ℂ)+v*I)
  exact h.trans (div_le_div₀ (by norm_num) le_rfl (abs_pos.mpr hv) hn)
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.zeroKernel_second_high
#print axioms DusartLegendreSmoothing.zeroKernel_left_uniform


