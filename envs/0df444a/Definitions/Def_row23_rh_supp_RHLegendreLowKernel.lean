-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendreLowKernel
-- name    : row23_rh_supp_RHLegendreLowKernel
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:02:55.65779+00:00
-- url     : https://prove2.me/theorems/fdd389ae-6be2-4263-9ad5-e437edb29712
-- title:
--   Row 23 RH support: RHLegendreLowKernel
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreAverage
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace DusartLegendreSmoothing
open Complex MeasureTheory intervalIntegral
noncomputable def zeroKernel (m : ℕ) (ρ : ℂ) (δ : ℝ) : ℂ :=
  ∫ t : ℝ in 0..1, (weight m t:ℂ)*((1+δ*t:ℝ):ℂ)^ρ/ρ
 theorem zeroKernel_low (m : ℕ) (ρ : ℂ) (δ : ℝ)
    (hd : 0≤δ) (hβ : ρ.re≤1) (hi : 0 < |ρ.im|) :
    ‖zeroKernel m ρ δ‖ ≤ (1+δ/2)/|ρ.im| := by
  let g : ℝ → ℝ := fun t => weight m t*(1+δ*t)/|ρ.im|
  have hg : IntervalIntegrable g volume 0 1 := by
    apply Continuous.intervalIntegrable
    dsimp [g]
    exact ((weight_continuous m).mul (continuous_const.add (continuous_const.mul continuous_id))).div_const _
  have hpoint : ∀ t ∈ Set.Ioc (0:ℝ) 1,
      ‖(weight m t:ℂ)*((1+δ*t:ℝ):ℂ)^ρ/ρ‖ ≤ g t := by
    intro t ht
    have hw : 0≤weight m t := weight_nonneg m t ⟨ht.1.le,ht.2⟩
    have hb : 1≤1+δ*t := by nlinarith [mul_nonneg hd ht.1.le]
    have hp : (1+δ*t)^ρ.re ≤ 1+δ*t :=
      (Real.rpow_le_rpow_of_exponent_le hb hβ).trans_eq (Real.rpow_one _)
    rw [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hw,
      Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0<1+δ*t)]
    exact div_le_div₀ (mul_nonneg hw (by linarith : 0≤1+δ*t))
      (mul_le_mul_of_nonneg_left hp hw) hi (Complex.abs_im_le_norm ρ)
  have h := intervalIntegral.norm_integral_le_of_norm_le (by norm_num : (0:ℝ)≤1)
    (Filter.Eventually.of_forall hpoint) hg
  have he : (∫ t : ℝ in 0..1, g t)=(1+δ/2)/|ρ.im| := by
    dsimp [g]
    rw [intervalIntegral.integral_div]
    congr 1
    simpa only [average,id_eq,one_mul] using average_id m 1 δ
  rw [he] at h
  exact h
 theorem zeroKernel_scaled_low (m : ℕ) (ρ : ℂ) (x δ : ℝ)
    (hx : 0<x) (hd : 0≤δ) (hβ : ρ.re≤1) (hi : 0 < |ρ.im|) :
    ‖(x:ℂ)^ρ*zeroKernel m ρ δ‖ ≤ x^ρ.re*(1+δ/2)/|ρ.im| := by
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hx]
  calc
    _ ≤ x^ρ.re*((1+δ/2)/|ρ.im|) :=
      mul_le_mul_of_nonneg_left (zeroKernel_low m ρ δ hd hβ hi) (Real.rpow_nonneg hx.le _)
    _ = _ := by ring
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.zeroKernel_low
#print axioms DusartLegendreSmoothing.zeroKernel_scaled_low


