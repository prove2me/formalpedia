-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendreSecondKernel
-- name    : row23_rh_supp_RHLegendreSecondKernel
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:08:47.011197+00:00
-- url     : https://prove2.me/theorems/b0847fa1-2756-422f-85ae-cd9f4d081a5c
-- title:
--   Row 23 RH support: RHLegendreSecondKernel
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreHighKernel
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace DusartLegendreSmoothing
open Polynomial MeasureTheory intervalIntegral
 theorem zeroKernel_second_derivative_integral (m : ℕ) (hm : 2 ≤ m) (ρ : ℂ) (δ : ℝ)
    (hd : 0 < δ) (hρ : ρ.im ≠ 0) :
    zeroKernel m ρ δ = ∫ t : ℝ in 0..1,
      ((iteratedDeriv 2 (weight m) t:ℝ):ℂ)*normalizedPrimitive 2 ρ δ t := by
  let F : ℕ → ℝ → ℂ := fun k => normalizedPrimitive (2-k) ρ δ
  have hc : ∀ k ≤ 2, ContinuousOn (F k) (Set.uIcc (0:ℝ) 1) := by
    intro k hk
    exact normalizedPrimitive_continuousOn (2-k) ρ δ hd.le
  have hder : ∀ k < 2, ∀ t ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (F k) (F (k+1) t) t := by
    intro k hk t ht
    dsimp only [F]
    rw [show 2-k=2-(k+1)+1 by omega]
    exact normalizedPrimitive_deriv (2-(k+1)) ρ δ t hd hρ (base_positive δ t hd.le ht)
  have hb : ∀ k < 2, (derivative^[k] (densityPolynomial m)).eval 0=0 ∧
      (derivative^[k] (densityPolynomial m)).eval 1=0 := by
    intro k hk
    constructor
    · rw [←iteratedDeriv_weight,derivative_at_zero m k (by omega)]
    · rw [←iteratedDeriv_weight,derivative_at_one m k (by omega)]
  have h := polynomial_integration_by_parts 2 (densityPolynomial m) F hc hder hb
  have he : zeroKernel m ρ δ = ∫ t : ℝ in 0..1, (weight m t:ℂ)*normalizedPrimitive 0 ρ δ t := by
    unfold zeroKernel
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [normalizedPrimitive_zero]
    push_cast
    ring
  rw [he]
  simpa only [F,Nat.reduceSub,densityPolynomial_eval,←iteratedDeriv_weight,
    neg_one_sq,one_mul] using h
 theorem affine_quadratic_kernel_scaled (ρ : ℂ) (x δ t : ℝ)
    (hx : 0 < x) (hd : 0 < δ) (ht : 0 < 1+δ*t) (hρ : ρ.im ≠ 0) :
    (((x*(1+δ*t):ℝ):ℂ)^(ρ+2)/(ρ*(ρ+1)*(ρ+2)))/((δ*x:ℝ):ℂ)^2 =
      (x:ℂ)^ρ*normalizedPrimitive 2 ρ δ t := by
  have hx' : (x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hd' : (δ:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hd.ne'
  have hn (k : ℕ) : ρ+(k:ℂ)≠0 := by
    intro he
    apply hρ
    simpa only [Complex.add_im,Complex.natCast_im,add_zero,Complex.zero_im] using congrArg Complex.im he
  have h0 : ρ≠0 := by simpa using hn 0
  have h1 : ρ+1≠0 := by simpa using hn 1
  have h2 : ρ+2≠0 := by simpa using hn 2
  have hr : rising ρ 2=ρ*(ρ+1)*(ρ+2) := by
    rw [rising_succ,rising_succ,rising_zero]
    simp only [Nat.cast_zero,Nat.cast_one,add_zero]
    ring
  unfold normalizedPrimitive
  rw [hr]
  rw [show (1:ℂ)+(δ:ℂ)*(t:ℂ)=((1+δ*t:ℝ):ℂ) by push_cast; rfl]
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hx.le ht.le,
    Complex.cpow_add ρ 2 hx',Complex.cpow_two]
  push_cast
  field_simp [h0,h1,h2,hx',hd'] <;> ring
 theorem integral_affine_quadratic_kernel (m : ℕ) (hm : 2 ≤ m) (ρ : ℂ) (x δ : ℝ)
    (hx : 0 < x) (hd : 0 < δ) (hρ : ρ.im≠0) :
    (∫ t : ℝ in 0..1, ((iteratedDeriv 2 (weight m) t:ℝ):ℂ)*
      (((x*(1+δ*t):ℝ):ℂ)^(ρ+2)/(ρ*(ρ+1)*(ρ+2))))/((δ*x:ℝ):ℂ)^2 =
      (x:ℂ)^ρ*zeroKernel m ρ δ := by
  rw [zeroKernel_second_derivative_integral m hm ρ δ hd hρ,
    ←intervalIntegral.integral_const_mul,←intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  have hb := base_positive δ t hd.le ht
  calc
    _ = ((iteratedDeriv 2 (weight m) t:ℝ):ℂ)*
        ((((x*(1+δ*t):ℝ):ℂ)^(ρ+2)/(ρ*(ρ+1)*(ρ+2)))/((δ*x:ℝ):ℂ)^2) := by ring
    _ = _ := by rw [affine_quadratic_kernel_scaled ρ x δ t hx hd hb hρ]; ring
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.zeroKernel_second_derivative_integral
#print axioms DusartLegendreSmoothing.integral_affine_quadratic_kernel


