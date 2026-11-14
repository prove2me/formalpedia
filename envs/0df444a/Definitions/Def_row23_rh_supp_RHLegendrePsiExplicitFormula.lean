-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendrePsiExplicitFormula
-- name    : row23_rh_supp_RHLegendrePsiExplicitFormula
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:13:57.08453+00:00
-- url     : https://prove2.me/theorems/761be924-f227-424c-9523-cbbe30404a0f
-- title:
--   Row 23 RH support: RHLegendrePsiExplicitFormula
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreSecondAveraging
import Definitions.Def_row23_rh_supp_RHLegendreSecondKernel
import Definitions.Def_row23_rh_supp_RHLegendreQuadraticSeries
import Definitions.Def_row23_rh_supp_RHLegendrePerronRemainder
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace DusartLegendreSmoothing
open Polynomial MeasureTheory intervalIntegral
open DusartSmoothing
 theorem twiceWeighted_quadratic_zero_series (m : ℕ) (hm : 2 ≤ m) (x δ : ℝ)
    (hx : 1 ≤ x) (hd : 0 < δ) :
    twiceWeightedRemainder m (fun y : ℝ => ∑' ρ : NontrivialZetaZero,
      (RvM.zeroMult ρ.val:ℂ)*quadraticKernel y ρ.val) x δ =
    ∑' ρ : NontrivialZetaZero, (RvM.zeroMult ρ.val:ℂ)*((x:ℂ)^ρ.val*zeroKernel m ρ.val δ) := by
  unfold twiceWeightedRemainder
  rw [(weighted_quadratic_zero_series_integrable_and_interchange m x δ hx hd).2,←tsum_div_const]
  apply tsum_congr
  intro ρ
  have hρ : ρ.val.im≠0 := by
    intro he
    have hh := RvM.nontrivial_zero_abs_height ρ.val ρ.property
    rw [he,abs_zero] at hh
    linarith [Real.pi_pos]
  have he : (fun t : ℝ => ((iteratedDeriv 2 (weight m) t:ℝ):ℂ)*
      ((RvM.zeroMult ρ.val:ℂ)*quadraticKernel (x*(1+δ*t)) ρ.val)) =
      (fun t : ℝ => (RvM.zeroMult ρ.val:ℂ)*
        (((iteratedDeriv 2 (weight m) t:ℝ):ℂ)*quadraticKernel (x*(1+δ*t)) ρ.val)) := by
    funext t
    ring
  rw [he,intervalIntegral.integral_const_mul,mul_div_assoc]
  congr 1
  exact integral_affine_quadratic_kernel m hm ρ.val x δ (lt_of_lt_of_le zero_lt_one hx) hd hρ
 theorem psi_average_explicit_formula (m : ℕ) (hm : 2 ≤ m) (x δ : ℝ)
    (hx : 1 ≤ x) (hd : 0 < δ) :
    ((average m Chebyshev.psi x δ-x*(1+δ/2):ℝ):ℂ) =
      -(∑' ρ : NontrivialZetaZero, (RvM.zeroMult ρ.val:ℂ)*((x:ℂ)^ρ.val*zeroKernel m ρ.val δ))+
        (-logDeriv riemannZeta 0+legendrePerronRemainder m x δ) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  obtain ⟨N,hN⟩ := exists_nat_ge (x*(1+δ))
  let y := fun t : ℝ => x*(1+δ*t)
  let W := fun t : ℝ => ((iteratedDeriv 2 (weight m) t:ℝ):ℂ)
  let A := fun t : ℝ => W t*(secondPsiPrimitive N (y t):ℂ)
  let B := fun t : ℝ => W t*((y t:ℂ)^3/6)
  let C := fun t : ℝ => (W t*((y t:ℂ)^2/2))*logDeriv riemannZeta 0
  let D := fun t : ℝ => W t*(∑' ρ : NontrivialZetaZero, (RvM.zeroMult ρ.val:ℂ)*quadraticKernel (y t) ρ.val)
  have hw : Continuous W := by
    have he : iteratedDeriv 2 (weight m) = fun t : ℝ => (Polynomial.derivative^[2] (densityPolynomial m)).eval t :=
      funext (iteratedDeriv_weight m 2)
    dsimp only [W]
    rw [he]
    exact Complex.continuous_ofReal.comp (Polynomial.derivative^[2] (densityPolynomial m)).continuous
  have hiA : IntervalIntegrable A volume 0 1 := by
    apply Continuous.intervalIntegrable
    have hp : Continuous (fun t : ℝ => (secondPsiPrimitive N (y t):ℂ)) := by
      unfold secondPsiPrimitive
      dsimp only [y]
      fun_prop
    exact hw.mul hp
  have hiB : IntervalIntegrable B volume 0 1 := by
    apply Continuous.intervalIntegrable
    dsimp only [B,y]
    fun_prop
  have hiC : IntervalIntegrable C volume 0 1 := by
    apply Continuous.intervalIntegrable
    dsimp only [C,y]
    fun_prop
  have hiD : IntervalIntegrable D volume 0 1 :=
    (weighted_quadratic_zero_series_integrable_and_interchange m x δ hx hd).1
  have he : (∫ t : ℝ in 0..1, W t*perronLeftRemainder (y t)) =
      (∫ t : ℝ in 0..1, A t)-(∫ t : ℝ in 0..1, B t)+
        (∫ t : ℝ in 0..1, C t)+(∫ t : ℝ in 0..1, D t) := by
    rw [←intervalIntegral.integral_sub hiA hiB,
      ←intervalIntegral.integral_add (hiA.sub hiB) hiC,
      ←intervalIntegral.integral_add ((hiA.sub hiB).add hiC) hiD]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    have hlow : 1 ≤ y t := by
      dsimp only [y]
      nlinarith [mul_nonneg hd.le ht.1,mul_nonneg hx0.le (mul_nonneg hd.le ht.1)]
    have hupper : y t ≤ N := by
      apply le_trans _ hN
      dsimp only [y]
      nlinarith [mul_le_mul_of_nonneg_left ht.2 (mul_nonneg hx0.le hd.le)]
    have hf := secondPsiPrimitive_explicit_formula N (y t) hlow hupper
    have hr : perronLeftRemainder (y t) = (secondPsiPrimitive N (y t):ℂ)-
        (y t:ℂ)^3/6+(y t:ℂ)^2/2*logDeriv riemannZeta 0+
        (∑' ρ : NontrivialZetaZero, (RvM.zeroMult ρ.val:ℂ)*quadraticKernel (y t) ρ.val) := by
      linear_combination -hf
    rw [hr]
    dsimp only [A,B,C,D]
    ring
  have hA : (∫ t : ℝ in 0..1, A t)/((δ*x:ℝ):ℂ)^2 = ((average m Chebyshev.psi x δ:ℝ):ℂ) :=
    twiceWeighted_secondPsiPrimitive m N hm x δ hx0 hd hN
  have hB : (∫ t : ℝ in 0..1, B t)/((δ*x:ℝ):ℂ)^2 = ((x*(1+δ/2):ℝ):ℂ) :=
    twiceWeighted_cubic_term m hm x δ hx0 hd
  have hC : (∫ t : ℝ in 0..1, C t)/((δ*x:ℝ):ℂ)^2 = logDeriv riemannZeta 0 := by
    dsimp only [C]
    rw [intervalIntegral.integral_mul_const,mul_div_right_comm]
    change twiceWeightedRemainder m (fun z : ℝ => (z:ℂ)^2/2) x δ*logDeriv riemannZeta 0 = _
    rw [twiceWeighted_quadratic_term m hm x δ hx0 hd,one_mul]
  have hD : (∫ t : ℝ in 0..1, D t)/((δ*x:ℝ):ℂ)^2 =
      ∑' ρ : NontrivialZetaZero, (RvM.zeroMult ρ.val:ℂ)*((x:ℂ)^ρ.val*zeroKernel m ρ.val δ) :=
    twiceWeighted_quadratic_zero_series m hm x δ hx hd
  have hR : legendrePerronRemainder m x δ = ((average m Chebyshev.psi x δ:ℝ):ℂ)-
      ((x*(1+δ/2):ℝ):ℂ)+logDeriv riemannZeta 0+
      (∑' ρ : NontrivialZetaZero, (RvM.zeroMult ρ.val:ℂ)*((x:ℂ)^ρ.val*zeroKernel m ρ.val δ)) := by
    change (∫ t : ℝ in 0..1, W t*perronLeftRemainder (y t))/((δ*x:ℝ):ℂ)^2 = _
    rw [he,add_div,add_div,sub_div,hA,hB,hC,hD]
  push_cast at hR ⊢
  linear_combination -hR
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.psi_average_explicit_formula


