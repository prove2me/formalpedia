-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendrePrimePrimitive
-- name    : row23_rh_supp_RHLegendrePrimePrimitive
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:04:16.304208+00:00
-- url     : https://prove2.me/theorems/775f69fd-82fd-40fd-821b-539c6e92fbb7
-- title:
--   Row 23 RH support: RHLegendrePrimePrimitive
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendrePolynomialStep
import Definitions.Def_row23_rh_supp_RHLegendreAverage
import Definitions.Def_dusart_psi_433_20261014_IntegratedPsi
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace DusartLegendreSmoothing
open Polynomial MeasureTheory intervalIntegral
lemma weight_step_second_primitive (m : ℕ) (hm : 2 ≤ m) (c : ℝ) :
    (∫ t : ℝ in 0..1, weight m t*unitStep c t) =
      ∫ t : ℝ in 0..1, iteratedDeriv 2 (weight m) t*(max (t-c) 0)^2/2 := by
  have h0 := derivative_at_zero m 0 (by omega : 0 < m)
  have h1 := derivative_at_one m 0 (by omega : 0 < m)
  have h0' := derivative_at_zero m 1 (by omega : 1 < m)
  have h1' := derivative_at_one m 1 (by omega : 1 < m)
  simp only [iteratedDeriv_weight,Function.iterate_succ_apply,Function.iterate_zero_apply] at h0 h1 h0' h1'
  simpa only [densityPolynomial_eval,iteratedDeriv_weight,Function.iterate_succ_apply,
    Function.iterate_zero_apply] using
    polynomial_step_second_primitive (densityPolynomial m) c h0 h1 h0' h1'
lemma prime_step_affine_primitive (m : ℕ) (hm : 2 ≤ m) (n : ℕ) (x δ : ℝ)
    (hx : 0 < x) (hd : 0 < δ) :
    (∫ t : ℝ in 0..1, weight m t*DusartSmoothing.primeStep n (x*(1+δ*t))) =
      (∫ t : ℝ in 0..1, iteratedDeriv 2 (weight m) t*(max (x*(1+δ*t)-n) 0)^2/2)/(δ*x)^2 := by
  let h := δ*x
  let c := ((n:ℝ)-x)/h
  have hh : 0 < h := mul_pos hd hx
  have he (t : ℝ) : x*(1+δ*t)-n=h*(t-c) := by
    dsimp only [h,c]
    field_simp [ne_of_gt hx,ne_of_gt hd]
    ring
  have hs (t : ℝ) : DusartSmoothing.primeStep n (x*(1+δ*t))=unitStep c t := by
    unfold DusartSmoothing.primeStep unitStep
    have hc : ((n:ℝ) ≤ x*(1+δ*t)) ↔ c ≤ t := by
      rw [←sub_nonneg,he,mul_nonneg_iff_of_pos_left hh,sub_nonneg]
    simp only [hc]
  have hr (t : ℝ) : (max (x*(1+δ*t)-n) 0)^2/2=h^2*((max (t-c) 0)^2/2) := by
    rw [he]
    by_cases ht : 0 ≤ t-c
    · rw [max_eq_left ht,max_eq_left (mul_nonneg hh.le ht)]
      ring
    · have ht' := le_of_lt (lt_of_not_ge ht)
      rw [max_eq_right ht',max_eq_right (mul_nonpos_of_nonneg_of_nonpos hh.le ht')]
      ring
  have hi : (∫ t : ℝ in 0..1, iteratedDeriv 2 (weight m) t*(max (x*(1+δ*t)-n) 0)^2/2) =
      h^2*(∫ t : ℝ in 0..1, iteratedDeriv 2 (weight m) t*(max (t-c) 0)^2/2) := by
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    calc
      _ = iteratedDeriv 2 (weight m) t*((max (x*(1+δ*t)-n) 0)^2/2) := by ring
      _ = _ := by rw [hr]; ring
  simp_rw [hs]
  rw [hi,weight_step_second_primitive m hm c]
  change _ = h^2*_ / h^2
  field_simp
 theorem average_finitePsi_eq_second_primitive (m N : ℕ) (hm : 2 ≤ m) (x δ : ℝ)
    (hx : 0 < x) (hd : 0 < δ) :
    average m (DusartSmoothing.finitePsi N) x δ =
      (∫ t : ℝ in 0..1, iteratedDeriv 2 (weight m) t*DusartSmoothing.secondPsiPrimitive N (x*(1+δ*t)))/(δ*x)^2 := by
  have hw : Continuous (iteratedDeriv 2 (weight m)) := by
    have he : iteratedDeriv 2 (weight m) = fun t : ℝ => (Polynomial.derivative^[2] (densityPolynomial m)).eval t :=
      funext (iteratedDeriv_weight m 2)
    rw [he]
    exact (Polynomial.derivative^[2] (densityPolynomial m)).continuous
  have hs (n : ℕ) : IntervalIntegrable
      (fun t : ℝ => ArithmeticFunction.vonMangoldt n*(weight m t*DusartSmoothing.primeStep n (x*(1+δ*t)))) volume 0 1 := by
    have hh := ((DusartSmoothing.primeStep_mono n).comp (affine_monotone x δ hx.le hd.le)).intervalIntegrable (μ:=volume) (a:=0) (b:=1)
    have hi : IntervalIntegrable (fun t : ℝ => weight m t*DusartSmoothing.primeStep n (x*(1+δ*t))) volume 0 1 := by
      simpa only [mul_comm,Function.comp_apply] using hh.mul_continuousOn (weight_continuous m).continuousOn
    exact hi.const_mul _
  have hr (n : ℕ) : IntervalIntegrable
      (fun t : ℝ => ArithmeticFunction.vonMangoldt n*(iteratedDeriv 2 (weight m) t*(max (x*(1+δ*t)-n) 0)^2/2)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have he (t : ℝ) : weight m t*DusartSmoothing.finitePsi N (x*(1+δ*t)) =
      ∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n*(weight m t*DusartSmoothing.primeStep n (x*(1+δ*t))) := by
    unfold DusartSmoothing.finitePsi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  have he' (t : ℝ) : iteratedDeriv 2 (weight m) t*DusartSmoothing.secondPsiPrimitive N (x*(1+δ*t)) =
      ∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n*(iteratedDeriv 2 (weight m) t*(max (x*(1+δ*t)-n) 0)^2/2) := by
    unfold DusartSmoothing.secondPsiPrimitive
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  unfold average
  simp_rw [he,he']
  rw [intervalIntegral.integral_finsetSum (fun n hn => hs n),
      intervalIntegral.integral_finsetSum (fun n hn => hr n),Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
      prime_step_affine_primitive m hm n x δ hx hd]
  ring
 theorem average_psi_eq_second_primitive (m N : ℕ) (hm : 2 ≤ m) (x δ : ℝ)
    (hx : 0 < x) (hd : 0 < δ) (hN : x*(1+δ) ≤ N) :
    average m Chebyshev.psi x δ =
      (∫ t : ℝ in 0..1, iteratedDeriv 2 (weight m) t*DusartSmoothing.secondPsiPrimitive N (x*(1+δ*t)))/(δ*x)^2 := by
  rw [←average_finitePsi_eq_second_primitive m N hm x δ hx hd]
  unfold average
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
  rw [DusartSmoothing.finitePsi_eq_psi N _
    (mul_nonneg hx.le (by nlinarith [mul_nonneg hd.le ht.1]))
    (le_trans (by nlinarith [mul_le_mul_of_nonneg_left ht.2 (mul_nonneg hx.le hd.le)]) hN)]
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.average_psi_eq_second_primitive


