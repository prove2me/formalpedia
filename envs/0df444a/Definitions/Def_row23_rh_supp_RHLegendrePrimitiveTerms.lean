-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendrePrimitiveTerms
-- name    : row23_rh_supp_RHLegendrePrimitiveTerms
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:05:54.411683+00:00
-- url     : https://prove2.me/theorems/59f165d9-2792-47e6-95d7-dc124a3b8a65
-- title:
--   Row 23 RH support: RHLegendrePrimitiveTerms
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendrePolynomialPairing
set_option autoImplicit false
namespace DusartLegendreSmoothing
open Polynomial MeasureTheory intervalIntegral
 theorem second_primitive_quadratic_term (m : ℕ) (hm : 2 ≤ m) (x δ : ℝ) (hx : 0 < x) (hd : 0 < δ) :
    (∫ t : ℝ in 0..1, iteratedDeriv 2 (weight m) t*((x*(1+δ*t))^2/2))/(δ*x)^2=1 := by
  let q : ℝ[X] := C (1/2:ℝ)*(C x+C (δ*x)*X)^2
  have hq (t : ℝ) : q.eval t=(x*(1+δ*t))^2/2 := by simp [q]; ring
  have hq' (t : ℝ) : q.derivative.derivative.eval t=(δ*x)^2 := by
    simp [q,Polynomial.derivative_mul,Polynomial.derivative_pow]
    ring
  have h := second_derivative_polynomial_pairing m hm q
  simp_rw [hq,hq'] at h
  rw [intervalIntegral.integral_mul_const,integral_weight,one_mul] at h
  rw [h]
  exact div_self (pow_ne_zero 2 (mul_pos hd hx).ne')
 theorem second_primitive_cubic_term (m : ℕ) (hm : 2 ≤ m) (x δ : ℝ) (hx : 0 < x) (hd : 0 < δ) :
    (∫ t : ℝ in 0..1, iteratedDeriv 2 (weight m) t*((x*(1+δ*t))^3/6))/(δ*x)^2=x*(1+δ/2) := by
  let q : ℝ[X] := C (1/6:ℝ)*(C x+C (δ*x)*X)^3
  have hq (t : ℝ) : q.eval t=(x*(1+δ*t))^3/6 := by simp [q]; ring
  have hq' (t : ℝ) : q.derivative.derivative.eval t=(δ*x)^2*(x*(1+δ*t)) := by
    simp [q,Polynomial.derivative_mul,Polynomial.derivative_pow]
    ring
  have h := second_derivative_polynomial_pairing m hm q
  simp_rw [hq,hq'] at h
  have he : (∫ t : ℝ in 0..1, weight m t*((δ*x)^2*(x*(1+δ*t)))) =
      (δ*x)^2*average m id x δ := by
    unfold average
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only [id_eq]
    ring
  rw [he,average_id] at h
  rw [h]
  field_simp
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.second_primitive_quadratic_term
#print axioms DusartLegendreSmoothing.second_primitive_cubic_term


