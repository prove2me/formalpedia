-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendreRodrigues
-- name    : row23_rh_supp_RHLegendreRodrigues
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T21:58:47.476779+00:00
-- url     : https://prove2.me/theorems/64b929d3-51d4-492a-99b1-8903bdd7544e
-- title:
--   Row 23 RH support: RHLegendreRodrigues
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreSmoothing
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace DusartLegendreSmoothing
open Polynomial MeasureTheory intervalIntegral
noncomputable def densityPolynomial (m : ℕ) : ℝ[X] :=
  C (normalization m) * (X^m*(1-X)^m)
lemma densityPolynomial_eval (m : ℕ) (t : ℝ) : (densityPolynomial m).eval t=weight m t := by
  simp [densityPolynomial,weight,mul_assoc]
lemma iteratedDeriv_polynomial (p : ℝ[X]) (k : ℕ) :
    iteratedDeriv k (fun t : ℝ => p.eval t) = fun t => (derivative^[k] p).eval t := by
  induction k with
  | zero => rw [iteratedDeriv_zero]; rfl
  | succ k ih =>
    rw [iteratedDeriv_succ,ih]
    funext t
    rw [Polynomial.deriv]
    simp only [Function.iterate_succ_apply']
lemma iteratedDeriv_weight (m k : ℕ) (t : ℝ) :
    iteratedDeriv k (weight m) t=(derivative^[k] (densityPolynomial m)).eval t := by
  have he : weight m=fun t : ℝ => (densityPolynomial m).eval t := by
    funext t
    exact (densityPolynomial_eval m t).symm
  rw [he,iteratedDeriv_polynomial]
lemma densityPolynomial_derivative (m : ℕ) :
    derivative^[m] (densityPolynomial m)=
      C (normalization m*(m.factorial:ℝ)) * (shiftedLegendre m).map (Int.castRingHom ℝ) := by
  have hid : derivative^[m] (X^m*(1-X)^m : ℝ[X])=
      (m.factorial:ℝ[X])*(shiftedLegendre m).map (Int.castRingHom ℝ) := by
    simpa only [Polynomial.map_mul,Polynomial.map_natCast,←iterate_derivative_map,
      Polynomial.map_pow,Polynomial.map_X,Polynomial.map_sub,Polynomial.map_one] using
      congrArg (Polynomial.map (Int.castRingHom ℝ)) (factorial_mul_shiftedLegendre_eq m).symm
  rw [densityPolynomial,iterate_derivative_C_mul,hid]
  simp only [map_mul,map_natCast]
  ring
 theorem rodrigues (m : ℕ) (t : ℝ) :
    iteratedDeriv m (weight m) t=
      (normalization m*(m.factorial:ℝ))*((shiftedLegendre m).map (Int.castRingHom ℝ)).eval t := by
  rw [iteratedDeriv_weight,densityPolynomial_derivative]
  simp only [eval_mul,eval_C]
 theorem derivative_at_zero (m k : ℕ) (hk : k < m) : iteratedDeriv k (weight m) 0=0 := by
  have hd : (X:ℝ[X])^m ∣ densityPolynomial m :=
    ⟨C (normalization m)*(1-X)^m,by unfold densityPolynomial; ring⟩
  obtain ⟨q,hq⟩ := pow_sub_dvd_iterate_derivative_of_pow_dvd k hd
  rw [iteratedDeriv_weight,hq,eval_mul,eval_pow,eval_X,zero_pow (by omega : m-k≠0),zero_mul]
 theorem derivative_at_one (m k : ℕ) (hk : k < m) : iteratedDeriv k (weight m) 1=0 := by
  have hd : (1-X:ℝ[X])^m ∣ densityPolynomial m :=
    ⟨C (normalization m)*X^m,by unfold densityPolynomial; ring⟩
  obtain ⟨q,hq⟩ := pow_sub_dvd_iterate_derivative_of_pow_dvd k hd
  rw [iteratedDeriv_weight,hq,eval_mul,eval_pow]
  simp only [eval_sub,eval_one,eval_X,sub_self,zero_pow (by omega : m-k≠0),zero_mul]
noncomputable def derivativeMass (m : ℕ) (δ : ℝ) : ℝ :=
  ∫ t : ℝ in 0..1, |iteratedDeriv m (weight m) t| *(1+δ*t)^(m+1)
 theorem derivativeMass_eq (m : ℕ) (δ : ℝ) :
    derivativeMass m δ = (((2*m+1).factorial:ℝ)/(m.factorial:ℝ)) *
      (∫ t : ℝ in 0..1, |((shiftedLegendre m).map (Int.castRingHom ℝ)).eval t| *(1+δ*t)^(m+1)) := by
  have hc : normalization m*(m.factorial:ℝ)=((2*m+1).factorial:ℝ)/(m.factorial:ℝ) := by
    unfold normalization
    have hm : (m.factorial:ℝ)≠0 := by positivity
    field_simp
  unfold derivativeMass
  simp only [rodrigues,abs_mul,hc,mul_assoc]
  rw [intervalIntegral.integral_const_mul,abs_of_nonneg (by positivity : (0:ℝ)≤((2*m+1).factorial:ℝ)/(m.factorial:ℝ))]
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.rodrigues
#print axioms DusartLegendreSmoothing.derivative_at_zero
#print axioms DusartLegendreSmoothing.derivative_at_one
#print axioms DusartLegendreSmoothing.derivativeMass_eq


