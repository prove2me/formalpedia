-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendreBernstein
-- name    : row23_rh_supp_RHLegendreBernstein
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:16:39.485754+00:00
-- url     : https://prove2.me/theorems/d289b8a2-99b4-4d23-b24a-56e017eba4ca
-- title:
--   Row 23 RH support: RHLegendreBernstein
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreSmoothing
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace DusartLegendreSmoothing
open Polynomial Finset MeasureTheory intervalIntegral
lemma bernstein_eval_nonneg (n k : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    0≤(bernsteinPolynomial ℝ n k).eval t := by
  simpa only [bernsteinPolynomial,eval_mul,eval_pow,eval_natCast,eval_X,eval_sub,eval_one] using
    mul_nonneg (mul_nonneg (Nat.cast_nonneg (n.choose k)) (pow_nonneg ht.1 k))
      (pow_nonneg (sub_nonneg.mpr ht.2) (n-k))
 theorem bernstein_integral (n k : ℕ) (hk : k≤n) :
    (∫ t : ℝ in 0..1, (bernsteinPolynomial ℝ n k).eval t)=1/((n:ℝ)+1) := by
  have he : (fun t : ℝ => (bernsteinPolynomial ℝ n k).eval t)=
      (fun t : ℝ => (n.choose k:ℝ)*(t^k*(1-t)^(n-k))) := by
    funext t
    simp only [bernsteinPolynomial,eval_mul,eval_pow,eval_natCast,eval_X,eval_sub,eval_one,mul_assoc]
  rw [he,intervalIntegral.integral_const_mul,beta_nat,show k+(n-k)+1=n+1 by omega,Nat.factorial_succ]
  push_cast
  have hfac : (n.choose k:ℝ)*(k.factorial:ℝ)*((n-k).factorial:ℝ)=(n.factorial:ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  have hn : (n.factorial:ℝ)≠0 := by positivity
  have hn1 : (n:ℝ)+1≠0 := by positivity
  calc
    _ = ((n.choose k:ℝ)*(k.factorial:ℝ)*((n-k).factorial:ℝ))/(((n:ℝ)+1)*(n.factorial:ℝ)) := by ring
    _ = (n.factorial:ℝ)/(((n:ℝ)+1)*(n.factorial:ℝ)) := by rw [hfac]
    _ = _ := by field_simp
 theorem bernstein_integral_abs_bound (n : ℕ) (c : Fin (n+1) → ℝ) :
    (∫ t : ℝ in 0..1, |∑ i : Fin (n+1), c i*(bernsteinPolynomial ℝ n i.val).eval t|) ≤
      (∑ i : Fin (n+1), |c i|)/((n:ℝ)+1) := by
  have hleft : IntervalIntegrable
      (fun t : ℝ => |∑ i : Fin (n+1), c i*(bernsteinPolynomial ℝ n i.val).eval t|) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hright : IntervalIntegrable
      (fun t : ℝ => ∑ i : Fin (n+1), |c i| *(bernsteinPolynomial ℝ n i.val).eval t) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ)≤1) hleft hright
    (show ∀ t ∈ Set.Icc (0:ℝ) 1,
      |∑ i : Fin (n+1), c i*(bernsteinPolynomial ℝ n i.val).eval t| ≤
        ∑ i : Fin (n+1), |c i| *(bernsteinPolynomial ℝ n i.val).eval t from by
      intro t ht
      calc
        _ ≤ ∑ i : Fin (n+1), |c i*(bernsteinPolynomial ℝ n i.val).eval t| := abs_sum_le_sum_abs _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [abs_mul,abs_of_nonneg (bernstein_eval_nonneg n i.val t ht)])
  apply h.trans_eq
  rw [intervalIntegral.integral_finset_sum]
  · calc
      _ = ∑ i : Fin (n+1), |c i|/((n:ℝ)+1) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [intervalIntegral.integral_const_mul,bernstein_integral n i.val (by omega)]
        ring
      _ = _ := by rw [Finset.sum_div]
  · intro i hi
    exact ((bernsteinPolynomial ℝ n i.val).continuous.const_mul |c i|).intervalIntegrable 0 1
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.bernstein_integral
#print axioms DusartLegendreSmoothing.bernstein_integral_abs_bound


