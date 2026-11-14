-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendreSmoothing
-- name    : row23_rh_supp_RHLegendreSmoothing
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T21:58:19.122458+00:00
-- url     : https://prove2.me/theorems/bb48cd66-21e6-4b6f-b313-5e7d35aa3459
-- title:
--   Row 23 RH support: RHLegendreSmoothing
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace DusartLegendreSmoothing
open MeasureTheory intervalIntegral
noncomputable def normalization (m : ℕ) : ℝ :=
  ((2*m+1).factorial : ℝ) / (m.factorial : ℝ)^2
noncomputable def weight (m : ℕ) (t : ℝ) : ℝ :=
  normalization m * t^m * (1-t)^m
lemma normalization_pos (m : ℕ) : 0 < normalization m := by
  unfold normalization
  positivity
lemma weight_nonneg (m : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : 0 ≤ weight m t := by
  unfold weight
  exact mul_nonneg (mul_nonneg (normalization_pos m).le (pow_nonneg ht.1 _))
    (pow_nonneg (sub_nonneg.mpr ht.2) _)
lemma weight_continuous (m : ℕ) : Continuous (weight m) := by
  unfold weight
  fun_prop
lemma weight_symmetric (m : ℕ) (t : ℝ) : weight m (1-t)=weight m t := by
  simp only [weight,sub_sub_cancel]
  ring
lemma beta_nat (m n : ℕ) :
    (∫ t : ℝ in 0..1, t^m*(1-t)^n) =
      (m.factorial:ℝ)*(n.factorial:ℝ)/((m+n+1).factorial:ℝ) := by
  apply Complex.ofReal_injective
  have h := Complex.betaIntegral_eq_Gamma_mul_div ((m:ℂ)+1) ((n:ℂ)+1)
    (by simp only [Complex.add_re,Complex.natCast_re,Complex.one_re]; positivity)
    (by simp only [Complex.add_re,Complex.natCast_re,Complex.one_re]; positivity)
  have he : (m:ℂ)+1+((n:ℂ)+1)=((m+n+1:ℕ):ℂ)+1 := by push_cast; ring
  rw [he,Complex.Gamma_nat_eq_factorial,Complex.Gamma_nat_eq_factorial,
    Complex.Gamma_nat_eq_factorial] at h
  simp only [Complex.betaIntegral,add_sub_cancel_right,Complex.cpow_natCast] at h
  rw [←intervalIntegral.integral_ofReal]
  push_cast
  exact h
lemma moment (m k : ℕ) :
    (∫ t : ℝ in 0..1, weight m t*t^k) =
      normalization m * ((m+k).factorial:ℝ)*(m.factorial:ℝ)/((2*m+k+1).factorial:ℝ) := by
  have he : (fun t : ℝ => weight m t*t^k) =
      (fun t : ℝ => normalization m * (t^(m+k)*(1-t)^m)) := by
    funext t
    rw [weight,pow_add]
    ring
  rw [he,intervalIntegral.integral_const_mul,beta_nat]
  have hn : m+k+m+1=2*m+k+1 := by omega
  rw [hn]
  ring
lemma integral_weight (m : ℕ) : (∫ t : ℝ in 0..1, weight m t)=1 := by
  have h := moment m 0
  simp only [pow_zero,mul_one,Nat.add_zero] at h
  rw [h]
  unfold normalization
  have hm : (m.factorial:ℝ)≠0 := by positivity
  have h2m : ((2*m+1).factorial:ℝ)≠0 := by positivity
  field_simp
lemma first_moment (m : ℕ) : (∫ t : ℝ in 0..1, weight m t*t)=1/2 := by
  have h := moment m 1
  simp only [pow_one] at h
  rw [h]
  have hm : (m.factorial:ℝ)≠0 := by positivity
  have h2m : ((2*m+1).factorial:ℝ)≠0 := by positivity
  rw [show 2*m+1+1=(2*m+1)+1 by omega,Nat.factorial_succ,Nat.factorial_succ]
  push_cast
  unfold normalization
  field_simp
  ring
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.beta_nat
#print axioms DusartLegendreSmoothing.integral_weight
#print axioms DusartLegendreSmoothing.first_moment


