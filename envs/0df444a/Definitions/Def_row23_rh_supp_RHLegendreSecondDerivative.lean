-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendreSecondDerivative
-- name    : row23_rh_supp_RHLegendreSecondDerivative
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:06:47.425324+00:00
-- url     : https://prove2.me/theorems/a00a0f31-3b5d-4b43-b595-6cbee1938d03
-- title:
--   Row 23 RH support: RHLegendreSecondDerivative
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreIntegration
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace DusartLegendreSmoothing
open MeasureTheory intervalIntegral
noncomputable def betaCoefficient (a b : ℕ) : ℝ :=
  ((a+b+1).factorial:ℝ)/((a.factorial:ℝ)*(b.factorial:ℝ))
noncomputable def betaDensity (a b : ℕ) (t : ℝ) : ℝ :=
  betaCoefficient a b*(t^a*(1-t)^b)
lemma betaCoefficient_pos (a b : ℕ) : 0 < betaCoefficient a b := by
  unfold betaCoefficient
  positivity
lemma betaCoefficient_comm (a b : ℕ) : betaCoefficient a b=betaCoefficient b a := by
  unfold betaCoefficient
  rw [Nat.add_comm a b,mul_comm (a.factorial:ℝ)]
lemma betaDensity_diagonal (m : ℕ) : betaDensity m m=weight m := by
  funext t
  simp only [betaDensity,betaCoefficient,weight,normalization,two_mul,pow_two]
  ring
lemma betaDensity_nonneg (a b : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    0 ≤ betaDensity a b t := by
  unfold betaDensity
  exact mul_nonneg (betaCoefficient_pos a b).le
    (mul_nonneg (pow_nonneg ht.1 _) (pow_nonneg (sub_nonneg.mpr ht.2) _))
lemma betaDensity_continuous (a b : ℕ) : Continuous (betaDensity a b) := by
  unfold betaDensity
  fun_prop
lemma integral_betaDensity (a b : ℕ) : (∫ t : ℝ in 0..1, betaDensity a b t)=1 := by
  unfold betaDensity
  rw [intervalIntegral.integral_const_mul,beta_nat]
  unfold betaCoefficient
  have ha : (a.factorial:ℝ) ≠ 0 := by positivity
  have hb : (b.factorial:ℝ) ≠ 0 := by positivity
  have hab : ((a+b+1).factorial:ℝ) ≠ 0 := by positivity
  field_simp
lemma betaCoefficient_succ_left (a b : ℕ) :
    betaCoefficient (a+1) b*((a:ℝ)+1)=((a+b+2:ℕ):ℝ)*betaCoefficient a b := by
  unfold betaCoefficient
  rw [show a+1+b+1=(a+b+1)+1 by omega,Nat.factorial_succ (a+b+1),Nat.factorial_succ a]
  have ha : (a.factorial:ℝ) ≠ 0 := by positivity
  have hb : (b.factorial:ℝ) ≠ 0 := by positivity
  have has : (a:ℝ)+1 ≠ 0 := by positivity
  push_cast
  field_simp [ha,hb,has]
  <;> ring
lemma betaCoefficient_succ_right (a b : ℕ) :
    betaCoefficient a (b+1)*((b:ℝ)+1)=((a+b+2:ℕ):ℝ)*betaCoefficient a b := by
  rw [betaCoefficient_comm a (b+1),betaCoefficient_succ_left,
    betaCoefficient_comm b a]
  push_cast
  ring
lemma betaDensity_hasDerivAt (a b : ℕ) (t : ℝ) :
    HasDerivAt (betaDensity (a+1) (b+1))
      (((a+b+3:ℕ):ℝ)*(betaDensity a (b+1) t-betaDensity (a+1) b t)) t := by
  have h := (((hasDerivAt_id t).pow (a+1)).mul
    (((hasDerivAt_id t).const_sub 1).pow (b+1))).const_mul (betaCoefficient (a+1) (b+1))
  simp only [Pi.pow_apply,Pi.mul_apply,Pi.sub_apply,id_eq,Nat.add_sub_cancel,mul_one] at h
  have hl := betaCoefficient_succ_left a (b+1)
  have hr := betaCoefficient_succ_right (a+1) b
  change HasDerivAt (fun y : ℝ => betaCoefficient (a+1) (b+1)*(y^(a+1)*(1-y)^(b+1))) _ t
  apply h.congr_deriv
  dsimp only [betaDensity]
  push_cast at hl hr ⊢
  linear_combination (t^a*(1-t)^(b+1))*hl - (t^(a+1)*(1-t)^b)*hr
lemma weight_second_derivative (k : ℕ) (t : ℝ) :
    iteratedDeriv 2 (weight (k+2)) t=
      ((2*(k+2):ℕ):ℝ)*((2*(k+2)+1:ℕ):ℝ)*
        (betaDensity k (k+2) t-2*betaDensity (k+1) (k+1) t+betaDensity (k+2) k t) := by
  have hfirst : deriv (weight (k+2))=fun y : ℝ =>
      ((2*(k+2)+1:ℕ):ℝ)*(betaDensity (k+1) (k+2) y-betaDensity (k+2) (k+1) y) := by
    funext y
    rw [←betaDensity_diagonal (k+2)]
    have h := (betaDensity_hasDerivAt (k+1) (k+1) y).deriv
    convert h using 1 <;> push_cast <;> ring
  have hsecond := ((betaDensity_hasDerivAt k (k+1) t).sub
    (betaDensity_hasDerivAt (k+1) k t)).const_mul (((2*(k+2)+1:ℕ):ℝ))
  rw [show k+1+1=k+2 by omega] at hsecond
  simp only [Pi.sub_apply] at hsecond
  rw [iteratedDeriv_succ,iteratedDeriv_succ,iteratedDeriv_zero,hfirst,hsecond.deriv]
  push_cast
  ring
 theorem integral_abs_second_derivative_add_two (k : ℕ) :
    (∫ t : ℝ in 0..1, |iteratedDeriv 2 (weight (k+2)) t|) ≤
      8*(k+2:ℝ)*(2*(k+2)+1) := by
  let K : ℝ := ((2*(k+2):ℕ):ℝ)*((2*(k+2)+1:ℕ):ℝ)
  let A := betaDensity k (k+2)
  let B := betaDensity (k+1) (k+1)
  let C := betaDensity (k+2) k
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
      |iteratedDeriv 2 (weight (k+2)) t| ≤ K*(A t+2*B t+C t) := by
    have ha : 0 ≤ A t := betaDensity_nonneg _ _ t ht
    have hb : 0 ≤ B t := betaDensity_nonneg _ _ t ht
    have hc : 0 ≤ C t := betaDensity_nonneg _ _ t ht
    rw [weight_second_derivative]
    change |K*(A t-2*B t+C t)| ≤ _
    rw [abs_mul,abs_of_nonneg hK]
    apply mul_le_mul_of_nonneg_left _ hK
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hA := (betaDensity_continuous k (k+2)).intervalIntegrable (μ:=volume) (a:=(0:ℝ)) (b:=1)
  have hB := (betaDensity_continuous (k+1) (k+1)).intervalIntegrable (μ:=volume) (a:=(0:ℝ)) (b:=1)
  have hC := (betaDensity_continuous (k+2) k).intervalIntegrable (μ:=volume) (a:=(0:ℝ)) (b:=1)
  have hi : IntervalIntegrable (fun t : ℝ => |iteratedDeriv 2 (weight (k+2)) t|) volume 0 1 := by
    have he : iteratedDeriv 2 (weight (k+2))=
        fun t => (Polynomial.derivative^[2] (densityPolynomial (k+2))).eval t := by
      funext t
      exact iteratedDeriv_weight _ _ _
    rw [he]
    exact (Polynomial.continuous _).abs.intervalIntegrable 0 1
  have hj : IntervalIntegrable (fun t : ℝ => K*(A t+2*B t+C t)) volume 0 1 :=
    ((hA.add (hB.const_mul 2)).add hC).const_mul K
  have h := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1) hi hj hpoint
  apply h.trans_eq
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hA.add (hB.const_mul 2)) hC,
    intervalIntegral.integral_add hA (hB.const_mul 2),intervalIntegral.integral_const_mul]
  rw [integral_betaDensity,integral_betaDensity,integral_betaDensity]
  dsimp [K]
  push_cast
  ring
 theorem integral_abs_second_derivative (m : ℕ) (hm : 2 ≤ m) :
    (∫ t : ℝ in 0..1, |iteratedDeriv 2 (weight m) t|) ≤ 8*(m:ℝ)*(2*m+1) := by
  have hn : m-2+2=m := by omega
  have hr : ((m-2:ℕ):ℝ)+2=(m:ℝ) := by exact_mod_cast hn
  simpa only [hn,hr] using integral_abs_second_derivative_add_two (m-2)
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.betaDensity_hasDerivAt
#print axioms DusartLegendreSmoothing.weight_second_derivative
#print axioms DusartLegendreSmoothing.integral_abs_second_derivative


