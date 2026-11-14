-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendreSecondRemainder
-- name    : row23_rh_supp_RHLegendreSecondRemainder
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:07:19.689979+00:00
-- url     : https://prove2.me/theorems/e29e4b61-de01-414d-9fb3-54008063ca4c
-- title:
--   Row 23 RH support: RHLegendreSecondRemainder
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreSecondDerivative
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace DusartLegendreSmoothing
open MeasureTheory intervalIntegral
noncomputable def twiceWeightedRemainder (m : ℕ) (R : ℝ → ℂ) (x δ : ℝ) : ℂ :=
  (∫ t : ℝ in 0..1, ((iteratedDeriv 2 (weight m) t:ℝ):ℂ)*R (x*(1+δ*t)))/((δ*x:ℝ):ℂ)^2
 theorem norm_twiceWeightedRemainder (m : ℕ) (R : ℝ → ℂ) (x δ C : ℝ)
    (hm : 2 ≤ m) (hx : 0 < x) (hd : 0 < δ) (hC : 0 ≤ C)
    (hR : ∀ y, 0 < y → ‖R y‖ ≤ C*y^(3/2:ℝ)) :
    ‖twiceWeightedRemainder m R x δ‖ ≤
      (C*(8*(m:ℝ)*(2*m+1))*(1+δ)^(3/2:ℝ)/δ^2)*x^(-1/2:ℝ) := by
  let D := C*(x*(1+δ))^(3/2:ℝ)
  let K := 8*(m:ℝ)*(2*m+1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hpoint (t : ℝ) (ht : t ∈ Set.Ioc (0:ℝ) 1) :
      ‖((iteratedDeriv 2 (weight m) t:ℝ):ℂ)*R (x*(1+δ*t))‖ ≤ D*|iteratedDeriv 2 (weight m) t| := by
    have hy0 : 0 < x*(1+δ*t) := mul_pos hx (by nlinarith [mul_nonneg hd.le ht.1.le])
    have hy : x*(1+δ*t) ≤ x*(1+δ) := by
      apply mul_le_mul_of_nonneg_left _ hx.le
      nlinarith [mul_le_mul_of_nonneg_left ht.2 hd.le]
    have hp : (x*(1+δ*t))^(3/2:ℝ) ≤ (x*(1+δ))^(3/2:ℝ) :=
      Real.rpow_le_rpow hy0.le hy (by norm_num)
    have hr : ‖R (x*(1+δ*t))‖ ≤ D :=
      (hR _ hy0).trans (mul_le_mul_of_nonneg_left hp hC)
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left hr (abs_nonneg _)).trans_eq (mul_comm _ _)
  have ha : IntervalIntegrable (fun t : ℝ => |iteratedDeriv 2 (weight m) t|) volume 0 1 := by
    simpa only [iteratedDeriv_weight] using
      ((Polynomial.continuous (Polynomial.derivative^[2] (densityPolynomial m))).abs.intervalIntegrable (0:ℝ) 1)
  have hi := intervalIntegral.norm_integral_le_of_norm_le (by norm_num : (0:ℝ) ≤ 1)
    (Filter.Eventually.of_forall hpoint) (ha.const_mul D)
  rw [intervalIntegral.integral_const_mul] at hi
  have hmass : (∫ t : ℝ in 0..1, |iteratedDeriv 2 (weight m) t|) ≤ K :=
    integral_abs_second_derivative m hm
  have hint := hi.trans (mul_le_mul_of_nonneg_left hmass hD)
  have hp : x^(3/2:ℝ)/x^2=x^(-1/2:ℝ) := by
    have h := Real.rpow_sub hx (3/2:ℝ) (2:ℝ)
    have he : x^(2:ℝ) = x^2 := Real.rpow_natCast x 2
    rw [he] at h
    convert h.symm using 1 <;> norm_num
  rw [twiceWeightedRemainder,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (mul_pos hd hx)]
  calc
    _ ≤ (D*K)/(δ*x)^2 := div_le_div_of_nonneg_right hint (by positivity)
    _ = (C*K*(1+δ)^(3/2:ℝ)/δ^2)*(x^(3/2:ℝ)/x^2) := by
      dsimp only [D]
      rw [Real.mul_rpow hx.le (by linarith : 0 ≤ 1+δ)]
      field_simp
      <;> ring
    _ = _ := by rw [hp]
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.norm_twiceWeightedRemainder


