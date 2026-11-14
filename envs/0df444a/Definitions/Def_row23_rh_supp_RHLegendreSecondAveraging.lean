-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendreSecondAveraging
-- name    : row23_rh_supp_RHLegendreSecondAveraging
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:08:08.827753+00:00
-- url     : https://prove2.me/theorems/e7131730-b0a1-4e60-ab64-b85bfb3ffe39
-- title:
--   Row 23 RH support: RHLegendreSecondAveraging
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendrePrimePrimitive
import Definitions.Def_row23_rh_supp_RHLegendrePrimitiveTerms
import Definitions.Def_row23_rh_supp_RHLegendreSecondRemainder
set_option autoImplicit false
namespace DusartLegendreSmoothing
open MeasureTheory intervalIntegral
 theorem twiceWeighted_secondPsiPrimitive (m N : ℕ) (hm : 2 ≤ m) (x δ : ℝ)
    (hx : 0 < x) (hd : 0 < δ) (hN : x*(1+δ) ≤ N) :
    twiceWeightedRemainder m (fun y : ℝ => (DusartSmoothing.secondPsiPrimitive N y:ℂ)) x δ =
      ((average m Chebyshev.psi x δ:ℝ):ℂ) := by
  have h := congrArg (fun y : ℝ => (y:ℂ)) (average_psi_eq_second_primitive m N hm x δ hx hd hN)
  push_cast at h
  rw [←intervalIntegral.integral_ofReal] at h
  push_cast at h
  simpa only [twiceWeightedRemainder,Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_one] using h.symm
 theorem twiceWeighted_quadratic_term (m : ℕ) (hm : 2 ≤ m) (x δ : ℝ)
    (hx : 0 < x) (hd : 0 < δ) :
    twiceWeightedRemainder m (fun y : ℝ => (y:ℂ)^2/2) x δ=1 := by
  have h := congrArg (fun y : ℝ => (y:ℂ)) (second_primitive_quadratic_term m hm x δ hx hd)
  push_cast at h
  rw [←intervalIntegral.integral_ofReal] at h
  push_cast at h
  simpa only [twiceWeightedRemainder,Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_one] using h
 theorem twiceWeighted_cubic_term (m : ℕ) (hm : 2 ≤ m) (x δ : ℝ)
    (hx : 0 < x) (hd : 0 < δ) :
    twiceWeightedRemainder m (fun y : ℝ => (y:ℂ)^3/6) x δ=((x*(1+δ/2):ℝ):ℂ) := by
  have h := congrArg (fun y : ℝ => (y:ℂ)) (second_primitive_cubic_term m hm x δ hx hd)
  push_cast at h
  rw [←intervalIntegral.integral_ofReal] at h
  push_cast at h
  simpa only [twiceWeightedRemainder,Complex.ofReal_mul,Complex.ofReal_add,
    Complex.ofReal_one,Complex.ofReal_div,Complex.ofReal_ofNat] using h
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.twiceWeighted_secondPsiPrimitive
#print axioms DusartLegendreSmoothing.twiceWeighted_cubic_term


