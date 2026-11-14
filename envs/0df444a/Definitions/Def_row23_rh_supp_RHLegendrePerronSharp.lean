-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendrePerronSharp
-- name    : row23_rh_supp_RHLegendrePerronSharp
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:21:32.206198+00:00
-- url     : https://prove2.me/theorems/0340062a-ac29-4bf3-8ba4-1eb7c30c69a6
-- title:
--   Row 23 RH support: RHLegendrePerronSharp
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendrePerronSwap
import Definitions.Def_row23_rh_supp_RHLegendreLeftIntegral
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace DusartLegendreSmoothing
open Complex MeasureTheory
 theorem norm_legendrePerronRemainder_sharp (m : ℕ) (hm : 2 ≤ m) (x δ : ℝ)
    (hx : 0 < x) (hd : 0 < δ) (hd1 : δ ≤ 1) :
    ‖legendrePerronRemainder m x δ‖ ≤
      (4096/Real.pi+32*(m:ℝ)/δ)*x^(-1/2:ℝ) := by
  have hm0 : 0 < m := by omega
  have hxp : 0 ≤ x^(-1/2:ℝ) := Real.rpow_nonneg hx.le _
  have hpoint (v : ℝ) :
      ‖-((x:ℂ)^(-(1/2:ℂ)+v*I))*zeroKernel m (-(1/2:ℂ)+v*I) δ *
        logDeriv riemannZeta (-(1/2:ℂ)+v*I)‖ ≤
        x^(-1/2:ℝ)*leftKernelMajorant m δ v := by
    rw [mul_assoc,norm_mul,norm_neg,Complex.norm_cpow_eq_rpow_re_of_pos hx]
    have he : (-(1/2:ℂ)+v*I).re=(-1/2:ℝ) := by norm_num
    rw [he]
    exact mul_le_mul_of_nonneg_left (norm_left_kernel_logDeriv m hm δ v hd hd1) hxp
  have hi := norm_integral_le_of_norm_le
    ((leftKernelMajorant_integrable m hm0 δ hd).const_mul (x^(-1/2:ℝ)))
    (Filter.Eventually.of_forall hpoint)
  rw [integral_const_mul,integral_leftKernelMajorant m hm0 δ hd] at hi
  have hc : ‖(1/(2*Real.pi):ℂ)‖=1/(2*Real.pi) := by
    norm_num [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  rw [legendrePerronRemainder_vertical m hm x δ hx hd,norm_mul,hc]
  calc
    _ ≤ (1/(2*Real.pi))*(x^(-1/2:ℝ)*(8192+64*(m:ℝ)*Real.pi/δ)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by field_simp [Real.pi_ne_zero,hd.ne']; ring
 theorem norm_legendrePerronRemainder_sharp_relative (m : ℕ) (hm : 2 ≤ m) (x δ : ℝ)
    (hx : 0 < x) (hd : 0 < δ) (hd1 : δ ≤ 1) :
    ‖legendrePerronRemainder m x δ‖/x ≤
      (4096/Real.pi+32*(m:ℝ)/δ)*x^(-3/2:ℝ) := by
  have h := div_le_div_of_nonneg_right (norm_legendrePerronRemainder_sharp m hm x δ hx hd hd1) hx.le
  have hp : x^(-1/2:ℝ)/x=x^(-3/2:ℝ) := by
    have hh := Real.rpow_sub hx (-1/2:ℝ) (1:ℝ)
    norm_num only [Real.rpow_one] at hh
    convert hh.symm using 1 <;> norm_num
  exact h.trans_eq (by rw [mul_div_assoc,hp])
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.norm_legendrePerronRemainder_sharp


