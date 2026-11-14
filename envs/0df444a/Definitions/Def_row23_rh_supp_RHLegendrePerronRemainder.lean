-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendrePerronRemainder
-- name    : row23_rh_supp_RHLegendrePerronRemainder
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:12:33.238215+00:00
-- url     : https://prove2.me/theorems/f5f24bab-e045-40b6-b5f3-95865a31d47f
-- title:
--   Row 23 RH support: RHLegendrePerronRemainder
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreSecondRemainder
import Definitions.Def_dusart_psi_433_20261014_ExplicitFormula
set_option autoImplicit false
namespace DusartLegendreSmoothing
noncomputable def legendrePerronRemainder (m : ℕ) (x δ : ℝ) : ℂ :=
  twiceWeightedRemainder m DusartSmoothing.perronLeftRemainder x δ
 theorem norm_legendrePerronRemainder (m : ℕ) (x δ : ℝ)
    (hm : 2 ≤ m) (hx : 0 < x) (hd : 0 < δ) :
    ‖legendrePerronRemainder m x δ‖ ≤
      (128*(8*(m:ℝ)*(2*m+1))*(1+δ)^(3/2:ℝ)/δ^2)*x^(-1/2:ℝ) := by
  exact norm_twiceWeightedRemainder m DusartSmoothing.perronLeftRemainder x δ 128 hm hx hd
    (by norm_num) DusartSmoothing.norm_perronLeftRemainder
 theorem norm_legendrePerronRemainder_relative (m : ℕ) (x δ : ℝ)
    (hm : 2 ≤ m) (hx : 0 < x) (hd : 0 < δ) :
    ‖legendrePerronRemainder m x δ‖/x ≤
      (128*(8*(m:ℝ)*(2*m+1))*(1+δ)^(3/2:ℝ)/δ^2)*x^(-3/2:ℝ) := by
  have h := div_le_div_of_nonneg_right (norm_legendrePerronRemainder m x δ hm hx hd) hx.le
  have hp : x^(-1/2:ℝ)/x=x^(-3/2:ℝ) := by
    have h := Real.rpow_sub hx (-1/2:ℝ) (1:ℝ)
    norm_num only [Real.rpow_one] at h
    convert h.symm using 1 <;> norm_num
  exact h.trans_eq (by rw [mul_div_assoc,hp])
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.norm_legendrePerronRemainder
#print axioms DusartLegendreSmoothing.norm_legendrePerronRemainder_relative


