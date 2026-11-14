-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendreMomentIntervals
-- name    : row23_rh_supp_RHLegendreMomentIntervals
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:12:26.974384+00:00
-- url     : https://prove2.me/theorems/f116c507-2f99-4646-ba0d-4adfd21c71e3
-- title:
--   Row 23 RH support: RHLegendreMomentIntervals
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreActualLowMoment
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace DusartLegendreSmoothing
 theorem zeroCountSlope_interval (a PL PU L U : ℝ)
    (ha : 0 < a) (hPL : 0 < PL) (hPlo : PL ≤ Real.pi) (hPhi : Real.pi ≤ PU)
    (hL : 0 < L) (hlogLo : L ≤ Real.log (a/(2*Real.pi)))
    (hlogHi : Real.log (a/(2*Real.pi)) ≤ U) :
    1/(2*PU)+9/(a*U) ≤ zeroCountSlope a ∧
      zeroCountSlope a ≤ 1/(2*PL)+9/(a*L) := by
  have hlog : 0 < Real.log (a/(2*Real.pi)) := hL.trans_le hlogLo
  have hπ0 : 0 < Real.pi := Real.pi_pos
  have h1 : (1:ℝ)/(2*PU) ≤ 1/(2*Real.pi) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  have h2 : (9:ℝ)/(a*U) ≤ 9/(a*Real.log (a/(2*Real.pi))) :=
    div_le_div_of_nonneg_left (by norm_num) (mul_pos ha hlog)
      (mul_le_mul_of_nonneg_left hlogHi ha.le)
  have h3 : (1:ℝ)/(2*Real.pi) ≤ 1/(2*PL) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  have h4 : (9:ℝ)/(a*Real.log (a/(2*Real.pi))) ≤ 9/(a*L) :=
    div_le_div_of_nonneg_left (by norm_num) (mul_pos ha hL)
      (mul_le_mul_of_nonneg_left hlogLo ha.le)
  exact ⟨add_le_add h1 h2,add_le_add h3 h4⟩
 theorem positiveMomentPrimitive_interval (k : ℕ) (a L U : ℝ) (ha : 0 < a)
    (hLo : L ≤ Real.log (a/(2*Real.pi))) (hHi : Real.log (a/(2*Real.pi)) ≤ U) :
    (1+((k:ℝ)+1)*L)/(((k:ℝ)+1)^2*a^(k+1)) ≤ positiveMomentPrimitive k a ∧
      positiveMomentPrimitive k a ≤ (1+((k:ℝ)+1)*U)/(((k:ℝ)+1)^2*a^(k+1)) := by
  have hden : 0 ≤ ((k:ℝ)+1)^2*a^(k+1) := by positivity
  constructor
  · unfold positiveMomentPrimitive
    apply div_le_div_of_nonneg_right _ hden
    gcongr
  · unfold positiveMomentPrimitive
    apply div_le_div_of_nonneg_right _ hden
    gcongr
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.zeroCountSlope_interval
#print axioms DusartLegendreSmoothing.positiveMomentPrimitive_interval


