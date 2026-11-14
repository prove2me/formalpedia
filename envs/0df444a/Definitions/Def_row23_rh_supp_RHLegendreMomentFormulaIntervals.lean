-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendreMomentFormulaIntervals
-- name    : row23_rh_supp_RHLegendreMomentFormulaIntervals
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:15:25.507734+00:00
-- url     : https://prove2.me/theorems/d94c1619-4212-45ad-80db-86231502ed66
-- title:
--   Row 23 RH support: RHLegendreMomentFormulaIntervals
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreMomentIntervals
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace DusartLegendreSmoothing
 theorem moment_band_interval (k : ℕ) (a b PL PU La Ua Lb Ub Va : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hPL : 0 < PL) (hPlo : PL ≤ Real.pi) (hPhi : Real.pi ≤ PU)
    (hLa : 0 < La) (haL : La ≤ Real.log (a/(2*Real.pi))) (haU : Real.log (a/(2*Real.pi)) ≤ Ua)
    (hLb : 0 < Lb) (hbL : Lb ≤ Real.log (b/(2*Real.pi))) (hbU : Real.log (b/(2*Real.pi)) ≤ Ub)
    (hV : Real.log (a+5) ≤ Va) :
    positiveMomentBandBound k a b ≤ 2*(9*Va+79)/a^(k+2)+
      (1/(2*PL)+9/(a*La))*((1+((k:ℝ)+1)*Ua)/(((k:ℝ)+1)^2*a^(k+1)))-
      (1/(2*PU)+9/(a*Ua))*((1+((k:ℝ)+1)*Lb)/(((k:ℝ)+1)^2*b^(k+1))) := by
  have hPU : 0 < PU := Real.pi_pos.trans_le hPhi
  have hUa : 0 < Ua := hLa.trans_le (haL.trans haU)
  have hC := zeroCountSlope_interval a PL PU La Ua ha hPL hPlo hPhi hLa haL haU
  have hPA := positiveMomentPrimitive_interval k a La Ua ha haL haU
  have hPB := positiveMomentPrimitive_interval k b Lb Ub hb hbL hbU
  have hCL0 : 0 ≤ 1/(2*PU)+9/(a*Ua) := by positivity
  have hCU0 : 0 ≤ 1/(2*PL)+9/(a*La) := by positivity
  have hPAlo : 0 ≤ (1+((k:ℝ)+1)*La)/(((k:ℝ)+1)^2*a^(k+1)) := by positivity
  have hPBlo : 0 ≤ (1+((k:ℝ)+1)*Lb)/(((k:ℝ)+1)^2*b^(k+1)) := by positivity
  have hE : 2*(9*Real.log (a+5)+79)/a^(k+2) ≤ 2*(9*Va+79)/a^(k+2) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith only [hV]
  have hU := mul_le_mul hC.2 hPA.2 (hPAlo.trans hPA.1) hCU0
  have hL := mul_le_mul hC.1 hPB.1 hPBlo (hCL0.trans hC.1)
  unfold positiveMomentBandBound
  nlinarith only [hE,hU,hL]
 theorem moment_tail_interval (k : ℕ) (a PL PU L U V : ℝ)
    (ha : 0 < a) (hPL : 0 < PL) (hPlo : PL ≤ Real.pi) (hPhi : Real.pi ≤ PU)
    (hL : 0 < L) (hLo : L ≤ Real.log (a/(2*Real.pi))) (hHi : Real.log (a/(2*Real.pi)) ≤ U)
    (hV : Real.log (a+5) ≤ V) :
    positiveMomentTailBound k a ≤ 2*(9*V+79)/a^(k+2)+
      (1/(2*PL)+9/(a*L))*((1+((k:ℝ)+1)*U)/(((k:ℝ)+1)^2*a^(k+1))) := by
  have hC := zeroCountSlope_interval a PL PU L U ha hPL hPlo hPhi hL hLo hHi
  have hP := positiveMomentPrimitive_interval k a L U ha hLo hHi
  have hPlo : 0 ≤ (1+((k:ℝ)+1)*L)/(((k:ℝ)+1)^2*a^(k+1)) := by positivity
  have hCu : 0 ≤ 1/(2*PL)+9/(a*L) := by positivity
  have hE : 2*(9*Real.log (a+5)+79)/a^(k+2) ≤ 2*(9*V+79)/a^(k+2) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith only [hV]
  have hU := mul_le_mul hC.2 hP.2 (hPlo.trans hP.1) hCu
  unfold positiveMomentTailBound
  linarith only [hE,hU]
 theorem low_moment_interval (a b S PL PU La Ua Lb Ub Va : ℝ)
    (ha : 0 < a) (hPL : 0 < PL) (hPlo : PL ≤ Real.pi) (hPhi : Real.pi ≤ PU)
    (hLa : 0 < La) (haL : La ≤ Real.log (a/(2*Real.pi))) (haU : Real.log (a/(2*Real.pi)) ≤ Ua)
    (hLb : 0 < Lb) (hbL : Lb ≤ Real.log (b/(2*Real.pi))) (hbU : Real.log (b/(2*Real.pi)) ≤ Ub)
    (hV : Real.log (a+5) ≤ Va) :
    positiveLowMomentBound a b S ≤ S+2*(9*Va+79)/a+
      ((1/(2*PL)+9/(a*La))*Ub^2-(1/(2*PU)+9/(a*Ua))*La^2)/2 := by
  have hPU : 0 < PU := Real.pi_pos.trans_le hPhi
  have hUa : 0 < Ua := hLa.trans_le (haL.trans haU)
  have hC := zeroCountSlope_interval a PL PU La Ua ha hPL hPlo hPhi hLa haL haU
  have hCL0 : 0 ≤ 1/(2*PU)+9/(a*Ua) := by positivity
  have hCU0 : 0 ≤ 1/(2*PL)+9/(a*La) := by positivity
  have hsB := pow_le_pow_left₀ (hLb.trans_le hbL).le hbU 2
  have hsA := pow_le_pow_left₀ hLa.le haL 2
  have hU := mul_le_mul hC.2 hsB (sq_nonneg _) hCU0
  have hL := mul_le_mul hC.1 hsA (sq_nonneg _) (hCL0.trans hC.1)
  have hE : 2*(9*Real.log (a+5)+79)/a ≤ 2*(9*Va+79)/a := by
    apply div_le_div_of_nonneg_right _ ha.le
    linarith only [hV]
  unfold positiveLowMomentBound
  nlinarith only [hE,hU,hL]
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.moment_band_interval
#print axioms DusartLegendreSmoothing.moment_tail_interval
#print axioms DusartLegendreSmoothing.low_moment_interval


