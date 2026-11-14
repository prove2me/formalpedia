-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendreLogCertificates_Batch01
-- name    : row23_rh_supp_RHLegendreLogCertificates_Batch01
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:17:08.63891+00:00
-- url     : https://prove2.me/theorems/1f0806ae-44eb-4f8c-878e-a89dc820d4e3
-- title:
--   Row 23 RH support: RHLegendreLogCertificates.Batch01
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreRationalLogCertificate
set_option autoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
namespace DusartLegendreSmoothing.RationalLog
theorem log_pi2_lower : (((1837877066409345483/1000000000000000000):ℚ):ℝ) ≤ Real.log (((157079632679489661923/25000000000000000000):ℚ):ℝ) ∧
    Real.log (((157079632679489661923/25000000000000000000):ℚ):ℝ) ≤ (((459469266602336371/250000000000000000):ℚ):ℝ) := by
  exact verified_bounds (157079632679489661923/25000000000000000000) 2 (1837877066409345483/1000000000000000000) (459469266602336371/250000000000000000) (by unfold certificate; decide +kernel)
#print axioms DusartLegendreSmoothing.RationalLog.log_pi2_lower
theorem log_pi2_upper : (((1837877066409345483/1000000000000000000):ℚ):ℝ) ≤ Real.log (((314159265358979323847/50000000000000000000):ℚ):ℝ) ∧
    Real.log (((314159265358979323847/50000000000000000000):ℚ):ℝ) ≤ (((459469266602336371/250000000000000000):ℚ):ℝ) := by
  exact verified_bounds (314159265358979323847/50000000000000000000) 2 (1837877066409345483/1000000000000000000) (459469266602336371/250000000000000000) (by unfold certificate; decide +kernel)
#print axioms DusartLegendreSmoothing.RationalLog.log_pi2_upper
theorem log_T0 : (((2787986034678742937/200000000000000000):ℚ):ℝ) ≤ Real.log (((566245491/500):ℚ):ℝ) ∧
    Real.log (((566245491/500):ℚ):ℝ) ≤ (((6969965086696857343/500000000000000000):ℚ):ℝ) := by
  exact verified_bounds (566245491/500) 20 (2787986034678742937/200000000000000000) (6969965086696857343/500000000000000000) (by unfold certificate; decide +kernel)
#print axioms DusartLegendreSmoothing.RationalLog.log_T0
theorem log_T0_plus5 : (((13939934588430162557/1000000000000000000):ℚ):ℝ) ≤ Real.log (((566247991/500):ℚ):ℝ) ∧
    Real.log (((566247991/500):ℚ):ℝ) ≤ (((6969967294215081279/500000000000000000):ℚ):ℝ) := by
  exact verified_bounds (566247991/500) 20 (13939934588430162557/1000000000000000000) (6969967294215081279/500000000000000000) (by unfold certificate; decide +kernel)
#print axioms DusartLegendreSmoothing.RationalLog.log_T0_plus5
end DusartLegendreSmoothing.RationalLog


