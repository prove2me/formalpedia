-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendreLogCertificates_Batch02
-- name    : row23_rh_supp_RHLegendreLogCertificates_Batch02
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:17:09.093198+00:00
-- url     : https://prove2.me/theorems/51a57ff8-b457-475a-ae08-37127b606aab
-- title:
--   Row 23 RH support: RHLegendreLogCertificates.Batch02
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
theorem log_H : (((14262737485842463451/500000000000000000):ℚ):ℝ) ≤ Real.log (((2445999556030):ℚ):ℝ) ∧
    Real.log (((2445999556030):ℚ):ℝ) ≤ (((28525474971684926903/1000000000000000000):ℚ):ℝ) := by
  exact verified_bounds (2445999556030) 41 (14262737485842463451/500000000000000000) (28525474971684926903/1000000000000000000) (by unfold certificate; decide +kernel)
#print axioms DusartLegendreSmoothing.RationalLog.log_H
theorem log_H_plus5 : (((1782842185730435691/62500000000000000):ℚ):ℝ) ≤ Real.log (((2445999556035):ℚ):ℝ) ∧
    Real.log (((2445999556035):ℚ):ℝ) ≤ (((28525474971686971057/1000000000000000000):ℚ):ℝ) := by
  exact verified_bounds (2445999556035) 41 (1782842185730435691/62500000000000000) (28525474971686971057/1000000000000000000) (by unfold certificate; decide +kernel)
#print axioms DusartLegendreSmoothing.RationalLog.log_H_plus5
theorem log_T_1132492 : (((13939931072296715803/1000000000000000000):ℚ):ℝ) ≤ Real.log (((1132492):ℚ):ℝ) ∧
    Real.log (((1132492):ℚ):ℝ) ≤ (((3484982768074178951/250000000000000000):ℚ):ℝ) := by
  exact verified_bounds (1132492) 20 (13939931072296715803/1000000000000000000) (3484982768074178951/250000000000000000) (by unfold certificate; decide +kernel)
#print axioms DusartLegendreSmoothing.RationalLog.log_T_1132492
theorem log_T_1132492_plus5 : (((3484983871832298749/250000000000000000):ℚ):ℝ) ≤ Real.log (((1132497):ℚ):ℝ) ∧
    Real.log (((1132497):ℚ):ℝ) ≤ (((13939935487329194997/1000000000000000000):ℚ):ℝ) := by
  exact verified_bounds (1132497) 20 (3484983871832298749/250000000000000000) (13939935487329194997/1000000000000000000) (by unfold certificate; decide +kernel)
#print axioms DusartLegendreSmoothing.RationalLog.log_T_1132492_plus5
end DusartLegendreSmoothing.RationalLog


