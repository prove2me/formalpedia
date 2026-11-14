-- Prove2me | Definitions.Def_row23_rh_supp_RHLocalLog380kRaw
-- name    : row23_rh_supp_RHLocalLog380kRaw
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:17:43.015459+00:00
-- url     : https://prove2.me/theorems/a04932db-cae5-4245-bd59-ee6982bd76d5
-- title:
--   Row 23 RH support: RHLocalLog380kRaw
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreRationalLogCertificate
set_option autoImplicit false
set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
namespace RHLocalLog380k
open DusartLegendreSmoothing.RationalLog
theorem log92500 : ((114348/10000:ℚ):ℝ) ≤ Real.log ((92500:ℚ):ℝ) ∧
    Real.log ((92500:ℚ):ℝ) ≤ ((114352/10000:ℚ):ℝ) := by
  exact verified_bounds 92500 16 (114348/10000) (114352/10000) (by unfold certificate; decide +kernel)
theorem log92505 : ((114348/10000:ℚ):ℝ) ≤ Real.log ((92505:ℚ):ℝ) ∧
    Real.log ((92505:ℚ):ℝ) ≤ ((114352/10000:ℚ):ℝ) := by
  exact verified_bounds 92505 16 (114348/10000) (114352/10000) (by unfold certificate; decide +kernel)
theorem log380000 : ((128478/10000:ℚ):ℝ) ≤ Real.log ((380000:ℚ):ℝ) ∧
    Real.log ((380000:ℚ):ℝ) ≤ ((128481/10000:ℚ):ℝ) := by
  exact verified_bounds 380000 16 (128478/10000) (128481/10000) (by unfold certificate; decide +kernel)
theorem log380005 : ((128478/10000:ℚ):ℝ) ≤ Real.log ((380005:ℚ):ℝ) ∧
    Real.log ((380005:ℚ):ℝ) ≤ ((128481/10000:ℚ):ℝ) := by
  exact verified_bounds 380005 16 (128478/10000) (128481/10000) (by unfold certificate; decide +kernel)
end RHLocalLog380k
#print axioms RHLocalLog380k.log92500
#print axioms RHLocalLog380k.log92505
#print axioms RHLocalLog380k.log380000
#print axioms RHLocalLog380k.log380005


