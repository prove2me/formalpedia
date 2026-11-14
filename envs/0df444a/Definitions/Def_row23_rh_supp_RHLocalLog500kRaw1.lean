-- Prove2me | Definitions.Def_row23_rh_supp_RHLocalLog500kRaw1
-- name    : row23_rh_supp_RHLocalLog500kRaw1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:17:54.420297+00:00
-- url     : https://prove2.me/theorems/a31003b7-a6b5-49f2-ab1e-8efcaff73c3e
-- title:
--   Row 23 RH support: RHLocalLog500kRaw1
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreRationalLogCertificate
set_option autoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
namespace RHLocalLog500k
open DusartLegendreSmoothing.RationalLog
theorem log107500 : ((1158/100:ℚ):ℝ) ≤ Real.log ((107500:ℚ):ℝ) ∧
    Real.log ((107500:ℚ):ℝ) ≤ ((1159/100:ℚ):ℝ) := by
  exact verified_bounds 107500 16 (1158/100) (1159/100) (by unfold certificate; decide +kernel)
theorem log107505 : ((1158/100:ℚ):ℝ) ≤ Real.log ((107505:ℚ):ℝ) ∧
    Real.log ((107505:ℚ):ℝ) ≤ ((116/10:ℚ):ℝ) := by
  exact verified_bounds 107505 16 (1158/100) (116/10) (by unfold certificate; decide +kernel)
end RHLocalLog500k
#print axioms RHLocalLog500k.log107500
#print axioms RHLocalLog500k.log107505


