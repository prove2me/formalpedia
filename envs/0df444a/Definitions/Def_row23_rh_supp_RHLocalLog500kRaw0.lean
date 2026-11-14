-- Prove2me | Definitions.Def_row23_rh_supp_RHLocalLog500kRaw0
-- name    : row23_rh_supp_RHLocalLog500kRaw0
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:17:23.359199+00:00
-- url     : https://prove2.me/theorems/9b2213d5-bbeb-4cda-aff2-0b89f7dbdf8e
-- title:
--   Row 23 RH support: RHLocalLog500kRaw0
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
theorem log1000 : ((6907/1000:ℚ):ℝ) ≤ Real.log ((1000:ℚ):ℝ) ∧
    Real.log ((1000:ℚ):ℝ) ≤ ((6909/1000:ℚ):ℝ) := by
  exact verified_bounds 1000 9 (6907/1000) (6909/1000) (by unfold certificate; decide +kernel)
theorem log1005 : ((69/10:ℚ):ℝ) ≤ Real.log ((1005:ℚ):ℝ) ∧
    Real.log ((1005:ℚ):ℝ) ≤ ((7:ℚ):ℝ) := by
  exact verified_bounds 1005 9 (69/10) (7) (by unfold certificate; decide +kernel)
end RHLocalLog500k
#print axioms RHLocalLog500k.log1000
#print axioms RHLocalLog500k.log1005


