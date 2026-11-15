-- Prove2me | Definitions.Def_row23_rh_supp_RHLowSlabWideCell08
-- name    : row23_rh_supp_RHLowSlabWideCell08
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T19:57:13.61469+00:00
-- url     : https://prove2.me/theorems/4b816978-3e30-4184-8605-0d5c36cb3206
-- title:
--   Row 23 RH support: RHLowSlabWideCell08
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLowSlabWideAboveTwoPiPilot
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 20000
noncomputable section
namespace RHLowSlabWideAboveTwoPiPilot
theorem cell08_checked : Arb4.cellOK slab 8 = true := by
  decide +kernel
end RHLowSlabWideAboveTwoPiPilot
#print axioms RHLowSlabWideAboveTwoPiPilot.cell08_checked


