-- Prove2me | Definitions.Def_row23_rh_supp_RHLowSlabTenthCell05
-- name    : row23_rh_supp_RHLowSlabTenthCell05
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T20:44:00.702865+00:00
-- url     : https://prove2.me/theorems/eb84e70a-4f9c-4bd2-abc4-eeb7f8560293
-- title:
--   Row 23 RH support: RHLowSlabTenthCell05
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLowSlabTenthPilot
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 20000
noncomputable section
namespace RHLowSlabTenthPilot
theorem cell05_checked : Arb4.cellOK slab 5 = true := by
  decide +kernel
end RHLowSlabTenthPilot
#print axioms RHLowSlabTenthPilot.cell05_checked


