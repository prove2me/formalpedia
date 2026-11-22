-- Prove2me | Definitions.Def_row23_rh_supp_RHLowSlabEighteenthCell15
-- name    : row23_rh_supp_RHLowSlabEighteenthCell15
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-21T20:13:09.095416+00:00
-- url     : https://prove2.me/theorems/88b7baa7-33df-4ea6-8c48-83770e173bfb
-- title:
--   Row 23 RH support: RHLowSlabEighteenthCell15
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLowSlabEighteenthPilot
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 20000
noncomputable section
namespace RHLowSlabEighteenthPilot
theorem cell15_checked : Arb4.cellOK slab 15 = true := by
  decide +kernel
end RHLowSlabEighteenthPilot
#print axioms RHLowSlabEighteenthPilot.cell15_checked


