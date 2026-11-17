-- Prove2me | Definitions.Def_row23_rh_supp_RHLowSlabSixteenthCell05
-- name    : row23_rh_supp_RHLowSlabSixteenthCell05
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-16T06:35:34.984207+00:00
-- url     : https://prove2.me/theorems/27945f6a-907e-4bb1-a636-4b2d9d87928b
-- title:
--   Row 23 RH support: RHLowSlabSixteenthCell05
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLowSlabSixteenthPilot
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 20000
noncomputable section
namespace RHLowSlabSixteenthPilot
theorem cell05_checked : Arb4.cellOK slab 5 = true := by
  decide +kernel
end RHLowSlabSixteenthPilot
#print axioms RHLowSlabSixteenthPilot.cell05_checked


