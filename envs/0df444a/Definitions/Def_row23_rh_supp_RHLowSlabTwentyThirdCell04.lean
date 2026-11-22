-- Prove2me | Definitions.Def_row23_rh_supp_RHLowSlabTwentyThirdCell04
-- name    : row23_rh_supp_RHLowSlabTwentyThirdCell04
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-21T20:29:29.917137+00:00
-- url     : https://prove2.me/theorems/bc8f5d80-ccfa-4c0d-ba0b-2bc985ce5467
-- title:
--   Row 23 RH support: RHLowSlabTwentyThirdCell04
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLowSlabTwentyThirdPilot
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 20000
noncomputable section
namespace RHLowSlabTwentyThirdPilot
theorem cell04_checked : Arb4.cellOK slab 4 = true := by
  decide +kernel
end RHLowSlabTwentyThirdPilot
#print axioms RHLowSlabTwentyThirdPilot.cell04_checked


