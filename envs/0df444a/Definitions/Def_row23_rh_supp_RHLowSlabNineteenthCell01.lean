-- Prove2me | Definitions.Def_row23_rh_supp_RHLowSlabNineteenthCell01
-- name    : row23_rh_supp_RHLowSlabNineteenthCell01
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-21T20:13:49.137796+00:00
-- url     : https://prove2.me/theorems/19a6203e-975e-4d50-9109-18536967f41e
-- title:
--   Row 23 RH support: RHLowSlabNineteenthCell01
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLowSlabNineteenthPilot
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 20000
noncomputable section
namespace RHLowSlabNineteenthPilot
theorem cell01_checked : Arb4.cellOK slab 1 = true := by
  decide +kernel
end RHLowSlabNineteenthPilot
#print axioms RHLowSlabNineteenthPilot.cell01_checked


