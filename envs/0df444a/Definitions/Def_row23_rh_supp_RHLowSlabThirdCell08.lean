-- Prove2me | Definitions.Def_row23_rh_supp_RHLowSlabThirdCell08
-- name    : row23_rh_supp_RHLowSlabThirdCell08
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T20:14:20.142542+00:00
-- url     : https://prove2.me/theorems/c5db323a-28b0-4a1a-a248-6375edc7316e
-- title:
--   Row 23 RH support: RHLowSlabThirdCell08
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLowSlabThirdPilot
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 20000
noncomputable section
namespace RHLowSlabThirdPilot
theorem cell08_checked : Arb4.cellOK slab 8 = true := by
  decide +kernel
end RHLowSlabThirdPilot
#print axioms RHLowSlabThirdPilot.cell08_checked


