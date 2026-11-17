-- Prove2me | Definitions.Def_row23_rh_supp_RHLowSlabFifteenthCell14
-- name    : row23_rh_supp_RHLowSlabFifteenthCell14
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-16T06:33:04.978483+00:00
-- url     : https://prove2.me/theorems/84723e1e-a3d3-4864-8454-62b2fff05534
-- title:
--   Row 23 RH support: RHLowSlabFifteenthCell14
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLowSlabFifteenthPilot
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 20000
noncomputable section
namespace RHLowSlabFifteenthPilot
theorem cell14_checked : Arb4.cellOK slab 14 = true := by
  decide +kernel
end RHLowSlabFifteenthPilot
#print axioms RHLowSlabFifteenthPilot.cell14_checked


