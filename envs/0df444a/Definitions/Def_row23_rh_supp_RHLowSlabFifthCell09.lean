-- Prove2me | Definitions.Def_row23_rh_supp_RHLowSlabFifthCell09
-- name    : row23_rh_supp_RHLowSlabFifthCell09
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T20:27:28.217084+00:00
-- url     : https://prove2.me/theorems/38137a0f-79ae-4ada-85b2-e704180cb86f
-- title:
--   Row 23 RH support: RHLowSlabFifthCell09
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLowSlabFifthPilot
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 20000
noncomputable section
namespace RHLowSlabFifthPilot
theorem cell09_checked : Arb4.cellOK slab 9 = true := by
  decide +kernel
end RHLowSlabFifthPilot
#print axioms RHLowSlabFifthPilot.cell09_checked


