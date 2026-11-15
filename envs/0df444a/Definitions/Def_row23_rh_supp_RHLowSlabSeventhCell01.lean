-- Prove2me | Definitions.Def_row23_rh_supp_RHLowSlabSeventhCell01
-- name    : row23_rh_supp_RHLowSlabSeventhCell01
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T20:32:12.623209+00:00
-- url     : https://prove2.me/theorems/04c15d99-07e1-40be-a059-4a2973d97a89
-- title:
--   Row 23 RH support: RHLowSlabSeventhCell01
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLowSlabSeventhPilot
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 20000
noncomputable section
namespace RHLowSlabSeventhPilot
theorem cell01_checked : Arb4.cellOK slab 1 = true := by
  decide +kernel
end RHLowSlabSeventhPilot
#print axioms RHLowSlabSeventhPilot.cell01_checked


