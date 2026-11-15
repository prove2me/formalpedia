-- Prove2me | Definitions.Def_row23_rh_supp_RHLowSlabSixthCell11
-- name    : row23_rh_supp_RHLowSlabSixthCell11
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T20:30:42.464355+00:00
-- url     : https://prove2.me/theorems/1792fb84-2531-47b4-989d-79cfc01074bc
-- title:
--   Row 23 RH support: RHLowSlabSixthCell11
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLowSlabSixthPilot
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 20000
noncomputable section
namespace RHLowSlabSixthPilot
theorem cell11_checked : Arb4.cellOK slab 11 = true := by
  decide +kernel
end RHLowSlabSixthPilot
#print axioms RHLowSlabSixthPilot.cell11_checked


