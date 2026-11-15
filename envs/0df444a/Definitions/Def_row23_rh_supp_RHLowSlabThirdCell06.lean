-- Prove2me | Definitions.Def_row23_rh_supp_RHLowSlabThirdCell06
-- name    : row23_rh_supp_RHLowSlabThirdCell06
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T20:13:33.293934+00:00
-- url     : https://prove2.me/theorems/7a19fe5e-5596-4940-a7c1-ca93b893708c
-- title:
--   Row 23 RH support: RHLowSlabThirdCell06
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
theorem cell06_checked : Arb4.cellOK slab 6 = true := by
  decide +kernel
end RHLowSlabThirdPilot
#print axioms RHLowSlabThirdPilot.cell06_checked


