-- Prove2me | Definitions.Def_row23_rh_supp_RH67156Slab16Fast15Block03
-- name    : row23_rh_supp_RH67156Slab16Fast15Block03
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-21T22:25:40.871789+00:00
-- url     : https://prove2.me/theorems/8ae0ed56-5f43-4510-8e46-93a4fa5c3545
-- title:
--   Row 23 RH support: RH67156Slab16Fast15Block03
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH67156Slab16Fast15Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open ArbEcon ArbEcon.Off
namespace RH67156Slab16Fast15
theorem transition03 : runO cfg oc 2000 state08 = state12 := by
  decide +kernel
end RH67156Slab16Fast15
#print axioms RH67156Slab16Fast15.transition03


