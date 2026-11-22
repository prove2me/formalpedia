-- Prove2me | Definitions.Def_row23_rh_supp_RH67156Slab16Fast11Block12
-- name    : row23_rh_supp_RH67156Slab16Fast11Block12
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-21T22:18:47.708016+00:00
-- url     : https://prove2.me/theorems/e118bdac-5c93-4dbd-a02f-24b50b967553
-- title:
--   Row 23 RH support: RH67156Slab16Fast11Block12
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH67156Slab16Fast11Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open ArbEcon ArbEcon.Off
namespace RH67156Slab16Fast11
theorem transition12 : runO cfg oc 1 state39 = state40 := by
  decide +kernel
end RH67156Slab16Fast11
#print axioms RH67156Slab16Fast11.transition12


