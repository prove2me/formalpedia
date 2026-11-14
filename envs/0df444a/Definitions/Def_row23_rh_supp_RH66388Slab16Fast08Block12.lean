-- Prove2me | Definitions.Def_row23_rh_supp_RH66388Slab16Fast08Block12
-- name    : row23_rh_supp_RH66388Slab16Fast08Block12
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:45:18.442212+00:00
-- url     : https://prove2.me/theorems/b53962d4-b628-4774-8ddc-e6e439d848b9
-- title:
--   Row 23 RH support: RH66388Slab16Fast08Block12
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH66388Slab16Fast08Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open ArbEcon ArbEcon.Off
namespace RH66388Slab16Fast08
theorem transition12 : runO cfg oc 1 state39 = state40 := by
  decide +kernel
end RH66388Slab16Fast08
#print axioms RH66388Slab16Fast08.transition12


