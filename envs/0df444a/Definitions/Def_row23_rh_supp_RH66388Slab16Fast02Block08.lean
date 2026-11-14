-- Prove2me | Definitions.Def_row23_rh_supp_RH66388Slab16Fast02Block08
-- name    : row23_rh_supp_RH66388Slab16Fast02Block08
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:41:09.645927+00:00
-- url     : https://prove2.me/theorems/f2463b9c-81e3-4d08-b435-ccedc406b7d9
-- title:
--   Row 23 RH support: RH66388Slab16Fast02Block08
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH66388Slab16Fast02Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open ArbEcon ArbEcon.Off
namespace RH66388Slab16Fast02
theorem transition08 : runO cfg oc 2000 state28 = state32 := by
  decide +kernel
end RH66388Slab16Fast02
#print axioms RH66388Slab16Fast02.transition08


