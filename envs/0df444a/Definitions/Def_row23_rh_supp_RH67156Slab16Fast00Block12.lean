-- Prove2me | Definitions.Def_row23_rh_supp_RH67156Slab16Fast00Block12
-- name    : row23_rh_supp_RH67156Slab16Fast00Block12
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-21T21:51:43.220041+00:00
-- url     : https://prove2.me/theorems/0fb0fcda-9025-42f7-aaec-60108a47ab88
-- title:
--   Row 23 RH support: RH67156Slab16Fast00Block12
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH67156Slab16Fast00Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open ArbEcon ArbEcon.Off
namespace RH67156Slab16Fast00
theorem transition12 : runO cfg oc 1 state39 = state40 := by
  decide +kernel
end RH67156Slab16Fast00
#print axioms RH67156Slab16Fast00.transition12


