-- Prove2me | Definitions.Def_row23_rh_supp_RH67156Slab16Fast15Block09
-- name    : row23_rh_supp_RH67156Slab16Fast15Block09
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-21T22:26:04.086108+00:00
-- url     : https://prove2.me/theorems/1e9e70e8-c222-497a-b97e-3f2bffda8bf5
-- title:
--   Row 23 RH support: RH67156Slab16Fast15Block09
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
theorem transition09 : runO cfg oc 2000 state32 = state36 := by
  decide +kernel
end RH67156Slab16Fast15
#print axioms RH67156Slab16Fast15.transition09


