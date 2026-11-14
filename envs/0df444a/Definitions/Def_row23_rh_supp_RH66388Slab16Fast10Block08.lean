-- Prove2me | Definitions.Def_row23_rh_supp_RH66388Slab16Fast10Block08
-- name    : row23_rh_supp_RH66388Slab16Fast10Block08
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:46:54.173514+00:00
-- url     : https://prove2.me/theorems/ccba4026-13fe-4c0b-998c-0d1607acf22c
-- title:
--   Row 23 RH support: RH66388Slab16Fast10Block08
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH66388Slab16Fast10Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open ArbEcon ArbEcon.Off
namespace RH66388Slab16Fast10
theorem transition08 : runO cfg oc 2000 state28 = state32 := by
  decide +kernel
end RH66388Slab16Fast10
#print axioms RH66388Slab16Fast10.transition08


