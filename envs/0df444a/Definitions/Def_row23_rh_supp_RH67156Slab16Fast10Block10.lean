-- Prove2me | Definitions.Def_row23_rh_supp_RH67156Slab16Fast10Block10
-- name    : row23_rh_supp_RH67156Slab16Fast10Block10
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-21T22:16:56.669078+00:00
-- url     : https://prove2.me/theorems/a88551e6-4e33-4b07-82e6-11283e65bff5
-- title:
--   Row 23 RH support: RH67156Slab16Fast10Block10
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH67156Slab16Fast10Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open ArbEcon ArbEcon.Off
namespace RH67156Slab16Fast10
theorem transition10 : runO cfg oc 1000 state36 = state38 := by
  decide +kernel
end RH67156Slab16Fast10
#print axioms RH67156Slab16Fast10.transition10


