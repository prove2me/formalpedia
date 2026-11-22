-- Prove2me | Definitions.Def_row23_rh_supp_RH67156FastPiece34Block05
-- name    : row23_rh_supp_RH67156FastPiece34Block05
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-21T21:42:20.5199+00:00
-- url     : https://prove2.me/theorems/34813016-3147-47c0-b888-1dc6e0273e3f
-- title:
--   Row 23 RH support: RH67156FastPiece34Block05
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH67156FastPiece34Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open ArbEcon ArbEcon.Off
namespace RH67156FastPiece34

theorem transition05 : runO cfg oc 3000 state32 = state38 := by
  decide +kernel
end RH67156FastPiece34
#print axioms RH67156FastPiece34.transition05


