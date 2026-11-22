-- Prove2me | Definitions.Def_row23_rh_supp_RH67156FastPiece21Block04
-- name    : row23_rh_supp_RH67156FastPiece21Block04
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-21T21:24:30.785649+00:00
-- url     : https://prove2.me/theorems/b55cc7b2-c0ac-4f3b-a7a5-4e85bdceb2e7
-- title:
--   Row 23 RH support: RH67156FastPiece21Block04
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH67156FastPiece21Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open ArbEcon ArbEcon.Off
namespace RH67156FastPiece21

theorem transition04 : runO cfg oc 4000 state24 = state32 := by
  decide +kernel
end RH67156FastPiece21
#print axioms RH67156FastPiece21.transition04


