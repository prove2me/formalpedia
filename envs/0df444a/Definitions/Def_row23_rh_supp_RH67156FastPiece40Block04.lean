-- Prove2me | Definitions.Def_row23_rh_supp_RH67156FastPiece40Block04
-- name    : row23_rh_supp_RH67156FastPiece40Block04
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-21T20:47:46.636114+00:00
-- url     : https://prove2.me/theorems/8a0e1b4c-0568-4d67-a869-af3f05846eeb
-- title:
--   Row 23 RH support: RH67156FastPiece40Block04
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH67156FastPiece40Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open ArbEcon ArbEcon.Off
namespace RH67156FastPiece40

theorem transition04 : runO cfg oc 4000 state24 = state32 := by
  decide +kernel
end RH67156FastPiece40
#print axioms RH67156FastPiece40.transition04


