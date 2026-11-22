-- Prove2me | Definitions.Def_row23_rh_supp_RH67156FastPiece06Block06
-- name    : row23_rh_supp_RH67156FastPiece06Block06
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-21T21:04:14.187092+00:00
-- url     : https://prove2.me/theorems/d19db207-fffd-46f3-99e7-6a93ac730653
-- title:
--   Row 23 RH support: RH67156FastPiece06Block06
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH67156FastPiece06Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open ArbEcon ArbEcon.Off
namespace RH67156FastPiece06

theorem transition06 : runO cfg oc 498 state38 = state39 := by
  decide +kernel
end RH67156FastPiece06
#print axioms RH67156FastPiece06.transition06


