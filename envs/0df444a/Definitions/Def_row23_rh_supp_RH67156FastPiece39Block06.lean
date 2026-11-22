-- Prove2me | Definitions.Def_row23_rh_supp_RH67156FastPiece39Block06
-- name    : row23_rh_supp_RH67156FastPiece39Block06
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-21T21:49:37.486465+00:00
-- url     : https://prove2.me/theorems/c8a1a915-0dbe-42f7-9d6a-b38fe4fa7fe9
-- title:
--   Row 23 RH support: RH67156FastPiece39Block06
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH67156FastPiece39Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open ArbEcon ArbEcon.Off
namespace RH67156FastPiece39

theorem transition06 : runO cfg oc 498 state38 = state39 := by
  decide +kernel
end RH67156FastPiece39
#print axioms RH67156FastPiece39.transition06


