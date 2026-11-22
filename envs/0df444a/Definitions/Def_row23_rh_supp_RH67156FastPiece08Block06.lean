-- Prove2me | Definitions.Def_row23_rh_supp_RH67156FastPiece08Block06
-- name    : row23_rh_supp_RH67156FastPiece08Block06
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-21T21:10:08.843882+00:00
-- url     : https://prove2.me/theorems/692f0bfe-dfc3-469c-ba38-b810d4c10347
-- title:
--   Row 23 RH support: RH67156FastPiece08Block06
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH67156FastPiece08Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open ArbEcon ArbEcon.Off
namespace RH67156FastPiece08

theorem transition06 : runO cfg oc 498 state38 = state39 := by
  decide +kernel
end RH67156FastPiece08
#print axioms RH67156FastPiece08.transition06


