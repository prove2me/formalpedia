-- Prove2me | Definitions.Def_row23_rh_supp_RH67156FastPiece10Block02
-- name    : row23_rh_supp_RH67156FastPiece10Block02
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-21T21:12:00.850167+00:00
-- url     : https://prove2.me/theorems/0052052a-b07a-4db1-8e1d-360b78bc9346
-- title:
--   Row 23 RH support: RH67156FastPiece10Block02
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH67156FastPiece10Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open ArbEcon ArbEcon.Off
namespace RH67156FastPiece10

theorem transition02 : runO cfg oc 4000 state08 = state16 := by
  decide +kernel
end RH67156FastPiece10
#print axioms RH67156FastPiece10.transition02


