-- Prove2me | Definitions.Def_row23_rh_supp_RH66388FastPiece20Block07
-- name    : row23_rh_supp_RH66388FastPiece20Block07
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:32:16.73093+00:00
-- url     : https://prove2.me/theorems/3ef9d5a8-ed88-4226-a261-6925d1178326
-- title:
--   Row 23 RH support: RH66388FastPiece20Block07
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH66388FastPiece20Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open ArbEcon ArbEcon.Off
namespace RH66388FastPiece20

theorem transition07 : runO cfg oc 1 state39 = state40 := by
  decide +kernel
end RH66388FastPiece20
#print axioms RH66388FastPiece20.transition07


