-- Prove2me | Definitions.Def_row23_rh_supp_RH66388FastPiece14Block07
-- name    : row23_rh_supp_RH66388FastPiece14Block07
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:29:11.955809+00:00
-- url     : https://prove2.me/theorems/661c2b81-aae9-4a50-9ed2-cce01fe1794f
-- title:
--   Row 23 RH support: RH66388FastPiece14Block07
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH66388FastPiece14Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open ArbEcon ArbEcon.Off
namespace RH66388FastPiece14

theorem transition07 : runO cfg oc 1 state39 = state40 := by
  decide +kernel
end RH66388FastPiece14
#print axioms RH66388FastPiece14.transition07


