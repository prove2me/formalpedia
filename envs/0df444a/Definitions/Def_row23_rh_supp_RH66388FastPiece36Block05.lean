-- Prove2me | Definitions.Def_row23_rh_supp_RH66388FastPiece36Block05
-- name    : row23_rh_supp_RH66388FastPiece36Block05
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:38:06.998615+00:00
-- url     : https://prove2.me/theorems/313a03b2-602d-4ada-8a3f-0427cbd0601f
-- title:
--   Row 23 RH support: RH66388FastPiece36Block05
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH66388FastPiece36Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open ArbEcon ArbEcon.Off
namespace RH66388FastPiece36

theorem transition05 : runO cfg oc 3000 state32 = state38 := by
  decide +kernel
end RH66388FastPiece36
#print axioms RH66388FastPiece36.transition05


