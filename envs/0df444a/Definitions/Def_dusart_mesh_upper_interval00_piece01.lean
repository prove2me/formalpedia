-- Prove2me | Definitions.Def_dusart_mesh_upper_interval00_piece01
-- name    : dusart_mesh_upper_interval00_piece01
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:33:12.260483+00:00
-- url     : https://prove2.me/theorems/bebc280a-b020-4606-95ed-c43f88bfc2c0
-- title:
--   Dusart finite mesh: proved subinterval 2 of upper interval 1
-- statement:
--   The proved subinterval 2 of upper interval 1 component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_soundness
import Definitions.Def_dusart_mesh_upper_group008
import Definitions.Def_dusart_mesh_upper_group009
import Definitions.Def_dusart_mesh_upper_group010
import Definitions.Def_dusart_mesh_upper_group011
import Definitions.Def_dusart_mesh_upper_group012
import Definitions.Def_dusart_mesh_upper_group013
import Definitions.Def_dusart_mesh_upper_group014
import Definitions.Def_dusart_mesh_upper_group015
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartUpperPieces
theorem i0p1_generic : DusartNumeric.GenericSpec 116777216 133554432 116769517294322 133544733738995 := by
 intro S step compose
 exact (compose (compose (compose (DusartFinitePlain.g8 S step @compose) (DusartFinitePlain.g9 S step @compose)) (compose (DusartFinitePlain.g10 S step @compose) (DusartFinitePlain.g11 S step @compose))) (compose (compose (DusartFinitePlain.g12 S step @compose) (DusartFinitePlain.g13 S step @compose)) (compose (DusartFinitePlain.g14 S step @compose) (DusartFinitePlain.g15 S step @compose))))
theorem i0p1 : DusartMeshUpper.Literal.Spec 116777216 133554432 116769517294322 133544733738995 :=
 DusartNumericBridge.generic_to_theta i0p1_generic
end DusartUpperPieces


