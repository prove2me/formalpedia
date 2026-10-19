-- Prove2me | Definitions.Def_dusart_mesh_upper_interval00_piece00
-- name    : dusart_mesh_upper_interval00_piece00
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:33:42.670075+00:00
-- url     : https://prove2.me/theorems/07cb26d5-0426-4fa2-b384-eebfc04fb535
-- title:
--   Dusart finite mesh: proved subinterval 1 of upper interval 1
-- statement:
--   The proved subinterval 1 of upper interval 1 component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_soundness
import Definitions.Def_dusart_mesh_upper_group000
import Definitions.Def_dusart_mesh_upper_group001
import Definitions.Def_dusart_mesh_upper_group002
import Definitions.Def_dusart_mesh_upper_group003
import Definitions.Def_dusart_mesh_upper_group004
import Definitions.Def_dusart_mesh_upper_group005
import Definitions.Def_dusart_mesh_upper_group006
import Definitions.Def_dusart_mesh_upper_group007
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartUpperPieces
theorem i0p0_generic : DusartNumeric.GenericSpec 100000000 116777216 99989691935170 116769517294322 := by
 intro S step compose
 exact (compose (compose (compose (DusartFinitePlain.g0 S step @compose) (DusartFinitePlain.g1 S step @compose)) (compose (DusartFinitePlain.g2 S step @compose) (DusartFinitePlain.g3 S step @compose))) (compose (compose (DusartFinitePlain.g4 S step @compose) (DusartFinitePlain.g5 S step @compose)) (compose (DusartFinitePlain.g6 S step @compose) (DusartFinitePlain.g7 S step @compose))))
theorem i0p0 : DusartMeshUpper.Literal.Spec 100000000 116777216 99989691935170 116769517294322 :=
 DusartNumericBridge.generic_to_theta i0p0_generic
end DusartUpperPieces


