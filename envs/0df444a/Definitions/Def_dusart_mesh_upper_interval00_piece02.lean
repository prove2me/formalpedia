-- Prove2me | Definitions.Def_dusart_mesh_upper_interval00_piece02
-- name    : dusart_mesh_upper_interval00_piece02
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:34:51.252295+00:00
-- url     : https://prove2.me/theorems/a523890d-6b1e-4c1d-98aa-f5b3e9b6bf92
-- title:
--   Dusart finite mesh: proved subinterval 3 of upper interval 1
-- statement:
--   The proved subinterval 3 of upper interval 1 component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_soundness
import Definitions.Def_dusart_mesh_upper_group016
import Definitions.Def_dusart_mesh_upper_group017
import Definitions.Def_dusart_mesh_upper_group018
import Definitions.Def_dusart_mesh_upper_group019
import Definitions.Def_dusart_mesh_upper_group020
import Definitions.Def_dusart_mesh_upper_group021
import Definitions.Def_dusart_mesh_upper_group022
import Definitions.Def_dusart_mesh_upper_group023
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartUpperPieces
theorem i0p2_generic : DusartNumeric.GenericSpec 133554432 150331648 133544733738995 150321997139092 := by
 intro S step compose
 exact (compose (compose (compose (DusartFinitePlain.g16 S step @compose) (DusartFinitePlain.g17 S step @compose)) (compose (DusartFinitePlain.g18 S step @compose) (DusartFinitePlain.g19 S step @compose))) (compose (compose (DusartFinitePlain.g20 S step @compose) (DusartFinitePlain.g21 S step @compose)) (compose (DusartFinitePlain.g22 S step @compose) (DusartFinitePlain.g23 S step @compose))))
theorem i0p2 : DusartMeshUpper.Literal.Spec 133554432 150331648 133544733738995 150321997139092 :=
 DusartNumericBridge.generic_to_theta i0p2_generic
end DusartUpperPieces


