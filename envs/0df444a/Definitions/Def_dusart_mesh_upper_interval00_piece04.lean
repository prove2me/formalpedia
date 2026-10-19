-- Prove2me | Definitions.Def_dusart_mesh_upper_interval00_piece04
-- name    : dusart_mesh_upper_interval00_piece04
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:37:01.224274+00:00
-- url     : https://prove2.me/theorems/4e582e70-0bab-4b8c-944b-e3fe99a2e9fb
-- title:
--   Dusart finite mesh: proved subinterval 5 of upper interval 1
-- statement:
--   The proved subinterval 5 of upper interval 1 component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_soundness
import Definitions.Def_dusart_mesh_upper_group032
import Definitions.Def_dusart_mesh_upper_group033
import Definitions.Def_dusart_mesh_upper_group034
import Definitions.Def_dusart_mesh_upper_group035
import Definitions.Def_dusart_mesh_upper_group036
import Definitions.Def_dusart_mesh_upper_group037
import Definitions.Def_dusart_mesh_upper_group038
import Definitions.Def_dusart_mesh_upper_group039
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartUpperPieces
theorem i0p4_generic : DusartNumeric.GenericSpec 167108864 183886080 167094547216418 183874229431280 := by
 intro S step compose
 exact (compose (compose (compose (DusartFinitePlain.g32 S step @compose) (DusartFinitePlain.g33 S step @compose)) (compose (DusartFinitePlain.g34 S step @compose) (DusartFinitePlain.g35 S step @compose))) (compose (compose (DusartFinitePlain.g36 S step @compose) (DusartFinitePlain.g37 S step @compose)) (compose (DusartFinitePlain.g38 S step @compose) (DusartFinitePlain.g39 S step @compose))))
theorem i0p4 : DusartMeshUpper.Literal.Spec 167108864 183886080 167094547216418 183874229431280 :=
 DusartNumericBridge.generic_to_theta i0p4_generic
end DusartUpperPieces


