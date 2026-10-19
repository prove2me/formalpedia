-- Prove2me | Definitions.Def_dusart_mesh_upper_interval00_piece03
-- name    : dusart_mesh_upper_interval00_piece03
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:35:43.153291+00:00
-- url     : https://prove2.me/theorems/38e1a0d3-1eeb-47a1-8a11-49caf8673315
-- title:
--   Dusart finite mesh: proved subinterval 4 of upper interval 1
-- statement:
--   The proved subinterval 4 of upper interval 1 component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_soundness
import Definitions.Def_dusart_mesh_upper_group024
import Definitions.Def_dusart_mesh_upper_group025
import Definitions.Def_dusart_mesh_upper_group026
import Definitions.Def_dusart_mesh_upper_group027
import Definitions.Def_dusart_mesh_upper_group028
import Definitions.Def_dusart_mesh_upper_group029
import Definitions.Def_dusart_mesh_upper_group030
import Definitions.Def_dusart_mesh_upper_group031
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartUpperPieces
theorem i0p3_generic : DusartNumeric.GenericSpec 150331648 167108864 150321997139092 167094547216418 := by
 intro S step compose
 exact (compose (compose (compose (DusartFinitePlain.g24 S step @compose) (DusartFinitePlain.g25 S step @compose)) (compose (DusartFinitePlain.g26 S step @compose) (DusartFinitePlain.g27 S step @compose))) (compose (compose (DusartFinitePlain.g28 S step @compose) (DusartFinitePlain.g29 S step @compose)) (compose (DusartFinitePlain.g30 S step @compose) (DusartFinitePlain.g31 S step @compose))))
theorem i0p3 : DusartMeshUpper.Literal.Spec 150331648 167108864 150321997139092 167094547216418 :=
 DusartNumericBridge.generic_to_theta i0p3_generic
end DusartUpperPieces


