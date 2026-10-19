-- Prove2me | Definitions.Def_dusart_mesh_upper_interval00_piece10
-- name    : dusart_mesh_upper_interval00_piece10
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:47:05.028959+00:00
-- url     : https://prove2.me/theorems/3bd289be-af71-426d-8748-931abd8e6a04
-- title:
--   Dusart finite mesh: proved subinterval 11 of upper interval 1
-- statement:
--   The proved subinterval 11 of upper interval 1 component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_soundness
import Definitions.Def_dusart_mesh_upper_group080
import Definitions.Def_dusart_mesh_upper_group081
import Definitions.Def_dusart_mesh_upper_group082
import Definitions.Def_dusart_mesh_upper_group083
import Definitions.Def_dusart_mesh_upper_group084
import Definitions.Def_dusart_mesh_upper_group085
import Definitions.Def_dusart_mesh_upper_group086
import Definitions.Def_dusart_mesh_upper_group087
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartUpperPieces
theorem i0p10_generic : DusartNumeric.GenericSpec 334881024 368435456 334862277062422 368414392930268 := by
 intro S step compose
 exact (compose (compose (compose (DusartFinitePlain.g80 S step @compose) (DusartFinitePlain.g81 S step @compose)) (compose (DusartFinitePlain.g82 S step @compose) (DusartFinitePlain.g83 S step @compose))) (compose (compose (DusartFinitePlain.g84 S step @compose) (DusartFinitePlain.g85 S step @compose)) (compose (DusartFinitePlain.g86 S step @compose) (DusartFinitePlain.g87 S step @compose))))
theorem i0p10 : DusartMeshUpper.Literal.Spec 334881024 368435456 334862277062422 368414392930268 :=
 DusartNumericBridge.generic_to_theta i0p10_generic
end DusartUpperPieces


