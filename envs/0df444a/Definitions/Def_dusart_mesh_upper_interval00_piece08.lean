-- Prove2me | Definitions.Def_dusart_mesh_upper_interval00_piece08
-- name    : dusart_mesh_upper_interval00_piece08
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:44:10.53342+00:00
-- url     : https://prove2.me/theorems/abc56ad9-6333-4ff3-a693-9762e70d558a
-- title:
--   Dusart finite mesh: proved subinterval 9 of upper interval 1
-- statement:
--   The proved subinterval 9 of upper interval 1 component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_soundness
import Definitions.Def_dusart_mesh_upper_group064
import Definitions.Def_dusart_mesh_upper_group065
import Definitions.Def_dusart_mesh_upper_group066
import Definitions.Def_dusart_mesh_upper_group067
import Definitions.Def_dusart_mesh_upper_group068
import Definitions.Def_dusart_mesh_upper_group069
import Definitions.Def_dusart_mesh_upper_group070
import Definitions.Def_dusart_mesh_upper_group071
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartUpperPieces
theorem i0p8_generic : DusartNumeric.GenericSpec 267772160 301326592 267757896932078 301312452401436 := by
 intro S step compose
 exact (compose (compose (compose (DusartFinitePlain.g64 S step @compose) (DusartFinitePlain.g65 S step @compose)) (compose (DusartFinitePlain.g66 S step @compose) (DusartFinitePlain.g67 S step @compose))) (compose (compose (DusartFinitePlain.g68 S step @compose) (DusartFinitePlain.g69 S step @compose)) (compose (DusartFinitePlain.g70 S step @compose) (DusartFinitePlain.g71 S step @compose))))
theorem i0p8 : DusartMeshUpper.Literal.Spec 267772160 301326592 267757896932078 301312452401436 :=
 DusartNumericBridge.generic_to_theta i0p8_generic
end DusartUpperPieces


