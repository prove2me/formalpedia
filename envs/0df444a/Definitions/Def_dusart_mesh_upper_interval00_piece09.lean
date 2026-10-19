-- Prove2me | Definitions.Def_dusart_mesh_upper_interval00_piece09
-- name    : dusart_mesh_upper_interval00_piece09
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:44:48.426253+00:00
-- url     : https://prove2.me/theorems/988ed40c-acf0-4340-8f39-cd54acb5131e
-- title:
--   Dusart finite mesh: proved subinterval 10 of upper interval 1
-- statement:
--   The proved subinterval 10 of upper interval 1 component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_soundness
import Definitions.Def_dusart_mesh_upper_group072
import Definitions.Def_dusart_mesh_upper_group073
import Definitions.Def_dusart_mesh_upper_group074
import Definitions.Def_dusart_mesh_upper_group075
import Definitions.Def_dusart_mesh_upper_group076
import Definitions.Def_dusart_mesh_upper_group077
import Definitions.Def_dusart_mesh_upper_group078
import Definitions.Def_dusart_mesh_upper_group079
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartUpperPieces
theorem i0p9_generic : DusartNumeric.GenericSpec 301326592 334881024 301312452401436 334862277062422 := by
 intro S step compose
 exact (compose (compose (compose (DusartFinitePlain.g72 S step @compose) (DusartFinitePlain.g73 S step @compose)) (compose (DusartFinitePlain.g74 S step @compose) (DusartFinitePlain.g75 S step @compose))) (compose (compose (DusartFinitePlain.g76 S step @compose) (DusartFinitePlain.g77 S step @compose)) (compose (DusartFinitePlain.g78 S step @compose) (DusartFinitePlain.g79 S step @compose))))
theorem i0p9 : DusartMeshUpper.Literal.Spec 301326592 334881024 301312452401436 334862277062422 :=
 DusartNumericBridge.generic_to_theta i0p9_generic
end DusartUpperPieces


