-- Prove2me | Definitions.Def_dusart_mesh_upper_interval00_piece06
-- name    : dusart_mesh_upper_interval00_piece06
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:40:01.7126+00:00
-- url     : https://prove2.me/theorems/27972577-ba59-40b9-af2f-4eaeb30ccdf0
-- title:
--   Dusart finite mesh: proved subinterval 7 of upper interval 1
-- statement:
--   The proved subinterval 7 of upper interval 1 component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_soundness
import Definitions.Def_dusart_mesh_upper_group048
import Definitions.Def_dusart_mesh_upper_group049
import Definitions.Def_dusart_mesh_upper_group050
import Definitions.Def_dusart_mesh_upper_group051
import Definitions.Def_dusart_mesh_upper_group052
import Definitions.Def_dusart_mesh_upper_group053
import Definitions.Def_dusart_mesh_upper_group054
import Definitions.Def_dusart_mesh_upper_group055
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartUpperPieces
theorem i0p6_generic : DusartNumeric.GenericSpec 200663296 234217728 200649157625116 234197530971831 := by
 intro S step compose
 exact (compose (compose (compose (DusartFinitePlain.g48 S step @compose) (DusartFinitePlain.g49 S step @compose)) (compose (DusartFinitePlain.g50 S step @compose) (DusartFinitePlain.g51 S step @compose))) (compose (compose (DusartFinitePlain.g52 S step @compose) (DusartFinitePlain.g53 S step @compose)) (compose (DusartFinitePlain.g54 S step @compose) (DusartFinitePlain.g55 S step @compose))))
theorem i0p6 : DusartMeshUpper.Literal.Spec 200663296 234217728 200649157625116 234197530971831 :=
 DusartNumericBridge.generic_to_theta i0p6_generic
end DusartUpperPieces


