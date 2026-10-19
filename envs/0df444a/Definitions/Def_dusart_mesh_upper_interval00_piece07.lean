-- Prove2me | Definitions.Def_dusart_mesh_upper_interval00_piece07
-- name    : dusart_mesh_upper_interval00_piece07
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:41:03.036443+00:00
-- url     : https://prove2.me/theorems/a855a4ca-dc17-452e-966f-c90ce4667ba3
-- title:
--   Dusart finite mesh: proved subinterval 8 of upper interval 1
-- statement:
--   The proved subinterval 8 of upper interval 1 component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_soundness
import Definitions.Def_dusart_mesh_upper_group056
import Definitions.Def_dusart_mesh_upper_group057
import Definitions.Def_dusart_mesh_upper_group058
import Definitions.Def_dusart_mesh_upper_group059
import Definitions.Def_dusart_mesh_upper_group060
import Definitions.Def_dusart_mesh_upper_group061
import Definitions.Def_dusart_mesh_upper_group062
import Definitions.Def_dusart_mesh_upper_group063
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartUpperPieces
theorem i0p7_generic : DusartNumeric.GenericSpec 234217728 267772160 234197530971831 267757896932078 := by
 intro S step compose
 exact (compose (compose (compose (DusartFinitePlain.g56 S step @compose) (DusartFinitePlain.g57 S step @compose)) (compose (DusartFinitePlain.g58 S step @compose) (DusartFinitePlain.g59 S step @compose))) (compose (compose (DusartFinitePlain.g60 S step @compose) (DusartFinitePlain.g61 S step @compose)) (compose (DusartFinitePlain.g62 S step @compose) (DusartFinitePlain.g63 S step @compose))))
theorem i0p7 : DusartMeshUpper.Literal.Spec 234217728 267772160 234197530971831 267757896932078 :=
 DusartNumericBridge.generic_to_theta i0p7_generic
end DusartUpperPieces


