-- Prove2me | Definitions.Def_dusart_mesh_upper_interval00_piece11
-- name    : dusart_mesh_upper_interval00_piece11
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:47:29.61798+00:00
-- url     : https://prove2.me/theorems/efb644b9-20e3-45ff-bca1-3aa44ef33538
-- title:
--   Dusart finite mesh: proved subinterval 12 of upper interval 1
-- statement:
--   The proved subinterval 12 of upper interval 1 component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_soundness
import Definitions.Def_dusart_mesh_upper_group088
import Definitions.Def_dusart_mesh_upper_group089
import Definitions.Def_dusart_mesh_upper_group090
import Definitions.Def_dusart_mesh_upper_group091
import Definitions.Def_dusart_mesh_upper_group092
import Definitions.Def_dusart_mesh_upper_group093
import Definitions.Def_dusart_mesh_upper_group094
import Definitions.Def_dusart_mesh_upper_group095
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartUpperPieces
theorem i0p11_generic : DusartNumeric.GenericSpec 368435456 401989888 368414392930268 401971882499010 := by
 intro S step compose
 exact (compose (compose (compose (DusartFinitePlain.g88 S step @compose) (DusartFinitePlain.g89 S step @compose)) (compose (DusartFinitePlain.g90 S step @compose) (DusartFinitePlain.g91 S step @compose))) (compose (compose (DusartFinitePlain.g92 S step @compose) (DusartFinitePlain.g93 S step @compose)) (compose (DusartFinitePlain.g94 S step @compose) (DusartFinitePlain.g95 S step @compose))))
theorem i0p11 : DusartMeshUpper.Literal.Spec 368435456 401989888 368414392930268 401971882499010 :=
 DusartNumericBridge.generic_to_theta i0p11_generic
end DusartUpperPieces


