-- Prove2me | Definitions.Def_dusart_mesh_upper_interval00_piece05
-- name    : dusart_mesh_upper_interval00_piece05
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:38:02.921172+00:00
-- url     : https://prove2.me/theorems/53a7d1a3-15dd-491e-8c1c-cc7c462aff2b
-- title:
--   Dusart finite mesh: proved subinterval 6 of upper interval 1
-- statement:
--   The proved subinterval 6 of upper interval 1 component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_soundness
import Definitions.Def_dusart_mesh_upper_group040
import Definitions.Def_dusart_mesh_upper_group041
import Definitions.Def_dusart_mesh_upper_group042
import Definitions.Def_dusart_mesh_upper_group043
import Definitions.Def_dusart_mesh_upper_group044
import Definitions.Def_dusart_mesh_upper_group045
import Definitions.Def_dusart_mesh_upper_group046
import Definitions.Def_dusart_mesh_upper_group047
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartUpperPieces
theorem i0p5_generic : DusartNumeric.GenericSpec 183886080 200663296 183874229431280 200649157625116 := by
 intro S step compose
 exact (compose (compose (compose (DusartFinitePlain.g40 S step @compose) (DusartFinitePlain.g41 S step @compose)) (compose (DusartFinitePlain.g42 S step @compose) (DusartFinitePlain.g43 S step @compose))) (compose (compose (DusartFinitePlain.g44 S step @compose) (DusartFinitePlain.g45 S step @compose)) (compose (DusartFinitePlain.g46 S step @compose) (DusartFinitePlain.g47 S step @compose))))
theorem i0p5 : DusartMeshUpper.Literal.Spec 183886080 200663296 183874229431280 200649157625116 :=
 DusartNumericBridge.generic_to_theta i0p5_generic
end DusartUpperPieces


