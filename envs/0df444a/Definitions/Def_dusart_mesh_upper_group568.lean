-- Prove2me | Definitions.Def_dusart_mesh_upper_group568
-- name    : dusart_mesh_upper_group568
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-17T00:02:09.940089+00:00
-- url     : https://prove2.me/theorems/b3df82ff-9b99-4dad-8812-1ecd4c240c86
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group568_part00
import Definitions.Def_dusart_mesh_upper_group568_part01
import Definitions.Def_dusart_mesh_upper_group568_part02
import Definitions.Def_dusart_mesh_upper_group568_part03
import Definitions.Def_dusart_mesh_upper_group568_part04
import Definitions.Def_dusart_mesh_upper_group568_part05
import Definitions.Def_dusart_mesh_upper_group568_part06
import Definitions.Def_dusart_mesh_upper_group568_part07
import Definitions.Def_dusart_mesh_upper_group568_part08
import Definitions.Def_dusart_mesh_upper_group568_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g568 : DusartNumeric.GenericSpec 7918182656 7934959872 7918066696337914 7934845582092564 := by
 intro S step compose
 exact (compose (g568_part0 S step @compose) (compose (g568_part1 S step @compose) (compose (g568_part2 S step @compose) (compose (g568_part3 S step @compose) (compose (g568_part4 S step @compose) (compose (g568_part5 S step @compose) (compose (g568_part6 S step @compose) (compose (g568_part7 S step @compose) (compose (g568_part8 S step @compose) (g568_part9 S step @compose))))))))))
end DusartFinitePlain


