-- Prove2me | Definitions.Def_dusart_mesh_upper_group394
-- name    : dusart_mesh_upper_group394
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:38:49.63428+00:00
-- url     : https://prove2.me/theorems/582fc5e8-0f6b-49b3-98f4-e3379cd2f707
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group394_part00
import Definitions.Def_dusart_mesh_upper_group394_part01
import Definitions.Def_dusart_mesh_upper_group394_part02
import Definitions.Def_dusart_mesh_upper_group394_part03
import Definitions.Def_dusart_mesh_upper_group394_part04
import Definitions.Def_dusart_mesh_upper_group394_part05
import Definitions.Def_dusart_mesh_upper_group394_part06
import Definitions.Def_dusart_mesh_upper_group394_part07
import Definitions.Def_dusart_mesh_upper_group394_part08
import Definitions.Def_dusart_mesh_upper_group394_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g394 : DusartNumeric.GenericSpec 4998947072 5015724288 4998863595651529 5015654636552506 := by
 intro S step compose
 exact (compose (g394_part0 S step @compose) (compose (g394_part1 S step @compose) (compose (g394_part2 S step @compose) (compose (g394_part3 S step @compose) (compose (g394_part4 S step @compose) (compose (g394_part5 S step @compose) (compose (g394_part6 S step @compose) (compose (g394_part7 S step @compose) (compose (g394_part8 S step @compose) (g394_part9 S step @compose))))))))))
end DusartFinitePlain


