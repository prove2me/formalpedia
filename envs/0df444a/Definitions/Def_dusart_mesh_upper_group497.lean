-- Prove2me | Definitions.Def_dusart_mesh_upper_group497
-- name    : dusart_mesh_upper_group497
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:51:27.005368+00:00
-- url     : https://prove2.me/theorems/e47d702f-7915-40f8-bd36-d12518ca2c4d
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group497_part00
import Definitions.Def_dusart_mesh_upper_group497_part01
import Definitions.Def_dusart_mesh_upper_group497_part02
import Definitions.Def_dusart_mesh_upper_group497_part03
import Definitions.Def_dusart_mesh_upper_group497_part04
import Definitions.Def_dusart_mesh_upper_group497_part05
import Definitions.Def_dusart_mesh_upper_group497_part06
import Definitions.Def_dusart_mesh_upper_group497_part07
import Definitions.Def_dusart_mesh_upper_group497_part08
import Definitions.Def_dusart_mesh_upper_group497_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g497 : DusartNumeric.GenericSpec 6727000320 6743777536 6726937500585803 6743706746028718 := by
 intro S step compose
 exact (compose (g497_part0 S step @compose) (compose (g497_part1 S step @compose) (compose (g497_part2 S step @compose) (compose (g497_part3 S step @compose) (compose (g497_part4 S step @compose) (compose (g497_part5 S step @compose) (compose (g497_part6 S step @compose) (compose (g497_part7 S step @compose) (compose (g497_part8 S step @compose) (g497_part9 S step @compose))))))))))
end DusartFinitePlain


