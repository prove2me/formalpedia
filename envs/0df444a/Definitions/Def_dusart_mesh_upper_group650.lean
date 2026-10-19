-- Prove2me | Definitions.Def_dusart_mesh_upper_group650
-- name    : dusart_mesh_upper_group650
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-17T00:10:36.357867+00:00
-- url     : https://prove2.me/theorems/9e0bc817-04b1-409b-bef2-efeb7a3e5692
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group650_part00
import Definitions.Def_dusart_mesh_upper_group650_part01
import Definitions.Def_dusart_mesh_upper_group650_part02
import Definitions.Def_dusart_mesh_upper_group650_part03
import Definitions.Def_dusart_mesh_upper_group650_part04
import Definitions.Def_dusart_mesh_upper_group650_part05
import Definitions.Def_dusart_mesh_upper_group650_part06
import Definitions.Def_dusart_mesh_upper_group650_part07
import Definitions.Def_dusart_mesh_upper_group650_part08
import Definitions.Def_dusart_mesh_upper_group650_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g650 : DusartNumeric.GenericSpec 9293914368 9310691584 9293842486148482 9310611837024355 := by
 intro S step compose
 exact (compose (g650_part0 S step @compose) (compose (g650_part1 S step @compose) (compose (g650_part2 S step @compose) (compose (g650_part3 S step @compose) (compose (g650_part4 S step @compose) (compose (g650_part5 S step @compose) (compose (g650_part6 S step @compose) (compose (g650_part7 S step @compose) (compose (g650_part8 S step @compose) (g650_part9 S step @compose))))))))))
end DusartFinitePlain


