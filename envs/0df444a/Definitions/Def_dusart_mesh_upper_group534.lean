-- Prove2me | Definitions.Def_dusart_mesh_upper_group534
-- name    : dusart_mesh_upper_group534
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:57:31.386158+00:00
-- url     : https://prove2.me/theorems/0997181a-8dce-4aa6-afeb-95677704c730
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group534_part00
import Definitions.Def_dusart_mesh_upper_group534_part01
import Definitions.Def_dusart_mesh_upper_group534_part02
import Definitions.Def_dusart_mesh_upper_group534_part03
import Definitions.Def_dusart_mesh_upper_group534_part04
import Definitions.Def_dusart_mesh_upper_group534_part05
import Definitions.Def_dusart_mesh_upper_group534_part06
import Definitions.Def_dusart_mesh_upper_group534_part07
import Definitions.Def_dusart_mesh_upper_group534_part08
import Definitions.Def_dusart_mesh_upper_group534_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g534 : DusartNumeric.GenericSpec 7347757312 7364534528 7347674755255158 7364451803499579 := by
 intro S step compose
 exact (compose (g534_part0 S step @compose) (compose (g534_part1 S step @compose) (compose (g534_part2 S step @compose) (compose (g534_part3 S step @compose) (compose (g534_part4 S step @compose) (compose (g534_part5 S step @compose) (compose (g534_part6 S step @compose) (compose (g534_part7 S step @compose) (compose (g534_part8 S step @compose) (g534_part9 S step @compose))))))))))
end DusartFinitePlain


