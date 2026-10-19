-- Prove2me | Definitions.Def_dusart_mesh_upper_group634
-- name    : dusart_mesh_upper_group634
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-17T00:09:08.237861+00:00
-- url     : https://prove2.me/theorems/3c078e39-ee97-4bce-b2f4-7d5365b7410b
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group634_part00
import Definitions.Def_dusart_mesh_upper_group634_part01
import Definitions.Def_dusart_mesh_upper_group634_part02
import Definitions.Def_dusart_mesh_upper_group634_part03
import Definitions.Def_dusart_mesh_upper_group634_part04
import Definitions.Def_dusart_mesh_upper_group634_part05
import Definitions.Def_dusart_mesh_upper_group634_part06
import Definitions.Def_dusart_mesh_upper_group634_part07
import Definitions.Def_dusart_mesh_upper_group634_part08
import Definitions.Def_dusart_mesh_upper_group634_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g634 : DusartNumeric.GenericSpec 9025478912 9042256128 9025401009141281 9042169324373999 := by
 intro S step compose
 exact (compose (g634_part0 S step @compose) (compose (g634_part1 S step @compose) (compose (g634_part2 S step @compose) (compose (g634_part3 S step @compose) (compose (g634_part4 S step @compose) (compose (g634_part5 S step @compose) (compose (g634_part6 S step @compose) (compose (g634_part7 S step @compose) (compose (g634_part8 S step @compose) (g634_part9 S step @compose))))))))))
end DusartFinitePlain


