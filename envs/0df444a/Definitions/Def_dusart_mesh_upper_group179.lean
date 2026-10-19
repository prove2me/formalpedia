-- Prove2me | Definitions.Def_dusart_mesh_upper_group179
-- name    : dusart_mesh_upper_group179
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T22:56:36.275983+00:00
-- url     : https://prove2.me/theorems/0d4e3e79-98f5-40fe-a311-9f3776e565b0
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group179_part00
import Definitions.Def_dusart_mesh_upper_group179_part01
import Definitions.Def_dusart_mesh_upper_group179_part02
import Definitions.Def_dusart_mesh_upper_group179_part03
import Definitions.Def_dusart_mesh_upper_group179_part04
import Definitions.Def_dusart_mesh_upper_group179_part05
import Definitions.Def_dusart_mesh_upper_group179_part06
import Definitions.Def_dusart_mesh_upper_group179_part07
import Definitions.Def_dusart_mesh_upper_group179_part08
import Definitions.Def_dusart_mesh_upper_group179_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g179 : DusartNumeric.GenericSpec 1391845632 1408622848 1391814207420695 1408581302966765 := by
 intro S step compose
 exact (compose (g179_part0 S step @compose) (compose (g179_part1 S step @compose) (compose (g179_part2 S step @compose) (compose (g179_part3 S step @compose) (compose (g179_part4 S step @compose) (compose (g179_part5 S step @compose) (compose (g179_part6 S step @compose) (compose (g179_part7 S step @compose) (compose (g179_part8 S step @compose) (g179_part9 S step @compose))))))))))
end DusartFinitePlain
#print axioms DusartFinitePlain.g179


