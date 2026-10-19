-- Prove2me | Definitions.Def_dusart_mesh_upper_group198
-- name    : dusart_mesh_upper_group198
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:01:07.285983+00:00
-- url     : https://prove2.me/theorems/1e56bbe9-7510-4ed5-8ca1-2d9dbb41aa5c
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group198_part00
import Definitions.Def_dusart_mesh_upper_group198_part01
import Definitions.Def_dusart_mesh_upper_group198_part02
import Definitions.Def_dusart_mesh_upper_group198_part03
import Definitions.Def_dusart_mesh_upper_group198_part04
import Definitions.Def_dusart_mesh_upper_group198_part05
import Definitions.Def_dusart_mesh_upper_group198_part06
import Definitions.Def_dusart_mesh_upper_group198_part07
import Definitions.Def_dusart_mesh_upper_group198_part08
import Definitions.Def_dusart_mesh_upper_group198_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g198 : DusartNumeric.GenericSpec 1710612736 1727389952 1710582910507471 1727361722337772 := by
 intro S step compose
 exact (compose (g198_part0 S step @compose) (compose (g198_part1 S step @compose) (compose (g198_part2 S step @compose) (compose (g198_part3 S step @compose) (compose (g198_part4 S step @compose) (compose (g198_part5 S step @compose) (compose (g198_part6 S step @compose) (compose (g198_part7 S step @compose) (compose (g198_part8 S step @compose) (g198_part9 S step @compose))))))))))
end DusartFinitePlain
#print axioms DusartFinitePlain.g198


