-- Prove2me | Definitions.Def_dusart_mesh_upper_group657
-- name    : dusart_mesh_upper_group657
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-17T00:13:17.749881+00:00
-- url     : https://prove2.me/theorems/07eb8bb1-4e53-4c1b-a97a-7fb2e9cad668
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group657_part00
import Definitions.Def_dusart_mesh_upper_group657_part01
import Definitions.Def_dusart_mesh_upper_group657_part02
import Definitions.Def_dusart_mesh_upper_group657_part03
import Definitions.Def_dusart_mesh_upper_group657_part04
import Definitions.Def_dusart_mesh_upper_group657_part05
import Definitions.Def_dusart_mesh_upper_group657_part06
import Definitions.Def_dusart_mesh_upper_group657_part07
import Definitions.Def_dusart_mesh_upper_group657_part08
import Definitions.Def_dusart_mesh_upper_group657_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g657 : DusartNumeric.GenericSpec 9411354880 9428132096 9411264939493626 9428053009794339 := by
 intro S step compose
 exact (compose (g657_part0 S step @compose) (compose (g657_part1 S step @compose) (compose (g657_part2 S step @compose) (compose (g657_part3 S step @compose) (compose (g657_part4 S step @compose) (compose (g657_part5 S step @compose) (compose (g657_part6 S step @compose) (compose (g657_part7 S step @compose) (compose (g657_part8 S step @compose) (g657_part9 S step @compose))))))))))
end DusartFinitePlain


