-- Prove2me | Definitions.Def_dusart_mesh_upper_group272
-- name    : dusart_mesh_upper_group272
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:08:38.314642+00:00
-- url     : https://prove2.me/theorems/424f6191-b180-49a8-ac03-e941d9e2043f
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group272_part00
import Definitions.Def_dusart_mesh_upper_group272_part01
import Definitions.Def_dusart_mesh_upper_group272_part02
import Definitions.Def_dusart_mesh_upper_group272_part03
import Definitions.Def_dusart_mesh_upper_group272_part04
import Definitions.Def_dusart_mesh_upper_group272_part05
import Definitions.Def_dusart_mesh_upper_group272_part06
import Definitions.Def_dusart_mesh_upper_group272_part07
import Definitions.Def_dusart_mesh_upper_group272_part08
import Definitions.Def_dusart_mesh_upper_group272_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g272 : DusartNumeric.GenericSpec 2952126720 2968903936 2952090443107997 2968860180781066 := by
 intro S step compose
 exact (compose (g272_part0 S step @compose) (compose (g272_part1 S step @compose) (compose (g272_part2 S step @compose) (compose (g272_part3 S step @compose) (compose (g272_part4 S step @compose) (compose (g272_part5 S step @compose) (compose (g272_part6 S step @compose) (compose (g272_part7 S step @compose) (compose (g272_part8 S step @compose) (g272_part9 S step @compose))))))))))
end DusartFinitePlain
#print axioms DusartFinitePlain.g272


