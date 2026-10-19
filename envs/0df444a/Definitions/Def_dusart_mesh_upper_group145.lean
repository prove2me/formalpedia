-- Prove2me | Definitions.Def_dusart_mesh_upper_group145
-- name    : dusart_mesh_upper_group145
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T22:57:05.159036+00:00
-- url     : https://prove2.me/theorems/b0508eb0-65fb-475c-8669-5ebc362ad749
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group145_part00
import Definitions.Def_dusart_mesh_upper_group145_part01
import Definitions.Def_dusart_mesh_upper_group145_part02
import Definitions.Def_dusart_mesh_upper_group145_part03
import Definitions.Def_dusart_mesh_upper_group145_part04
import Definitions.Def_dusart_mesh_upper_group145_part05
import Definitions.Def_dusart_mesh_upper_group145_part06
import Definitions.Def_dusart_mesh_upper_group145_part07
import Definitions.Def_dusart_mesh_upper_group145_part08
import Definitions.Def_dusart_mesh_upper_group145_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g145 : DusartNumeric.GenericSpec 821420288 838197504 821399771891351 838177896673063 := by
 intro S step compose
 exact (compose (g145_part0 S step @compose) (compose (g145_part1 S step @compose) (compose (g145_part2 S step @compose) (compose (g145_part3 S step @compose) (compose (g145_part4 S step @compose) (compose (g145_part5 S step @compose) (compose (g145_part6 S step @compose) (compose (g145_part7 S step @compose) (compose (g145_part8 S step @compose) (g145_part9 S step @compose))))))))))
end DusartFinitePlain
#print axioms DusartFinitePlain.g145


