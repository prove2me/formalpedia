-- Prove2me | Definitions.Def_dusart_mesh_upper_group199
-- name    : dusart_mesh_upper_group199
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:02:46.9937+00:00
-- url     : https://prove2.me/theorems/ac40b150-9d73-4b3b-93ac-b460289f9cc4
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group199_part00
import Definitions.Def_dusart_mesh_upper_group199_part01
import Definitions.Def_dusart_mesh_upper_group199_part02
import Definitions.Def_dusart_mesh_upper_group199_part03
import Definitions.Def_dusart_mesh_upper_group199_part04
import Definitions.Def_dusart_mesh_upper_group199_part05
import Definitions.Def_dusart_mesh_upper_group199_part06
import Definitions.Def_dusart_mesh_upper_group199_part07
import Definitions.Def_dusart_mesh_upper_group199_part08
import Definitions.Def_dusart_mesh_upper_group199_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g199 : DusartNumeric.GenericSpec 1727389952 1744167168 1727361722337772 1744130242829047 := by
 intro S step compose
 exact (compose (g199_part0 S step @compose) (compose (g199_part1 S step @compose) (compose (g199_part2 S step @compose) (compose (g199_part3 S step @compose) (compose (g199_part4 S step @compose) (compose (g199_part5 S step @compose) (compose (g199_part6 S step @compose) (compose (g199_part7 S step @compose) (compose (g199_part8 S step @compose) (g199_part9 S step @compose))))))))))
end DusartFinitePlain
#print axioms DusartFinitePlain.g199


