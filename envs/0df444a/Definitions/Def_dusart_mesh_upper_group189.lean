-- Prove2me | Definitions.Def_dusart_mesh_upper_group189
-- name    : dusart_mesh_upper_group189
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T22:57:49.9646+00:00
-- url     : https://prove2.me/theorems/b4ebdfb3-a375-4298-890b-5d5136c08924
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group189_part00
import Definitions.Def_dusart_mesh_upper_group189_part01
import Definitions.Def_dusart_mesh_upper_group189_part02
import Definitions.Def_dusart_mesh_upper_group189_part03
import Definitions.Def_dusart_mesh_upper_group189_part04
import Definitions.Def_dusart_mesh_upper_group189_part05
import Definitions.Def_dusart_mesh_upper_group189_part06
import Definitions.Def_dusart_mesh_upper_group189_part07
import Definitions.Def_dusart_mesh_upper_group189_part08
import Definitions.Def_dusart_mesh_upper_group189_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g189 : DusartNumeric.GenericSpec 1559617792 1576395008 1559595749109272 1576356499225903 := by
 intro S step compose
 exact (compose (g189_part0 S step @compose) (compose (g189_part1 S step @compose) (compose (g189_part2 S step @compose) (compose (g189_part3 S step @compose) (compose (g189_part4 S step @compose) (compose (g189_part5 S step @compose) (compose (g189_part6 S step @compose) (compose (g189_part7 S step @compose) (compose (g189_part8 S step @compose) (g189_part9 S step @compose))))))))))
end DusartFinitePlain
#print axioms DusartFinitePlain.g189


