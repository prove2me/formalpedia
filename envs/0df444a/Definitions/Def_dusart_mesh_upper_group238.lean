-- Prove2me | Definitions.Def_dusart_mesh_upper_group238
-- name    : dusart_mesh_upper_group238
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:03:47.917624+00:00
-- url     : https://prove2.me/theorems/e1a03515-fa45-49e5-9173-c920d0f1f402
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group238_part00
import Definitions.Def_dusart_mesh_upper_group238_part01
import Definitions.Def_dusart_mesh_upper_group238_part02
import Definitions.Def_dusart_mesh_upper_group238_part03
import Definitions.Def_dusart_mesh_upper_group238_part04
import Definitions.Def_dusart_mesh_upper_group238_part05
import Definitions.Def_dusart_mesh_upper_group238_part06
import Definitions.Def_dusart_mesh_upper_group238_part07
import Definitions.Def_dusart_mesh_upper_group238_part08
import Definitions.Def_dusart_mesh_upper_group238_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g238 : DusartNumeric.GenericSpec 2381701376 2398478592 2381651840670648 2398429711850490 := by
 intro S step compose
 exact (compose (g238_part0 S step @compose) (compose (g238_part1 S step @compose) (compose (g238_part2 S step @compose) (compose (g238_part3 S step @compose) (compose (g238_part4 S step @compose) (compose (g238_part5 S step @compose) (compose (g238_part6 S step @compose) (compose (g238_part7 S step @compose) (compose (g238_part8 S step @compose) (g238_part9 S step @compose))))))))))
end DusartFinitePlain
#print axioms DusartFinitePlain.g238


