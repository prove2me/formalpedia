-- Prove2me | Definitions.Def_dusart_mesh_upper_group414
-- name    : dusart_mesh_upper_group414
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:43:01.66905+00:00
-- url     : https://prove2.me/theorems/9a4cf98e-9309-46e5-9baa-c665cd387058
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group414_part00
import Definitions.Def_dusart_mesh_upper_group414_part01
import Definitions.Def_dusart_mesh_upper_group414_part02
import Definitions.Def_dusart_mesh_upper_group414_part03
import Definitions.Def_dusart_mesh_upper_group414_part04
import Definitions.Def_dusart_mesh_upper_group414_part05
import Definitions.Def_dusart_mesh_upper_group414_part06
import Definitions.Def_dusart_mesh_upper_group414_part07
import Definitions.Def_dusart_mesh_upper_group414_part08
import Definitions.Def_dusart_mesh_upper_group414_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g414 : DusartNumeric.GenericSpec 5334491392 5351268608 5334411725302886 5351192999739227 := by
 intro S step compose
 exact (compose (g414_part0 S step @compose) (compose (g414_part1 S step @compose) (compose (g414_part2 S step @compose) (compose (g414_part3 S step @compose) (compose (g414_part4 S step @compose) (compose (g414_part5 S step @compose) (compose (g414_part6 S step @compose) (compose (g414_part7 S step @compose) (compose (g414_part8 S step @compose) (g414_part9 S step @compose))))))))))
end DusartFinitePlain


