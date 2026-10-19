-- Prove2me | Definitions.Def_dusart_mesh_upper_group538
-- name    : dusart_mesh_upper_group538
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:57:14.638427+00:00
-- url     : https://prove2.me/theorems/c6c3d01f-77e1-43ba-a809-4ac9f4114b13
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group538_part00
import Definitions.Def_dusart_mesh_upper_group538_part01
import Definitions.Def_dusart_mesh_upper_group538_part02
import Definitions.Def_dusart_mesh_upper_group538_part03
import Definitions.Def_dusart_mesh_upper_group538_part04
import Definitions.Def_dusart_mesh_upper_group538_part05
import Definitions.Def_dusart_mesh_upper_group538_part06
import Definitions.Def_dusart_mesh_upper_group538_part07
import Definitions.Def_dusart_mesh_upper_group538_part08
import Definitions.Def_dusart_mesh_upper_group538_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g538 : DusartNumeric.GenericSpec 7414866176 7431643392 7414786871743058 7431563557371260 := by
 intro S step compose
 exact (compose (g538_part0 S step @compose) (compose (g538_part1 S step @compose) (compose (g538_part2 S step @compose) (compose (g538_part3 S step @compose) (compose (g538_part4 S step @compose) (compose (g538_part5 S step @compose) (compose (g538_part6 S step @compose) (compose (g538_part7 S step @compose) (compose (g538_part8 S step @compose) (g538_part9 S step @compose))))))))))
end DusartFinitePlain


