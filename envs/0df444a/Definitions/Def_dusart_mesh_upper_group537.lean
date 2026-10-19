-- Prove2me | Definitions.Def_dusart_mesh_upper_group537
-- name    : dusart_mesh_upper_group537
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:55:44.512142+00:00
-- url     : https://prove2.me/theorems/1ee81b2c-d639-4c20-b689-2922f6b998f9
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group537_part00
import Definitions.Def_dusart_mesh_upper_group537_part01
import Definitions.Def_dusart_mesh_upper_group537_part02
import Definitions.Def_dusart_mesh_upper_group537_part03
import Definitions.Def_dusart_mesh_upper_group537_part04
import Definitions.Def_dusart_mesh_upper_group537_part05
import Definitions.Def_dusart_mesh_upper_group537_part06
import Definitions.Def_dusart_mesh_upper_group537_part07
import Definitions.Def_dusart_mesh_upper_group537_part08
import Definitions.Def_dusart_mesh_upper_group537_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g537 : DusartNumeric.GenericSpec 7398088960 7414866176 7397998470388378 7414786871743058 := by
 intro S step compose
 exact (compose (g537_part0 S step @compose) (compose (g537_part1 S step @compose) (compose (g537_part2 S step @compose) (compose (g537_part3 S step @compose) (compose (g537_part4 S step @compose) (compose (g537_part5 S step @compose) (compose (g537_part6 S step @compose) (compose (g537_part7 S step @compose) (compose (g537_part8 S step @compose) (g537_part9 S step @compose))))))))))
end DusartFinitePlain


