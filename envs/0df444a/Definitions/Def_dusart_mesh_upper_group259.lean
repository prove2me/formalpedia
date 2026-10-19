-- Prove2me | Definitions.Def_dusart_mesh_upper_group259
-- name    : dusart_mesh_upper_group259
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:06:49.057139+00:00
-- url     : https://prove2.me/theorems/fb7bd83e-0922-4317-a3e4-42616dd5befb
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group259_part00
import Definitions.Def_dusart_mesh_upper_group259_part01
import Definitions.Def_dusart_mesh_upper_group259_part02
import Definitions.Def_dusart_mesh_upper_group259_part03
import Definitions.Def_dusart_mesh_upper_group259_part04
import Definitions.Def_dusart_mesh_upper_group259_part05
import Definitions.Def_dusart_mesh_upper_group259_part06
import Definitions.Def_dusart_mesh_upper_group259_part07
import Definitions.Def_dusart_mesh_upper_group259_part08
import Definitions.Def_dusart_mesh_upper_group259_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g259 : DusartNumeric.GenericSpec 2734022912 2750800128 2733978841949255 2750744977759491 := by
 intro S step compose
 exact (compose (g259_part0 S step @compose) (compose (g259_part1 S step @compose) (compose (g259_part2 S step @compose) (compose (g259_part3 S step @compose) (compose (g259_part4 S step @compose) (compose (g259_part5 S step @compose) (compose (g259_part6 S step @compose) (compose (g259_part7 S step @compose) (compose (g259_part8 S step @compose) (g259_part9 S step @compose))))))))))
end DusartFinitePlain
#print axioms DusartFinitePlain.g259


