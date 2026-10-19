-- Prove2me | Definitions.Def_dusart_mesh_upper_group169
-- name    : dusart_mesh_upper_group169
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T22:59:29.947798+00:00
-- url     : https://prove2.me/theorems/f25d141b-3d5c-4dee-b2ad-bf7cad40cb66
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group169_part00
import Definitions.Def_dusart_mesh_upper_group169_part01
import Definitions.Def_dusart_mesh_upper_group169_part02
import Definitions.Def_dusart_mesh_upper_group169_part03
import Definitions.Def_dusart_mesh_upper_group169_part04
import Definitions.Def_dusart_mesh_upper_group169_part05
import Definitions.Def_dusart_mesh_upper_group169_part06
import Definitions.Def_dusart_mesh_upper_group169_part07
import Definitions.Def_dusart_mesh_upper_group169_part08
import Definitions.Def_dusart_mesh_upper_group169_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g169 : DusartNumeric.GenericSpec 1224073472 1240850688 1224038429973267 1240804140420313 := by
 intro S step compose
 exact (compose (g169_part0 S step @compose) (compose (g169_part1 S step @compose) (compose (g169_part2 S step @compose) (compose (g169_part3 S step @compose) (compose (g169_part4 S step @compose) (compose (g169_part5 S step @compose) (compose (g169_part6 S step @compose) (compose (g169_part7 S step @compose) (compose (g169_part8 S step @compose) (g169_part9 S step @compose))))))))))
end DusartFinitePlain
#print axioms DusartFinitePlain.g169


