-- Prove2me | Definitions.Def_dusart_mesh_upper_group114
-- name    : dusart_mesh_upper_group114
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T22:54:51.937719+00:00
-- url     : https://prove2.me/theorems/91f2d25e-1a44-4289-88f9-a75d55890eb2
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group114_part00
import Definitions.Def_dusart_mesh_upper_group114_part01
import Definitions.Def_dusart_mesh_upper_group114_part02
import Definitions.Def_dusart_mesh_upper_group114_part03
import Definitions.Def_dusart_mesh_upper_group114_part04
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g114 : DusartNumeric.GenericSpec 552984832 561373440 552963477152353 561346317415022 := by
 intro S step compose
 exact (compose (g114_part0 S step @compose) (compose (g114_part1 S step @compose) (compose (g114_part2 S step @compose) (compose (g114_part3 S step @compose) (g114_part4 S step @compose)))))
end DusartFinitePlain
#print axioms DusartFinitePlain.g114


