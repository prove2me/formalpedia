-- Prove2me | Definitions.Def_dusart_mesh_upper_group251
-- name    : dusart_mesh_upper_group251
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:03:28.858592+00:00
-- url     : https://prove2.me/theorems/b0de8032-6a9c-4953-98ef-d4547036134c
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group251_part00
import Definitions.Def_dusart_mesh_upper_group251_part01
import Definitions.Def_dusart_mesh_upper_group251_part02
import Definitions.Def_dusart_mesh_upper_group251_part03
import Definitions.Def_dusart_mesh_upper_group251_part04
import Definitions.Def_dusart_mesh_upper_group251_part05
import Definitions.Def_dusart_mesh_upper_group251_part06
import Definitions.Def_dusart_mesh_upper_group251_part07
import Definitions.Def_dusart_mesh_upper_group251_part08
import Definitions.Def_dusart_mesh_upper_group251_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g251 : DusartNumeric.GenericSpec 2599805184 2616582400 2599787636627402 2616552440330254 := by
 intro S step compose
 exact (compose (g251_part0 S step @compose) (compose (g251_part1 S step @compose) (compose (g251_part2 S step @compose) (compose (g251_part3 S step @compose) (compose (g251_part4 S step @compose) (compose (g251_part5 S step @compose) (compose (g251_part6 S step @compose) (compose (g251_part7 S step @compose) (compose (g251_part8 S step @compose) (g251_part9 S step @compose))))))))))
end DusartFinitePlain
#print axioms DusartFinitePlain.g251


