-- Prove2me | Definitions.Def_dusart_mesh_upper_group209
-- name    : dusart_mesh_upper_group209
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:04:16.415949+00:00
-- url     : https://prove2.me/theorems/57939ce6-c244-4e44-93e4-ae39e2a10b4e
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group209_part00
import Definitions.Def_dusart_mesh_upper_group209_part01
import Definitions.Def_dusart_mesh_upper_group209_part02
import Definitions.Def_dusart_mesh_upper_group209_part03
import Definitions.Def_dusart_mesh_upper_group209_part04
import Definitions.Def_dusart_mesh_upper_group209_part05
import Definitions.Def_dusart_mesh_upper_group209_part06
import Definitions.Def_dusart_mesh_upper_group209_part07
import Definitions.Def_dusart_mesh_upper_group209_part08
import Definitions.Def_dusart_mesh_upper_group209_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g209 : DusartNumeric.GenericSpec 1895162112 1911939328 1895112577348767 1911891082943374 := by
 intro S step compose
 exact (compose (g209_part0 S step @compose) (compose (g209_part1 S step @compose) (compose (g209_part2 S step @compose) (compose (g209_part3 S step @compose) (compose (g209_part4 S step @compose) (compose (g209_part5 S step @compose) (compose (g209_part6 S step @compose) (compose (g209_part7 S step @compose) (compose (g209_part8 S step @compose) (g209_part9 S step @compose))))))))))
end DusartFinitePlain
#print axioms DusartFinitePlain.g209


