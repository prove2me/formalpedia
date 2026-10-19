-- Prove2me | Definitions.Def_dusart_mesh_upper_group177
-- name    : dusart_mesh_upper_group177
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T22:59:56.30003+00:00
-- url     : https://prove2.me/theorems/d547931d-1eac-447f-9f17-7dcc474fe5e8
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group177_part00
import Definitions.Def_dusart_mesh_upper_group177_part01
import Definitions.Def_dusart_mesh_upper_group177_part02
import Definitions.Def_dusart_mesh_upper_group177_part03
import Definitions.Def_dusart_mesh_upper_group177_part04
import Definitions.Def_dusart_mesh_upper_group177_part05
import Definitions.Def_dusart_mesh_upper_group177_part06
import Definitions.Def_dusart_mesh_upper_group177_part07
import Definitions.Def_dusart_mesh_upper_group177_part08
import Definitions.Def_dusart_mesh_upper_group177_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g177 : DusartNumeric.GenericSpec 1358291200 1375068416 1358264169415383 1375037742016640 := by
 intro S step compose
 exact (compose (g177_part0 S step @compose) (compose (g177_part1 S step @compose) (compose (g177_part2 S step @compose) (compose (g177_part3 S step @compose) (compose (g177_part4 S step @compose) (compose (g177_part5 S step @compose) (compose (g177_part6 S step @compose) (compose (g177_part7 S step @compose) (compose (g177_part8 S step @compose) (g177_part9 S step @compose))))))))))
end DusartFinitePlain
#print axioms DusartFinitePlain.g177


