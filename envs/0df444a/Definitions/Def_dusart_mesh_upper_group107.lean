-- Prove2me | Definitions.Def_dusart_mesh_upper_group107
-- name    : dusart_mesh_upper_group107
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T22:55:59.470441+00:00
-- url     : https://prove2.me/theorems/a025cc2f-6285-40b0-a800-7985de76abd1
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group107_part00
import Definitions.Def_dusart_mesh_upper_group107_part01
import Definitions.Def_dusart_mesh_upper_group107_part02
import Definitions.Def_dusart_mesh_upper_group107_part03
import Definitions.Def_dusart_mesh_upper_group107_part04
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g107 : DusartNumeric.GenericSpec 494264576 502653184 494249080063817 502634065851743 := by
 intro S step compose
 exact (compose (g107_part0 S step @compose) (compose (g107_part1 S step @compose) (compose (g107_part2 S step @compose) (compose (g107_part3 S step @compose) (g107_part4 S step @compose)))))
end DusartFinitePlain
#print axioms DusartFinitePlain.g107


