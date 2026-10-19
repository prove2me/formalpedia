-- Prove2me | Definitions.Def_dusart_mesh_upper_group101
-- name    : dusart_mesh_upper_group101
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T22:55:36.738302+00:00
-- url     : https://prove2.me/theorems/2146a635-d5db-4a38-9864-300889609d32
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group101_part00
import Definitions.Def_dusart_mesh_upper_group101_part01
import Definitions.Def_dusart_mesh_upper_group101_part02
import Definitions.Def_dusart_mesh_upper_group101_part03
import Definitions.Def_dusart_mesh_upper_group101_part04
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g101 : DusartNumeric.GenericSpec 443932928 452321536 443916799798832 452304594241221 := by
 intro S step compose
 exact (compose (g101_part0 S step @compose) (compose (g101_part1 S step @compose) (compose (g101_part2 S step @compose) (compose (g101_part3 S step @compose) (g101_part4 S step @compose)))))
end DusartFinitePlain
#print axioms DusartFinitePlain.g101


