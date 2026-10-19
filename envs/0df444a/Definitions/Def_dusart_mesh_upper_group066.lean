-- Prove2me | Definitions.Def_dusart_mesh_upper_group066
-- name    : dusart_mesh_upper_group066
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T22:54:14.905982+00:00
-- url     : https://prove2.me/theorems/95b41d23-7296-4cce-a93b-e2392de4cfbf
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group066_part00
import Definitions.Def_dusart_mesh_upper_group066_part01
import Definitions.Def_dusart_mesh_upper_group066_part02
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g66 : DusartNumeric.GenericSpec 276160768 280355072 276146296237433 280343127555749 := by
 intro S step compose
 exact (compose (g66_part0 S step @compose) (compose (g66_part1 S step @compose) (g66_part2 S step @compose)))
end DusartFinitePlain
#print axioms DusartFinitePlain.g66


