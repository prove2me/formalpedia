-- Prove2me | Definitions.Def_dusart_mesh_upper_group048
-- name    : dusart_mesh_upper_group048
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T22:52:52.565392+00:00
-- url     : https://prove2.me/theorems/c13940ba-d155-4b61-aa30-dc8f8be8070b
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group048_part00
import Definitions.Def_dusart_mesh_upper_group048_part01
import Definitions.Def_dusart_mesh_upper_group048_part02
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g48 : DusartNumeric.GenericSpec 200663296 204857600 200649157625116 204843737672861 := by
 intro S step compose
 exact (compose (g48_part0 S step @compose) (compose (g48_part1 S step @compose) (g48_part2 S step @compose)))
end DusartFinitePlain
#print axioms DusartFinitePlain.g48


