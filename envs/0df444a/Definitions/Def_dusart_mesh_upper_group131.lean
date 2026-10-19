-- Prove2me | Definitions.Def_dusart_mesh_upper_group131
-- name    : dusart_mesh_upper_group131
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T22:55:36.649889+00:00
-- url     : https://prove2.me/theorems/700751f0-1158-4986-8773-d36e266ad268
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group131_part00
import Definitions.Def_dusart_mesh_upper_group131_part01
import Definitions.Def_dusart_mesh_upper_group131_part02
import Definitions.Def_dusart_mesh_upper_group131_part03
import Definitions.Def_dusart_mesh_upper_group131_part04
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g131 : DusartNumeric.GenericSpec 695591168 703979776 695575061878447 703961399614935 := by
 intro S step compose
 exact (compose (g131_part0 S step @compose) (compose (g131_part1 S step @compose) (compose (g131_part2 S step @compose) (compose (g131_part3 S step @compose) (g131_part4 S step @compose)))))
end DusartFinitePlain
#print axioms DusartFinitePlain.g131


