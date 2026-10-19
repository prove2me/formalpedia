-- Prove2me | Definitions.Def_dusart_mesh_upper_group073
-- name    : dusart_mesh_upper_group073
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T22:53:21.27868+00:00
-- url     : https://prove2.me/theorems/180d6518-7c1a-4321-9cd5-7555a4ec18cd
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group073_part00
import Definitions.Def_dusart_mesh_upper_group073_part01
import Definitions.Def_dusart_mesh_upper_group073_part02
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g73 : DusartNumeric.GenericSpec 305520896 309715200 305503987964008 309704254147871 := by
 intro S step compose
 exact (compose (g73_part0 S step @compose) (compose (g73_part1 S step @compose) (g73_part2 S step @compose)))
end DusartFinitePlain
#print axioms DusartFinitePlain.g73


