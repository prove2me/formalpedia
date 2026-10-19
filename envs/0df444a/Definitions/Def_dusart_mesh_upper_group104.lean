-- Prove2me | Definitions.Def_dusart_mesh_upper_group104
-- name    : dusart_mesh_upper_group104
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T22:53:32.10121+00:00
-- url     : https://prove2.me/theorems/748b8050-1cbc-4fd4-ac9b-f528d148c0cf
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group104_part00
import Definitions.Def_dusart_mesh_upper_group104_part01
import Definitions.Def_dusart_mesh_upper_group104_part02
import Definitions.Def_dusart_mesh_upper_group104_part03
import Definitions.Def_dusart_mesh_upper_group104_part04
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g104 : DusartNumeric.GenericSpec 469098752 477487360 469084854459180 477468388845449 := by
 intro S step compose
 exact (compose (g104_part0 S step @compose) (compose (g104_part1 S step @compose) (compose (g104_part2 S step @compose) (compose (g104_part3 S step @compose) (g104_part4 S step @compose)))))
end DusartFinitePlain
#print axioms DusartFinitePlain.g104


