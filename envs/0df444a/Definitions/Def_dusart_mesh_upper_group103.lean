-- Prove2me | Definitions.Def_dusart_mesh_upper_group103
-- name    : dusart_mesh_upper_group103
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T22:53:51.464369+00:00
-- url     : https://prove2.me/theorems/45d234b0-e636-4ce9-8e8c-c026c4501630
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group103_part00
import Definitions.Def_dusart_mesh_upper_group103_part01
import Definitions.Def_dusart_mesh_upper_group103_part02
import Definitions.Def_dusart_mesh_upper_group103_part03
import Definitions.Def_dusart_mesh_upper_group103_part04
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g103 : DusartNumeric.GenericSpec 460710144 469098752 460691603070200 469084854459180 := by
 intro S step compose
 exact (compose (g103_part0 S step @compose) (compose (g103_part1 S step @compose) (compose (g103_part2 S step @compose) (compose (g103_part3 S step @compose) (g103_part4 S step @compose)))))
end DusartFinitePlain
#print axioms DusartFinitePlain.g103


