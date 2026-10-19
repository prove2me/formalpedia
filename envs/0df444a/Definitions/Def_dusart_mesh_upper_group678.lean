-- Prove2me | Definitions.Def_dusart_mesh_upper_group678
-- name    : dusart_mesh_upper_group678
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-17T00:16:26.909837+00:00
-- url     : https://prove2.me/theorems/d99e8c02-2f49-43f0-9580-36b0e27b8411
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group678_part00
import Definitions.Def_dusart_mesh_upper_group678_part01
import Definitions.Def_dusart_mesh_upper_group678_part02
import Definitions.Def_dusart_mesh_upper_group678_part03
import Definitions.Def_dusart_mesh_upper_group678_part04
import Definitions.Def_dusart_mesh_upper_group678_part05
import Definitions.Def_dusart_mesh_upper_group678_part06
import Definitions.Def_dusart_mesh_upper_group678_part07
import Definitions.Def_dusart_mesh_upper_group678_part08
import Definitions.Def_dusart_mesh_upper_group678_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g678 : DusartNumeric.GenericSpec 9763676416 9780453632 9763621668972664 9780401294627483 := by
 intro S step compose
 exact (compose (g678_part0 S step @compose) (compose (g678_part1 S step @compose) (compose (g678_part2 S step @compose) (compose (g678_part3 S step @compose) (compose (g678_part4 S step @compose) (compose (g678_part5 S step @compose) (compose (g678_part6 S step @compose) (compose (g678_part7 S step @compose) (compose (g678_part8 S step @compose) (g678_part9 S step @compose))))))))))
end DusartFinitePlain


