-- Prove2me | Definitions.Def_dusart_mesh_upper_group029
-- name    : dusart_mesh_upper_group029
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T22:51:38.032263+00:00
-- url     : https://prove2.me/theorems/a392f8da-9339-43aa-a472-53d3271f22d4
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group029_part00
import Definitions.Def_dusart_mesh_upper_group029_part01
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g29 : DusartNumeric.GenericSpec 160817408 162914560 160804854096877 162900023398825 := by
 intro S step compose
 exact (compose (g29_part0 S step @compose) (g29_part1 S step @compose))
end DusartFinitePlain
#print axioms DusartFinitePlain.g29


