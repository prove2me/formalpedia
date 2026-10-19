-- Prove2me | Definitions.Def_dusart_mesh_upper_group134
-- name    : dusart_mesh_upper_group134
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T22:55:38.44121+00:00
-- url     : https://prove2.me/theorems/976b13a4-4a5d-4169-ac3a-0b467916bc82
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group134_part00
import Definitions.Def_dusart_mesh_upper_group134_part01
import Definitions.Def_dusart_mesh_upper_group134_part02
import Definitions.Def_dusart_mesh_upper_group134_part03
import Definitions.Def_dusart_mesh_upper_group134_part04
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g134 : DusartNumeric.GenericSpec 720756992 729145600 720735444082394 729122699391182 := by
 intro S step compose
 exact (compose (g134_part0 S step @compose) (compose (g134_part1 S step @compose) (compose (g134_part2 S step @compose) (compose (g134_part3 S step @compose) (g134_part4 S step @compose)))))
end DusartFinitePlain
#print axioms DusartFinitePlain.g134


