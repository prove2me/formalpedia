-- Prove2me | Definitions.Def_dusart_mesh_upper_group484
-- name    : dusart_mesh_upper_group484
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:52:46.158981+00:00
-- url     : https://prove2.me/theorems/09bd69da-2cd7-41b7-8bff-2372e085e5c7
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group484_part00
import Definitions.Def_dusart_mesh_upper_group484_part01
import Definitions.Def_dusart_mesh_upper_group484_part02
import Definitions.Def_dusart_mesh_upper_group484_part03
import Definitions.Def_dusart_mesh_upper_group484_part04
import Definitions.Def_dusart_mesh_upper_group484_part05
import Definitions.Def_dusart_mesh_upper_group484_part06
import Definitions.Def_dusart_mesh_upper_group484_part07
import Definitions.Def_dusart_mesh_upper_group484_part08
import Definitions.Def_dusart_mesh_upper_group484_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g484 : DusartNumeric.GenericSpec 6508896512 6525673728 6508809854856894 6525602548389890 := by
 intro S step compose
 exact (compose (g484_part0 S step @compose) (compose (g484_part1 S step @compose) (compose (g484_part2 S step @compose) (compose (g484_part3 S step @compose) (compose (g484_part4 S step @compose) (compose (g484_part5 S step @compose) (compose (g484_part6 S step @compose) (compose (g484_part7 S step @compose) (compose (g484_part8 S step @compose) (g484_part9 S step @compose))))))))))
end DusartFinitePlain


