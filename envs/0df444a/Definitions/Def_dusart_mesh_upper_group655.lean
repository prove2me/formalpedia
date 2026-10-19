-- Prove2me | Definitions.Def_dusart_mesh_upper_group655
-- name    : dusart_mesh_upper_group655
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-17T00:10:46.974973+00:00
-- url     : https://prove2.me/theorems/6a3b0d05-884c-4e31-b5d7-8e9d18d1bbdb
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group655_part00
import Definitions.Def_dusart_mesh_upper_group655_part01
import Definitions.Def_dusart_mesh_upper_group655_part02
import Definitions.Def_dusart_mesh_upper_group655_part03
import Definitions.Def_dusart_mesh_upper_group655_part04
import Definitions.Def_dusart_mesh_upper_group655_part05
import Definitions.Def_dusart_mesh_upper_group655_part06
import Definitions.Def_dusart_mesh_upper_group655_part07
import Definitions.Def_dusart_mesh_upper_group655_part08
import Definitions.Def_dusart_mesh_upper_group655_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g655 : DusartNumeric.GenericSpec 9377800448 9394577664 9377698979977643 9394490159695874 := by
 intro S step compose
 exact (compose (g655_part0 S step @compose) (compose (g655_part1 S step @compose) (compose (g655_part2 S step @compose) (compose (g655_part3 S step @compose) (compose (g655_part4 S step @compose) (compose (g655_part5 S step @compose) (compose (g655_part6 S step @compose) (compose (g655_part7 S step @compose) (compose (g655_part8 S step @compose) (g655_part9 S step @compose))))))))))
end DusartFinitePlain


