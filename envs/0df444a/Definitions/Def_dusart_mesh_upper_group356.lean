-- Prove2me | Definitions.Def_dusart_mesh_upper_group356
-- name    : dusart_mesh_upper_group356
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:34:02.143997+00:00
-- url     : https://prove2.me/theorems/5dd6a796-25f5-4e94-bca5-9463797a5444
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group356_part00
import Definitions.Def_dusart_mesh_upper_group356_part01
import Definitions.Def_dusart_mesh_upper_group356_part02
import Definitions.Def_dusart_mesh_upper_group356_part03
import Definitions.Def_dusart_mesh_upper_group356_part04
import Definitions.Def_dusart_mesh_upper_group356_part05
import Definitions.Def_dusart_mesh_upper_group356_part06
import Definitions.Def_dusart_mesh_upper_group356_part07
import Definitions.Def_dusart_mesh_upper_group356_part08
import Definitions.Def_dusart_mesh_upper_group356_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g356 : DusartNumeric.GenericSpec 4361412864 4378190080 4361360155298708 4378143440479471 := by
 intro S step compose
 exact (compose (g356_part0 S step @compose) (compose (g356_part1 S step @compose) (compose (g356_part2 S step @compose) (compose (g356_part3 S step @compose) (compose (g356_part4 S step @compose) (compose (g356_part5 S step @compose) (compose (g356_part6 S step @compose) (compose (g356_part7 S step @compose) (compose (g356_part8 S step @compose) (g356_part9 S step @compose))))))))))
end DusartFinitePlain


