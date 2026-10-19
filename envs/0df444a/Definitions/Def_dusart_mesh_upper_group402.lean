-- Prove2me | Definitions.Def_dusart_mesh_upper_group402
-- name    : dusart_mesh_upper_group402
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:40:42.827503+00:00
-- url     : https://prove2.me/theorems/3d9408db-014d-4541-8230-080f769780ca
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group402_part00
import Definitions.Def_dusart_mesh_upper_group402_part01
import Definitions.Def_dusart_mesh_upper_group402_part02
import Definitions.Def_dusart_mesh_upper_group402_part03
import Definitions.Def_dusart_mesh_upper_group402_part04
import Definitions.Def_dusart_mesh_upper_group402_part05
import Definitions.Def_dusart_mesh_upper_group402_part06
import Definitions.Def_dusart_mesh_upper_group402_part07
import Definitions.Def_dusart_mesh_upper_group402_part08
import Definitions.Def_dusart_mesh_upper_group402_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g402 : DusartNumeric.GenericSpec 5133164800 5149942016 5133086539280327 5149866295198825 := by
 intro S step compose
 exact (compose (g402_part0 S step @compose) (compose (g402_part1 S step @compose) (compose (g402_part2 S step @compose) (compose (g402_part3 S step @compose) (compose (g402_part4 S step @compose) (compose (g402_part5 S step @compose) (compose (g402_part6 S step @compose) (compose (g402_part7 S step @compose) (compose (g402_part8 S step @compose) (g402_part9 S step @compose))))))))))
end DusartFinitePlain


