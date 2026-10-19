-- Prove2me | Definitions.Def_dusart_mesh_upper_group530
-- name    : dusart_mesh_upper_group530
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:56:30.128865+00:00
-- url     : https://prove2.me/theorems/efca766e-1e82-46d6-bcfd-66fef8d358b2
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group530_part00
import Definitions.Def_dusart_mesh_upper_group530_part01
import Definitions.Def_dusart_mesh_upper_group530_part02
import Definitions.Def_dusart_mesh_upper_group530_part03
import Definitions.Def_dusart_mesh_upper_group530_part04
import Definitions.Def_dusart_mesh_upper_group530_part05
import Definitions.Def_dusart_mesh_upper_group530_part06
import Definitions.Def_dusart_mesh_upper_group530_part07
import Definitions.Def_dusart_mesh_upper_group530_part08
import Definitions.Def_dusart_mesh_upper_group530_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g530 : DusartNumeric.GenericSpec 7280648448 7297425664 7280565266332884 7297332617577867 := by
 intro S step compose
 exact (compose (g530_part0 S step @compose) (compose (g530_part1 S step @compose) (compose (g530_part2 S step @compose) (compose (g530_part3 S step @compose) (compose (g530_part4 S step @compose) (compose (g530_part5 S step @compose) (compose (g530_part6 S step @compose) (compose (g530_part7 S step @compose) (compose (g530_part8 S step @compose) (g530_part9 S step @compose))))))))))
end DusartFinitePlain


