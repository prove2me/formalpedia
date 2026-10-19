-- Prove2me | Definitions.Def_dusart_mesh_upper_group202
-- name    : dusart_mesh_upper_group202
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:03:56.638018+00:00
-- url     : https://prove2.me/theorems/ab21a94e-e096-4bde-b60b-51722ae9f008
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group202_part00
import Definitions.Def_dusart_mesh_upper_group202_part01
import Definitions.Def_dusart_mesh_upper_group202_part02
import Definitions.Def_dusart_mesh_upper_group202_part03
import Definitions.Def_dusart_mesh_upper_group202_part04
import Definitions.Def_dusart_mesh_upper_group202_part05
import Definitions.Def_dusart_mesh_upper_group202_part06
import Definitions.Def_dusart_mesh_upper_group202_part07
import Definitions.Def_dusart_mesh_upper_group202_part08
import Definitions.Def_dusart_mesh_upper_group202_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g202 : DusartNumeric.GenericSpec 1777721600 1794498816 1777681838997207 1794465260341457 := by
 intro S step compose
 exact (compose (g202_part0 S step @compose) (compose (g202_part1 S step @compose) (compose (g202_part2 S step @compose) (compose (g202_part3 S step @compose) (compose (g202_part4 S step @compose) (compose (g202_part5 S step @compose) (compose (g202_part6 S step @compose) (compose (g202_part7 S step @compose) (compose (g202_part8 S step @compose) (g202_part9 S step @compose))))))))))
end DusartFinitePlain
#print axioms DusartFinitePlain.g202


