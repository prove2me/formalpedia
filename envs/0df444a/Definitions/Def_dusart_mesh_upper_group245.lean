-- Prove2me | Definitions.Def_dusart_mesh_upper_group245
-- name    : dusart_mesh_upper_group245
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:01:43.832194+00:00
-- url     : https://prove2.me/theorems/1c26d279-2a2d-4c06-b476-3bb9b11a91f1
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group245_part00
import Definitions.Def_dusart_mesh_upper_group245_part01
import Definitions.Def_dusart_mesh_upper_group245_part02
import Definitions.Def_dusart_mesh_upper_group245_part03
import Definitions.Def_dusart_mesh_upper_group245_part04
import Definitions.Def_dusart_mesh_upper_group245_part05
import Definitions.Def_dusart_mesh_upper_group245_part06
import Definitions.Def_dusart_mesh_upper_group245_part07
import Definitions.Def_dusart_mesh_upper_group245_part08
import Definitions.Def_dusart_mesh_upper_group245_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g245 : DusartNumeric.GenericSpec 2499141888 2515919104 2499083701534043 2515867244804953 := by
 intro S step compose
 exact (compose (g245_part0 S step @compose) (compose (g245_part1 S step @compose) (compose (g245_part2 S step @compose) (compose (g245_part3 S step @compose) (compose (g245_part4 S step @compose) (compose (g245_part5 S step @compose) (compose (g245_part6 S step @compose) (compose (g245_part7 S step @compose) (compose (g245_part8 S step @compose) (g245_part9 S step @compose))))))))))
end DusartFinitePlain
#print axioms DusartFinitePlain.g245


