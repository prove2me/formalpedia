-- Prove2me | Definitions.Def_dusart_mesh_upper_group611
-- name    : dusart_mesh_upper_group611
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-17T00:03:28.828157+00:00
-- url     : https://prove2.me/theorems/66148ebc-be4a-420d-a638-0a251e6e9454
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group611_part00
import Definitions.Def_dusart_mesh_upper_group611_part01
import Definitions.Def_dusart_mesh_upper_group611_part02
import Definitions.Def_dusart_mesh_upper_group611_part03
import Definitions.Def_dusart_mesh_upper_group611_part04
import Definitions.Def_dusart_mesh_upper_group611_part05
import Definitions.Def_dusart_mesh_upper_group611_part06
import Definitions.Def_dusart_mesh_upper_group611_part07
import Definitions.Def_dusart_mesh_upper_group611_part08
import Definitions.Def_dusart_mesh_upper_group611_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g611 : DusartNumeric.GenericSpec 8639602944 8656380160 8639535176784722 8656310595611643 := by
 intro S step compose
 exact (compose (g611_part0 S step @compose) (compose (g611_part1 S step @compose) (compose (g611_part2 S step @compose) (compose (g611_part3 S step @compose) (compose (g611_part4 S step @compose) (compose (g611_part5 S step @compose) (compose (g611_part6 S step @compose) (compose (g611_part7 S step @compose) (compose (g611_part8 S step @compose) (g611_part9 S step @compose))))))))))
end DusartFinitePlain


