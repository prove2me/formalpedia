-- Prove2me | solution 1 for AlgebraicCurve.Place.taylorRem_eq_mul_inv_pow_of_forall_taylorCoeff_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/738be6ff-676e-5c98-9532-1df807778d9d

import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_taylorRem_eq_mul_inv_pow_of_forall_taylorCoeff_eq_zero

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Place

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (t f : F) {e : ℕ} (h : ∀ q, q < e → taylorCoeff v t q f = 0) :
    taylorRem v t f e = f * t⁻¹ ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [taylorRem_succ', h e (Nat.lt_succ_self e), map_zero, sub_zero,
      ih (fun q hq => h q (Nat.lt_succ_of_lt hq)), pow_succ, mul_assoc]

end S_AlgebraicCurve_Place_taylorRem_eq_mul_inv_pow_of_forall_taylorCoeff_eq_zero
end P2MW
export P2MW.S_AlgebraicCurve_Place_taylorRem_eq_mul_inv_pow_of_forall_taylorCoeff_eq_zero (solution)
