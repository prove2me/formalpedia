-- Prove2me | solution 1 for AlgebraicCurve.Divisor.evalFun_zsmul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/eadcb4a1-ca56-546b-b913-e134813d2bcd

import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Divisor_evalFun_zsmul

open AlgebraicCurve AlgebraicCurve.Divisor

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (f : F) (D : Divisor K F) (n : ℤ) : Divisor.evalFun f (n • D) = Divisor.evalFun f D ^ n := by
  rw [show evalFun f (n • D) = ∏ v ∈ D.support, v.evalAt f ^ ((n • D) v) from
      Finsupp.prod_of_support_subset _ Finsupp.support_smul _ fun v _ => zpow_zero _,
    evalFun_def, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul, mul_comm n (D v), zpow_mul]

end S_AlgebraicCurve_Divisor_evalFun_zsmul
end P2MW
export P2MW.S_AlgebraicCurve_Divisor_evalFun_zsmul (solution)
