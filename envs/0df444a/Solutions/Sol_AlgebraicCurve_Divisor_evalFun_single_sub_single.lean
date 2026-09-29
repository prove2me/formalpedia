-- Prove2me | solution 1 for AlgebraicCurve.Divisor.evalFun_single_sub_single
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/ed888c75-a761-5ed9-a1e8-63d520b1acb7

import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_AlgebraicCurve_Divisor_evalFun_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Divisor_evalFun_single_sub_single

open AlgebraicCurve AlgebraicCurve.Divisor

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (f : F) {v₁ v₂ : Place K F} (h₁ : v₁.evalAt f ≠ 0) (h₂ : v₂.evalAt f ≠ 0) : Divisor.evalFun f (Finsupp.single v₁ 1 + Finsupp.single v₂ (-1)) = v₁.evalAt f / v₂.evalAt f := by
  have hsupp : ∀ (w : Place K F) (n : ℤ), w.evalAt f ≠ 0 →
      ∀ v ∈ (Finsupp.single w n).support, Place.evalAt v f ≠ 0 := by
    intro w n hw v hv
    have := Finsupp.support_single_subset hv
    rw [Finset.mem_singleton] at this
    rw [this]
    exact hw
  rw [AlgebraicCurve.Divisor.evalFun_add f (hsupp v₁ 1 h₁) (hsupp v₂ (-1) h₂), evalFun_single, evalFun_single,
    zpow_one, zpow_neg_one, div_eq_mul_inv]

end S_AlgebraicCurve_Divisor_evalFun_single_sub_single
end P2MW
export P2MW.S_AlgebraicCurve_Divisor_evalFun_single_sub_single (solution)
