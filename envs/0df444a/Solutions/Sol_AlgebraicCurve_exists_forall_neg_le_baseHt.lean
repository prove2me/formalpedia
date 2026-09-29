-- Prove2me | solution 1 for AlgebraicCurve.exists_forall_neg_le_baseHt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/f82042e3-de17-5b53-a9a6-208c91db2fed

import Definitions.Def_ModularCurve_JZeroHeightForm
import Theorems.Thm_AlgebraicCurve_exists_forall_neg_le_pairHt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_forall_neg_le_baseHt

set_option autoImplicit false

open AlgebraicCurve

theorem solution {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]
    {r : ℕ} (s : Fin r → F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b v : Place (AlgebraicClosure ℚ) F, -C ≤ baseHt s b v := by
  classical
  obtain ⟨C, hC0, hC⟩ := AlgebraicCurve.exists_forall_neg_le_pairHt s
  refine ⟨C, hC0, fun b v => ?_⟩
  unfold baseHt
  split_ifs with h
  · linarith
  · exact hC v b

end S_AlgebraicCurve_exists_forall_neg_le_baseHt
end P2MW
export P2MW.S_AlgebraicCurve_exists_forall_neg_le_baseHt (solution)
