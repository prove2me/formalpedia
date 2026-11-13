-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F006
-- name    : ProbabilityTheory_chapter_01_thm_1_2_F006
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:53:46.346666+00:00
-- url     : https://prove2.me/theorems/1378d41c-06ee-471e-95ad-942bcbd89897
-- title:
--   Chapter 1, thm_1_2: supporting Lean bundle F006
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `thm_1_2`: `lowerStep_le_tag`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_2.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F000
import Mathlib.Tactic

open scoped BigOperators Pointwise

open Finset Set

noncomputable section Thm_1_2

namespace DarbouxRS

lemma lowerStep_le_tag {a b : ℝ} {f : ℝ → ℝ}
    (P : Partition a b) (i : Fin P.n)
    (hfBelow : BddBelow (f '' Set.Icc a b))
    {x : ℝ} (hx : x ∈ Partition.subinterval P i) :
    lowerStep P f i ≤ f x := by
  have hcellBelow : BddBelow (f '' Partition.subinterval P i) :=
    BddBelow.mono
      (Set.image_mono (subinterval_subset_Icc_core P))
      hfBelow
  unfold lowerStep
  exact csInf_le hcellBelow ⟨x, hx, rfl⟩

end DarbouxRS

end Thm_1_2

noncomputable section Darboux_fundamental_result

namespace Refinement

end Refinement

namespace Partition

end Partition

end Darboux_fundamental_result


