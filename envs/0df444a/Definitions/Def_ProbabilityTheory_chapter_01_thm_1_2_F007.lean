-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F007
-- name    : ProbabilityTheory_chapter_01_thm_1_2_F007
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:53:57.665064+00:00
-- url     : https://prove2.me/theorems/74f7afaf-1ac1-4b9c-953d-d0a17db5d43f
-- title:
--   Chapter 1, thm_1_2: supporting Lean bundle F007
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `thm_1_2`: `tag_le_upperStep`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_2.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F000
import Mathlib.Tactic

open scoped BigOperators Pointwise

open Finset Set

noncomputable section Thm_1_2

namespace DarbouxRS

lemma tag_le_upperStep {a b : ℝ} {f : ℝ → ℝ}
    (P : Partition a b) (i : Fin P.n)
    (hfAbove : BddAbove (f '' Set.Icc a b))
    {x : ℝ} (hx : x ∈ Partition.subinterval P i) :
    f x ≤ upperStep P f i := by
  have hcellAbove : BddAbove (f '' Partition.subinterval P i) :=
    BddAbove.mono
      (Set.image_mono (subinterval_subset_Icc_core P))
      hfAbove
  unfold upperStep
  exact le_csSup hcellAbove ⟨x, hx, rfl⟩
end DarbouxRS

end Thm_1_2

noncomputable section Darboux_fundamental_result

namespace Refinement

end Refinement

namespace Partition

end Partition

end Darboux_fundamental_result


