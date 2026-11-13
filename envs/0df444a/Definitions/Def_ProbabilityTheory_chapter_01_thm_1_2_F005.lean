-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F005
-- name    : ProbabilityTheory_chapter_01_thm_1_2_F005
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:53:28.804907+00:00
-- url     : https://prove2.me/theorems/e945ced0-4e61-427c-8150-8375bbff1b81
-- title:
--   Chapter 1, thm_1_2: supporting Lean bundle F005
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `thm_1_2`: `tag_mem_Icc_of_tagsInPartition_core`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_2.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F000
import Mathlib.Tactic

open scoped BigOperators Pointwise

open Finset Set

noncomputable section Thm_1_2

namespace DarbouxRS

lemma tag_mem_Icc_of_tagsInPartition_core {a b : ℝ} (P : Partition a b)
    {tags : Fin P.n → ℝ} (htags : tagsInPartition P tags)
    (i : Fin P.n) :
    tags i ∈ Set.Icc a b :=

  subinterval_subset_Icc_core P (htags i)

end DarbouxRS

end Thm_1_2

noncomputable section Darboux_fundamental_result

namespace Refinement

end Refinement

namespace Partition

end Partition

end Darboux_fundamental_result


