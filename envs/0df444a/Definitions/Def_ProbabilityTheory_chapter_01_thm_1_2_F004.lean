-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F004
-- name    : ProbabilityTheory_chapter_01_thm_1_2_F004
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:53:07.941754+00:00
-- url     : https://prove2.me/theorems/20aaa537-dfdf-4a15-999c-f7289b733eb1
-- title:
--   Chapter 1, thm_1_2: supporting Lean bundle F004
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `thm_1_2`: `taggedSum_const_mul_core`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_2.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Mathlib.Tactic

open scoped BigOperators Pointwise

open Finset Set

noncomputable section Thm_1_2

namespace DarbouxRS

theorem taggedSum_const_mul_core {a b c : ℝ} (P : Partition a b) (tags : Fin P.n → ℝ)
    (f alpha : ℝ → ℝ) :
    taggedSum P tags (fun x => c * f x) alpha = c * taggedSum P tags f alpha := by
  unfold taggedSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

end DarbouxRS

end Thm_1_2

noncomputable section Darboux_fundamental_result

namespace Refinement

end Refinement

namespace Partition

end Partition

end Darboux_fundamental_result


