-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F010
-- name    : ProbabilityTheory_chapter_01_thm_1_2_F010
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T15:28:06.029806+00:00
-- url     : https://prove2.me/theorems/96e41ca7-7b54-49be-8795-cc315d760aad
-- title:
--   Chapter 1, thm_1_2: supporting Lean bundle F010
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `thm_1_2`: `sum_range_sub_from`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_2.lean

import Mathlib.Tactic

open scoped BigOperators Pointwise

open Finset Set

noncomputable section Thm_1_2

namespace DarbouxRS

end DarbouxRS

end Thm_1_2

noncomputable section Darboux_fundamental_result

namespace Refinement

end Refinement

lemma sum_range_sub_from (u : ℕ → ℝ) (m d : ℕ) :
    (∑ t ∈ Finset.range d, (u (m + (t + 1)) - u (m + t)))
      =
    u (m + d) - u m := by
  induction d with
  | zero =>
      simp
  | succ d ih =>
      rw [Finset.sum_range_succ, ih]
      ring
namespace Partition

end Partition

end Darboux_fundamental_result


