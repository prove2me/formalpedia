-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F011
-- name    : ProbabilityTheory_chapter_01_thm_1_2_F011
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T22:46:19.501561+00:00
-- url     : https://prove2.me/theorems/cc3e28b0-ec1e-4a56-aa8b-59daad7cadad
-- title:
--   Chapter 1, thm_1_2: supporting Lean bundle F011
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `thm_1_2`: `Refinement.index_zero`, `Refinement.index_last`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_2.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F009
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

lemma Refinement.index_zero
    {a b : ℝ} {P P' : Partition a b}
    (R : Refinement P P') :
    R.index (0 : Fin (P.n + 1)) = (0 : Fin (P'.n + 1)) := by
  by_contra hne

  have hne' :
      (0 : Fin (P'.n + 1)) ≠ R.index (0 : Fin (P.n + 1)) := by
    intro h
    exact hne h.symm

  have hlt :
      (0 : Fin (P'.n + 1)) < R.index (0 : Fin (P.n + 1)) := by
    exact lt_of_le_of_ne (Fin.zero_le _) hne'

  have hpts_lt :
      P'.pts (0 : Fin (P'.n + 1)) <
        P'.pts (R.index (0 : Fin (P.n + 1))) :=
    P'.strict_mono hlt

  have : a < a := by
    calc
      a = P'.pts (0 : Fin (P'.n + 1)) := P'.pts_start.symm
      _ < P'.pts (R.index (0 : Fin (P.n + 1))) := hpts_lt
      _ = P.pts (0 : Fin (P.n + 1)) := (R.index_spec 0).symm
      _ = a := P.pts_start

  exact (lt_irrefl a) this
lemma Refinement.index_last
    {a b : ℝ} {P P' : Partition a b}
    (R : Refinement P P') :
    R.index (Fin.last P.n) = Fin.last P'.n := by
  by_contra hne

  have hlt :
      R.index (Fin.last P.n) < Fin.last P'.n := by
    exact lt_of_le_of_ne (Fin.le_last _) hne

  have hpts_lt :
      P'.pts (R.index (Fin.last P.n)) <
        P'.pts (Fin.last P'.n) :=
    P'.strict_mono hlt

  have : b < b := by
    calc
      b = P.pts (Fin.last P.n) := P.pts_end.symm
      _ = P'.pts (R.index (Fin.last P.n)) := R.index_spec (Fin.last P.n)
      _ < P'.pts (Fin.last P'.n) := hpts_lt
      _ = b := P'.pts_end

  exact (lt_irrefl b) this
namespace Partition

end Partition

end Darboux_fundamental_result


