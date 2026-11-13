-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F001
-- name    : ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:46:28.223254+00:00
-- url     : https://prove2.me/theorems/12af058b-6e40-421a-98a6-69c8d1215c6f
-- title:
--   Chapter 1, thm_1_1_bad_cells: supporting Lean bundle F001
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `thm_1_1_bad_cells`: `abs_sub_le_cell_length_of_mem_subinterval`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_bad_cells.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep

open Finset BigOperators
open Set Topology

noncomputable section

namespace Thm11SourceRoute

lemma abs_sub_le_cell_length_of_mem_subinterval {a b x y : ℝ}
    (P : Partition a b) {i : Fin P.n}
    (hx : x ∈ Partition.subinterval P i)
    (hy : y ∈ Partition.subinterval P i) :
    |x - y| ≤ P.pts i.succ - P.pts i.castSucc := by
  rcases hx with ⟨hix, hxi⟩
  rcases hy with ⟨hiy, hyi⟩
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith
end Thm11SourceRoute


