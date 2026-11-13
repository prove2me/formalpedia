-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F002
-- name    : ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:48:06.44888+00:00
-- url     : https://prove2.me/theorems/59b03414-008f-480d-b1d2-82937de022fe
-- title:
--   Chapter 1, thm_1_1_bad_cells: supporting Lean bundle F002
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `thm_1_1_bad_cells`: `abs_sub_lt_of_mem_subinterval_of_endpoints_abs_lt`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_bad_cells.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep

open Finset BigOperators
open Set Topology

noncomputable section

namespace Thm11SourceRoute

lemma abs_sub_lt_of_mem_subinterval_of_endpoints_abs_lt
    {a b c delta : ℝ} (P : Partition a b) {i : Fin P.n}
    {x : ℝ}
    (hx : x ∈ Partition.subinterval P i)
    (hleft : |P.pts i.castSucc - c| < delta)
    (hright : |P.pts i.succ - c| < delta) :
    |x - c| < delta := by
  rcases hx with ⟨hleft_x, hx_right⟩
  rcases abs_lt.mp hleft with ⟨hcl, hlc⟩
  rcases abs_lt.mp hright with ⟨_hcr, hrc⟩
  refine abs_lt.mpr ⟨?_, ?_⟩
  · linarith
  · linarith
end Thm11SourceRoute


