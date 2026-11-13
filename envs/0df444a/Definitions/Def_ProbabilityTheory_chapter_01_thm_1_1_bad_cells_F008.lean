-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F008
-- name    : ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F008
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T23:05:28.756952+00:00
-- url     : https://prove2.me/theorems/f57d7338-4e3a-4de0-b30f-b46ad8f56ad7
-- title:
--   Chapter 1, thm_1_1_bad_cells: supporting Lean bundle F008
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `thm_1_1_bad_cells`: `subintervalAtNat`, `subintervalAtNat_eq`, `badCellIndices`, `mem_badCellIndices_iff`, `cell_subset_goodRemainder_of_not_mem_badCellIndices`, and 1 others. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_bad_cells.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F000
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep

open Finset BigOperators
open Set Topology

noncomputable section

namespace Thm11SourceRoute

private def subintervalAtNat {a b : ℝ} (P : Partition a b) (i : ℕ) : Set ℝ :=
  if h : i < P.n then Partition.subinterval P ⟨i, h⟩ else ∅
private lemma subintervalAtNat_eq {a b : ℝ} (P : Partition a b)
    {i : ℕ} (hi : i < P.n) :
    subintervalAtNat P i = Partition.subinterval P ⟨i, hi⟩ := by
  simp [subintervalAtNat, hi]
noncomputable def badCellIndices {a b : ℝ}
    (P : Partition a b) (S : Finset ℝ) (rho : ℝ → ℝ) :
    Finset ℕ := by
  classical
  exact (Finset.range P.n).filter
    (fun i => ¬ subintervalAtNat P i ⊆ goodRemainder a b S rho)






end Thm11SourceRoute


