-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F003
-- name    : ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:51:20.446499+00:00
-- url     : https://prove2.me/theorems/f2cfc0ff-8fc9-44e7-bf7a-bbfeb57a2f5a
-- title:
--   Chapter 1, thm_1_1_bad_cells: supporting Lean bundle F003
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `thm_1_1_bad_cells`: `sum_adjacent_sub`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_bad_cells.lean

import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep

open Finset BigOperators
open Set Topology

noncomputable section

namespace Thm11SourceRoute

private lemma sum_adjacent_sub {n : ℕ} (g : Fin (n + 1) → ℝ) :
    (∑ i : Fin n, (g i.succ - g i.castSucc)) =
      g (Fin.last n) - g 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_succ]
      have htail := ih (fun i : Fin (n + 1) => g i.succ)
      have htail' :
          (∑ i : Fin n, (g i.succ.succ - g i.succ.castSucc)) =
            g (Fin.last n).succ - g (Fin.succ 0) := by
        simpa only [Fin.succ_castSucc] using htail
      rw [htail']
      simp
end Thm11SourceRoute


