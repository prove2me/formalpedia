-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F000
-- name    : ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T15:30:40.568313+00:00
-- url     : https://prove2.me/theorems/dd510734-02a5-47aa-b85c-ff8ad96f2e63
-- title:
--   Chapter 1, thm_1_1_bad_cells: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `thm_1_1_bad_cells`: `goodRemainder`, `mem_goodRemainder_iff`, `isCompact_goodRemainder`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_bad_cells.lean

import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep

open Finset BigOperators
open Set Topology

noncomputable section

namespace Thm11SourceRoute

def goodRemainder (a b : ℝ) (S : Finset ℝ) (rho : ℝ → ℝ) : Set ℝ :=
  Icc a b ∩ ⋂ c ∈ S, {x : ℝ | rho c ≤ |x - c|}



end Thm11SourceRoute


