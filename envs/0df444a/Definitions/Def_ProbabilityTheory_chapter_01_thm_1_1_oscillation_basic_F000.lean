-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_oscillation_basic_F000
-- name    : ProbabilityTheory_chapter_01_thm_1_1_oscillation_basic_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T22:19:28.355739+00:00
-- url     : https://prove2.me/theorems/f8603e86-3ac0-4160-8336-6e3794e7d11e
-- title:
--   Chapter 1, thm_1_1_oscillation_basic: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `thm_1_1_oscillation_basic`: `partitionOscillation`, `upperSum_sub_lowerSum_eq_partitionOscillation`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_oscillation_basic.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_basic_F001
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep

open Finset BigOperators
open Set Topology

noncomputable section

namespace Thm11SourceRoute

noncomputable def partitionOscillation {a b : ℝ}
    (P : Partition a b) (f α : ℝ → ℝ) : ℝ :=
  ∑ i : Fin P.n,
    (upperStep P f i - lowerStep P f i) *
      (α (P.pts i.succ) - α (P.pts i.castSucc))


end Thm11SourceRoute


