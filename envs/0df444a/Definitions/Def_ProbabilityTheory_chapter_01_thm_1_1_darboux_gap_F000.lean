-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_darboux_gap_F000
-- name    : ProbabilityTheory_chapter_01_thm_1_1_darboux_gap_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T22:47:15.323204+00:00
-- url     : https://prove2.me/theorems/b3072baf-55fa-454f-9851-2f7f825f6d3b
-- title:
--   Chapter 1, thm_1_1_darboux_gap: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `thm_1_1_darboux_gap`: `ClosedIntervalDarbouxOscillationSmall`, `ClosedIntervalDarbouxGapSmall`, `ClosedIntervalDarbouxFineCauchy`, `upperSum_sub_lowerSum_nonneg_of_source`, `closedIntervalDarbouxAbsGapSmall_of_gapSmall`, and 1 others. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_darboux_gap.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_oscillation_basic_F000
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep

open Finset BigOperators
open Set Topology

noncomputable section

namespace Thm11SourceRoute

def ClosedIntervalDarbouxOscillationSmall
    (a b : ℝ) (f α : ℝ → ℝ) : Prop :=
  ∀ eps > 0, ∃ δ > 0, ∀ P : Partition a b,
    P.mesh < δ → partitionOscillation P f α < eps

def ClosedIntervalDarbouxGapSmall
    (a b : ℝ) (f α : ℝ → ℝ) : Prop :=
  ∀ eps > 0, ∃ δ > 0, ∀ P : Partition a b,
    P.mesh < δ →
      upperSum P f α - lowerSum P f α < eps

def ClosedIntervalDarbouxFineCauchy
    (a b : ℝ) (f α : ℝ → ℝ) : Prop :=
  ∀ eps > 0, ∃ δ > 0, ∀ P Q : Partition a b,
    P.mesh < δ →
    Q.mesh < δ →
      |upperSum P f α - upperSum Q f α| < eps ∧
      |lowerSum P f α - lowerSum Q f α| < eps ∧
      |upperSum P f α - lowerSum Q f α| < eps ∧
      |lowerSum P f α - upperSum Q f α| < eps






end Thm11SourceRoute


