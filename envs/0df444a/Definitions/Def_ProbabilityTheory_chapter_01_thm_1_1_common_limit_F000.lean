-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_common_limit_F000
-- name    : ProbabilityTheory_chapter_01_thm_1_1_common_limit_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T22:49:18.515034+00:00
-- url     : https://prove2.me/theorems/1fc7b6c2-4c31-450b-bb36-6ab0b858fc64
-- title:
--   Chapter 1, thm_1_1_common_limit: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `thm_1_1_common_limit`: `ClosedIntervalDarbouxFineCauchyFromGap`, `closedIntervalDarbouxFineCauchyFromGap_of_commonRefinementSandwich`, `closedIntervalDarbouxFineCauchyFromGap_proof`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_common_limit.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_common_refinement_points_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_darboux_gap_F000
import Mathlib.Data.List.GetD
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep

open Finset BigOperators
open Set Topology

noncomputable section

namespace Thm11SourceRoute

def ClosedIntervalDarbouxFineCauchyFromGap : Prop :=
  ∀ {f α : ℝ → ℝ} {a b : ℝ},
    SourceHypotheses a b f α →
    ClosedIntervalDarbouxGapSmall a b f α →
    ClosedIntervalDarbouxFineCauchy a b f α



end Thm11SourceRoute


