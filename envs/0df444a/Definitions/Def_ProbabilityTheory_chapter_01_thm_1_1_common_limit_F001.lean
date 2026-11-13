-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_common_limit_F001
-- name    : ProbabilityTheory_chapter_01_thm_1_1_common_limit_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T22:49:50.255289+00:00
-- url     : https://prove2.me/theorems/06f9e7f1-aa0c-4eb9-8d75-0745bb5fb442
-- title:
--   Chapter 1, thm_1_1_common_limit: supporting Lean bundle F001
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `thm_1_1_common_limit`: `ClosedIntervalDarbouxCommonLimitFromOscillation`, `ClosedIntervalDarbouxCommonLimitFromGap`, `closedIntervalDarbouxCommonLimitFromGap_of_fineCauchy`, `closedIntervalDarbouxCommonLimitFromOscillation_of_gap`, `strict_upperLower_criterion_of_oscillation`, and 7 others. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_common_limit.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_basic_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_basic_F001
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_common_limit_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_darboux_gap_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_finite_discontinuity_F000
import Mathlib.Data.List.GetD
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep

open Finset BigOperators
open Set Topology

noncomputable section

namespace Thm11SourceRoute

def ClosedIntervalDarbouxCommonLimitFromOscillation : Prop :=
  ∀ {f α : ℝ → ℝ} {a b : ℝ},
    SourceHypotheses a b f α →
    ClosedIntervalDarbouxOscillationSmall a b f α →
    ∃ L, rsUpperLowerCommonLimit a b f α L

def ClosedIntervalDarbouxCommonLimitFromGap : Prop :=
  ∀ {f α : ℝ → ℝ} {a b : ℝ},
    SourceHypotheses a b f α →
    ClosedIntervalDarbouxGapSmall a b f α →
    ∃ L, rsUpperLowerCommonLimit a b f α L










def StrictFiniteDiscontinuityCommonLimitCriterion : Prop :=
  ∀ {f α : ℝ → ℝ} {a b : ℝ},
    a < b →
    Monotone α →
    BddAbove (f '' Icc a b) →
    BddBelow (f '' Icc a b) →
    (discontinuitySetOn f a b).Finite →
    (∀ ⦃x : ℝ⦄, x ∈ discontinuitySetOn f a b → ContinuousAt α x) →
    ∃ L, rsUpperLowerCommonLimit a b f α L ∧ rsTaggedCommonLimit a b f α L






end Thm11SourceRoute


