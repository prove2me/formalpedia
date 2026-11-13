-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_finite_discontinuity_F000
-- name    : ProbabilityTheory_chapter_01_thm_1_1_finite_discontinuity_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T22:48:10.745037+00:00
-- url     : https://prove2.me/theorems/33ba47d2-7f4b-44d1-9d02-0de5e19eb6e3
-- title:
--   Chapter 1, thm_1_1_finite_discontinuity: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `thm_1_1_finite_discontinuity`: `StrictFiniteDiscontinuityOscillationCriterion`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_finite_discontinuity.lean

import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_basic_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_darboux_gap_F000
import Mathlib.Data.List.GetD
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep

open Finset BigOperators
open Set Topology

noncomputable section

namespace Thm11SourceRoute

def StrictFiniteDiscontinuityOscillationCriterion : Prop :=
  ∀ {f α : ℝ → ℝ} {a b : ℝ},
    a < b →
    Monotone α →
    BddAbove (f '' Icc a b) →
    BddBelow (f '' Icc a b) →
    (discontinuitySetOn f a b).Finite →
    (∀ ⦃x : ℝ⦄, x ∈ discontinuitySetOn f a b → ContinuousAt α x) →
    ClosedIntervalDarbouxOscillationSmall a b f α
end Thm11SourceRoute


