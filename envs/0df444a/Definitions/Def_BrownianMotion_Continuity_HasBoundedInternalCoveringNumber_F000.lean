-- Prove2me | Definitions.Def_BrownianMotion_Continuity_HasBoundedInternalCoveringNumber_F000
-- name    : BrownianMotion_Continuity_HasBoundedInternalCoveringNumber_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T07:23:39.991712+00:00
-- url     : https://prove2.me/theorems/5d7b34af-8b49-4bce-94e0-bf714e89b87a
-- title:
--   Source declarations: BrownianMotion.Continuity.HasBoundedInternalCoveringNumber
-- statement:
--   Source-preserving extracted declarations from BrownianMotion.Continuity.HasBoundedInternalCoveringNumber. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Continuity_CoveringNumber_F000
import Definitions.Def_BrownianMotion_Continuity_CoveringNumber_F001

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
# HasBoundedCoveringNumber

-/

@[expose] public section

open MeasureTheory Metric
open scoped ENNReal NNReal

variable {T : Type*} [PseudoEMetricSpace T] {A : Set T} {c : ℝ≥0∞} {ε : ℝ≥0} {d : ℝ}

/-- A set `A` in a pseudoemetric space has bounded covering number with constant `c` and exponent
`d` if it has finite diameter and for all `ε ∈ (0, diam(A)]`, the covering number of `A`
at scale `ε` is bounded by `c * ε^{-d}`. -/
structure HasBoundedCoveringNumber (A : Set T) (c : ℝ≥0∞) (d : ℝ) : Prop where
  ediam_lt_top : Metric.ediam A < ∞
  coveringNumber_le : ∀ ε : ℝ≥0, ε ≤ Metric.ediam A → coveringNumber ε A ≤ c * (ε : ℝ≥0∞)⁻¹ ^ d
lemma HasBoundedCoveringNumber.coveringNumber_lt_top
    (h : HasBoundedCoveringNumber A c d) (hε_ne : ε ≠ 0)
    (hc : c ≠ ∞) (hd : 0 ≤ d) :
    coveringNumber ε A < ⊤ := by
  by_cases hε_le : ε ≤ Metric.ediam A
  · suffices (coveringNumber ε A : ℝ≥0∞) < ∞ by norm_cast at this
    calc (coveringNumber ε A : ℝ≥0∞)
    _ ≤ c * (ε : ℝ≥0∞)⁻¹ ^ d := h.coveringNumber_le _ hε_le
    _ < ∞ := by
      refine ENNReal.mul_lt_top hc.lt_top ?_
      exact ENNReal.rpow_lt_top_of_nonneg hd (by simp [hε_ne])
  · calc coveringNumber ε A
    _ ≤ 1 := coveringNumber_le_one_of_ediam_le (not_le.mp hε_le).le
    _ < ⊤ := by simp


