-- Prove2me | Definitions.Def_BrownianMotion_Continuity_HasBoundedInternalCoveringNumber_F001
-- name    : BrownianMotion_Continuity_HasBoundedInternalCoveringNumber_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T07:25:35.273181+00:00
-- url     : https://prove2.me/theorems/b5a74e92-f206-484b-87de-3af4eae8e510
-- title:
--   Source declarations: BrownianMotion.Continuity.HasBoundedInternalCoveringNumber
-- statement:
--   Source-preserving extracted declarations from BrownianMotion.Continuity.HasBoundedInternalCoveringNumber. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Continuity_HasBoundedInternalCoveringNumber_F000

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

structure IsCoverWithBoundedCoveringNumber (C : ℕ → Set T) (A : Set T) (c : ℕ → ℝ≥0∞) (d : ℕ → ℝ)
    where
  c_ne_top : ∀ n, c n ≠ ∞
  d_pos : ∀ n, 0 < d n
  isOpen : ∀ n, IsOpen (C n)
  totallyBounded : ∀ n, TotallyBounded (C n)
  hasBoundedCoveringNumber : ∀ n, HasBoundedCoveringNumber (C n) (c n) (d n)
  mono : ∀ n m, n ≤ m → C n ⊆ C m
  subset_iUnion : A ⊆ ⋃ i, C i


