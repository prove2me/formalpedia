-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_03_def_3_8_F000
-- name    : ProbabilityTheory_chapter_03_def_3_8_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:57:59.929768+00:00
-- url     : https://prove2.me/theorems/e0fd5305-ae21-42b0-83b5-8627c49e9d22
-- title:
--   Chapter 3, def_3_8: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 3, source module `def_3_8`: `IsFinitelyAdditive`, `IsSigmaSubadditive`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_03/def_3_8.lean

import Mathlib.MeasureTheory.Measure.MeasureSpace

open scoped ENNReal

def IsFinitelyAdditive {α : Type _} (F₀ : Set (Set α)) (μ : Set α → ℝ≥0∞) : Prop :=
  ∀ {n : ℕ} (A : Fin n → Set α),
    (∀ i, A i ∈ F₀) →
    (∀ i j, i ≠ j → Disjoint (A i) (A j)) →
    μ (Set.iUnion A) = Finset.sum (Finset.univ : Finset (Fin n)) (fun i => μ (A i))

def IsSigmaSubadditive {α : Type _} (F₀ : Set (Set α)) (μ : Set α → ℝ≥0∞) : Prop :=
  ∀ (A : ℕ → Set α),
    (∀ i, A i ∈ F₀) →
    (Set.iUnion A ∈ F₀) →
    μ (Set.iUnion A) ≤ ∑' i, μ (A i)


