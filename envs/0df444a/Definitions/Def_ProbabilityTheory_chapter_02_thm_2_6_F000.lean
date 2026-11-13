-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_02_thm_2_6_F000
-- name    : ProbabilityTheory_chapter_02_thm_2_6_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:56:45.466572+00:00
-- url     : https://prove2.me/theorems/7a70b9bc-155c-4a3e-8b82-a905e25f4292
-- title:
--   Chapter 2, thm_2_6: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 2, source module `thm_2_6`: `SigmaFieldContains`, `sigmaFieldIntersection`, `sigmaFieldsContaining_nonempty`, `sigmaFieldIntersection_univ`, `sigmaFieldIntersection_compl`, and 6 others. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/thm_2_6.lean

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

open Set MeasureTheory

def SigmaFieldContains {Ω : Type*} (C : Set (Set Ω)) (F : MeasurableSpace Ω) : Prop :=
  ∀ s ∈ C, @MeasurableSet Ω F s

def sigmaFieldIntersection {Ω : Type*} (C : Set (Set Ω)) : Set (Set Ω) :=
  {s | ∀ F : MeasurableSpace Ω, SigmaFieldContains C F → @MeasurableSet Ω F s}

lemma sigmaFieldsContaining_nonempty {Ω : Type*} (C : Set (Set Ω)) :
    ∃ F : MeasurableSpace Ω, SigmaFieldContains C F := by
  refine ⟨⊤, ?_⟩
  intro s hs
  trivial

lemma sigmaFieldIntersection_univ {Ω : Type*} (C : Set (Set Ω)) :
    Set.univ ∈ sigmaFieldIntersection C := by
  intro F hF
  exact MeasurableSet.univ

lemma sigmaFieldIntersection_compl {Ω : Type*} (C : Set (Set Ω)) {A : Set Ω}
    (hA : A ∈ sigmaFieldIntersection C) : Aᶜ ∈ sigmaFieldIntersection C := by
  intro F hF
  exact (hA F hF).compl

lemma sigmaFieldIntersection_iUnion {Ω : Type*} (C : Set (Set Ω)) {A : ℕ → Set Ω}
    (hA : ∀ n, A n ∈ sigmaFieldIntersection C) :
    (⋃ n, A n) ∈ sigmaFieldIntersection C := by
  intro F hF
  exact MeasurableSet.iUnion (fun n => hA n F hF)

lemma sigmaFieldIntersection_contains {Ω : Type*} (C : Set (Set Ω)) {A : Set Ω}
    (hA : A ∈ C) : A ∈ sigmaFieldIntersection C := by
  intro F hF
  exact hF A hA

lemma sigmaFieldIntersection_minimal {Ω : Type*} (C : Set (Set Ω))
    (F : MeasurableSpace Ω) (hF : SigmaFieldContains C F) :
    ∀ A, A ∈ sigmaFieldIntersection C → @MeasurableSet Ω F A := by
  intro A hA
  exact hA F hF

@[reducible]
def intersectionMeasurableSpace {Ω : Type*} (C : Set (Set Ω)) : MeasurableSpace Ω where
  MeasurableSet' := sigmaFieldIntersection C
  measurableSet_empty := by
    intro F hF
    exact MeasurableSet.empty
  measurableSet_compl := by
    intro A hA F hF
    exact (hA F hF).compl
  measurableSet_iUnion := by
    intro A hA F hF
    exact MeasurableSet.iUnion (fun n => hA n F hF)

lemma intersectionMeasurableSpace_eq_generateFrom {Ω : Type*} (C : Set (Set Ω)) :
    intersectionMeasurableSpace C = MeasurableSpace.generateFrom C := by
  apply le_antisymm
  · intro A hA
    exact hA (MeasurableSpace.generateFrom C)
      (fun s hs => MeasurableSpace.GenerateMeasurable.basic s hs)
  · exact MeasurableSpace.generateFrom_le
      (fun A hA => sigmaFieldIntersection_contains C hA)

theorem thm_2_6_intersection_spine {Ω : Type*} (C : Set (Set Ω)) :
    (∃ F : MeasurableSpace Ω, SigmaFieldContains C F) ∧
      Set.univ ∈ sigmaFieldIntersection C ∧
      (∀ A, A ∈ sigmaFieldIntersection C → Aᶜ ∈ sigmaFieldIntersection C) ∧
      (∀ A : ℕ → Set Ω, (∀ n, A n ∈ sigmaFieldIntersection C) →
        (⋃ n, A n) ∈ sigmaFieldIntersection C) ∧
      (∀ A ∈ C, A ∈ sigmaFieldIntersection C) ∧
      ∀ F : MeasurableSpace Ω, SigmaFieldContains C F →
        ∀ A, A ∈ sigmaFieldIntersection C → @MeasurableSet Ω F A := by
  exact ⟨
    sigmaFieldsContaining_nonempty C,
    sigmaFieldIntersection_univ C,
    fun A hA => sigmaFieldIntersection_compl C hA,
    fun A hA => sigmaFieldIntersection_iUnion C hA,
    fun A hA => sigmaFieldIntersection_contains C hA,
    fun F hF A hA => sigmaFieldIntersection_minimal C F hF A hA⟩


