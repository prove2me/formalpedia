-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_03_def_3_1_F000
-- name    : ProbabilityTheory_chapter_03_def_3_1_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:57:17.881969+00:00
-- url     : https://prove2.me/theorems/2e426762-df8a-45b0-87ee-2dc457247173
-- title:
--   Chapter 3, def_3_1: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 3, source module `def_3_1`: `FieldOfSets`, `Premeasure`, `inter_mem`, `sdiff_mem`, `isSetRing`, and 3 others. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_03/def_3_1.lean

import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.Tactic

open Set ENNReal Function MeasureTheory

structure FieldOfSets (Ω : Type*) where
  carrier : Set (Set Ω)
  empty_mem : ∅ ∈ carrier
  compl_mem : ∀ s ∈ carrier, sᶜ ∈ carrier
  union_mem : ∀ s t, s ∈ carrier → t ∈ carrier → s ∪ t ∈ carrier

structure Premeasure {Ω : Type*} (F₀ : FieldOfSets Ω) where

  μ₀ : {s : Set Ω // s ∈ F₀.carrier} → ℝ≥0∞

  map_empty : μ₀ ⟨∅, F₀.empty_mem⟩ = 0

  sigma_additive :
    ∀ (A : ℕ → Set Ω) (hA : ∀ i, A i ∈ F₀.carrier)
    (hU : (⋃ i, A i) ∈ F₀.carrier),
    Pairwise (Disjoint on A) →
    μ₀ ⟨⋃ i, A i, hU⟩ = ∑' i, μ₀ ⟨A i, hA i⟩
namespace FieldOfSets

lemma inter_mem {Ω : Type*} (F₀ : FieldOfSets Ω) {s t : Set Ω}
    (hs : s ∈ F₀.carrier) (ht : t ∈ F₀.carrier) : s ∩ t ∈ F₀.carrier := by
  rw [show s ∩ t = (sᶜ ∪ tᶜ)ᶜ by ext x; simp]
  exact F₀.compl_mem _ (F₀.union_mem _ _ (F₀.compl_mem _ hs) (F₀.compl_mem _ ht))

lemma sdiff_mem {Ω : Type*} (F₀ : FieldOfSets Ω) {s t : Set Ω}
    (hs : s ∈ F₀.carrier) (ht : t ∈ F₀.carrier) : s \ t ∈ F₀.carrier := by
  rw [show s \ t = s ∩ tᶜ by ext x; simp]
  exact F₀.inter_mem hs (F₀.compl_mem _ ht)

lemma isSetRing {Ω : Type*} (F₀ : FieldOfSets Ω) : IsSetRing F₀.carrier where
  empty_mem := F₀.empty_mem
  union_mem := by
    intro s t hs ht
    exact F₀.union_mem s t hs ht
  sdiff_mem := by
    intro s t hs ht
    exact F₀.sdiff_mem hs ht
end FieldOfSets

namespace Premeasure

variable {Ω : Type*} {F₀ : FieldOfSets Ω}

noncomputable def toSetFunction (pm : Premeasure F₀) (s : Set Ω) : ℝ≥0∞ :=
  by
    classical
    exact if hs : s ∈ F₀.carrier then pm.μ₀ ⟨s, hs⟩ else 0
@[simp]
lemma toSetFunction_of_mem (pm : Premeasure F₀) {s : Set Ω} (hs : s ∈ F₀.carrier) :
    pm.toSetFunction s = pm.μ₀ ⟨s, hs⟩ := by
  classical
  simp only [toSetFunction, dif_pos hs]
@[simp]
lemma toSetFunction_empty (pm : Premeasure F₀) : pm.toSetFunction ∅ = 0 := by
  rw [pm.toSetFunction_of_mem F₀.empty_mem]
  exact pm.map_empty
end Premeasure


