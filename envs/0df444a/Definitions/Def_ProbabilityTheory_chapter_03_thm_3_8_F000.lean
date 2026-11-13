-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_03_thm_3_8_F000
-- name    : ProbabilityTheory_chapter_03_thm_3_8_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T16:25:28.794786+00:00
-- url     : https://prove2.me/theorems/a0dbd5de-7ed1-49da-82ef-8e292f755717
-- title:
--   Chapter 3, thm_3_8: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 3, source module `thm_3_8`: `thm_3_8`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_03/thm_3_8.lean

import Definitions.Def_ProbabilityTheory_chapter_03_def_3_3_F000
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.MeasureTheory.PiSystem
import Mathlib.Tactic

open MeasureTheory Set ENNReal MeasurableSpace

theorem thm_3_8 {Ω : Type*} [m : MeasurableSpace Ω] (F₀ : Set (Set Ω))
  (h_gen : m = MeasurableSpace.generateFrom F₀)
  (h_field_compl : ∀ s ∈ F₀, sᶜ ∈ F₀)
  (h_field_union : ∀ s ∈ F₀, ∀ t ∈ F₀, s ∪ t ∈ F₀)
  (μ1 μ2 : Measure Ω)
  (h_eq_on_F₀ : ∀ s ∈ F₀, μ1 s = μ2 s)
  (Ω_seq : ℕ → Set Ω)
  (h_in_F₀ : ∀ i, Ω_seq i ∈ F₀)
  (h_univ : (⋃ i, Ω_seq i) = univ)
  (h_finite : ∀ i, μ1 (Ω_seq i) = μ2 (Ω_seq i) ∧ μ1 (Ω_seq i) < ⊤) :
  μ1 = μ2 := by
  apply Measure.ext_of_generateFrom_of_iUnion F₀ Ω_seq h_gen
  · intro s hs t ht _
    have : s ∩ t = (sᶜ ∪ tᶜ)ᶜ := by ext x; simp
    rw [this]
    exact h_field_compl _ (h_field_union _ (h_field_compl _ hs) _ (h_field_compl _ ht))
  · exact h_univ
  · exact h_in_F₀
  · intro i
    exact (h_finite i).2.ne
  · exact h_eq_on_F₀


