-- Prove2me | solution 1 for ActuarialValuation.csCausePartition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:56:04.128667+00:00
-- url     : https://prove2.me/submissions/c18d5537-ffe7-46b3-be21-8a6d22fc9698

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_csCauseOne
import Definitions.Def_actuarial_csCauseTwo
import Definitions.Def_actuarial_csShockCause
import Definitions.Def_actuarial_csPrimitiveTie

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (U V Z : Ω → ℝ)
    [MeasureTheory.IsProbabilityMeasure μ]
    (hU : Measurable U) (hV : Measurable V) (hZ : Measurable Z)
    (htie : csPrimitiveTie μ U V Z = 0) :
    csCauseOne μ U V Z + csCauseTwo μ U V Z +
      csShockCause μ U V Z = 1 := by
  classical
  let A : Set Ω := {ω | U ω < V ω ∧ U ω < Z ω}
  let B : Set Ω := {ω | V ω < U ω ∧ V ω < Z ω}
  let C : Set Ω := {ω | Z ω < U ω ∧ Z ω < V ω}
  let T : Set Ω := {ω | U ω = V ω ∨ U ω = Z ω ∨ V ω = Z ω}
  have hBmeas : MeasurableSet B := by
    dsimp [B]
    exact (measurableSet_lt hV hU).inter (measurableSet_lt hV hZ)
  have hCmeas : MeasurableSet C := by
    dsimp [C]
    exact (measurableSet_lt hZ hU).inter (measurableSet_lt hZ hV)
  have hAB : Disjoint A B := Set.disjoint_left.mpr (by
    intro ω ha hb
    exact lt_asymm ha.1 hb.1)
  have hABC : Disjoint (A ∪ B) C := Set.disjoint_left.mpr (by
    intro ω hab hc
    rcases hab with ha | hb
    · exact lt_asymm ha.2 hc.1
    · exact lt_asymm hb.2 hc.2)
  have hCover : A ∪ B ∪ C ∪ T = Set.univ := by
    ext ω
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    rcases lt_trichotomy (U ω) (V ω) with huv | huv | hvu
    · rcases lt_trichotomy (U ω) (Z ω) with huz | huz | hzu
      · exact Or.inl (Or.inl (Or.inl ⟨huv, huz⟩))
      · exact Or.inr (Or.inr (Or.inl huz))
      · have hzv : Z ω < V ω := lt_trans hzu huv
        exact Or.inl (Or.inr ⟨hzu, hzv⟩)
    · exact Or.inr (Or.inl huv)
    · rcases lt_trichotomy (V ω) (Z ω) with hvz | hvz | hzv
      · exact Or.inl (Or.inl (Or.inr ⟨hvu, hvz⟩))
      · exact Or.inr (Or.inr (Or.inr hvz))
      · have hzu : Z ω < U ω := lt_trans hzv hvu
        exact Or.inl (Or.inr ⟨hzu, hzv⟩)
  have hT : μ T = 0 := by
    change csPrimitiveTie μ U V Z = 0
    exact htie
  have hABmeasure : μ (A ∪ B) = μ A + μ B := by
    exact measure_union hAB hBmeas
  have hABCmeasure : μ (A ∪ B ∪ C) = μ A + μ B + μ C := by
    rw [measure_union hABC hCmeas, hABmeasure]
  have hlow : μ Set.univ ≤ μ (A ∪ B ∪ C) := by
    calc
      μ Set.univ = μ ((A ∪ B ∪ C) ∪ T) := by rw [hCover]
      _ ≤ μ (A ∪ B ∪ C) + μ T := measure_union_le _ _
      _ = μ (A ∪ B ∪ C) := by simp [hT]
  have htotal : μ (A ∪ B ∪ C) = 1 := by
    have hhi : μ (A ∪ B ∪ C) ≤ μ Set.univ :=
      measure_mono (Set.subset_univ _)
    have heq : μ (A ∪ B ∪ C) = μ Set.univ :=
      le_antisymm hhi hlow
    simpa using heq
  change μ A + μ B + μ C = 1
  rw [← hABCmeasure]
  exact htotal
