-- Prove2me | Definitions.Def_LevyStochCalc_Probability_AugmentationMeasurable_F000
-- name    : LevyStochCalc_Probability_AugmentationMeasurable_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:33:39.321847+00:00
-- url     : https://prove2.me/theorems/d5449213-dc0b-4b3f-91b9-9e3473ee4ec7
-- title:
--   Source declarations: LevyStochCalc.Probability.AugmentationMeasurable
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.AugmentationMeasurable. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_Augmentation_F000
import Definitions.Def_LevyStochCalc_Probability_SubSigmaLimit_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Measurability for an augmented σ-algebra

A set measurable for `aug m m₀ μ` differs from an `m`-measurable set by a `μ`-null set, so its
indicator is almost everywhere an `m`-measurable indicator. Passing through simple functions and
their limits, a function strongly measurable for `aug m m₀ μ` is almost everywhere equal to an
`m`-strongly-measurable function.
-/

open MeasureTheory Filter
open scoped symmDiff

namespace LevyStochCalc.Probability

variable {Ω : Type*} {E : Type*} [TopologicalSpace E]
variable {m m₀ : MeasurableSpace Ω} {μ : Measure[m₀] Ω}

/-- The indicator of an augmented-measurable set is almost everywhere the indicator of an
`m`-measurable set. -/
theorem aestronglyMeasurable_indicator_aug [Zero E] {A : Set Ω}
    (hA : MeasurableSet[aug m m₀ μ] A) (c : E) :
    AEStronglyMeasurable[m] (A.indicator fun _ => c) μ := by
  obtain ⟨-, B, hB, hAB⟩ := hA
  refine ⟨B.indicator fun _ => c, stronglyMeasurable_const.indicator hB, ?_⟩
  have hsub : {ω | ¬ A.indicator (fun _ => c) ω = B.indicator (fun _ => c) ω} ⊆ A ∆ B := by
    intro ω hω
    by_contra hmem
    rw [Set.mem_symmDiff] at hmem
    have hiff : ω ∈ A ↔ ω ∈ B := by tauto
    refine hω ?_
    by_cases h : ω ∈ A
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.mp h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem fun hb => h (hiff.mpr hb)]
  rw [Filter.EventuallyEq, ae_iff]
  exact measure_mono_null hsub hAB
/-- A simple function for an augmented σ-algebra is almost everywhere `m`-strongly measurable. -/
theorem aestronglyMeasurable_simpleFunc_aug [AddZeroClass E] [ContinuousAdd E]
    (s : @MeasureTheory.SimpleFunc Ω (aug m m₀ μ) E) :
    AEStronglyMeasurable[m] (⇑s) μ := by
  induction s using MeasureTheory.SimpleFunc.induction with
  | const c hs =>
      exact aestronglyMeasurable_indicator_aug hs c
  | add _ hf hg => exact (by simpa using hf.add hg)
variable {F : Type*} [NormedAddCommGroup F] [CompleteSpace F]

/-- **Strong measurability for an augmented σ-algebra.** A function strongly measurable for
`aug m m₀ μ` is almost everywhere equal to an `m`-strongly-measurable function. -/
theorem aestronglyMeasurable_of_stronglyMeasurable_aug {f : Ω → F}
    (hf : StronglyMeasurable[aug m m₀ μ] f) : AEStronglyMeasurable[m] f μ := by
  choose g hgm hgae using fun n => aestronglyMeasurable_simpleFunc_aug (m := m) (hf.approx n)
  refine aestronglyMeasurable_of_tendsto_ae_sub hgm ?_
  have hall : ∀ᵐ ω ∂μ, ∀ n, (hf.approx n) ω = g n ω := ae_all_iff.mpr hgae
  filter_upwards [hall] with ω hω
  simpa only [hω] using hf.tendsto_approx ω
end LevyStochCalc.Probability


