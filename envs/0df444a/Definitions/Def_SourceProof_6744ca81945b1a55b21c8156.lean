-- Prove2me | Definitions.Def_SourceProof_6744ca81945b1a55b21c8156
-- name    : SourceProof_6744ca81945b1a55b21c8156
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:00:37.493845+00:00
-- url     : https://prove2.me/theorems/188d04d8-a090-4f0f-9d3c-a4c2c0974007
-- title:
--   StochLean source theorem: MeasureTheory.Filtration.exists_measurableSet_eventually_iff

import Mathlib.Probability.Martingale.Convergence

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Eventually correct event approximations along an increasing filtration

Thresholding the conditional expectations of an indicator at one half gives
events in the individual sigma-fields whose membership eventually agrees
with the original event almost surely. This is native Levy upward convergence,
not a claim that every terminal event belongs to a finite sigma-field.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace MeasureTheory.Filtration

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]

theorem _root_.Prove2MeSourceProof.h_6744ca81945b1a55b21c8156 (F : Filtration ℕ mΩ) {A : Set Ω}
    (hA : MeasurableSet[⨆ n, F n] A) :
    ∃ B : ℕ → Set Ω, (∀ n, MeasurableSet[F n] (B n)) ∧
      ∀ᵐ ω ∂P, ∀ᶠ n in atTop, (ω ∈ B n ↔ ω ∈ A) := by
  let Z : Ω → ℝ := A.indicator (fun _ ↦ 1)
  have hZA : StronglyMeasurable[⨆ n, F n] Z := stronglyMeasurable_const.indicator hA
  have hAm : MeasurableSet A := (iSup_le F.le) A hA
  have hZi : Integrable Z P := (integrable_const 1).indicator hAm
  have hl := hZi.tendsto_ae_condExp (ℱ := F) hZA
  refine ⟨fun n ↦ {ω | (1 / 2 : ℝ) < P[Z | F n] ω}, fun n ↦ ?_, ?_⟩
  · exact measurableSet_lt measurable_const stronglyMeasurable_condExp.measurable
  · filter_upwards [hl] with ω hω
    by_cases hωA : ω ∈ A
    · have he : Z ω = 1 := Set.indicator_of_mem hωA _
      rw [he] at hω
      filter_upwards [hω.eventually (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1))]
        with n hn
      exact iff_of_true hn hωA
    · have he : Z ω = 0 := Set.indicator_of_notMem hωA _
      rw [he] at hω
      filter_upwards [hω.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
        with n hn
      exact iff_of_false (not_lt.mpr hn.le) hωA
end MeasureTheory.Filtration


