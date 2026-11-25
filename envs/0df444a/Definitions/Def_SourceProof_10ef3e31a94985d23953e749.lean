-- Prove2me | Definitions.Def_SourceProof_10ef3e31a94985d23953e749
-- name    : SourceProof_10ef3e31a94985d23953e749
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:27:50.258273+00:00
-- url     : https://prove2.me/theorems/19157dce-8349-47c7-80a3-13641b721b26
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.exists_stieltjes_indistinguishable_of_usual

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_FiniteVariation_Stieltjes_F000
import Definitions.Def_SourceProof_59b26859132e89360b279698

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Adapted Stieltjes realizations of almost surely increasing paths

A single initial null-event reset produces genuine Stieltjes paths, retaining
the original process at all times on one event. No moment assumption is used.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory StochLean Set
open scoped NNReal

namespace MeasureTheory

namespace Adapted
theorem _root_.Prove2MeSourceProof.h_10ef3e31a94985d23953e749
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} (ha : Adapted F X) (hF : F.IsUsual P)
    (hm : HasMonotonePaths X P) (hr : HasRightContinuousPaths X P) :
    ∃ B : Ω → StieltjesFunction ℝ≥0,
      Adapted F (fun t ω ↦ B ω t) ∧ Indistinguishable X (fun t ω ↦ B ω t) P := by
  classical
  let bad := {ω | ¬ (Monotone (fun t ↦ X t ω) ∧ ProbabilityTheory.IsRightContinuousPath (fun t ↦ X t ω))}
  have hbad : MeasurableSet[F 0] bad := (_root_.Prove2MeSourceProof.h_59b26859132e89360b279698 hF) bad (ae_iff.mp (hm.and hr))
  let Y : ℝ≥0 → Ω → ℝ := fun t ω ↦ if ω ∈ bad then 0 else X t ω
  have hYa : Adapted F Y := fun t ↦
    Measurable.ite (F.mono bot_le _ hbad) measurable_const (ha t)
  have hY (ω : Ω) : Monotone (fun t ↦ Y t ω) ∧ ProbabilityTheory.IsRightContinuousPath (fun t ↦ Y t ω) := by
    by_cases hb : ω ∈ bad
    · simp only [Y, if_pos hb]
      exact ⟨monotone_const, fun _ ↦ continuousWithinAt_const⟩
    · simpa only [Y, if_neg hb] using
        (not_not.mp hb : Monotone (fun t ↦ X t ω) ∧ ProbabilityTheory.IsRightContinuousPath (fun t ↦ X t ω))
  let B : Ω → StieltjesFunction ℝ≥0 := fun ω ↦ ⟨fun t ↦ Y t ω, (hY ω).1, (hY ω).2⟩
  refine ⟨B, hYa, ?_⟩
  filter_upwards [hm, hr] with ω hmω hrω t
  exact (if_neg (show ω ∉ bad from fun hb ↦ hb ⟨hmω, hrω⟩)).symm
end Adapted

end MeasureTheory


