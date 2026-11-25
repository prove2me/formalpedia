-- Prove2me | Definitions.Def_SourceProof_669e8684f0a562efdd6c1030
-- name    : SourceProof_669e8684f0a562efdd6c1030
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:06:35.792385+00:00
-- url     : https://prove2.me/theorems/6581bbfc-6ec9-5395-90aa-380a8200d345
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.exists_cadlag_finiteVariation_indistinguishable_of_usual

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_FiniteVariation_Jordan_F000
import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Definitions.Def_SourceProof_59b26859132e89360b279698
import Definitions.Def_SourceProof_6a141fa6412d14db4fc15aeb
import Definitions.Def_SourceProof_a2cb63993a652b5632791121
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Kernel.Basic

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Random Stieltjes measures of finite-variation processes

The three kernels are the deterministic canonical measures on each path. Their
restrictions through time `T` are measurable for the original `F T`, not merely
the ambient sigma-algebra. A common null-event reset supplies everywhere-good
versions from the almost-sure source assumptions under usual conditions.
-/

@[expose] public section

open MeasureTheory StochLean Set Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  (X : ℝ≥0 → Ω → ℝ) (ha : Adapted F X)
  (hv : ∀ ω, LocallyBoundedVariationOn (fun t ↦ X t ω) univ)
  (hr : ∀ ω, IsRightContinuousPath (fun t ↦ X t ω))

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

namespace Adapted
theorem _root_.Prove2MeSourceProof.h_669e8684f0a562efdd6c1030
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} (ha : Adapted F X) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) (hv : HasFiniteVariationPaths X P) :
    ∃ Y : ℝ≥0 → Ω → ℝ, Indistinguishable X Y P ∧ IsStronglyProgressive F Y ∧
      ∀ ω, IsCadlagPath (fun t ↦ Y t ω) ∧ LocallyBoundedVariationOn (fun t ↦ Y t ω) univ := by
  classical
  let bad := {ω | ¬ (ProbabilityTheory.IsCadlagPath (fun t ↦ X t ω) ∧
    LocallyBoundedVariationOn (fun t ↦ X t ω) univ)}
  have hbad : MeasurableSet[F 0] bad := (_root_.Prove2MeSourceProof.h_59b26859132e89360b279698 hF) bad (ae_iff.mp (hc.and hv))
  let Y : ℝ≥0 → Ω → ℝ := fun t ω ↦ if ω ∈ bad then 0 else X t ω
  have hYa : StronglyAdapted F Y := fun t ↦
    StronglyMeasurable.ite (F.mono bot_le _ hbad) stronglyMeasurable_const (ha t).stronglyMeasurable
  have hY : ∀ ω, ProbabilityTheory.IsCadlagPath (fun t ↦ Y t ω) ∧
      LocallyBoundedVariationOn (fun t ↦ Y t ω) univ := by
    intro ω
    by_cases hb : ω ∈ bad
    · simp only [Y, if_pos hb]
      exact ⟨_root_.Prove2MeSourceProof.h_a2cb63993a652b5632791121 continuous_const,
        (monotone_const.monotoneOn univ).locallyBoundedVariationOn⟩
    · simpa only [Y, if_neg hb] using (not_not.mp hb : ProbabilityTheory.IsCadlagPath (fun t ↦ X t ω) ∧
        LocallyBoundedVariationOn (fun t ↦ X t ω) univ)
  refine ⟨Y, ?_, (_root_.Prove2MeSourceProof.h_6a141fa6412d14db4fc15aeb hYa) (fun ω ↦ (hY ω).1.1), hY⟩
  filter_upwards [hc, hv] with ω hcω hvω t
  exact (if_neg (show ω ∉ bad from fun hb ↦ hb ⟨hcω, hvω⟩)).symm
end Adapted

end MeasureTheory


