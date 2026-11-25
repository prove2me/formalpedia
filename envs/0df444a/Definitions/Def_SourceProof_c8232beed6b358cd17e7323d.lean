-- Prove2me | Definitions.Def_SourceProof_c8232beed6b358cd17e7323d
-- name    : SourceProof_c8232beed6b358cd17e7323d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:40:51.410208+00:00
-- url     : https://prove2.me/theorems/0451e31a-b217-5f08-a115-3579970ff08b
-- title:
--   StochLean source theorem: MeasureTheory.StronglyAdapted.exists_cadlag_indistinguishable_of_usual

import Definitions.Def_StochLean_Probability_Process_Measurability_Progressive_F001
import Definitions.Def_SourceProof_59b26859132e89360b279698
import Definitions.Def_SourceProof_6a141fa6412d14db4fc15aeb
import Definitions.Def_SourceProof_a2cb63993a652b5632791121

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Everywhere-cadlag indistinguishable versions under usual conditions -/

@[expose] public section

open ProbabilityTheory MeasureTheory Filter Set TopologicalSpace
open scoped NNReal

namespace MeasureTheory

namespace StronglyAdapted
theorem _root_.Prove2MeSourceProof.h_c8232beed6b358cd17e7323d
    {Ω E : Type*} {mΩ : MeasurableSpace Ω} [TopologicalSpace E]
    [PseudoMetrizableSpace E] [Zero E] {F : Filtration ℝ≥0 mΩ}
    {P : Measure Ω} {X : ℝ≥0 → Ω → E}
    (ha : StronglyAdapted F X) (hF : F.IsUsual P) (hc : HasCadlagPaths X P) :
    ∃ Y : ℝ≥0 → Ω → E, Indistinguishable X Y P ∧ IsStronglyProgressive F Y ∧
      ∀ ω, IsCadlagPath (fun t ↦ Y t ω) := by
  classical
  let bad := {ω | ¬ ProbabilityTheory.IsCadlagPath (fun t ↦ X t ω)}
  have hbad : MeasurableSet[F 0] bad := (_root_.Prove2MeSourceProof.h_59b26859132e89360b279698 hF) bad (ae_iff.mp hc)
  let Y : ℝ≥0 → Ω → E := fun t ω ↦ if ω ∈ bad then 0 else X t ω
  have hYa : StronglyAdapted F Y := fun t ↦
    StronglyMeasurable.ite (F.mono bot_le _ hbad) stronglyMeasurable_const (ha t)
  have hYc : ∀ ω, ProbabilityTheory.IsCadlagPath (fun t ↦ Y t ω) := by
    intro ω
    by_cases hb : ω ∈ bad
    · simp only [Y, if_pos hb]
      exact _root_.Prove2MeSourceProof.h_a2cb63993a652b5632791121 continuous_const
    · simpa only [Y, if_neg hb] using (not_not.mp hb : ProbabilityTheory.IsCadlagPath (fun t ↦ X t ω))
  refine ⟨Y, ?_, (_root_.Prove2MeSourceProof.h_6a141fa6412d14db4fc15aeb hYa) (fun ω ↦ (hYc ω).1), hYc⟩
  filter_upwards [hc] with ω hω t
  exact (if_neg (show ω ∉ bad from fun hb ↦ hb hω)).symm
end StronglyAdapted

end MeasureTheory


