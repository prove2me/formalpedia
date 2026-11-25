-- Prove2me | Definitions.Def_SourceProof_d01ba5ff5c179dcd321a94d0
-- name    : SourceProof_d01ba5ff5c179dcd321a94d0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:36:11.599166+00:00
-- url     : https://prove2.me/theorems/bbed5ec6-c069-5ece-8a39-eccf5d093d7e
-- title:
--   StochLean source theorem: MeasureTheory.StronglyAdapted.exists_continuous_indistinguishable_of_usual

import Definitions.Def_StochLean_Probability_Process_Measurability_Progressive_F001
import Definitions.Def_SourceProof_59b26859132e89360b279698
import Definitions.Def_SourceProof_6a141fa6412d14db4fc15aeb

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Everywhere-continuous indistinguishable versions

Relative completeness makes the single exceptional path event measurable at time zero.
The constructed version is zero there; no joint regularity of the original exceptional paths
is claimed. This version permits continuous-path first-passage constructions.
-/

@[expose] public section

open ProbabilityTheory MeasureTheory Filter Set TopologicalSpace
open scoped NNReal

namespace MeasureTheory

namespace StronglyAdapted
theorem _root_.Prove2MeSourceProof.h_d01ba5ff5c179dcd321a94d0
    {Ω E : Type*} {mΩ : MeasurableSpace Ω} [TopologicalSpace E]
    [PseudoMetrizableSpace E] [Zero E] {F : Filtration ℝ≥0 mΩ}
    {P : Measure Ω} {X : ℝ≥0 → Ω → E}
    (hX : StronglyAdapted F X) (hF : F.IsUsual P) (hc : HasContinuousPaths X P) :
    ∃ Y : ℝ≥0 → Ω → E, Indistinguishable X Y P ∧ IsStronglyProgressive F Y ∧
      ∀ ω, Continuous (Y · ω) := by
  classical
  let bad := {ω | ¬ Continuous (X · ω)}
  have hbad : MeasurableSet[F 0] bad := (_root_.Prove2MeSourceProof.h_59b26859132e89360b279698 hF) bad (ae_iff.mp hc)
  let Y : ℝ≥0 → Ω → E := fun t ω ↦ if ω ∈ bad then 0 else X t ω
  have ha : StronglyAdapted F Y := fun t ↦
    StronglyMeasurable.ite (F.mono bot_le bad hbad) stronglyMeasurable_const (hX t)
  have hY : ∀ ω, Continuous (Y · ω) := by
    intro ω
    by_cases hb : ω ∈ bad
    · simpa only [Y, if_pos hb] using (continuous_const : Continuous (fun _ : ℝ≥0 ↦ (0 : E)))
    · have hcont : Continuous (X · ω) := not_not.mp hb
      simpa only [Y, if_neg hb] using hcont
  refine ⟨Y, ?_, (_root_.Prove2MeSourceProof.h_6a141fa6412d14db4fc15aeb ha)
    (fun ω _ ↦ (hY ω).continuousWithinAt), hY⟩
  filter_upwards [hc] with ω hω t
  exact (if_neg (show ω ∉ bad from fun h ↦ h hω)).symm
end StronglyAdapted

end MeasureTheory


