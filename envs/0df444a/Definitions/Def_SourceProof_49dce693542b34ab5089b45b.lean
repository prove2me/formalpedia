-- Prove2me | Definitions.Def_SourceProof_49dce693542b34ab5089b45b
-- name    : SourceProof_49dce693542b34ab5089b45b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:20:06.855509+00:00
-- url     : https://prove2.me/theorems/89db8cb6-29f9-56b0-a006-ad61acca567a
-- title:
--   StochLean source theorem: MeasureTheory.StronglyAdapted.exists_isStronglyProgressive_modification_of_hasRightContinuousPaths

import Definitions.Def_StochLean_Probability_Process_Measurability_Joint_F000
import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F000
import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Definitions.Def_SourceProof_59b26859132e89360b279698
import Definitions.Def_SourceProof_6a141fa6412d14db4fc15aeb
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.Floor

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Progressive measurability from right-continuous paths

For nonnegative real time, a strongly adapted process with right-continuous trajectories is
strongly progressive. The proof uses measurable countable-range right-grid approximations; it
does not strengthen right continuity to continuity.
-/

@[expose] public section

open NNReal TopologicalSpace
open scoped Topology

namespace MeasureTheory

namespace StronglyAdapted


theorem _root_.Prove2MeSourceProof.h_49dce693542b34ab5089b45b
    {Ω E : Type*} {mΩ : MeasurableSpace Ω} [TopologicalSpace E]
    [PseudoMetrizableSpace E] [Zero E] {ℱ : Filtration ℝ≥0 mΩ}
    {P : Measure Ω} {X : ℝ≥0 → Ω → E}
    (hX : StronglyAdapted ℱ X) (hℱ : ℱ.IsUsual P)
    (hpaths : ProbabilityTheory.HasRightContinuousPaths X P) :
    ∃ Y : ℝ≥0 → Ω → E, ProbabilityTheory.IsModification X Y P ∧
      IsStronglyProgressive ℱ Y ∧
      ∀ ω, ProbabilityTheory.IsRightContinuousPath fun t ↦ Y t ω := by
  classical
  let bad := {ω | ¬ ProbabilityTheory.IsRightContinuousPath fun t ↦ X t ω}
  have hbad0 : P bad = 0 := ae_iff.mp hpaths
  have hbad_bot : MeasurableSet[ℱ ⊥] bad := (_root_.Prove2MeSourceProof.h_59b26859132e89360b279698 hℱ) bad hbad0
  let Y (t : ℝ≥0) (ω : Ω) := if ω ∈ bad then 0 else X t ω
  have hYadapted : StronglyAdapted ℱ Y := by
    intro t
    have hbad_t : MeasurableSet[ℱ t] bad := ℱ.mono bot_le bad hbad_bot
    exact StronglyMeasurable.ite hbad_t stronglyMeasurable_const (hX t)
  have hYpaths : ∀ ω, ProbabilityTheory.IsRightContinuousPath fun t ↦ Y t ω := by
    intro ω
    by_cases hω : ω ∈ bad
    · simp only [Y, if_pos hω]
      exact fun _ ↦ continuousWithinAt_const
    · have hreg : ProbabilityTheory.IsRightContinuousPath fun t ↦ X t ω := by
        change ¬ (¬ ProbabilityTheory.IsRightContinuousPath fun t ↦ X t ω) at hω
        exact not_not.mp hω
      simpa only [Y, if_neg hω] using hreg
  refine ⟨Y, ?_, (_root_.Prove2MeSourceProof.h_6a141fa6412d14db4fc15aeb hYadapted) hYpaths, hYpaths⟩
  intro t
  filter_upwards [hpaths] with ω hω
  have hωbad : ω ∉ bad := by
    intro hbad
    exact hbad hω
  simp only [Y, if_neg hωbad]
end StronglyAdapted

end MeasureTheory


