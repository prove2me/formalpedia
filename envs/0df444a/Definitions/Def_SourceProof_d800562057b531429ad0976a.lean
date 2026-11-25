-- Prove2me | Definitions.Def_SourceProof_d800562057b531429ad0976a
-- name    : SourceProof_d800562057b531429ad0976a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:16:25.478976+00:00
-- url     : https://prove2.me/theorems/83b4e949-1d9f-55e5-a14e-cd4540904de0
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.exists_caglad_indistinguishable_of_usual

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_Path_Caglad_F000
import Definitions.Def_SourceProof_50bef199e170152e0882c89e
import Definitions.Def_SourceProof_59b26859132e89360b279698
import Mathlib.Probability.Process.Adapted

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Everywhere-caglad indistinguishable adapted versions

The single exceptional path event is reset at time zero using usual completeness.
The original initial value is retained on the common full-measure event.
-/

@[expose] public section

open ProbabilityTheory MeasureTheory Set
open scoped NNReal

namespace MeasureTheory

namespace Adapted
theorem _root_.Prove2MeSourceProof.h_d800562057b531429ad0976a
    {Ω E : Type*} {mΩ : MeasurableSpace Ω} [TopologicalSpace E]
    [MeasurableSpace E] [Zero E] {F : Filtration ℝ≥0 mΩ}
    {P : Measure Ω} {X : ℝ≥0 → Ω → E}
    (hX : Adapted F X) (hF : F.IsUsual P) (hc : HasCagladPaths X P) :
    ∃ Y : ℝ≥0 → Ω → E, Indistinguishable X Y P ∧ Adapted F Y ∧
      ∀ ω, IsCagladPath (Y · ω) := by
  classical
  let bad := {ω | ¬ ProbabilityTheory.IsCagladPath (X · ω)}
  have hbad : MeasurableSet[F 0] bad := (_root_.Prove2MeSourceProof.h_59b26859132e89360b279698 hF) bad (ae_iff.mp hc)
  let Y : ℝ≥0 → Ω → E := fun t ω ↦ if ω ∈ bad then 0 else X t ω
  refine ⟨Y, ?_, fun t ↦
    Measurable.ite (F.mono bot_le bad hbad) measurable_const (hX t), ?_⟩
  · filter_upwards [hc] with ω hω t
    exact (if_neg (show ω ∉ bad from fun h ↦ h hω)).symm
  · intro ω
    by_cases hb : ω ∈ bad
    · simpa only [Y, if_pos hb] using
        (_root_.Prove2MeSourceProof.h_50bef199e170152e0882c89e (continuous_const : Continuous (fun _ : ℝ≥0 ↦ (0 : E))))
    · simpa only [Y, if_neg hb] using (not_not.mp hb : ProbabilityTheory.IsCagladPath (X · ω))
end Adapted

end MeasureTheory


