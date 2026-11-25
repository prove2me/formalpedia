-- Prove2me | Definitions.Def_SourceProof_2d0886ee2025f07cabb3dec2
-- name    : SourceProof_2d0886ee2025f07cabb3dec2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:55:13.659807+00:00
-- url     : https://prove2.me/theorems/e7af318b-d769-52a2-90c0-74e77c38c02b
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.leftLimitProcess_of_usual

import Definitions.Def_SourceProof_13d74fe230d87debed607218
import Definitions.Def_SourceProof_46e00cd1de49de31920230f6
import Definitions.Def_SourceProof_59b26859132e89360b279698
import Definitions.Def_SourceProof_60e710b522febb5ad2df8d23
import Definitions.Def_SourceProof_6fe8e798f5fa5227db6c7521
import Definitions.Def_SourceProof_a2cb63993a652b5632791121

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Adaptedness of the source left-limit and jump processes -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

namespace Adapted

theorem _root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 (ha : Adapted F X) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) : Adapted F (ProbabilityTheory.leftLimitProcess X) := by
  classical
  let bad := {ω | ¬ ProbabilityTheory.IsCadlagPath (fun t ↦ X t ω)}
  have hbad : MeasurableSet[F 0] bad := (_root_.Prove2MeSourceProof.h_59b26859132e89360b279698 hF) bad (ae_iff.mp hc)
  let Y : ℝ≥0 → Ω → ℝ := fun t ω ↦ if ω ∈ bad then 0 else X t ω
  have hYa : Adapted F Y := fun t ↦
    Measurable.ite (F.mono bot_le _ hbad) measurable_const (ha t)
  have hYc : ∀ ω, ProbabilityTheory.IsCadlagPath (fun t ↦ Y t ω) := by
    intro ω
    by_cases hb : ω ∈ bad
    · simpa only [Y, if_pos hb] using
        (_root_.Prove2MeSourceProof.h_a2cb63993a652b5632791121 (continuous_const : Continuous (fun _ : ℝ≥0 ↦ (0 : ℝ))))
    · simpa only [Y, if_neg hb] using (not_not.mp hb : ProbabilityTheory.IsCadlagPath (fun t ↦ X t ω))
  have hXY : ProbabilityTheory.Indistinguishable X Y P := by
    filter_upwards [hc] with ω hω t
    exact (if_neg (show ω ∉ bad from fun hb ↦ hb hω)).symm
  have hleft := (_root_.Prove2MeSourceProof.h_6fe8e798f5fa5227db6c7521 hYa) hYc
  intro t
  have hcomplete : MeasureTheory.IsCompleteSubMeasurableSpace P (F t) :=
    fun s hs ↦ F.mono bot_le s ((_root_.Prove2MeSourceProof.h_59b26859132e89360b279698 hF) s hs)
  exact (_root_.Prove2MeSourceProof.h_46e00cd1de49de31920230f6 hcomplete) (hleft t)
    (((_root_.Prove2MeSourceProof.h_13d74fe230d87debed607218 (_root_.Prove2MeSourceProof.h_60e710b522febb5ad2df8d23 hXY))).mono (fun _ hω ↦ hω t))
end Adapted

end MeasureTheory


