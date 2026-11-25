-- Prove2me | Definitions.Def_SourceProof_f60f6796fd78b83be1f764d1
-- name    : SourceProof_f60f6796fd78b83be1f764d1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:15:52.012829+00:00
-- url     : https://prove2.me/theorems/283b644e-d5f2-4cdc-8263-6c4b692b1445
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.rightLimitProcess_of_usual

import Definitions.Def_SourceProof_13d74fe230d87debed607218
import Definitions.Def_SourceProof_46e00cd1de49de31920230f6
import Definitions.Def_SourceProof_50bef199e170152e0882c89e
import Definitions.Def_SourceProof_59b26859132e89360b279698
import Definitions.Def_SourceProof_75a69f168b91f3bff282b188
import Definitions.Def_SourceProof_94fc4811fced36c599242ba4
import Definitions.Def_SourceProof_a3bc82106adf606a13e0e393

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Adaptedness of a caglad process's right-limit process

The right limit at `t` is measurable in every `F_u`, `u > t`, by actual sequences
inside `(t,u)`. Right continuity of the filtration then gives `F_t` measurability.
Usual completeness transports the statement on one common exceptional path event.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

namespace Adapted
theorem _root_.Prove2MeSourceProof.h_f60f6796fd78b83be1f764d1 (ha : Adapted F X) (hF : F.IsUsual P)
    (hc : HasCagladPaths X P) : Adapted F (ProbabilityTheory.rightLimitProcess X) := by
  classical
  let bad := {ω | ¬ ProbabilityTheory.IsCagladPath (X · ω)}
  have hbad : MeasurableSet[F 0] bad := (_root_.Prove2MeSourceProof.h_59b26859132e89360b279698 hF) bad (ae_iff.mp hc)
  let Y : ℝ≥0 → Ω → ℝ := fun t ω ↦ if ω ∈ bad then 0 else X t ω
  have hYa : Adapted F Y := fun t ↦
    Measurable.ite (F.mono bot_le _ hbad) measurable_const (ha t)
  have hYc : ∀ ω, ProbabilityTheory.IsCagladPath (Y · ω) := by
    intro ω
    by_cases hb : ω ∈ bad
    · simpa only [Y, if_pos hb] using
        (_root_.Prove2MeSourceProof.h_50bef199e170152e0882c89e (continuous_const : Continuous (fun _ : ℝ≥0 ↦ (0 : ℝ))))
    · simpa only [Y, if_neg hb] using (not_not.mp hb : ProbabilityTheory.IsCagladPath (X · ω))
  have hXY : ProbabilityTheory.Indistinguishable X Y P := by
    filter_upwards [hc] with ω hω t
    exact (if_neg (show ω ∉ bad from fun hb ↦ hb hω)).symm
  let : F.IsRightContinuous := (_root_.Prove2MeSourceProof.h_94fc4811fced36c599242ba4 hF)
  have hright := (_root_.Prove2MeSourceProof.h_75a69f168b91f3bff282b188 hYa) hYc
  intro t
  have hcomplete : MeasureTheory.IsCompleteSubMeasurableSpace P (F t) :=
    fun s hs ↦ F.mono bot_le s ((_root_.Prove2MeSourceProof.h_59b26859132e89360b279698 hF) s hs)
  exact (_root_.Prove2MeSourceProof.h_46e00cd1de49de31920230f6 hcomplete) (hright t)
    (((_root_.Prove2MeSourceProof.h_13d74fe230d87debed607218 (_root_.Prove2MeSourceProof.h_a3bc82106adf606a13e0e393 hXY))).mono (fun _ hω ↦ hω t))
end Adapted

end MeasureTheory


