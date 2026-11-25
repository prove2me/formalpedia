-- Prove2me | Definitions.Def_SourceProof_85cd6acbb88cb0e0bb47ef85
-- name    : SourceProof_85cd6acbb88cb0e0bb47ef85
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:32:27.794924+00:00
-- url     : https://prove2.me/theorems/80ed17fc-2a3d-52cc-a31f-5bb77dfbdc18
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.tendstoUCP_elementaryIntegralProcess_zero

import Definitions.Def_StochLean_Probability_Process_UCP_F001
import Definitions.Def_SourceProof_8e0613e9c6d4fca4e5d3181f
import Definitions.Def_SourceProof_c85f5070e7769bac711d7f66

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # UCP continuity of the source elementary integral process

Protter II.11 on the full simple predictable source class. Actual left-continuous
first-exit truncations are uniformly bounded and agree with the source before the
exit. A slightly larger input horizon avoids attributing an open hit to its boundary,
including a right jump at time zero. No density, completeness or limit selector is assumed.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_85cd6acbb88cb0e0bb47ef85
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    {H : ℕ → ℝ≥0 → Ω → ℝ} (hH : ∀ n, IsSimplePredictable (H n) F)
    (hu : TendstoUCP P H atTop 0) :
    TendstoUCP P (fun n ↦ (hH n).elementaryIntegralProcess X) atTop 0 := by
  apply _root_.Prove2MeSourceProof.h_c85f5070e7769bac711d7f66.mpr
  intro T ε hε
  simp only [Pi.zero_apply, sub_zero]
  apply ENNReal.tendsto_atTop_zero.mpr
  intro η hη
  obtain ⟨δ, hδ, hb⟩ := (_root_.Prove2MeSourceProof.h_8e0613e9c6d4fca4e5d3181f hX) hF T (T + 1)
    (lt_add_one T) ε hε (η / 2) (ENNReal.half_pos hη.ne')
  have hin := _root_.Prove2MeSourceProof.h_c85f5070e7769bac711d7f66.mp hu (T + 1) δ hδ
  simp only [Pi.zero_apply, sub_zero] at hin
  obtain ⟨N, hN⟩ := ENNReal.tendsto_atTop_zero.mp hin (η / 2) (ENNReal.half_pos hη.ne')
  refine ⟨N, fun n hn ↦ ?_⟩
  calc
    _ ≤ η / 2 + P {ω | ∃ t ≤ T + 1, δ < ‖H n t ω‖} := hb (H n) (hH n)
    _ ≤ η / 2 + η / 2 := add_le_add le_rfl (hN n hn)
    _ = η := ENNReal.add_halves η
end IsSemimartingale

end ProbabilityTheory


