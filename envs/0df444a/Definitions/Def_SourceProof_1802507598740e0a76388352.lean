-- Prove2me | Definitions.Def_SourceProof_1802507598740e0a76388352
-- name    : SourceProof_1802507598740e0a76388352
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:32:47.886797+00:00
-- url     : https://prove2.me/theorems/ca314eb8-faae-58b2-9f7a-4a72a0bbe7a1
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.elementaryIntegralProcess_cauchyUCP

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_Basic_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_FirstExitTruncation_F000
import Definitions.Def_SourceProof_8e0613e9c6d4fca4e5d3181f
import Definitions.Def_SourceProof_bc53441c2020b643491018cd
import Definitions.Def_SourceProof_cc0035184dadaa0334c1eb46
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.LocalProperty

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

theorem _root_.Prove2MeSourceProof.h_1802507598740e0a76388352
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    {H : ℕ → ℝ≥0 → Ω → ℝ} (hH : ∀ n, IsSimplePredictable (H n) F)
    (hc : ∀ T : ℝ≥0, ∀ ε : ℝ, 0 < ε → ∀ η : ℝ≥0∞, 0 < η → ∃ N : ℕ,
      ∀ m n, N ≤ m → N ≤ n → P {ω | ∃ t ≤ T, ε < ‖H m t ω - H n t ω‖} ≤ η) :
    ∀ T : ℝ≥0, ∀ ε : ℝ, 0 < ε → ∀ η : ℝ≥0∞, 0 < η → ∃ N : ℕ,
      ∀ m n, N ≤ m → N ≤ n → P {ω | ∃ t ≤ T,
        ε < ‖(hH m).elementaryIntegralProcess X t ω -
          (hH n).elementaryIntegralProcess X t ω‖} ≤ η := by
  intro T ε hε η hη
  obtain ⟨δ, hδ, hb⟩ := (_root_.Prove2MeSourceProof.h_8e0613e9c6d4fca4e5d3181f hX) hF T (T + 1)
    (lt_add_one T) ε hε (η / 2) (ENNReal.half_pos hη.ne')
  obtain ⟨N, hN⟩ := hc (T + 1) δ hδ (η / 2) (ENNReal.half_pos hη.ne')
  refine ⟨N, fun m n hm hn ↦ ?_⟩
  have h := hb (H m - H n) ((_root_.Prove2MeSourceProof.h_bc53441c2020b643491018cd (hH m)) (hH n))
  rw [(_root_.Prove2MeSourceProof.h_cc0035184dadaa0334c1eb46 (hH m)) (hH n) X] at h
  exact h.trans ((add_le_add le_rfl (hN m n hm hn)).trans (ENNReal.add_halves η).le)
end IsSemimartingale

end ProbabilityTheory


