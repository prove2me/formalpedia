-- Prove2me | Definitions.Def_SourceProof_8e0613e9c6d4fca4e5d3181f
-- name    : SourceProof_8e0613e9c6d4fca4e5d3181f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:29:04.635624+00:00
-- url     : https://prove2.me/theorems/625e7ea1-115a-4b26-9561-33875e5a4dd8
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.elementaryIntegralProcess_ucp_bound

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_FirstExitTruncation_F000
import Definitions.Def_SourceProof_44d1656187b87c7a69eb114b
import Definitions.Def_SourceProof_673028e029d6cd61fe3f19f1
import Definitions.Def_SourceProof_7c62585004f7ea17ee8c1e76
import Definitions.Def_SourceProof_94fc4811fced36c599242ba4
import Definitions.Def_SourceProof_c9eacbbef1c8e0923f7b8eda

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
theorem _root_.Prove2MeSourceProof.h_8e0613e9c6d4fca4e5d3181f
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (T S : ℝ≥0) (hTS : T < S) (ε : ℝ) (hε : 0 < ε) (η : ℝ≥0∞) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ H : ℝ≥0 → Ω → ℝ, ∀ hH : IsSimplePredictable H F,
      P {ω | ∃ t ≤ T, ε < ‖hH.elementaryIntegralProcess X t ω‖} ≤
        η + P {ω | ∃ t ≤ S, δ < ‖H t ω‖} := by
  let : F.IsRightContinuous := (_root_.Prove2MeSourceProof.h_94fc4811fced36c599242ba4 hF)
  obtain ⟨δ, hδ, hb⟩ := (_root_.Prove2MeSourceProof.h_7c62585004f7ea17ee8c1e76 hX) hF T ε hε η hη
  refine ⟨δ, hδ, fun H hH ↦ ?_⟩
  let τ := hittingAfter H {x | δ < ‖x‖} 0
  have hmax := hb (ProbabilityTheory.firstExitTruncation H δ) ((_root_.Prove2MeSourceProof.h_c9eacbbef1c8e0923f7b8eda hH) δ)
    ((_root_.Prove2MeSourceProof.h_673028e029d6cd61fe3f19f1 hH) hδ.le)
  have hbad : P {ω | τ ω ≤ (T : WithTop ℝ≥0)} ≤ P {ω | ∃ t ≤ S, δ < ‖H t ω‖} := by
    apply measure_mono
    intro ω hω
    have hlt : τ ω < (S : WithTop ℝ≥0) := hω.trans_lt (WithTop.coe_lt_coe.mpr hTS)
    obtain ⟨t, ht, hhit⟩ := hittingAfter_lt_iff.mp hlt
    exact ⟨t, ht.2.le, hhit⟩
  have hsub : {ω | ∃ t ≤ T, ε < ‖hH.elementaryIntegralProcess X t ω‖} ⊆
      {ω | ∃ t ≤ T, ε < ‖((_root_.Prove2MeSourceProof.h_c9eacbbef1c8e0923f7b8eda hH) δ).elementaryIntegralProcess X t ω‖} ∪
        {ω | τ ω ≤ (T : WithTop ℝ≥0)} := by
    rintro ω ⟨t, ht, hω⟩
    by_cases hτ : τ ω ≤ (T : WithTop ℝ≥0)
    · exact Or.inr hτ
    · refine Or.inl ⟨t, ht, ?_⟩
      rw [(_root_.Prove2MeSourceProof.h_44d1656187b87c7a69eb114b hH) δ X
        ((WithTop.coe_le_coe.mpr ht).trans_lt (lt_of_not_ge hτ))]
      exact hω
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add hmax hbad))
end IsSemimartingale

end ProbabilityTheory


