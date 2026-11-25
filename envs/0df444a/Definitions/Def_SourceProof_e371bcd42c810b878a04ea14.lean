-- Prove2me | Definitions.Def_SourceProof_e371bcd42c810b878a04ea14
-- name    : SourceProof_e371bcd42c810b878a04ea14
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:17:42.835016+00:00
-- url     : https://prove2.me/theorems/097ba0a0-4b40-53cd-a6b1-c62f26db85d3
-- title:
--   StochLean source theorem: ProbabilityTheory.IsTotalSemimartingale.elementaryIntegralProcess_maximal_uniform

import Definitions.Def_StochLean_Probability_Process_Semimartingale_Basic_F001
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F006
import Definitions.Def_SourceProof_81fed43029cb26012ba5024c
import Definitions.Def_SourceProof_91776c6d66e3ec9a393c48f3
import Definitions.Def_SourceProof_932e1321dcffebeba90e2ea9
import Definitions.Def_SourceProof_9f2f3563711c68b81e63664c
import Definitions.Def_SourceProof_b755025803f0c28ce74bcca6
import Definitions.Def_SourceProof_bae5ae9701ba5ce704cf231a
import Definitions.Def_SourceProof_c33d5d3cc46a7b08b3b6917b
import Definitions.Def_SourceProof_d14c6a5c22923c1d07f1756e
import Definitions.Def_SourceProof_ebaf9e73dbb24b573c624591

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The source elementary integral maximal estimate

This is the uniform-input step in Protter II.11. A total good integrator controls
the entire elementary integral process on each compact horizon by applying the
existing terminal estimate to the simple integrand cut off at a finite first exit.
It does not yet assume or prove UCP density, completeness or a general integral.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

namespace IsTotalSemimartingale
theorem _root_.Prove2MeSourceProof.h_e371bcd42c810b878a04ea14
    (hX : IsTotalSemimartingale X F P) (hF : F.IsUsual P)
    (ε : ℝ) (hε : 0 < ε) (η : ℝ≥0∞) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ H : ℝ≥0 → Ω → ℝ,
      ∀ hH : IsSimplePredictable H F, (∀ t ω, ‖H t ω‖ ≤ δ) → ∀ T : ℝ≥0,
      P {ω | ∃ t ≤ T, ε < ‖hH.elementaryIntegralProcess X t ω‖} ≤ η := by
  obtain ⟨δ, hδ, hb⟩ := (_root_.Prove2MeSourceProof.h_91776c6d66e3ec9a393c48f3.mp hX.2.2) ε hε η hη
  refine ⟨δ, hδ, fun H hH hbound T ↦ ?_⟩
  let Y := hH.elementaryIntegralProcess X
  have hrY : ProbabilityTheory.HasRightContinuousPaths Y P :=
    (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c ((_root_.Prove2MeSourceProof.h_932e1321dcffebeba90e2ea9 hH) hX.2.1))
  have haY : Adapted F Y := (_root_.Prove2MeSourceProof.h_bae5ae9701ba5ce704cf231a hH) hX.1 hF
    (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c hX.2.1)
  have hτ := (_root_.Prove2MeSourceProof.h_b755025803f0c28ce74bcca6 haY) hF hrY ε
  let σ := ProbabilityTheory.FiniteStoppingTime.truncate hτ T
  have hσ : IsStoppingTime F σ.withTop := σ.isStoppingTime
  have hsize : ∀ t ω, ‖ProbabilityTheory.cutoffIntegrand H σ.withTop t ω‖ ≤ δ := by
    intro t ω
    simp only [ProbabilityTheory.cutoffIntegrand]
    split_ifs
    · exact hbound t ω
    · simpa only [norm_zero] using hδ.le
  have hi := hb _ ((_root_.Prove2MeSourceProof.h_ebaf9e73dbb24b573c624591 hH) hσ) hsize
  have heq (ω : Ω) : ((_root_.Prove2MeSourceProof.h_ebaf9e73dbb24b573c624591 hH) hσ).elementaryIntegral X ω =
      stoppedProcess Y (hittingAfter Y {x | ε < ‖x‖} 0) T ω := by
    rw [(_root_.Prove2MeSourceProof.h_d14c6a5c22923c1d07f1756e hH) hσ X,
      (_root_.Prove2MeSourceProof.h_c33d5d3cc46a7b08b3b6917b hH) X σ]
    rfl
  calc
    _ ≤ P {ω | ε ≤ ‖stoppedProcess Y (hittingAfter Y {x | ε < ‖x‖} 0) T ω‖} :=
      _root_.Prove2MeSourceProof.h_81fed43029cb26012ba5024c hrY ε T
    _ = P {ω | ε ≤ ‖((_root_.Prove2MeSourceProof.h_ebaf9e73dbb24b573c624591 hH) hσ).elementaryIntegral X ω‖} := by simp only [heq]
    _ ≤ η := hi
end IsTotalSemimartingale

end ProbabilityTheory


