-- Prove2me | Definitions.Def_SourceProof_9f462e2767fad5b3edec7d2e
-- name    : SourceProof_9f462e2767fad5b3edec7d2e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:15:03.101005+00:00
-- url     : https://prove2.me/theorems/351fb9c2-4cff-4394-9c71-cd07d5ae9158
-- title:
--   StochLean source theorem: ProbabilityTheory.isSemimartingale_of_preLocalizingSequence

import Definitions.Def_SourceProof_056f0ffa0965e1b3a522e2ff
import Definitions.Def_SourceProof_1557efb7e848f4cf57c0170c
import Definitions.Def_SourceProof_42afccfd7ebdae0f6473035d
import Definitions.Def_SourceProof_9127ba9e47e57c570411dae8
import Definitions.Def_SourceProof_96c0d23ed76988d7c3d3ef45
import Definitions.Def_SourceProof_a239f509638bc9274841d0b5
import Definitions.Def_SourceProof_d708bd4cbd825857e79d3668
import Definitions.Def_SourceProof_faea1308e58b2b1b6deb90cf

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Localization of source good integrators and semimartingales

Elementary integrals agree when entire integrator paths agree. This proves closure under
approximation outside sets of vanishing probability and then the local-to-global direction
for ordinary semimartingales, including the Protter time-zero mask.
-/

@[expose] public section

open MeasureTheory Filter Set Finset
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X Y : ℝ≥0 → Ω → ℝ}

variable [IsFiniteMeasure P]


theorem _root_.Prove2MeSourceProof.h_9f462e2767fad5b3edec7d2e (ha : Adapted F X) (hc : HasCadlagPaths X P)
    {τ : ℕ → Ω → WithTop ℝ≥0} (hτ : IsPreLocalizingSequence F τ P)
    (hY : ∀ n, IsSemimartingale
      (stoppedProcess (fun s ↦ {ω | 0 < τ n ω}.indicator (X s)) (τ n)) F P) :
    IsSemimartingale X F P := by
  intro T
  change ProbabilityTheory.IsTotalSemimartingale (stoppedProcess X (ProbabilityTheory.FiniteStoppingTime.const F T).withTop) F P
  rw [_root_.Prove2MeSourceProof.h_faea1308e58b2b1b6deb90cf]
  refine ⟨fun t ↦ (ha _).mono (F.mono (min_le_left t T)) le_rfl,
    hc.mono (fun _ h ↦ (_root_.Prove2MeSourceProof.h_056f0ffa0965e1b3a522e2ff h) T), ?_⟩
  let Y : ℕ → ℝ≥0 → Ω → ℝ := fun n ↦
    stoppedProcess (fun s ↦ {ω | 0 < τ n ω}.indicator (X s)) (τ n)
  apply _root_.Prove2MeSourceProof.h_42afccfd7ebdae0f6473035d (fun n t ↦ Y n (min t T))
    (fun n ↦ {ω | τ n ω ≤ T}) ?_ ?_ ((_root_.Prove2MeSourceProof.h_d708bd4cbd825857e79d3668 hτ) T)
  · intro n
    have h := (hY n T).2.2
    change ProbabilityTheory.IsGoodIntegrator (stoppedProcess (Y n) (ProbabilityTheory.FiniteStoppingTime.const F T).withTop) F P at h
    rwa [_root_.Prove2MeSourceProof.h_faea1308e58b2b1b6deb90cf] at h
  · intro n ω hn t
    have hT : (T : WithTop ℝ≥0) < τ n ω := lt_of_not_ge hn
    have hp : 0 < τ n ω := lt_of_le_of_lt bot_le hT
    have ht : (min t T : WithTop ℝ≥0) ≤ τ n ω :=
      (WithTop.coe_le_coe.mpr (min_le_right _ _)).trans hT.le
    dsimp only [Y]
    rw [stoppedProcess_eq_of_le ht, indicator_of_mem (show ω ∈ {ω | 0 < τ n ω} from hp)]
    rfl
end ProbabilityTheory


