-- Prove2me | Definitions.Def_SourceProof_c723bba90ef663ed2d82d1f9
-- name    : SourceProof_c723bba90ef663ed2d82d1f9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:18:55.597439+00:00
-- url     : https://prove2.me/theorems/16400148-132a-4512-bfd4-64ca4b5098ef
-- title:
--   StochLean source theorem: ProbabilityTheory.IsFundamentalSequence.min_other

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F000
import Definitions.Def_SourceProof_1557efb7e848f4cf57c0170c
import Definitions.Def_SourceProof_5ac3f4c5fe22f7841ec0a6bc
import Definitions.Def_SourceProof_7e41a7708f0759111a0ce622
import Definitions.Def_SourceProof_9f2f3563711c68b81e63664c
import Definitions.Def_SourceProof_aa372c8273bcd3cd6307f406
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.Adapted

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Stopping and linear stability of Protter local martingales

Fundamental sequences are actual witnesses. A shared localizer is the pointwise
minimum of two existing localizers. Its time-zero mask is the intersection of
their masks; the unmasked Klenke definition is not silently substituted.

Source: Protter I.48 (stopping and linear operations).
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X Y : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P]

namespace IsFundamentalSequence

theorem _root_.Prove2MeSourceProof.h_c723bba90ef663ed2d82d1f9 {τ σ : ℕ → Ω → WithTop ℝ≥0}
    (hτ : IsFundamentalSequence X F P τ) (hcad : HasCadlagPaths X P)
    (hF : F.IsUsual P) (hσ : IsPreLocalizingSequence F σ P) (hmono : Monotone σ) :
    IsFundamentalSequence X F P (min τ σ) := by
  refine ⟨⟨fun n ↦ (hτ.1.isStoppingTime n).min (hσ.isStoppingTime n), ?_⟩,
    hτ.2.1.inf hmono, fun n ↦ ?_⟩
  · filter_upwards [hτ.1.tendsto_top, hσ.tendsto_top] with ω hτω hσω
    simpa only [Pi.inf_apply, min_self] using hτω.min hσω
  · have hB : MeasurableSet[F 0] {ω | 0 < σ n ω} := by
      simpa only [WithTop.coe_zero, Set.compl_ofPred, not_le] using
        (hσ.isStoppingTime n 0).compl
    have hbase := (_root_.Prove2MeSourceProof.h_5ac3f4c5fe22f7841ec0a6bc (hτ.2.2 n)) hB
    have hr := (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c ((_root_.Prove2MeSourceProof.h_7e41a7708f0759111a0ce622 ((_root_.Prove2MeSourceProof.h_1557efb7e848f4cf57c0170c ((_root_.Prove2MeSourceProof.h_7e41a7708f0759111a0ce622 hcad) {ω | 0 < τ n ω})) (τ n)))
      {ω | 0 < σ n ω}))
    have hstop := (_root_.Prove2MeSourceProof.h_aa372c8273bcd3cd6307f406 hbase) hF hr (hσ.isStoppingTime n)
    convert hstop using 1
    simp_rw [stoppedProcess_indicator_comm', Set.indicator_indicator]
    rw [← stoppedProcess_indicator_comm', stoppedProcess_stoppedProcess]
    ext t ω
    simp only [stoppedProcess_indicator_comm, Pi.inf_apply, lt_inf_iff,
      Set.ofPred_and, Set.inter_comm, inf_comm]
end IsFundamentalSequence

end ProbabilityTheory


