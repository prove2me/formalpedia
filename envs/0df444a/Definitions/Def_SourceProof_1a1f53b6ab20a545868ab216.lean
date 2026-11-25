-- Prove2me | Definitions.Def_SourceProof_1a1f53b6ab20a545868ab216
-- name    : SourceProof_1a1f53b6ab20a545868ab216
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:14:15.298751+00:00
-- url     : https://prove2.me/theorems/246d294a-008e-4ad3-8b44-a32f2d7a0490
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.isKlenkeLocalizingSequence_nat

import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F000
import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F001
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F001
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F002
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F003
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F004
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F006
import Definitions.Def_SourceProof_d88de88ea95a20532b35d607
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Martingales are locally uniformly integrable

Protter I.6 Example 1 and Klenke 21.69(i). Stopping at deterministic time T
closes the martingale with the terminal variable X_T. Thus it is UI even when
the original martingale is not UI over the whole half-line. No continuous-time
optional sampling or integrability of an unbounded stopping value is used.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}


theorem _root_.Prove2MeSourceProof.h_1a1f53b6ab20a545868ab216
    [IsFiniteMeasure P] [SigmaFiniteFiltration P F] (hX : Martingale X F P) :
    IsKlenkeLocalizingSequence X F P (fun n _ ↦ ((n : ℝ≥0) : WithTop ℝ≥0)) := by
  refine ⟨⟨fun n ↦ isStoppingTime_const F n, ?_⟩, ?_, fun n ↦
    ((_root_.Prove2MeSourceProof.h_d88de88ea95a20532b35d607 hX) n).2⟩
  · exact ae_of_all _ fun _ ↦ WithTop.tendsto_coe_atTop.comp tendsto_natCast_atTop_atTop
  · intro n m hnm ω
    exact WithTop.coe_le_coe.mpr (Nat.cast_le.mpr hnm)
end ProbabilityTheory


