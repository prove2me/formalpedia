-- Prove2me | Definitions.Def_SourceProof_d88de88ea95a20532b35d607
-- name    : SourceProof_d88de88ea95a20532b35d607
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:35:38.324504+00:00
-- url     : https://prove2.me/theorems/98ea2842-0a2c-5611-9152-2d90a0450da6
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.isReducingStoppingTime_const

import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F000
import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F001
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F001
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F002
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F003
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F004
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F006
import Definitions.Def_SourceProof_0bdd61215a21f3b253c38ea5
import Definitions.Def_SourceProof_faea1308e58b2b1b6deb90cf
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

theorem _root_.Prove2MeSourceProof.h_d88de88ea95a20532b35d607
    [IsFiniteMeasure P] [SigmaFiniteFiltration P F] (hX : Martingale X F P) (T : ℝ≥0) :
    IsReducingStoppingTime X F P (fun _ ↦ (T : WithTop ℝ≥0)) := by
  refine ⟨isStoppingTime_const F T, ?_⟩
  change ProbabilityTheory.IsUIMartingale (stoppedProcess X (ProbabilityTheory.FiniteStoppingTime.const F T).withTop) F P
  rw [_root_.Prove2MeSourceProof.h_faea1308e58b2b1b6deb90cf]
  exact (_root_.Prove2MeSourceProof.h_0bdd61215a21f3b253c38ea5 hX) T
end ProbabilityTheory


