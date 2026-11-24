-- Prove2me | Definitions.Def_SourceProof_3ad064b37d71e89ec9f818b4
-- name    : SourceProof_3ad064b37d71e89ec9f818b4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:21:18.162801+00:00
-- url     : https://prove2.me/theorems/f8e45573-ae57-4600-94a7-2a6e593a07a3
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.integral_const_mul_integrator

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F002
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F003

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Elementary linearity in the integrator

These declarations retain their original public names and statements. They live below
good-integrator stability so that the source simple-process algebra can reuse them directly.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

namespace SimplePredictableRep
theorem _root_.Prove2MeSourceProof.h_3ad064b37d71e89ec9f818b4 (H : SimplePredictableRep F)
    (c : ℝ) (X : ℝ≥0 → Ω → ℝ) :
    H.integral (fun t ω ↦ c * X t ω) = fun ω ↦ c * H.integral X ω := by
  funext ω
  unfold ProbabilityTheory.SimplePredictableRep.integral
  have hsum : (∑ i, H.coefficient i ω *
      (c * X (H.partition.point i.succ ω) ω - c * X (H.partition.point i.castSucc ω) ω)) =
      c * ∑ i, H.coefficient i ω *
        (X (H.partition.point i.succ ω) ω - X (H.partition.point i.castSucc ω) ω) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  rw [hsum]
  ring
end SimplePredictableRep

end ProbabilityTheory


