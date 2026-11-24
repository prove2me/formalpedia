-- Prove2me | Definitions.Def_SourceProof_2d015c300a40edcbe97cb76a
-- name    : SourceProof_2d015c300a40edcbe97cb76a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:21:23.453099+00:00
-- url     : https://prove2.me/theorems/d05c529d-cf95-4e16-8a5c-cd1546d0eb12
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.integral_add_integrator

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
theorem _root_.Prove2MeSourceProof.h_2d015c300a40edcbe97cb76a (H : SimplePredictableRep F)
    (X Y : ℝ≥0 → Ω → ℝ) : H.integral (X + Y) = H.integral X + H.integral Y := by
  funext ω
  simp only [ProbabilityTheory.SimplePredictableRep.integral, Pi.add_apply, add_sub_add_comm,
    mul_add, sum_add_distrib]
  ring
end SimplePredictableRep

end ProbabilityTheory


