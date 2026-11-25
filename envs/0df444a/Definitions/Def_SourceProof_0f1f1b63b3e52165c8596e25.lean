-- Prove2me | Definitions.Def_SourceProof_0f1f1b63b3e52165c8596e25
-- name    : SourceProof_0f1f1b63b3e52165c8596e25
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:35:52.58852+00:00
-- url     : https://prove2.me/theorems/5c79ce0c-8ba5-4bcb-97ed-929a64cc6d8e
-- title:
--   StochLean source theorem: ProbabilityTheory.isSemimartingale_const_initial

import Definitions.Def_StochLean_Probability_Process_Semimartingale_Basic_F001
import Definitions.Def_SourceProof_91cbcdd434ea8c8e4843298e

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Semimartingales as good integrators

The canonical predicate is zero-sequential continuity of the elementary
integral for uniform convergence in `(t,ω)`. The epsilon/delta source
continuity criterion is proved equivalent. Classical decompositions are not
part of this definition. This file does not select a stochastic integral for
general caglad integrands or a quadratic variation.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

variable {X : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}

theorem _root_.Prove2MeSourceProof.h_0f1f1b63b3e52165c8596e25 [IsFiniteMeasure P] {Z : Ω → ℝ}
    (hZ : Measurable[F 0] Z) : IsSemimartingale (fun _ : ℝ≥0 ↦ Z) F P := by
  intro t
  simpa only [stoppedProcess_const] using _root_.Prove2MeSourceProof.h_91cbcdd434ea8c8e4843298e hZ
end ProbabilityTheory


