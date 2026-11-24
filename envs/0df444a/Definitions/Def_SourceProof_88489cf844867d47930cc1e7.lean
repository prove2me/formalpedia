-- Prove2me | Definitions.Def_SourceProof_88489cf844867d47930cc1e7
-- name    : SourceProof_88489cf844867d47930cc1e7
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:46:08.878356+00:00
-- url     : https://prove2.me/theorems/e1e57ba0-85f1-4b95-97d7-f0a9aabdaa44
-- title:
--   StochLean source theorem: ProbabilityTheory.cutoffIntegrand_zero

import Definitions.Def_StochLean_Probability_Process_Stopping_Integrand_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Cutting an integrand off after a stopping time

Unlike a stopped process, the cutoff is zero strictly after the stopping time.
The closed endpoint preserves the stopping jump and the initial value.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

@[simp] theorem _root_.Prove2MeSourceProof.h_88489cf844867d47930cc1e7 (H : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    cutoffIntegrand H τ 0 ω = H 0 ω := by
  simp [ProbabilityTheory.cutoffIntegrand]
end ProbabilityTheory


