-- Prove2me | Definitions.Def_SourceProof_2685819f27d6afe556e1f973
-- name    : SourceProof_2685819f27d6afe556e1f973
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:21:27.19119+00:00
-- url     : https://prove2.me/theorems/0e1dc202-ce78-4a8f-95b9-60fa394ae67e
-- title:
--   StochLean source theorem: ProbabilityTheory.masked_stoppedProcess_masked_stoppedProcess

import Definitions.Def_SourceProof_1557efb7e848f4cf57c0170c
import Definitions.Def_SourceProof_9127ba9e47e57c570411dae8
import Definitions.Def_SourceProof_96c0d23ed76988d7c3d3ef45
import Definitions.Def_SourceProof_a239f509638bc9274841d0b5

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Composition of the masked stopping operation

Both initial-event masks are retained, including when either stopping time is zero.
The identity is pointwise and needs no stopping-time or measurability premise.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

theorem _root_.Prove2MeSourceProof.h_2685819f27d6afe556e1f973 {Ω E : Type*} [Zero E]
    (X : ℝ≥0 → Ω → E) (σ τ : Ω → WithTop ℝ≥0) :
    stoppedProcess (fun t ↦ {ω | 0 < σ ω}.indicator
      (stoppedProcess (fun u ↦ {ω | 0 < τ ω}.indicator (X u)) τ t)) σ =
      stoppedProcess (fun t ↦ {ω | 0 < min σ τ ω}.indicator (X t)) (min σ τ) := by
  simp_rw [stoppedProcess_indicator_comm', stoppedProcess_stoppedProcess,
    Set.indicator_indicator]
  have hset : {ω | 0 < σ ω} ∩ {ω | 0 < τ ω} = {ω | 0 < min σ τ ω} := by
    ext ω
    change (0 < σ ω ∧ 0 < τ ω) ↔ 0 < min (σ ω) (τ ω)
    exact lt_min_iff.symm
  rw [hset]
end ProbabilityTheory


