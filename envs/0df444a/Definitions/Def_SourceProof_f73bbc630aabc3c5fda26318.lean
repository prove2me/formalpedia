-- Prove2me | Definitions.Def_SourceProof_f73bbc630aabc3c5fda26318
-- name    : SourceProof_f73bbc630aabc3c5fda26318
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:57:18.392358+00:00
-- url     : https://prove2.me/theorems/b8c08924-8862-489c-b16d-d165303e4232
-- title:
--   StochLean source theorem: ProbabilityTheory.mem_stoppingTimeGraph

import Definitions.Def_StochLean_Probability_Process_Stopping_Graph_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Finite-time graphs of stopping times

Protter III.2 includes time zero in a stopping-time graph and excludes infinity.
The strict-future region is predictable, the closed-future region is optional,
and every stopping-time graph is optional. Predictability of the graph is not
asserted for an arbitrary stopping time.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

@[simp] theorem _root_.Prove2MeSourceProof.h_f73bbc630aabc3c5fda26318 {Ω : Type*} {τ : Ω → WithTop ℝ≥0}
    {p : ℝ≥0 × Ω} : p ∈ stoppingTimeGraph τ ↔ τ p.2 = (p.1 : WithTop ℝ≥0) := Iff.rfl
end ProbabilityTheory

namespace MeasureTheory.IsStoppingTime

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {τ : Ω → WithTop ℝ≥0}

end MeasureTheory.IsStoppingTime


