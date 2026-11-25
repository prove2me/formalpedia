-- Prove2me | Definitions.Def_SourceProof_35649b1a80f47b6121901d45
-- name    : SourceProof_35649b1a80f47b6121901d45
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:32:03.977712+00:00
-- url     : https://prove2.me/theorems/c6210b10-07d2-5dc3-a1f0-b263caa686a4
-- title:
--   StochLean source theorem: MeasureTheory.IsStoppingTime.measurableSet_predictable_lt

import Definitions.Def_SourceProof_27ae6b74ff4070edc078bdb8

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

end ProbabilityTheory

namespace MeasureTheory.IsStoppingTime

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {τ : Ω → WithTop ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_35649b1a80f47b6121901d45 (hτ : IsStoppingTime F τ) :
    MeasurableSet[F.predictable] {p : ℝ≥0 × Ω | τ p.2 < (p.1 : WithTop ℝ≥0)} := by
  have hm := (_root_.Prove2MeSourceProof.h_27ae6b74ff4070edc078bdb8 hτ).measurable (measurableSet_singleton (1 : ℝ))
  convert hm using 1
  ext ⟨t, ω⟩
  simp [Function.uncurry]
end MeasureTheory.IsStoppingTime


