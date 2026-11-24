-- Prove2me | Definitions.Def_SourceProof_7afbc88789b9bcaafb30a87c
-- name    : SourceProof_7afbc88789b9bcaafb30a87c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:19:38.732951+00:00
-- url     : https://prove2.me/theorems/5de46ec7-c1af-46bf-b5c9-02bf369a4bad
-- title:
--   StochLean source theorem: MeasureTheory.IsStoppingTime.measurableSet_lt_before

import Definitions.Def_SourceProof_b56782530437a70393044b28

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Strict comparison events in the pre-stopping sigma-field

Protter III.7 uses a countable union over deterministic times strictly between
the two stopping times. Infinite upper times are allowed. Terminal information
is also measurable before `T` after restriction to `{T = ∞}`.
-/

@[expose] public section

open Set
open scoped NNReal

namespace MeasureTheory.IsStoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
variable {σ τ : Ω → WithTop ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_7afbc88789b9bcaafb30a87c (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ) :
    MeasurableSet[hτ.measurableSpaceBefore] {ω | σ ω < τ ω} := by
  simpa only [univ_inter] using (_root_.Prove2MeSourceProof.h_b56782530437a70393044b28 hσ) hτ MeasurableSet.univ
end MeasureTheory.IsStoppingTime


