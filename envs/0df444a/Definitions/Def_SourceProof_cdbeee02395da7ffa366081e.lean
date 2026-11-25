-- Prove2me | Definitions.Def_SourceProof_cdbeee02395da7ffa366081e
-- name    : SourceProof_cdbeee02395da7ffa366081e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:32:47.834897+00:00
-- url     : https://prove2.me/theorems/78a76741-861e-4243-954a-df59a83255f9
-- title:
--   StochLean source theorem: ProbabilityTheory.IsPredictableStoppingTime.measurableSet_eq_finite_before

import Definitions.Def_SourceProof_c5f065710bd45a18bc8b167b
import Definitions.Def_SourceProof_d6d3239f29afcc05f08f5261

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Comparison with a predictable time before a stopping time

If sigma is predictable and tau is a stopping time, then sigma <= tau is
measurable strictly before tau, provided the initial sigma-field contains
all ambient null sets. A capped announcing sequence gives the comparison
on the positive-tau event. The zero event is handled with initial information,
and completeness turns the almost-sure announcing equivalence into exact
measurability of the original comparison event.

Neither right continuity of the filtration, finiteness of the measure, nor
predictability of the second time is needed. Equality at infinity is allowed
in the equality theorem; the finite-equality theorem removes it explicitly.
These events can later support predictable restrictions and graph deduplication.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {σ τ : Ω → WithTop ℝ≥0}

namespace IsPredictableStoppingTime

theorem _root_.Prove2MeSourceProof.h_cdbeee02395da7ffa366081e
    (hσ : IsPredictableStoppingTime F σ P) (hτ : IsStoppingTime F τ)
    (hc0 : IsCompleteSubMeasurableSpace P (F 0)) :
    MeasurableSet[hτ.measurableSpaceBefore] {ω | σ ω = τ ω ∧ τ ω ≠ ⊤} := by
  exact ((_root_.Prove2MeSourceProof.h_c5f065710bd45a18bc8b167b hσ) hτ hc0).inter
    ((_root_.Prove2MeSourceProof.h_d6d3239f29afcc05f08f5261 hτ) (measurableSet_singleton ⊤)).compl
end IsPredictableStoppingTime

end ProbabilityTheory


