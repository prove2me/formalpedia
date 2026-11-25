-- Prove2me | Definitions.Def_SourceProof_aac175930a79ec503e2de8ac
-- name    : SourceProof_aac175930a79ec503e2de8ac
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:32:08.076486+00:00
-- url     : https://prove2.me/theorems/d6af6aaa-ae87-421f-b09e-94ea08da78e0
-- title:
--   StochLean source theorem: ProbabilityTheory.IsAnnouncingSequence.predictable_restricted_of_eventual_events

import Definitions.Def_StochLean_Probability_Process_Stopping_Announcing_F000
import Definitions.Def_SourceProof_1e2874883d783423a9f7ae8e
import Definitions.Def_SourceProof_cf4eebeacf06bc4488688354

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Restricting announcing data using eventually correct events

Tail infima of event-restricted announcing terms, capped by integers, announce
the restricted target. Initial completeness repairs the exceptional event by
zero; right continuity makes the countable tail infima stopping times.
In particular, infinity is still announced by finite terms outside the event.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  {τ : Ω → WithTop ℝ≥0} {σ : ℕ → Ω → WithTop ℝ≥0}

namespace IsAnnouncingSequence
theorem _root_.Prove2MeSourceProof.h_aac175930a79ec503e2de8ac
    (hs : IsAnnouncingSequence F P τ σ) (hτ : IsStoppingTime F τ) (hF : F.IsUsual P)
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) {B : ℕ → Set Ω}
    (hB : ∀ n, MeasurableSet[(hs.isStoppingTime n).measurableSpace] (B n))
    (hBA : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, (ω ∈ B n ↔ ω ∈ A)) :
    IsPredictableStoppingTime F (restrictedStoppingTime τ A) P :=
  _root_.Prove2MeSourceProof.h_1e2874883d783423a9f7ae8e hs.isStoppingTime hs.monotone
    hs.tendsto hτ hF hA (fun n ω _ ↦ hs.strict n ω) hB hBA
end IsAnnouncingSequence

end ProbabilityTheory


