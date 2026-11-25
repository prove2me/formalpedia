-- Prove2me | Definitions.Def_SourceProof_5f682bdcd01340f68959a08f
-- name    : SourceProof_5f682bdcd01340f68959a08f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:10:44.368007+00:00
-- url     : https://prove2.me/theorems/f2238473-c408-50b9-b91f-2e6b5e8cc74c
-- title:
--   StochLean source theorem: ProbabilityTheory.IsPredictableStoppingTime.min

import Definitions.Def_SourceProof_8fbfcb8380b592eeb5076ad9
import Definitions.Def_SourceProof_fd96f6b974ce4fcd7a2dda99

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Stability of announcing sequences

Capping each announcing term by its target preserves the source relation and
makes domination pointwise, even at exceptional zero-time samples. Finite
minima and maxima of predictable times are predictable. No claim about
decreasing limits or arbitrary stopped-event restrictions is made.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  {τ ρ : Ω → WithTop ℝ≥0} {σ π : ℕ → Ω → WithTop ℝ≥0}

namespace IsPredictableStoppingTime
theorem _root_.Prove2MeSourceProof.h_5f682bdcd01340f68959a08f (h : IsPredictableStoppingTime F τ P)
    (h' : IsPredictableStoppingTime F ρ P) :
    IsPredictableStoppingTime F (fun ω ↦ min (τ ω) (ρ ω)) P := by
  obtain ⟨σ, hs⟩ := h.2
  obtain ⟨π, hp⟩ := h'.2
  exact (_root_.Prove2MeSourceProof.h_fd96f6b974ce4fcd7a2dda99 ((_root_.Prove2MeSourceProof.h_8fbfcb8380b592eeb5076ad9 hs) hp)) (h.1.min h'.1)
end IsPredictableStoppingTime

end ProbabilityTheory


