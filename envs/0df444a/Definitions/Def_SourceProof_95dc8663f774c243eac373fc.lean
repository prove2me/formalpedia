-- Prove2me | Definitions.Def_SourceProof_95dc8663f774c243eac373fc
-- name    : SourceProof_95dc8663f774c243eac373fc
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:07:32.64049+00:00
-- url     : https://prove2.me/theorems/d2e8abf5-7449-5848-8322-56187bf88924
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.stronglyAdapted_largeJumpResidual

import Definitions.Def_StochLean_Probability_Process_Stopping_LargeJumpResidual_F000
import Definitions.Def_SourceProof_335e23439381136e5a7ba192
import Definitions.Def_SourceProof_c6bf0251dfd0b9d2b4772331

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Actual finite-prefix large-jump residuals

The residual removes exactly the first `K` entries of the actual large-jump sequence.
At infinite entries the coefficient is explicitly zero. On the measurable coverage
event all its positive-time jumps on the horizon are small. Fixed-cap short-window
moments are derived from this event, whose complement tends to zero in probability.
No integrability of a random total jump count is required.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*}

variable {X : ℝ≥0 → Ω → ℝ} {ω : Ω} {b : ℝ}

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {b : ℝ}

namespace Adapted
theorem _root_.Prove2MeSourceProof.h_95dc8663f774c243eac373fc [F.IsRightContinuous]
    (hX : Adapted F X) (hc : ∀ ω, IsCadlagPath (X · ω)) (hb : 0 < b) (K : ℕ) :
    StronglyAdapted F (largeJumpResidual X b K) :=
  (_root_.Prove2MeSourceProof.h_c6bf0251dfd0b9d2b4772331 hX) hc (Finset.range K)
    (ProbabilityTheory.largeJumpSequence X b) (fun i _ ↦ (_root_.Prove2MeSourceProof.h_335e23439381136e5a7ba192 hX) hc hb i)
end Adapted

end MeasureTheory


