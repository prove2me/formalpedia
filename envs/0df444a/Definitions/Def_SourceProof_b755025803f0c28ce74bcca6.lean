-- Prove2me | Definitions.Def_SourceProof_b755025803f0c28ce74bcca6
-- name    : SourceProof_b755025803f0c28ce74bcca6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:30:54.11182+00:00
-- url     : https://prove2.me/theorems/3406b6f9-fc57-5467-a0fa-3138f7e4bfee
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.isStoppingTime_hittingAfter_norm_of_usual

import Definitions.Def_SourceProof_58d80c4855ee4c65780d30d0

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Norm bounds at a right-continuous first exit

Strictly before the first exit the norm is at most the threshold. At a finite
first exit the norm is at least the threshold; jumps may overshoot it. No equality
or upper bound at the stopping endpoint is asserted without additional continuity.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ}

variable {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}

namespace Adapted
theorem _root_.Prove2MeSourceProof.h_b755025803f0c28ce74bcca6
    (hX : Adapted F X) (hF : F.IsUsual P)
    (hr : ProbabilityTheory.HasRightContinuousPaths X P) (a : ℝ) :
    IsStoppingTime F (hittingAfter X {x | a < ‖x‖} 0) :=
  (_root_.Prove2MeSourceProof.h_58d80c4855ee4c65780d30d0 hX) hF hr
    (isOpen_lt continuous_const continuous_norm) 0
end Adapted

end MeasureTheory


