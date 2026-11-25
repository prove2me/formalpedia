-- Prove2me | Definitions.Def_SourceProof_75a69f168b91f3bff282b188
-- name    : SourceProof_75a69f168b91f3bff282b188
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:56:26.464672+00:00
-- url     : https://prove2.me/theorems/3feaf639-95a5-4f1d-82e2-4364436a9497
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.rightLimitProcess_of_caglad

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_Path_RightLimit_F000
import Definitions.Def_SourceProof_a3bc82106adf606a13e0e393
import Definitions.Def_SourceProof_eff9df1f090a05dc4bbe1884
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Process.Adapted

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Adaptedness of a caglad process's right-limit process

The right limit at `t` is measurable in every `F_u`, `u > t`, by actual sequences
inside `(t,u)`. Right continuity of the filtration then gives `F_t` measurability.
Usual completeness transports the statement on one common exceptional path event.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

namespace Adapted
theorem _root_.Prove2MeSourceProof.h_75a69f168b91f3bff282b188 [F.IsRightContinuous]
    (ha : Adapted F X) (hc : ∀ ω, IsCagladPath (X · ω)) :
    Adapted F (ProbabilityTheory.rightLimitProcess X) :=
  (_root_.Prove2MeSourceProof.h_eff9df1f090a05dc4bbe1884 ha) fun ω ↦ (hc ω).2
end Adapted

end MeasureTheory


