-- Prove2me | Definitions.Def_SourceProof_7697f46ddf08897a14ff00d9
-- name    : SourceProof_7697f46ddf08897a14ff00d9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:02:24.470402+00:00
-- url     : https://prove2.me/theorems/b924d4e1-1626-4559-9480-19ed586f5e75
-- title:
--   StochLean source theorem: ProbabilityTheory.isClassD_indicator_stoppingTime_le

import Definitions.Def_StochLean_Probability_Process_Stopping_TotallyInaccessibleJumps_F000
import Definitions.Def_SourceProof_279b2c6861b684f378e6b7d6
import Definitions.Def_SourceProof_4a90e1998d81dac996f193f9
import Definitions.Def_SourceProof_4d66c8d394bf81c5a531f8d4
import Definitions.Def_SourceProof_59937584270f7495d3b7f3c7
import Definitions.Def_SourceProof_b81c9b8175076e0b66117dff
import Mathlib.Probability.Martingale.Basic
import Mathlib.Topology.Algebra.Group.Basic

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Integrable single jumps for continuous Doob decomposition

The coefficient is revealed at its native stopped sigma-field. Its closed
lifetime indicator is the existing step process, not a new process owner.
Integrable coefficients give Class D without bounded lifetimes or amplitudes.
A nonpositive coefficient gives an actual supermartingale. A totally
inaccessible lifetime gives totally inaccessible positive-time jumps.
An infinite lifetime never activates at finite time; the initial jump is
retained when the lifetime is zero, and is almost surely zero for a totally
inaccessible lifetime.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0} {Z : Ω → ℝ}

namespace ProbabilityTheory


theorem _root_.Prove2MeSourceProof.h_7697f46ddf08897a14ff00d9 (hτ : IsStoppingTime F τ)
    (hm : StronglyMeasurable[hτ.measurableSpace] Z) (hi : Integrable Z P) :
    IsClassD (fun t : ℝ≥0 ↦ {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator Z) F P := by
  have ho := (fun p2mMethodArg0 => _root_.Prove2MeSourceProof.h_b81c9b8175076e0b66117dff p2mMethodArg0 hm) hτ
  apply (_root_.Prove2MeSourceProof.h_4d66c8d394bf81c5a531f8d4 (_root_.Prove2MeSourceProof.h_59937584270f7495d3b7f3c7 (F := F) hi))
  · intro σ
    exact (((_root_.Prove2MeSourceProof.h_279b2c6861b684f378e6b7d6 ho) σ).mono
      (_root_.Prove2MeSourceProof.h_4a90e1998d81dac996f193f9 σ)).aestronglyMeasurable
  · intro σ
    exact Eventually.of_forall fun ω ↦ norm_indicator_le_norm_self _ _
end ProbabilityTheory

namespace MeasureTheory

end MeasureTheory


