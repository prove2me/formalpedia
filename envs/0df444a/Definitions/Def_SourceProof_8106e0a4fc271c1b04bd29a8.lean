-- Prove2me | Definitions.Def_SourceProof_8106e0a4fc271c1b04bd29a8
-- name    : SourceProof_8106e0a4fc271c1b04bd29a8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:31:08.823217+00:00
-- url     : https://prove2.me/theorems/253091b0-389f-52b6-8d99-174f6cebbb1d
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.norm_integral_le_variation

import Definitions.Def_SourceProof_7d58eb4e8ca0b9afe6bb32b4
import Definitions.Def_SourceProof_a9c44e06617a4753cffd0417
import Definitions.Def_SourceProof_ac7ce9a51c9b630bf39062ad
import Definitions.Def_SourceProof_eb865f08ccda32d7488379ff
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.UniformSpace.HeineCantor

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Pathwise variation bounds on elementary integrals

The source time-zero contribution is included separately from increment variation. Real
conversion of extended variation is used only after the corresponding finiteness proof.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped NNReal ENNReal BigOperators

namespace ProbabilityTheory.SimplePredictableRep

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_8106e0a4fc271c1b04bd29a8 (H : SimplePredictableRep F) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ t ω, ‖H.toProcess t ω‖ ≤ C) (ω : Ω)
    (hf : BoundedVariationOn (fun t ↦ X t ω) (Icc 0 (H.partition.terminal ω))) :
    ‖H.integral X ω‖ ≤ C * (‖X 0 ω‖ +
      (eVariationOn (fun t ↦ X t ω) (Icc 0 (H.partition.terminal ω))).toReal) := by
  rw [← (_root_.Prove2MeSourceProof.h_ac7ce9a51c9b630bf39062ad H)]
  exact (_root_.Prove2MeSourceProof.h_eb865f08ccda32d7488379ff H.removeEmptyIntervals) hC
    (fun ω ↦ by
      change ‖H.initial ω‖ ≤ C
      simpa only [_root_.Prove2MeSourceProof.h_a9c44e06617a4753cffd0417] using hb 0 ω)
    ((_root_.Prove2MeSourceProof.h_7d58eb4e8ca0b9afe6bb32b4 H) hC hb) ω hf
end ProbabilityTheory.SimplePredictableRep


