-- Prove2me | Definitions.Def_SourceProof_354b37228f98fe5fdec5bcbb
-- name    : SourceProof_354b37228f98fe5fdec5bcbb
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:21:12.336597+00:00
-- url     : https://prove2.me/theorems/0eeb1e8d-a2e4-5bc6-831b-bc1dc6d13974
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.isStronglyPredictable_of_leftContinuous

import Definitions.Def_StochLean_Probability_Process_Measurability_PredictableGrid_F000
import Definitions.Def_SourceProof_40c22f8cb9dd1f12ac3b079a
import Definitions.Def_SourceProof_759c53f2ad519b1a6435ff2c
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Predictability from left-continuous adapted paths

Mathlib's predictable sigma-field remains the canonical owner. Strict-past grids
prove the source Chapter III bridge. For merely almost-sure path regularity a
single exceptional event is removed: the conclusion is an indistinguishable
predictable version, not predictability of arbitrary exceptional trajectories.
This file does not extend the Chapter II integral to all predictable integrands.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

namespace Adapted
theorem _root_.Prove2MeSourceProof.h_354b37228f98fe5fdec5bcbb (ha : Adapted F X)
    (hc : ∀ ω, IsLeftContinuousPath (fun t ↦ X t ω)) : IsStronglyPredictable F X := by
  let : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  change StronglyMeasurable (Function.uncurry X)
  apply stronglyMeasurable_of_tendsto atTop
    (fun n : ℕ ↦ ((_root_.Prove2MeSourceProof.h_40c22f8cb9dd1f12ac3b079a ha)
      (show 0 < (1 : ℝ≥0) / ((n : ℝ≥0) + 1) from by positivity)).stronglyMeasurable)
  apply tendsto_pi_nhds.mpr
  intro z
  exact (hc z.2 z.1).tendsto.comp (_root_.Prove2MeSourceProof.h_759c53f2ad519b1a6435ff2c z.1)
end Adapted

end MeasureTheory


