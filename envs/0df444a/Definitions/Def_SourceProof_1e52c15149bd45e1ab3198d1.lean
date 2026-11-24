-- Prove2me | Definitions.Def_SourceProof_1e52c15149bd45e1ab3198d1
-- name    : SourceProof_1e52c15149bd45e1ab3198d1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T16:07:57.777742+00:00
-- url     : https://prove2.me/theorems/ec87d52a-2c49-47aa-9c19-97cea9565667
-- title:
--   StochLean source theorem: MeasureTheory.norm_le_of_lt_hittingAfter_norm

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Bases
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LeftRight

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

theorem _root_.Prove2MeSourceProof.h_1e52c15149bd45e1ab3198d1 {a : ℝ} {t : ℝ≥0} {ω : Ω}
    (ht : (t : WithTop ℝ≥0) < hittingAfter X {x | a < ‖x‖} 0 ω) : ‖X t ω‖ ≤ a := by
  have hnot : X t ω ∉ {x : ℝ | a < ‖x‖} :=
    notMem_of_lt_hittingAfter (u := X) (s := {x | a < ‖x‖}) ht
      (bot_le : (0 : ℝ≥0) ≤ t)
  exact le_of_not_gt hnot
variable {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}

end MeasureTheory


