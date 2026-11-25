-- Prove2me | Definitions.Def_SourceProof_3416e99a223013e5435c7120
-- name    : SourceProof_3416e99a223013e5435c7120
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:57:34.750134+00:00
-- url     : https://prove2.me/theorems/17c0fe9b-adc8-5aed-aaf9-ef45bde5ef64
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.stronglyAdapted_largeJumpSumProcesses_of_cadlag

import Definitions.Def_StochLean_Probability_Process_Path_LargeJumpSum_F000
import Definitions.Def_SourceProof_d815abe7babc7f9241f3edfd
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Order.WithBot
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Predictable
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Instances.Rat

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Measurability of the actual large-jump cumulative processes

The literal sums over positive times are identified with the existing countable
stopping-time enumeration. For almost-sure cadlag paths, an everywhere-cadlag
indistinguishable version and relative completeness recover measurability of
the original sums, not merely of a chosen replacement process.
-/

@[expose] public section

open ProbabilityTheory Set
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} {b : ℝ}

namespace Adapted

theorem _root_.Prove2MeSourceProof.h_3416e99a223013e5435c7120 [F.IsRightContinuous]
    (ha : Adapted F X) (hc : ∀ ω, IsCadlagPath (X · ω)) (hb : 0 < b) :
    StronglyAdapted F (largeJumpSumProcess X b) ∧
      StronglyAdapted F (largeJumpNormSumProcess X b) :=
  ⟨(_root_.Prove2MeSourceProof.h_d815abe7babc7f9241f3edfd ha) hc hb measurable_id,
    (_root_.Prove2MeSourceProof.h_d815abe7babc7f9241f3edfd ha) hc hb measurable_norm⟩
end Adapted

end MeasureTheory


