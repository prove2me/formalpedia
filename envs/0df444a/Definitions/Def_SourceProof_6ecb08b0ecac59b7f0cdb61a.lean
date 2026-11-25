-- Prove2me | Definitions.Def_SourceProof_6ecb08b0ecac59b7f0cdb61a
-- name    : SourceProof_6ecb08b0ecac59b7f0cdb61a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:25:34.679586+00:00
-- url     : https://prove2.me/theorems/8f48bb39-501c-5c1f-af1e-784d26d246b2
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.indicator_initial

import Definitions.Def_StochLean_Probability_Process_Semimartingale_Basic_F001
import Definitions.Def_SourceProof_781f128351dbe75a9f7e4573
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Probability.Process.Adapted
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.UniformSpace.HeineCantor

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Initial-event masks preserve source semimartingales

The good-integrator estimate is a direct outer-measure contraction. Adaptedness
uses only measurability of the event at time zero.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_6ecb08b0ecac59b7f0cdb61a (hX : IsSemimartingale X F P)
    {s : Set Ω} (hs : MeasurableSet[F 0] s) :
    IsSemimartingale (fun t ↦ s.indicator (X t)) F P := by
  intro t
  rw [stoppedProcess_indicator_comm']
  exact (_root_.Prove2MeSourceProof.h_781f128351dbe75a9f7e4573 (hX t)) hs
end IsSemimartingale

end ProbabilityTheory


