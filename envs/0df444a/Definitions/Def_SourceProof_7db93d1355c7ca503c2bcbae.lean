-- Prove2me | Definitions.Def_SourceProof_7db93d1355c7ca503c2bcbae
-- name    : SourceProof_7db93d1355c7ca503c2bcbae
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:38:15.489238+00:00
-- url     : https://prove2.me/theorems/f031c3ed-2c2d-478e-be1c-a6df68851f32
-- title:
--   StochLean source theorem: ProbabilityTheory.IsLocalMartingale.const_smul

import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F000
import Definitions.Def_SourceProof_1b3d64819f52c9f5cf5f792e
import Definitions.Def_SourceProof_264b430747bbe6ee020dbafc
import Definitions.Def_SourceProof_7e41a7708f0759111a0ce622
import Definitions.Def_SourceProof_7fe27d80761f531095784a17
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Stopping

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Stopping and linear stability of Protter local martingales

Fundamental sequences are actual witnesses. A shared localizer is the pointwise
minimum of two existing localizers. Its time-zero mask is the intersection of
their masks; the unmasked Klenke definition is not silently substituted.

Source: Protter I.48 (stopping and linear operations).
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X Y : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P]

namespace IsLocalMartingale
theorem _root_.Prove2MeSourceProof.h_7db93d1355c7ca503c2bcbae (hX : IsLocalMartingale X F P) (c : ℝ) :
    IsLocalMartingale (c • X) F P := by
  obtain ⟨τ, hτ⟩ := hX.2.2
  refine ⟨(hX.1.stronglyAdapted.smul c).adapted, ?_, τ, hτ.1, hτ.2.1, fun n ↦ ?_⟩
  · exact (_root_.Prove2MeSourceProof.h_264b430747bbe6ee020dbafc hX.2.1)
      (show Continuous (fun x : ℝ ↦ c * x) from continuous_const.mul continuous_id)
  · have heq : (fun t ↦ {ω | 0 < τ n ω}.indicator ((c • X) t)) =
        c • (fun t ↦ {ω | 0 < τ n ω}.indicator (X t)) := by
      funext t ω
      by_cases h : 0 < τ n ω <;> simp [h]
    rw [heq, stoppedProcess_const_smul]
    exact (_root_.Prove2MeSourceProof.h_1b3d64819f52c9f5cf5f792e (hτ.2.2 n)) c
end IsLocalMartingale

end ProbabilityTheory


