-- Prove2me | Definitions.Def_SourceProof_e79cc5d7fc8aa48d10e205ad
-- name    : SourceProof_e79cc5d7fc8aa48d10e205ad
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:21:24.935317+00:00
-- url     : https://prove2.me/theorems/af9ba22b-7fd5-5ed7-8202-b24eeeeba73d
-- title:
--   StochLean source theorem: ProbabilityTheory.IsContinuousLocalMartingale.stoppedProcess

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F000
import Definitions.Def_SourceProof_2c97b0da88fd3eb21715f5f0
import Definitions.Def_SourceProof_96c0d23ed76988d7c3d3ef45
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.Adapted
import Mathlib.Topology.Algebra.Monoid

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

namespace IsContinuousLocalMartingale
theorem _root_.Prove2MeSourceProof.h_e79cc5d7fc8aa48d10e205ad (hX : IsContinuousLocalMartingale X F P)
    (hF : F.IsUsual P) {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime F σ) :
    IsContinuousLocalMartingale (MeasureTheory.stoppedProcess X σ) F P :=
  ⟨(_root_.Prove2MeSourceProof.h_2c97b0da88fd3eb21715f5f0 hX.1) hF hσ, (_root_.Prove2MeSourceProof.h_96c0d23ed76988d7c3d3ef45 hX.2) σ⟩
end IsContinuousLocalMartingale

end ProbabilityTheory


