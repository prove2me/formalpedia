-- Prove2me | Definitions.Def_SourceProof_5be316bda063706d2135fb14
-- name    : SourceProof_5be316bda063706d2135fb14
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:13:24.274792+00:00
-- url     : https://prove2.me/theorems/ad4f11b0-09c0-5231-ae73-d8e0be1f548d
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.isSemimartingale_of_memLp

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_Basic_F001
import Definitions.Def_SourceProof_05cca3ad57990de6ee8064ab
import Definitions.Def_SourceProof_1557efb7e848f4cf57c0170c
import Definitions.Def_SourceProof_9127ba9e47e57c570411dae8
import Definitions.Def_SourceProof_96c0d23ed76988d7c3d3ef45
import Definitions.Def_SourceProof_a239f509638bc9274841d0b5
import Definitions.Def_SourceProof_faea1308e58b2b1b6deb90cf
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.Centering
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.LocalProperty

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Square-integrable martingales are source semimartingales

The good-integrator property is proved from the elementary L2 estimate and Markov's
inequality, not assumed as part of a martingale definition or inferred from a decomposition.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsFiniteMeasure P] {X : ℝ≥0 → Ω → ℝ}

variable [SigmaFiniteFiltration P F]


theorem _root_.Prove2MeSourceProof.h_5be316bda063706d2135fb14
    (hX : Martingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (hlp : ∀ T, MemLp (X T) 2 P) : IsSemimartingale X F P := by
  intro T
  change ProbabilityTheory.IsTotalSemimartingale (stoppedProcess X (ProbabilityTheory.FiniteStoppingTime.const F T).withTop) F P
  rw [_root_.Prove2MeSourceProof.h_faea1308e58b2b1b6deb90cf]
  exact (_root_.Prove2MeSourceProof.h_05cca3ad57990de6ee8064ab hX) hF hc T (hlp T)
end ProbabilityTheory


