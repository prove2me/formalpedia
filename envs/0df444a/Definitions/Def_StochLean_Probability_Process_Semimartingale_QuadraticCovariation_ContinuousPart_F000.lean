-- Prove2me | Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticCovariation_ContinuousPart_F000
-- name    : StochLean_Probability_Process_Semimartingale_QuadraticCovariation_ContinuousPart_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T21:09:24.321778+00:00
-- url     : https://prove2.me/theorems/68dae4bb-7aff-507e-88b8-431dad52d850
-- title:
--   StochLean: Probability.Process.Semimartingale.QuadraticCovariation.ContinuousPart F000

import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticVariation_ContinuousPart_F000
import Definitions.Def_SourceProof_31d0de13ef1656df97c05a7d
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The continuous component of mixed quadratic covariation

Polarization is applied to the continuous components of the same raw square
brackets. The actual mixed-jump series is absolutely summable, and the raw
covariation decomposes into its initial product, continuous part and that series.
Mixed continuous covariation is not asserted to be increasing.
-/

@[expose] public section

open MeasureTheory StochLean Set Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

noncomputable def IsSemimartingale.continuousQuadraticCovariation
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    ℝ≥0 → Ω → ℝ := fun t ω ↦ (1 / 2 : ℝ) *
      (((_root_.Prove2MeSourceProof.h_31d0de13ef1656df97c05a7d hX) hY).continuousQuadraticVariation hF t ω - hX.continuousQuadraticVariation hF t ω -
        hY.continuousQuadraticVariation hF t ω)
end ProbabilityTheory


