-- Prove2me | Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticVariation_PureJump_F000
-- name    : StochLean_Probability_Process_Semimartingale_QuadraticVariation_PureJump_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T21:20:38.849321+00:00
-- url     : https://prove2.me/theorems/b65afc7e-b81a-4699-b24f-41dcf4abc3f8
-- title:
--   StochLean: Probability.Process.Semimartingale.QuadraticVariation.PureJump F000

import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticVariation_ContinuousPart_F000
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Topology.Compactness.Compact

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Quadratic pure-jump semimartingales

This is a property of the existing semimartingale and its sole continuous
bracket, not a competing process or bracket owner. Quadratic pure jump does
not mean a process is constant between jumps: continuous FV drift qualifies.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

def IsSemimartingale.IsQuadraticPureJump
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) : Prop :=
  Indistinguishable (hX.continuousQuadraticVariation hF) 0 P
end ProbabilityTheory


