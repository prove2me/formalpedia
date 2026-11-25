-- Prove2me | Definitions.Def_SourceProof_41065a6db1832742f7329248
-- name    : SourceProof_41065a6db1832742f7329248
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:27:58.403093+00:00
-- url     : https://prove2.me/theorems/be47dcca-220f-50d2-b019-db802e4ce78c
-- title:
--   StochLean source theorem: ProbabilityTheory.IsContinuousLocalMartingale.isSemimartingale

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_Basic_F001
import Definitions.Def_SourceProof_079c7ce547fc1a0e6f00ab0a
import Definitions.Def_SourceProof_122b20548f56d05fe641da9a
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Probability.Martingale.Centering
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.HittingTime
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Order.Compact

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Locally square-integrable and continuous local martingale examples

The existing bounded masked localization supplies the L2 witnesses for continuous local
martingales. No L1 or L2 assumption on their unmasked initial values is introduced.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsFiniteMeasure P] [SigmaFiniteFiltration P F]
  {X : ℝ≥0 → Ω → ℝ}

namespace IsContinuousLocalMartingale
theorem _root_.Prove2MeSourceProof.h_41065a6db1832742f7329248
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P) :
    IsSemimartingale X F P :=
  _root_.Prove2MeSourceProof.h_079c7ce547fc1a0e6f00ab0a hF hX.1.2.1
    ((_root_.Prove2MeSourceProof.h_122b20548f56d05fe641da9a hX) hF)
end IsContinuousLocalMartingale

end ProbabilityTheory


