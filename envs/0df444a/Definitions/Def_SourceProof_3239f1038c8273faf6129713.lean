-- Prove2me | Definitions.Def_SourceProof_3239f1038c8273faf6129713
-- name    : SourceProof_3239f1038c8273faf6129713
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:12:43.629668+00:00
-- url     : https://prove2.me/theorems/0ea393c8-fc22-5c6b-9a13-cfd771344fa9
-- title:
--   StochLean source theorem: ProbabilityTheory.HasFiniteTotalVariationPaths.stoppedProcess

import Definitions.Def_StochLean_Probability_Process_Path_FiniteVariation_F000
import Definitions.Def_StochLean_Probability_Process_Stopping_TerminalValue_F000
import Definitions.Def_SourceProof_50a177887096eaca73013898
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.LocalProperty
import Mathlib.Probability.Process.Predictable
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Order
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.UniformSpace.HeineCantor

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Whole-half-line variation after stopping

The actual extended variation of a stopped path is its variation up to the
stopping time, including the stopping endpoint. Infinite times use the
original whole-half-line variation through the existing terminal-valued
sampling owner. None of these pathwise statements require stopping-time
measurability, cadlag paths, or finite variation.
-/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ℝ≥0 → Ω → ℝ}

namespace HasFiniteTotalVariationPaths
theorem _root_.Prove2MeSourceProof.h_3239f1038c8273faf6129713
    (hv : HasFiniteTotalVariationPaths X P) (τ : Ω → WithTop ℝ≥0) :
    HasFiniteTotalVariationPaths (stoppedProcess X τ) P := by
  filter_upwards [hv] with ω hω
  exact ne_top_of_le_ne_top hω (_root_.Prove2MeSourceProof.h_50a177887096eaca73013898 X τ ω)
end HasFiniteTotalVariationPaths

end ProbabilityTheory


