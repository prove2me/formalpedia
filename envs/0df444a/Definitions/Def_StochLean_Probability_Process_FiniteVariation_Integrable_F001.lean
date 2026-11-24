-- Prove2me | Definitions.Def_StochLean_Probability_Process_FiniteVariation_Integrable_F001
-- name    : StochLean_Probability_Process_FiniteVariation_Integrable_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T16:06:46.388787+00:00
-- url     : https://prove2.me/theorems/01d1ca6f-a8f2-4aef-af7d-92a233373e10
-- title:
--   StochLean: Probability.Process.FiniteVariation.Integrable F001

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Bases
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.UniformSpace.HeineCantor

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Integrable variation on the whole half-line

The variation owner is Mathlib's `eVariationOn`, not a new terminal process.
Finiteness almost surely is an explicit part of the predicate: integrability
of `toReal` alone would incorrectly accept infinite variation, since that
conversion sends infinity to zero.

Adaptedness, cadlag paths, and the zero initial value in Protter's normalized
FV convention are separate hypotheses. In particular an arbitrary random
process constant in time has zero variation, even without a measurable or
integrable initial value. This module does not define local integrable
variation or choose a terminal limit of the process.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

variable {X Y : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

private theorem eVariationOn_const_path (C : ℝ) :
    eVariationOn (fun _ : ℝ≥0 ↦ C) univ = 0 := by
  apply (eVariationOn.eq_zero_iff _).mpr
  intro s _ t _
  exact edist_self C
end ProbabilityTheory


