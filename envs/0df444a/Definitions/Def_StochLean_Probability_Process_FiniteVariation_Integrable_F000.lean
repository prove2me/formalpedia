-- Prove2me | Definitions.Def_StochLean_Probability_Process_FiniteVariation_Integrable_F000
-- name    : StochLean_Probability_Process_FiniteVariation_Integrable_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:46:22.824291+00:00
-- url     : https://prove2.me/theorems/da98b57f-1ed8-49c6-b878-287911a8e0ad
-- title:
--   StochLean: Probability.Process.FiniteVariation.Integrable F000

import Definitions.Def_StochLean_Probability_Process_Path_FiniteVariation_F000
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
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Bases
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

/-- Finite total path variation almost surely, with integrable actual total
variation. No initial-value or process measurability condition is implicit. -/
def HasIntegrableVariation (X : ℝ≥0 → Ω → ℝ) (P : Measure Ω := by volume_tac) : Prop :=
  HasFiniteTotalVariationPaths X P ∧
    Integrable (fun ω ↦ (eVariationOn (X · ω) univ).toReal) P
variable {X Y : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

end ProbabilityTheory


