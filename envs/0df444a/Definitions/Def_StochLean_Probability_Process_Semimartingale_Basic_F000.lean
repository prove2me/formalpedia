-- Prove2me | Definitions.Def_StochLean_Probability_Process_Semimartingale_Basic_F000
-- name    : StochLean_Probability_Process_Semimartingale_Basic_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:07:30.74035+00:00
-- url     : https://prove2.me/theorems/7b466445-6974-4fc8-9e6f-45b99f46aa7d
-- title:
--   StochLean: Probability.Process.Semimartingale.Basic F000

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F000
import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F002
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F003
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Semimartingales as good integrators

The canonical predicate is zero-sequential continuity of the elementary
integral for uniform convergence in `(t,ω)`. The epsilon/delta source
continuity criterion is proved equivalent. Classical decompositions are not
part of this definition. This file does not select a stochastic integral for
general caglad integrands or a quadratic variation.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Zero-sequential continuity of the elementary integral on the Protter source class. -/
def IsGoodIntegrator (X : ℝ≥0 → Ω → ℝ) (F : Filtration ℝ≥0 mΩ) (P : Measure Ω) : Prop :=
  ∀ H : ℕ → ℝ≥0 → Ω → ℝ, ∀ hH : ∀ n, IsSimplePredictable (H n) F,
    TendstoUniformly (fun n (z : ℝ≥0 × Ω) ↦ H n z.1 z.2) (fun _ ↦ 0) atTop →
      TendstoInMeasure P (fun n ↦ (hH n).elementaryIntegral X) atTop 0
/-- Neighborhood formulation of source continuity at zero, with uniform input
neighborhoods and probability output neighborhoods. -/
def ElementaryIntegralContinuousAtZero (X : ℝ≥0 → Ω → ℝ)
    (F : Filtration ℝ≥0 mΩ) (P : Measure Ω) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ η : ℝ≥0∞, 0 < η → ∃ δ : ℝ, 0 < δ ∧
    ∀ H : ℝ≥0 → Ω → ℝ, ∀ hH : IsSimplePredictable H F,
      (∀ t ω, ‖H t ω‖ ≤ δ) → P {ω | ε ≤ ‖hH.elementaryIntegral X ω‖} ≤ η
variable {X : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}

end ProbabilityTheory


