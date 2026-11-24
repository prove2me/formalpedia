-- Prove2me | Definitions.Def_StochLean_Probability_Process_UCP_F000
-- name    : StochLean_Probability_Process_UCP_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:56:43.016007+00:00
-- url     : https://prove2.me/theorems/7deb060b-1508-4bb8-998f-e5380001c85e
-- title:
--   StochLean: Probability.Process.UCP F000

import Definitions.Def_StochLean_Probability_Process_Path_Supremum_F000
import Definitions.Def_StochLean_Probability_Process_Path_Supremum_F001
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Uniform convergence on compact time intervals in probability

The compact deviation has an extended nonnegative value, so it never uses a
default real supremum of an unbounded set. Its equality with a countable dense
supremum is proved on right-continuous paths. Measurability is then a theorem,
not an assumption hidden in the definition of an uncountable supremum.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X Y : ℝ≥0 → Ω → ℝ}

noncomputable def compactDeviation (X Y : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  ⨆ t : ℝ≥0, ⨆ (_ : t ≤ T), ENNReal.ofReal ‖X t ω - Y t ω‖
end ProbabilityTheory


