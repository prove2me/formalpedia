-- Prove2me | Definitions.Def_StochLean_Analysis_PathVariation_LeftStepApproximation_F000
-- name    : StochLean_Analysis_PathVariation_LeftStepApproximation_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:14:48.513066+00:00
-- url     : https://prove2.me/theorems/f49d04ff-31e8-4960-924e-01da574d28b5
-- title:
--   StochLean: Analysis.PathVariation.LeftStepApproximation F000

import Definitions.Def_StochLean_Analysis_PathVariation_Approximation_F000
import Definitions.Def_StochLean_Analysis_PathVariation_Approximation_F002
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Left-endpoint step approximation on a finite partition

Cells are left-open and right-closed. Repeated endpoints are permitted: every
positive time before the horizon belongs to exactly one nonempty cell.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace StochLean.TimePartition

variable {T : ℝ≥0}

noncomputable def leftStep (π : TimePartition T) (f : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  if t = 0 then f 0 else
    ∑ i : Fin π.size, (Ioc (π.left i) (π.right i)).indicator (fun _ ↦ f (π.left i)) t
end StochLean.TimePartition


