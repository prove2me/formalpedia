-- Prove2me | Definitions.Def_StochLean_Analysis_PathVariation_Oscillation_F000
-- name    : StochLean_Analysis_PathVariation_Oscillation_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:57:05.521449+00:00
-- url     : https://prove2.me/theorems/587ffb18-0cb2-4221-a1cb-ab6da597c0ab
-- title:
--   StochLean: Analysis.PathVariation.Oscillation F000

import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F002
import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F003
import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F005
import Mathlib.Topology.UniformSpace.HeineCantor

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Vanishing increments on fine deterministic partitions -/

@[expose] public section

open Filter Finset Set
open scoped NNReal Topology

namespace StochLean.TimePartition

variable {T : ℝ≥0}

/-- Finite maximum increment, including the empty partition at zero. -/
noncomputable def maxIncrement (π : TimePartition T) (f : ℝ≥0 → ℝ) : ℝ≥0 :=
  Finset.univ.sup (fun i ↦ ‖π.increment f i‖₊)
end StochLean.TimePartition


