-- Prove2me | Definitions.Def_StochLean_Analysis_PathVariation_VectorEnergy_F000
-- name    : StochLean_Analysis_PathVariation_VectorEnergy_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:57:06.344486+00:00
-- url     : https://prove2.me/theorems/2ed78a6e-a0a2-45f0-81eb-4da2b11fb692
-- title:
--   StochLean: Analysis.PathVariation.VectorEnergy F000

import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F002
import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F003
import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F005
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Real

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Vector increment energies bounded by the existing coordinate square sums

These are deterministic finite sums, not a new stochastic bracket. The finite
product uses Mathlib's sup norm; domination by coordinate squares also covers
the empty coordinate type.
-/

@[expose] public section

open Finset Filter
open scoped NNReal

namespace StochLean

noncomputable def normSquareVariationSum {E : Type*} [NormedAddCommGroup E]
    {T : ℝ≥0} (π : TimePartition T) (x : ℝ≥0 → E) : ℝ :=
  ∑ i : Fin π.size, ‖x (π.right i) - x (π.left i)‖ ^ 2
end StochLean


