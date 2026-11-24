-- Prove2me | Definitions.Def_StochLean_Analysis_PathVariation_TaggedStepApproximation_F000
-- name    : StochLean_Analysis_PathVariation_TaggedStepApproximation_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:01:05.308034+00:00
-- url     : https://prove2.me/theorems/eeebcf97-0a93-441f-b7af-72c39c7ad91a
-- title:
--   StochLean: Analysis.PathVariation.TaggedStepApproximation F000

import Definitions.Def_StochLean_Analysis_PathVariation_LeftStepApproximation_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Arbitrarily tagged step approximations

Tags may be either endpoint or any point between. They need not be ordered
separately from their containing cells; repeated partition endpoints are allowed.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace StochLean.TimePartition

variable {T : ℝ≥0}

noncomputable def taggedStep (π : TimePartition T) (ξ : Fin π.size → ℝ≥0)
    (f : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  if t = 0 then f 0 else
    ∑ i : Fin π.size, (Ioc (π.left i) (π.right i)).indicator (fun _ ↦ f (ξ i)) t
end StochLean.TimePartition


