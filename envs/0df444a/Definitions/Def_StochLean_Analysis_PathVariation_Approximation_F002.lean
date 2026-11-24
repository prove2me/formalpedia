-- Prove2me | Definitions.Def_StochLean_Analysis_PathVariation_Approximation_F002
-- name    : StochLean_Analysis_PathVariation_Approximation_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:07:28.735052+00:00
-- url     : https://prove2.me/theorems/cba81f0b-2ec4-4631-8112-9f612a464f2f
-- title:
--   StochLean: Analysis.PathVariation.Approximation F002

import Definitions.Def_StochLean_Analysis_PathVariation_Approximation_F001
import Definitions.Def_SourceProof_2fc3a11ac71f58f5ac32af7f

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Endpoint approximations for finite partitions

The right endpoint projection is monotone, remains in the original endpoint
set, and is at distance at most the mesh on the compact horizon. This is a
deterministic approximation: no extra grid is inserted.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace StochLean.TimePartition

variable {T : ℝ≥0}

noncomputable def ceilingIndex (π : TimePartition T) (t : ℝ≥0) : Fin (π.size + 1) :=
  (upperIndices π t).min' (_root_.Prove2MeSourceProof.h_2fc3a11ac71f58f5ac32af7f π t)
noncomputable def ceilingPoint (π : TimePartition T) (t : ℝ≥0) : ℝ≥0 :=
  π.point (π.ceilingIndex t)
end StochLean.TimePartition


