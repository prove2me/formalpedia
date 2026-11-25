-- Prove2me | Definitions.Def_SourceProof_c900c7734142f37ce8586a84
-- name    : SourceProof_c900c7734142f37ce8586a84
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:46:04.500807+00:00
-- url     : https://prove2.me/theorems/4969020c-6583-47d8-9540-324abe9b97fb
-- title:
--   StochLean source theorem: StochLean.TimePartition.increment_add

import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F004

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Deterministic variation along finite partitions

This layer has no probability space or filtration. Partitions may repeat endpoints;
zero-length cells contribute zero to quadratic variation. The empty partition is
available precisely at horizon zero. Raw stochastic brackets, which retain the
initial square, are not defined here.
-/

@[expose] public section

open Filter Finset
open scoped NNReal Topology BigOperators

namespace StochLean

namespace TimePartition

variable {T : ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_c900c7734142f37ce8586a84 (π : TimePartition T) (f g : ℝ≥0 → ℝ) (i : Fin π.size) :
    π.increment (f + g) i = π.increment f i + π.increment g i := by
  simp only [StochLean.TimePartition.increment, Pi.add_apply]
  ring
end TimePartition

variable {T : ℝ≥0}

end StochLean


