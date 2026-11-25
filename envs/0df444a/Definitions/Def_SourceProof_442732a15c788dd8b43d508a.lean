-- Prove2me | Definitions.Def_SourceProof_442732a15c788dd8b43d508a
-- name    : SourceProof_442732a15c788dd8b43d508a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:30:58.07878+00:00
-- url     : https://prove2.me/theorems/a396ac6d-8e10-4aab-995e-c93b7a77f132
-- title:
--   StochLean source theorem: StochLean.quadraticPairSum_stop_terminal

import Definitions.Def_StochLean_Analysis_PathVariation_QuadraticPairSums_F000
import Definitions.Def_SourceProof_939d8318cd36045b63ec8877
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Order.Filter.Finite
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Jump-series convergence for partial quadratic-pair sums

Partition horizons may vary and only need eventually cover the fixed
evaluation time. Clipping retains repeated endpoints and the last partial
cell; no additional mesh rate or refinement assumption is introduced.
-/

@[expose] public section

open Set Finset Filter ProbabilityTheory
open scoped NNReal Topology

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_442732a15c788dd8b43d508a {S T : ℝ≥0} (π : TimePartition S) (hT : T ≤ S)
    (Φ : ℝ → ℝ → ℝ) (x : ℝ≥0 → ℝ) :
    quadraticPairSum (π.stop T hT) Φ x T = quadraticPairSum π Φ x T := by
  simp only [StochLean.quadraticPairSum, StochLean.TimePartition.left, StochLean.TimePartition.right, StochLean.TimePartition.stop,
    min_assoc, min_self]
  rfl
end StochLean


