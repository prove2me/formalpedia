-- Prove2me | Definitions.Def_SourceProof_e1f3ecca529106853c30fa13
-- name    : SourceProof_e1f3ecca529106853c30fa13
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:14:20.672887+00:00
-- url     : https://prove2.me/theorems/cff82acf-0dee-4db5-bdaa-948d5b12f7f3
-- title:
--   StochLean source theorem: StochLean.TimePartition.sum_increment

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

theorem _root_.Prove2MeSourceProof.h_e1f3ecca529106853c30fa13 (π : TimePartition T) (f : ℝ≥0 → ℝ) :
    (∑ i, π.increment f i) = f T - f 0 := by
  have h := (Fin.sum_univ_succ (fun i ↦ f (π.point i))).symm.trans
    (Fin.sum_univ_castSucc (fun i ↦ f (π.point i)))
  rw [π.first_eq_zero, π.last_eq_horizon] at h
  simp only [StochLean.TimePartition.increment, right, left, sum_sub_distrib]
  linarith
end TimePartition

variable {T : ℝ≥0}

end StochLean


