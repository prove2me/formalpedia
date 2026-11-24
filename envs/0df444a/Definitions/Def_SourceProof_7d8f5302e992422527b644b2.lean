-- Prove2me | Definitions.Def_SourceProof_7d8f5302e992422527b644b2
-- name    : SourceProof_7d8f5302e992422527b644b2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:00:36.912222+00:00
-- url     : https://prove2.me/theorems/0e853197-5cf8-4e63-9256-5dfb81c378c3
-- title:
--   StochLean source theorem: StochLean.continuousLinearMap_apply_eq_sum_single

import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Group.Real

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Coordinate derivatives of finite real vectors

Coordinates are evaluations of Mathlib's Frechet derivatives on the standard
basis. The identities expand the existing linear and bilinear maps exactly.
-/

@[expose] public section

open Finset

namespace StochLean

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem _root_.Prove2MeSourceProof.h_7d8f5302e992422527b644b2 (L : (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ) :
    L v = ∑ i, L (Pi.single i 1) * v i := by
  conv_lhs => rw [pi_eq_sum_univ' v]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply sum_congr rfl
  intro i _
  exact mul_comm _ _
end StochLean


