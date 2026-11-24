-- Prove2me | Definitions.Def_SourceProof_70e19260acc6d4f0931811a5
-- name    : SourceProof_70e19260acc6d4f0931811a5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:45:13.947676+00:00
-- url     : https://prove2.me/theorems/72c8ada5-9d94-437b-819b-f6635266d166
-- title:
--   StochLean source theorem: StochLean.continuousBilinearMap_apply_eq_sum_single

import Definitions.Def_SourceProof_7d8f5302e992422527b644b2
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

theorem _root_.Prove2MeSourceProof.h_70e19260acc6d4f0931811a5
    (L : (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ) (v w : ι → ℝ) :
    L v w = ∑ i, ∑ j, L (Pi.single i 1) (Pi.single j 1) * v i * w j := by
  have h := _root_.Prove2MeSourceProof.h_7d8f5302e992422527b644b2 (L.flip w) v
  simp only [ContinuousLinearMap.flip_apply] at h
  rw [h]
  apply sum_congr rfl
  intro i _
  rw [_root_.Prove2MeSourceProof.h_7d8f5302e992422527b644b2 (L (Pi.single i 1)) w, sum_mul]
  apply sum_congr rfl
  intro j _
  ring
end StochLean


