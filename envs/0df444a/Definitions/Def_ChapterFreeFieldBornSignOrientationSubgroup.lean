-- Prove2me | Definitions.Def_ChapterFreeFieldBornSignOrientationSubgroup
-- name    : ChapterFreeFieldBornSignOrientationSubgroup
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-06T01:55:05.972673+00:00
-- url     : https://prove2.me/theorems/24454535-0e82-4686-8d32-36fddde9db1a
-- title:
--   Chapter FreeFieldBornSignOrientationSubgroup
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterFreeFieldBornSignOrientationSubgroup.lean`): generated def bundle for ChapterFreeFieldBornSignOrientationSubgroup. See BookProof/ChapterFreeFieldBornSignOrientationSubgroup.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFreeFieldBornSignOrientationSubgroup.lean

import Theorems.Thm_BookProof_ChapterFreeFieldBornSignOrientationKernel_orientationPreserving_false

import Theorems.Thm_BookProof_ChapterFreeFieldBornSignOrientationKernel_orientationPreserving_xor

import Definitions.Def_ChapterFreeFieldBornSignOrientationKernel
import Definitions.Def_ChapterFreeFieldBornSignHom
import Definitions.Def_ChapterFreeFieldBornSignMatrix
import Definitions.Def_ChapterFreeFieldBornSignOrientation
import Definitions.Def_ChapterFreeFieldBornSignOrientationCard
import Mathlib


/-!
# The orientation-preserving Born sign gauge as an additive subgroup

The boolean sign choices carry their standard elementary abelian `2`-group
structure: pointwise addition on `Bool` is xor. This file packages the
orientation-preserving choices as an actual `AddSubgroup`, rather than only
recording closure as separate propositions.
-/

open BookProof.ChapterFreeFieldBornSignHom
open BookProof.ChapterFreeFieldBornSignMatrix
open BookProof.ChapterFreeFieldBornSignOrientation
open BookProof.ChapterFreeFieldBornSignOrientationKernel
open BookProof.ChapterFreeFieldBornSignOrientationCard

namespace BookProof.ChapterFreeFieldBornSignOrientationSubgroup

variable {n : ℕ}

/-- The additive subgroup of boolean sign choices whose diagonal matrices have
determinant `+1`. -/
def orientationPreservingSigns (n : ℕ) : AddSubgroup (Fin n → Bool) where
  carrier := {b | flipMatrix b ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ}
  zero_mem' := by
    change flipMatrix (fun _ => false) ∈
      Matrix.specialOrthogonalGroup (Fin n) ℝ
    exact orientationPreserving_false
  add_mem' := by
    intro b₁ b₂ h₁ h₂
    have hadd : b₁ + b₂ = fun k => xor (b₁ k) (b₂ k) := by
      funext k
      change b₁ k + b₂ k = xor (b₁ k) (b₂ k)
      cases b₁ k <;> cases b₂ k <;> rfl
    rw [hadd]
    exact orientationPreserving_xor h₁ h₂
  neg_mem' := by
    intro b hb
    exact hb

@[simp] theorem mem_orientationPreservingSigns_iff (b : Fin n → Bool) :
    b ∈ orientationPreservingSigns n ↔
      flipMatrix b ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ :=
  Iff.rfl





/-
In positive dimension, the orientation-preserving subgroup has index two.
-/


end BookProof.ChapterFreeFieldBornSignOrientationSubgroup


