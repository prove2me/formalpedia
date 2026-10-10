-- Prove2me | Definitions.Def_ChapterFreeFieldBornSignRepresentation
-- name    : ChapterFreeFieldBornSignRepresentation
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-10T09:00:23.722864+00:00
-- url     : https://prove2.me/theorems/d64f8803-c664-40a9-a7f7-eb8bfb7df7d6
-- title:
--   ChapterFreeFieldBornSignRepresentation

import Theorems.Thm_BookProof_ChapterFreeFieldBornSignMatrix_flipMatrix_false

import Theorems.Thm_BookProof_ChapterFreeFieldBornSignMatrix_flipMatrix_xor

import Theorems.Thm_BookProof_ChapterFreeFieldBornSignOrientation_flipMatrix_mem_orthogonalGroup

import Definitions.Def_ChapterFreeFieldBornSignOrientationQuotient
import Definitions.Def_ChapterFreeFieldBornSignAction
import Definitions.Def_ChapterFreeFieldBornSignHom
import Definitions.Def_ChapterFreeFieldBornSignMatrix
import Definitions.Def_ChapterFreeFieldBornSignOrientation
import Definitions.Def_ChapterFreeFieldBornSignOrientationSubgroup
import Mathlib


/-!
# Faithful orthogonal representation of the Born sign gauge

The diagonal boolean sign action is packaged here as a genuine monoid
representation in the real orthogonal group.  It is faithful, and its
special-orthogonal preimage is exactly the multiplicative copy of the
orientation-preserving additive subgroup.
-/

open BookProof.ChapterFreeFieldBornSignAction
open BookProof.ChapterFreeFieldBornSignHom
open BookProof.ChapterFreeFieldBornSignMatrix
open BookProof.ChapterFreeFieldBornSignOrientation
open BookProof.ChapterFreeFieldBornSignOrientationSubgroup

namespace BookProof.ChapterFreeFieldBornSignRepresentation

variable {n : ℕ}

/-- The faithful diagonal representation of boolean sign choices in `O(n)`. -/
def flipRepresentation (n : ℕ) :
    Multiplicative (Fin n → Bool) →* Matrix.orthogonalGroup (Fin n) ℝ where
  toFun b := ⟨flipMatrix b.toAdd, flipMatrix_mem_orthogonalGroup b.toAdd⟩
  map_one' := by
    ext i j
    exact congrFun (congrFun (flipMatrix_false (n := n)) i) j
  map_mul' := by
    intro b₁ b₂
    apply Subtype.ext
    change flipMatrix (b₁.toAdd + b₂.toAdd) =
      flipMatrix b₁.toAdd * flipMatrix b₂.toAdd
    have hadd : b₁.toAdd + b₂.toAdd =
        fun k => xor (b₁.toAdd k) (b₂.toAdd k) := by
      funext k
      change b₁.toAdd k + b₂.toAdd k = xor (b₁.toAdd k) (b₂.toAdd k)
      cases b₁.toAdd k <;> cases b₂.toAdd k <;> rfl
    rw [hadd, flipMatrix_xor]

@[simp] theorem flipRepresentation_apply (b : Multiplicative (Fin n → Bool)) :
    (flipRepresentation n b : Matrix (Fin n) (Fin n) ℝ) = flipMatrix b.toAdd :=
  rfl

/-
Equality of diagonal sign matrices recovers the underlying sign choice.
-/


/-
The diagonal orthogonal representation is faithful.
-/






end BookProof.ChapterFreeFieldBornSignRepresentation


