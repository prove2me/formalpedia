-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_PureMath_BinaryMatrix
-- name    : LeanPool_FormalLearningTheory_PureMath_BinaryMatrix
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:31:24.9979+00:00
-- url     : https://prove2.me/theorems/9ec60297-1318-4844-9e23-ca98f7176258
-- title:
--   Binary Matrix
-- statement:
--   Definitions and structural lemmas for Binary Matrix, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/BinaryMatrix.lean

module
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
universe u
abbrev BinaryMatrix (m n : ℕ) := Fin m → Fin n → Bool
namespace BinaryMatrix
def shatters {m n : ℕ} (M : BinaryMatrix m n) (S : Finset (Fin n)) : Prop :=
  ∀ t ⊆ S, ∃ i : Fin m, ∀ j ∈ S, (M i j = true) ↔ (j ∈ t)
def transpose {m n : ℕ} (M : BinaryMatrix m n) : BinaryMatrix n m :=
  fun j i => M i j
def toFinsetFamily {m n : ℕ} (M : BinaryMatrix m n) :
    Finset (Finset (Fin n)) :=
  Finset.univ.image (fun i : Fin m => Finset.univ.filter (fun j => M i j = true))
noncomputable def vcDim {m n : ℕ} (M : BinaryMatrix m n) : ℕ :=
  M.toFinsetFamily.vcDim
end BinaryMatrix


