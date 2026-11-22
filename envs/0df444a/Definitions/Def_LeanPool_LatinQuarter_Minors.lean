-- Prove2me | Definitions.Def_LeanPool_LatinQuarter_Minors
-- name    : LeanPool_LatinQuarter_Minors
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:20:08.32547+00:00
-- url     : https://prove2.me/theorems/4751f1dd-727e-4c82-9035-aaa9a1c38c28
-- title:
--   Minors
-- statement:
--   Definitions and structural lemmas for Minors, from Richard Bean; LeanPool contributors's pinned Critical sets in Latin squares development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Minors.lean

module
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.RingTheory.Ideal.Operations
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LatinQuarter
open scoped BigOperators Matrix
variable {R : Type*} [CommRing R]
def AllMinorsIn {m n : Type*} (M : Matrix m n R) (t : ℕ) (J : Ideal R) : Prop :=
  ∀ (r : Fin t → m) (c : Fin t → n), (M.submatrix r c).det ∈ J
end LatinQuarter


