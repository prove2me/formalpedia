-- Prove2me | Definitions.Def_LeanPool_LatinQuarter_Rows
-- name    : LeanPool_LatinQuarter_Rows
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:20:24.117969+00:00
-- url     : https://prove2.me/theorems/c8ca0c5f-64ec-4a06-a1f2-776637c02ab0
-- title:
--   Rows
-- statement:
--   Definitions and structural lemmas for Rows, from Richard Bean; LeanPool contributors's pinned Critical sets in Latin squares development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Rows.lean

module
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.CharP.Two
public import Definitions.Def_LeanPool_LatinQuarter_Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LatinQuarter
open scoped BigOperators Matrix
abbrev FreeColumn {n : ℕ} (P : Finset (Cell n)) (r : Fin n) :=
  {c : Fin n // (r, c) ∉ P}
abbrev RowChoices {n : ℕ} (P : Finset (Cell n)) :=
  (r : Fin n) → Equiv.Perm (FreeColumn P r)
noncomputable def chosenSquare {n : ℕ} (P : Finset (Cell n))
    (L : Square n) (σ : RowChoices P) : Square n := by
  classical
  exact fun r c => L r ((σ r).subtypeCongr (Equiv.refl _) c)
end LatinQuarter


