-- Prove2me | Definitions.Def_LeanPool_LatinQuarter_Counting
-- name    : LeanPool_LatinQuarter_Counting
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:20:40.521962+00:00
-- url     : https://prove2.me/theorems/15e797e4-f238-49ca-b7f7-dfca927ef109
-- title:
--   Counting
-- statement:
--   Definitions and structural lemmas for Counting, from Richard Bean; LeanPool contributors's pinned Critical sets in Latin squares development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Counting.lean

module
public import Definitions.Def_LeanPool_LatinQuarter_Rows
public import Definitions.Def_LeanPool_LatinQuarter_Tags
public import Definitions.Def_LeanPool_LatinQuarter_SquareZero
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LatinQuarter
open scoped BigOperators Matrix
open MvPolynomial
noncomputable def clueProduct {n : ℕ} {R : Type*} [CommRing R]
    (P : Finset (Cell n)) (L : Square n) (Y : Matrix (Fin n) (Fin n) R) : R := by
  classical
  exact ∏ r, ∏ c : {c : Fin n // (r, c) ∈ P}, Y c (L r c)
noncomputable def rowMinorProduct {n : ℕ} {R : Type*} [CommRing R]
    (P : Finset (Cell n)) (L : Square n) (Y : Matrix (Fin n) (Fin n) R) : R := by
  classical
  exact ∏ r, (Y.submatrix (fun c : FreeColumn P r => c.val)
    (fun c : FreeColumn P r => L r c)).det
abbrev columnSymbol {n : ℕ} (M : Square n) (p : Cell n) : Cell n :=
  (p.2, M p.1 p.2)
end LatinQuarter


