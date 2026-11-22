-- Prove2me | Definitions.Def_LeanPool_LatinQuarter_Vanishing
-- name    : LeanPool_LatinQuarter_Vanishing
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:20:27.75146+00:00
-- url     : https://prove2.me/theorems/0e63a8db-c07c-48ff-baec-280520895223
-- title:
--   Vanishing
-- statement:
--   Definitions and structural lemmas for Vanishing, from Richard Bean; LeanPool contributors's pinned Critical sets in Latin squares development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Vanishing.lean

module
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Algebra.CharP.Frobenius
public import Definitions.Def_LeanPool_LatinQuarter_Minors
public import Definitions.Def_LeanPool_LatinQuarter_SquareZero
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LatinQuarter
open scoped BigOperators Matrix
variable {R : Type*} [CommRing R] [CharP R 2]
noncomputable abbrev squareHom : R →+* R := frobenius R 2
end LatinQuarter


