-- Prove2me | Definitions.Def_LeanPool_CorlessNilpotent_Matrix
-- name    : LeanPool_CorlessNilpotent_Matrix
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T22:40:50.026115+00:00
-- url     : https://prove2.me/theorems/fbcc6aca-6a34-4a4f-8a0d-4c5cfd928c2f
-- title:
--   Matrix
-- statement:
--   Definitions and structural lemmas for Matrix, from Marcel Blattner; maintained by LeanPool contributors's pinned Corless's nilpotent Bohemian matrix conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Matrix.lean

module
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Definitions.Def_LeanPool_CorlessNilpotent_Main
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Polynomial Matrix
namespace Corless
def T (m : ℕ) (u : ℕ → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => if (j : ℕ) = i + 1 then u i else if (i : ℕ) = j + 1 then -u j else 0
noncomputable def CM (m : ℕ) (u : ℕ → ℂ) : Matrix (Fin m) (Fin m) ℂ[X] := charmatrix (T m u)
noncomputable def E (s : ℕ → ℤ) (j : ℕ) : ℂ[X] := expand ℂ 2 ((Dv s j).map (Int.castRingHom ℂ))
noncomputable def entrySign (z : ℂ) : ℤ := if z = 1 then 1 else -1
end Corless


