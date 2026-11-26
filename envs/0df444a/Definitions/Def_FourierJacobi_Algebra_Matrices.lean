-- Prove2me | Definitions.Def_FourierJacobi_Algebra_Matrices
-- name    : FourierJacobi_Algebra_Matrices
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:25:50.939813+00:00
-- url     : https://prove2.me/theorems/79491501-c615-4cd7-8edc-ea9aff2721f4
-- title:
--   Matrices
-- statement:
--   Definitions and structural lemmas for Matrices, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/Matrices.lean

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
set_option autoImplicit false
namespace FourierJacobi
namespace LocalMatrix
open Matrix
variable {K : Type*} [Field K]
def X (u : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, u, 0, 0; 0, 1, 0, 0; 0, 0, 1, -u; 0, 0, 0, 1]
def YZ (y z : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, y, z; 0, 1, 0, y; 0, 0, 1, 0; 0, 0, 0, 1]
def N (x y z : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, y, z; 0, 1, x, y; 0, 0, 1, 0; 0, 0, 0, 1]
def D (a : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; 0, a, 0, 0; 0, 0, a⁻¹, 0; 0, 0, 0, 1]
def E (p : K) : Matrix (Fin 4) (Fin 4) K :=
  !![p, 0, 0, 0; 0, 1, 0, 0; 0, 0, p, 0; 0, 0, 0, 1]
def w : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; 0, 0, 1, 0; 0, -1, 0, 0; 0, 0, 0, 1]
def wInv : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; 0, 0, -1, 0; 0, 1, 0, 0; 0, 0, 0, 1]
def J : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]
def g (a x y z : K) : Matrix (Fin 4) (Fin 4) K := D a * N x y z
def indexPairs : Fin 6 → Fin 4 × Fin 4 :=
  ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
def secondCompound (A : Matrix (Fin 4) (Fin 4) K) : Matrix (Fin 6) (Fin 6) K :=
  fun i j =>
    A (indexPairs i).1 (indexPairs j).1 * A (indexPairs i).2 (indexPairs j).2 -
    A (indexPairs i).1 (indexPairs j).2 * A (indexPairs i).2 (indexPairs j).1
end LocalMatrix
end FourierJacobi


