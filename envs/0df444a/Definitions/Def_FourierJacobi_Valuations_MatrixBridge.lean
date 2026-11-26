-- Prove2me | Definitions.Def_FourierJacobi_Valuations_MatrixBridge
-- name    : FourierJacobi_Valuations_MatrixBridge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:27:29.849503+00:00
-- url     : https://prove2.me/theorems/dbff3f41-f4f5-5402-8953-e2a90768e232
-- title:
--   Matrix Bridge
-- statement:
--   Definitions and structural lemmas for Matrix Bridge, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/MatrixBridge.lean

import Definitions.Def_FourierJacobi_Algebra_Matrices
import Definitions.Def_FourierJacobi_Valuations_Cartan
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.Tactic.LinearCombination
set_option autoImplicit false
namespace FourierJacobi
namespace Valuations
open LocalMatrix
variable {K : Type*} [Field K]
def matrixMinimum {n m : ℕ} (v : AddValuation K (WithTop ℤ))
    (A : Matrix (Fin n) (Fin m) K) : WithTop ℤ :=
  Finset.univ.inf fun i => Finset.univ.inf fun j => v (A i j)
def entryListMinimum (v : AddValuation K (WithTop ℤ)) (a x y z : K) : WithTop ℤ :=
  min (min (min (min (min (min 0 (v a)) (v a⁻¹)) (v (a * x))) (v y))
    (v (a * y))) (v z)
def minorListMinimum (v : AddValuation K (WithTop ℤ)) (a x y z : K) : WithTop ℤ :=
  min (min (min (min (min (min (min (min 0 (v a)) (v a⁻¹)) (v (a * x)))
    (v y)) (v (a * y))) (v (a * z))) (v (z / a))) (v (a * (y ^ 2 - x * z)))
def firstColumnShape (d b₁ b₂ c p q r s u w : K) : Matrix (Fin 4) (Fin 4) K :=
  !![d, b₁, b₂, c; 0, p, q, u; 0, r, s, w; 0, 0, 0, d⁻¹]
def cartanEliminator (d b₁ b₂ c : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, -b₁ / d, -b₂ / d, -c / d;
     0, 1, 0, -b₂ / d;
     0, 0, 1, b₁ / d;
     0, 0, 0, 1]
end Valuations
end FourierJacobi


