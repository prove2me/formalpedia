-- Prove2me | Definitions.Def_JacobianConjecture_Definitions
-- name    : JacobianConjecture_Definitions
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T07:58:29.060091+00:00
-- url     : https://prove2.me/theorems/1fa924cd-061d-4214-bf50-5b6cbd08bbed
-- title:
--   Definitions
-- statement:
--   Definitions and structural lemmas for Definitions, from Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz (Arthur742Ramos/jacobian-conjecture-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Alpöge-Fable 3D Jacobian conjecture counterexample development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Arthur742Ramos/jacobian-conjecture-lean/blob/8db55ea3ffa8ba90094d6ef78ee3351ddfce01ca/JacobianConjecture/Definitions.lean

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
set_option autoImplicit true
noncomputable section
open Matrix Function
namespace MvPolynomial
variable {R : Type*} {σ : Type*}
def jacobianMatrix [CommSemiring R] [DecidableEq σ]
    (F : σ → MvPolynomial σ R) : Matrix σ σ (MvPolynomial σ R) :=
  Matrix.of fun i j => pderiv j (F i)
def jacobianDet [CommRing R] [Fintype σ] [DecidableEq σ]
    (F : σ → MvPolynomial σ R) : MvPolynomial σ R :=
  (jacobianMatrix F).det
def evalMap [CommSemiring R] (F : σ → MvPolynomial σ R) (p : σ → R) : σ → R :=
  fun i => eval p (F i)
end MvPolynomial
namespace JacobianCounterexample
open MvPolynomial
variable (K : Type*) [Field K]
def F : Fin 3 → MvPolynomial (Fin 3) K :=
  ![(1 + X 0 * X 1) ^ 3 * X 2 + X 1 ^ 2 * (1 + X 0 * X 1) *
      (C 4 + C 3 * (X 0 * X 1)),
    X 1 + C 3 * X 0 * (1 + X 0 * X 1) ^ 2 * X 2 +
      C 3 * X 0 * X 1 ^ 2 * (C 4 + C 3 * (X 0 * X 1)),
    C 2 * X 0 - C 3 * X 0 ^ 2 * X 1 - X 0 ^ 3 * X 2]
end JacobianCounterexample


