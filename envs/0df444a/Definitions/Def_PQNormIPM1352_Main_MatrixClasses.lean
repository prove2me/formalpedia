-- Prove2me | Definitions.Def_PQNormIPM1352_Main_MatrixClasses
-- name    : PQNormIPM1352_Main_MatrixClasses
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:06:03.08465+00:00
-- url     : https://prove2.me/theorems/08e88649-22e5-4865-8ed8-fd6dc5340e47
-- title:
--   SDD matrices, M-matrices and non-zero counts
-- statement:
--   Let $A$ be a real square matrix indexed by a finite set.
--
--   1. $A$ is **symmetric diagonally dominant (SDD)** if it is symmetric and $A(j,j) \ge \sum_{i \ne j} |A(i,j)|$ for every $j$; it is **strictly** diagonally dominant if the inequality is strict for every $j$.
--   2. $A$ is an **M-matrix** if it is positive semidefinite (in particular symmetric) and all its off-diagonal entries are non-positive.
--   3. $\mathrm{nnz}(A)$ is the number of non-zero entries of a matrix.
--
--   Linear systems in positive definite SDD matrices can be solved in nearly linear time (Theorem 2 of the paper), and a positive definite M-matrix becomes SDD after a diagonal scaling. These classes describe the Schur complement of Theorem 10 and the input of the solver oracle.
-- source:
--   Marco Pirazzini, Daniel Spielman, A Fast and Accurate Algorithm for the p → q Norm of Sparse Non-Negative Matrices, STOC 2027 submission #1352 (October 2026), §2.1.2, p. 3

import Mathlib

/-!
# SDD matrices, M-matrices and sparsity counts

Pirazzini–Spielman, STOC 2027 submission #1352, §2.1.2, p. 3.
-/

open Matrix

namespace PQNormIPM1352.Main

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A symmetric diagonally dominant (SDD) matrix (§2.1.2, p. 3): `A` is symmetric and for every
`j`, `A(j,j) ≥ ∑_{i ≠ j} |A(i,j)|`. -/
def IsSDD (A : Matrix ι ι ℝ) : Prop :=
  Aᵀ = A ∧ ∀ j, ∑ i ∈ Finset.univ.erase j, |A i j| ≤ A j j

/-- A strictly diagonally dominant symmetric matrix: symmetric and for every `j`,
`A(j,j) > ∑_{i ≠ j} |A(i,j)|`. -/
def IsStrictlySDD (A : Matrix ι ι ℝ) : Prop :=
  Aᵀ = A ∧ ∀ j, ∑ i ∈ Finset.univ.erase j, |A i j| < A j j

/-- A (symmetric) M-matrix in the sense of §2.1.2, p. 3: a positive semidefinite matrix whose
off-diagonal entries are non-positive. (Mathlib's `PosSemidef` includes symmetry.) -/
def IsMMatrix (A : Matrix ι ι ℝ) : Prop :=
  A.PosSemidef ∧ ∀ i j, i ≠ j → A i j ≤ 0

/-- The number of non-zero entries of a matrix. -/
noncomputable def nnz {κ : Type*} [Fintype κ] (A : Matrix ι κ ℝ) : ℕ :=
  (Finset.univ.filter fun ij : ι × κ => A ij.1 ij.2 ≠ 0).card

end PQNormIPM1352.Main


