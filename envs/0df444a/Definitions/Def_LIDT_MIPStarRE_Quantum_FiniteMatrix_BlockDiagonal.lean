-- Prove2me | Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
-- name    : LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T10:47:44.573628+00:00
-- url     : https://prove2.me/theorems/a0bad8f5-b2af-430b-805f-d8e7cffceb60
-- title:
--   LIDT definitions: Quantum / FiniteMatrix / BlockDiagonal
-- statement:
--   This bundle provides block-diagonal matrix identities and positivity criteria for finite-dimensional operator arguments. It expands a block diagonal as a sum of Kronecker products, exposes the associated linear map, and characterizes positive semidefiniteness block by block.
--
--   Principal definitions:
--   - `blockDiagonal_eq_sum_kronecker_diagonal`: expands a block diagonal matrix into Kronecker-diagonal terms.
--   - `blockDiagonalLinearMap`: views block diagonalization as a linear map.
--   - `blockDiagonalLinearMap_apply`: gives the application rule for that linear map.
--   - `blockDiagonal_nonneg`: proves positivity from positivity of every diagonal block.
--   - `blockDiagonal_nonneg_iff`: characterizes block-diagonal positivity by its diagonal blocks.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/Quantum/FiniteMatrix/BlockDiagonal.lean#L21-L95

-- Generated from MIPStarRE/Quantum/FiniteMatrix/BlockDiagonal.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Mathlib

namespace LIDT

/-!
# Block-diagonal finite matrix operators

This module contains block-diagonal trace and positive-semidefinite order facts
for finite complex matrices.  The canonical SDP block algebra in Section 9 uses
these lemmas to compare the paper's block form with Mathlib's
`Matrix.blockDiagonal`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder _root_.Matrix.Norms.Elementwise
open WithLp

namespace Matrix

/-- A block-diagonal matrix is the sum of its blocks tensored with the
coordinate projections on the block index. -/
theorem blockDiagonal_eq_sum_kronecker_diagonal {o m : Type*}
    [Fintype o] [DecidableEq o] [Finite m] (B : o → Matrix m m ℂ) :
    Matrix.blockDiagonal B =
      ∑ b : o, Matrix.kronecker (B b)
        (Matrix.diagonal fun c : o => if c = b then (1 : ℂ) else 0) := by
  classical
  let : Fintype m := Fintype.ofFinite m
  ext x y
  rcases x with ⟨i, bx⟩
  rcases y with ⟨j, cy⟩
  rw [Matrix.sum_apply]
  by_cases hxy : bx = cy
  · subst cy
    simp [Matrix.blockDiagonal_apply, Matrix.kronecker, Matrix.kroneckerMap_apply]
  · simp [Matrix.blockDiagonal_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, hxy]

/-- `Matrix.blockDiagonal` as a linear map.

Mathlib provides `Matrix.blockDiagonalAddMonoidHom` and
`Matrix.blockDiagonal_smul`; this declaration packages these two facts in the
linear form needed by finite-dimensional block SDP arguments. -/
def blockDiagonalLinearMap (R : Type*) (m n o α : Type*)
    [Semiring R] [DecidableEq o] [AddCommMonoid α] [Module R α] :
    (o → Matrix m n α) →ₗ[R] Matrix (m × o) (n × o) α where
  toFun := Matrix.blockDiagonal
  map_add' := Matrix.blockDiagonal_add
  map_smul' := Matrix.blockDiagonal_smul

@[simp]
theorem blockDiagonalLinearMap_apply (R : Type*) (m n o α : Type*)
    [Semiring R] [DecidableEq o] [AddCommMonoid α] [Module R α]
    (B : o → Matrix m n α) :
    Matrix.blockDiagonalLinearMap R m n o α B = Matrix.blockDiagonal B :=
  rfl

/-- A block-diagonal complex matrix is positive semidefinite when all of its
diagonal blocks are positive semidefinite. -/
theorem blockDiagonal_nonneg {o m : Type*}
    [Finite o] [DecidableEq o] [Finite m]
    (B : o → Matrix m m ℂ) (hB : ∀ b, 0 ≤ B b) :
    0 ≤ Matrix.blockDiagonal B := by
  classical
  let : Fintype o := Fintype.ofFinite o
  let : Fintype m := Fintype.ofFinite m
  rw [Matrix.blockDiagonal_eq_sum_kronecker_diagonal B]
  exact Finset.sum_nonneg fun b _ =>
    MIPStarRE.Quantum.kronecker_nonneg (hB b) (by
      refine Matrix.nonneg_iff_posSemidef.mpr ?_
      exact Matrix.PosSemidef.diagonal <| by
        intro c
        by_cases hc : c = b <;> simp [hc])

/-- A block-diagonal complex matrix is positive semidefinite exactly when each
of its diagonal blocks is positive semidefinite. -/
theorem blockDiagonal_nonneg_iff {o m : Type*}
    [Finite o] [DecidableEq o] [Finite m]
    (B : o → Matrix m m ℂ) :
    0 ≤ Matrix.blockDiagonal B ↔ ∀ b, 0 ≤ B b := by
  classical
  let : Fintype o := Fintype.ofFinite o
  let : Fintype m := Fintype.ofFinite m
  constructor
  · intro hB b
    refine Matrix.nonneg_iff_posSemidef.mpr ?_
    let e : m → m × o := fun i => (i, b)
    have hsub :
        ((Matrix.blockDiagonal B).submatrix e e).PosSemidef :=
      (Matrix.nonneg_iff_posSemidef.mp hB).submatrix e
    have hEq : (Matrix.blockDiagonal B).submatrix e e = B b := by
      ext i j
      simp [e, Matrix.blockDiagonal_apply_eq]
    simpa [hEq] using hsub
  · exact Matrix.blockDiagonal_nonneg B

end Matrix

end

end LIDT


