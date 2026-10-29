-- Prove2me | Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
-- name    : LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T10:46:25.017887+00:00
-- url     : https://prove2.me/theorems/f92dd6b7-f5a3-41c6-a354-0807492fe5c2
-- title:
--   LIDT definitions: Quantum / FiniteMatrix / Basic
-- statement:
--   This bundle provides the basic finite-matrix operations used by the quantum and LDT developments. It supplies reindexing invariance, linear submatrix extraction, the square complex operator type, and Kronecker subtraction identities.
--
--   Principal definitions:
--   - `trace_reindex`: simultaneous row and column reindexing preserves matrix trace.
--   - `submatrixLinearMap`: submatrix extraction is linear in the ambient matrix.
--   - `submatrixLinearMap_apply`: the application rule for the submatrix linear map.
--   - `Op`: the square complex-matrix operator type on a finite index set.
--   - `kronecker_sub_right`: subtraction in the right factor of a Kronecker product.
--   - `kronecker_sub_left`: subtraction in the left factor of a Kronecker product.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/Quantum/FiniteMatrix/Basic.lean#L28-L115

-- Generated from MIPStarRE/Quantum/FiniteMatrix/Basic.lean by skeleton subtraction.
import Mathlib

namespace LIDT

/-!
# Basic finite-dimensional matrix operators

This module contains the elementary trace and matrix-algebra facts used by the
finite-dimensional quantum layer.  It introduces the local operator abbreviation
`Op d = Matrix d d ℂ` and keeps the basic trace bookkeeping independent of the
positive-semidefinite order and normalized-trace material.

## References

The declarations in this file are matrix facts for the LDT
formalization of `references/ldt-paper/`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder _root_.Matrix.Norms.Elementwise
open WithLp

namespace Matrix

/-! ### Trace bookkeeping -/

/-- Reindexing rows and columns by the same equivalence preserves matrix trace.

This generic matrix lemma is used when moving between equivalent finite index
presentations of the same operator. -/
theorem trace_reindex {α β R : Type*} [Fintype α] [Fintype β]
    [AddCommMonoid R] (e : α ≃ β) (M : Matrix α α R) :
    Matrix.trace (Matrix.reindex e e M) = Matrix.trace M := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.reindex_apply]
  rw [← e.symm.sum_comp (fun i : α => M i i)]
  rfl

/-! ### Linear matrix maps -/

/-- Taking a submatrix is linear in the ambient matrix.

This packages the entrywise linearity of `Matrix.submatrix` in the same style
as Mathlib's block-diagonal additive and linear maps. -/
def submatrixLinearMap (R : Type*) {m n m' n' α : Type*}
    [Semiring R] [AddCommMonoid α] [Module R α]
    (row : m' → m) (col : n' → n) :
    Matrix m n α →ₗ[R] Matrix m' n' α where
  toFun := fun A => Matrix.submatrix A row col
  map_add' := by
    intro A B
    ext i j
    rfl
  map_smul' := by
    intro c A
    ext i j
    rfl

@[simp]
theorem submatrixLinearMap_apply (R : Type*) {m n m' n' α : Type*}
    [Semiring R] [AddCommMonoid α] [Module R α]
    (row : m' → m) (col : n' → n) (A : Matrix m n α) :
    Matrix.submatrixLinearMap R row col A = Matrix.submatrix A row col :=
  rfl



end Matrix

namespace MIPStarRE.Quantum

/-! ### Basic operator type -/

/-- Square complex matrices as the finite-dimensional operator algebra. -/
abbrev Op (d : Type*) := Matrix d d ℂ

/-! ### Kronecker product bookkeeping -/

/-- Kronecker product is additive in the right factor, rewritten for subtraction. -/
theorem kronecker_sub_right
    {d₁ d₂ : Type*} {A : Op d₁} {B₁ B₂ : Op d₂} :
    Matrix.kronecker A B₁ - Matrix.kronecker A B₂ =
      Matrix.kronecker A (B₁ - B₂) := by
  have hneg : Matrix.kronecker A (-B₂) = -Matrix.kronecker A B₂ := by
    simpa using (Matrix.kronecker_smul (-1 : ℂ) A B₂)
  calc
    Matrix.kronecker A B₁ - Matrix.kronecker A B₂
        = Matrix.kronecker A B₁ + Matrix.kronecker A (-B₂) := by
            rw [hneg]
            simp [sub_eq_add_neg]
    _ = Matrix.kronecker A (B₁ - B₂) := by
          simpa [sub_eq_add_neg] using (Matrix.kronecker_add A B₁ (-B₂)).symm

/-- Kronecker product is additive in the left factor, rewritten for subtraction. -/
theorem kronecker_sub_left
    {d₁ d₂ : Type*} {A₁ A₂ : Op d₁} {B : Op d₂} :
    Matrix.kronecker A₁ B - Matrix.kronecker A₂ B =
      Matrix.kronecker (A₁ - A₂) B := by
  have hneg : Matrix.kronecker (-A₂) B = -Matrix.kronecker A₂ B := by
    simpa using (Matrix.smul_kronecker (-1 : ℂ) A₂ B)
  calc
    Matrix.kronecker A₁ B - Matrix.kronecker A₂ B
        = Matrix.kronecker A₁ B + Matrix.kronecker (-A₂) B := by
            rw [hneg]
            simp [sub_eq_add_neg]
    _ = Matrix.kronecker (A₁ - A₂) B := by
          simpa [sub_eq_add_neg] using (Matrix.add_kronecker A₁ (-A₂) B).symm

end MIPStarRE.Quantum

end

end LIDT


