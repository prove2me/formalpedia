-- Prove2me | Definitions.Def_TC433_LinearAlgebra_Matrix_GeneralLinearGroup_Equivalence_f50a30e018
-- name    : TC433_LinearAlgebra_Matrix_GeneralLinearGroup_Equivalence_f50a30e018
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:32:47.895621+00:00
-- url     : https://prove2.me/theorems/4ada53dd-6bd1-443b-8154-c6130dd70ab0
-- title:
--   TauCeti: LinearAlgebra / Matrix / GeneralLinearGroup / Equivalence
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Equivalence for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/Equivalence.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Two-sided invertible equivalence of matrices

Matrices related by `L * A * R` with `L` and `R` invertible. Rows and columns are transformed
independently, so the two index types are separate, and nothing here needs more than a
semiring.

## Main results

* `Matrix.GeneralLinearGroup.inv_mul_mul_inv_of_mul_mul_eq`: inverting a two-sided
  invertible transformation.
* `Equiv.reindexGL`: reindexing the rows and columns of a general linear group along an
  equivalence of index types, with `Equiv.reindexGL_refl` and `Equiv.reindexGL_symm`.
-/

namespace Matrix.GeneralLinearGroup

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

public section
set_option backward.isDefEq.respectTransparency.types false

/-- **Inverting a two-sided invertible transformation.** The rows and columns are transformed
independently, so they need not share an index type. -/
theorem inv_mul_mul_inv_of_mul_mul_eq {S : Type*} [Semiring S]
    {A B : Matrix ι κ S} (L : GeneralLinearGroup ι S) (R : GeneralLinearGroup κ S)
    (h : (L : Matrix ι ι S) * A * (R : Matrix κ κ S) = B) :
    (↑L⁻¹ : Matrix ι ι S) * B * (↑R⁻¹ : Matrix κ κ S) = A := by
  -- with the rows and columns indexed separately, the two cancellations are named rather
  -- than left to `simp`, which no longer matches them across the differing index types
  have hL : (↑L⁻¹ : Matrix ι ι S) * (L : Matrix ι ι S) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hR : (R : Matrix κ κ S) * (↑R⁻¹ : Matrix κ κ S) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [← h]
  simp only [Matrix.mul_assoc, hR, Matrix.mul_one]
  rw [← Matrix.mul_assoc, hL, Matrix.one_mul]

end

end Matrix.GeneralLinearGroup

namespace Equiv

public section

universe u

variable {n p : Type*} [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p]
  (e : n ≃ p) (R : Type u) [CommSemiring R]

/-- Reindexing along an equivalence of index types, as a group isomorphism of general linear
groups. -/
def reindexGL : GL n R ≃* GL p R :=
  Units.mapEquiv (Matrix.reindexAlgEquiv R R e).toRingEquiv.toMulEquiv

@[simp]
theorem coe_reindexGL (M : GL n R) :
    (reindexGL e R M : Matrix p p R) = (M : Matrix n n R).submatrix e.symm e.symm := by
  simp [reindexGL, Units.coe_mapEquiv, Matrix.reindex_apply]

/-- Reindexing along the identity equivalence is the identity. -/
@[simp]
theorem reindexGL_refl : (Equiv.refl n).reindexGL R = MulEquiv.refl (GL n R) := by
  ext M i j
  simp

/-- Reindexing along the inverse equivalence is the inverse isomorphism. -/
theorem reindexGL_symm : e.symm.reindexGL R = (e.reindexGL R).symm := by
  refine MulEquiv.ext fun M => (e.reindexGL R).injective ?_
  rw [MulEquiv.apply_symm_apply]
  ext i j
  simp

end

end Equiv


