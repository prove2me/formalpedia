-- Prove2me | Definitions.Def_TC433_LinearAlgebra_Matrix_Submatrix_316eb08705
-- name    : TC433_LinearAlgebra_Matrix_Submatrix_316eb08705
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:25:42.601591+00:00
-- url     : https://prove2.me/theorems/62c3f677-4549-4065-9de6-7fb0f65d748b
-- title:
--   TauCeti: LinearAlgebra / Matrix / Submatrix
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.LinearAlgebra.Matrix.Submatrix for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/LinearAlgebra/Matrix/Submatrix.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Matrix.submatrix` and `Matrix.submatrix_submatrix` occur in the statements and proofs below.
public import Mathlib.LinearAlgebra.Matrix.Defs
-- `Subgroup` and the group structure on `Equiv.Perm` are used by `TauCeti.matrixSymmetryGroup`.
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.GroupTheory.Perm.Basic

/-!
# Permutations preserving a square matrix

A permutation `σ` of the index set of a square matrix `M` *preserves* `M` when
`M.submatrix σ σ = M`. This file records the three closure properties
`TauCeti.submatrix_perm_refl`, `TauCeti.submatrix_perm_trans` and `TauCeti.submatrix_perm_symm`,
and packages them as the subgroup `TauCeti.matrixSymmetryGroup` of `Equiv.Perm`.

For the Cartan matrix of a Dynkin diagram these permutations are the diagram symmetries.

## Main definitions

* `TauCeti.matrixSymmetryGroup`: the group of permutations preserving a given square matrix.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

namespace TauCeti

variable {B α : Type*} {M : Matrix B B α} {σ τ : Equiv.Perm B}

/-- The identity permutation preserves every square matrix.

This is Mathlib's `Matrix.submatrix_id_id` with the reindexing spelled as `Equiv.refl` rather than
as `id`. The two are equal only by unfolding the coercion `⇑(Equiv.refl B) = id`, which `rw` and
`simp` do not do: a statement carrying `Matrix.submatrix_id_id` where a proof about
`⇑(Equiv.refl B)` is expected is not type-correct at their `implicit` transparency, so no such
statement can be rewritten with. -/
theorem submatrix_perm_refl (M : Matrix B B α) :
    M.submatrix (Equiv.refl B) (Equiv.refl B) = M := by
  rw [Equiv.coe_refl, Matrix.submatrix_id_id]

/-- If `σ` and `τ` preserve a square matrix then so does `σ.trans τ`. -/
theorem submatrix_perm_trans (hσ : M.submatrix σ σ = M) (hτ : M.submatrix τ τ = M) :
    M.submatrix (σ.trans τ) (σ.trans τ) = M := by
  rw [Equiv.coe_trans, ← Matrix.submatrix_submatrix, hτ, hσ]

/-- If `σ` preserves a square matrix then so does `σ.symm`. -/
theorem submatrix_perm_symm (hσ : M.submatrix σ σ = M) : M.submatrix σ.symm σ.symm = M :=
  calc M.submatrix ⇑σ.symm ⇑σ.symm
      = (M.submatrix ⇑σ ⇑σ).submatrix ⇑σ.symm ⇑σ.symm := by rw [hσ]
    _ = M := by rw [Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id]

/-- **The symmetry group of a square matrix**: the permutations of its index type which leave it
unchanged when both axes are reindexed along them. -/
def matrixSymmetryGroup (M : Matrix B B α) : Subgroup (Equiv.Perm B) where
  carrier := {σ | M.submatrix σ σ = M}
  one_mem' := submatrix_perm_refl M
  mul_mem' hσ hτ := submatrix_perm_trans hτ hσ
  inv_mem' hσ := submatrix_perm_symm hσ

theorem mem_matrixSymmetryGroup_iff : σ ∈ matrixSymmetryGroup M ↔ M.submatrix σ σ = M :=
  Iff.rfl

end TauCeti


