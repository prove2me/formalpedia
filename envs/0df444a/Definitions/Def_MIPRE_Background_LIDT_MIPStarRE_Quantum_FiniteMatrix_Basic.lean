-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
-- name    : MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:11:17.488711+00:00
-- url     : https://prove2.me/theorems/43657d81-5bbf-45a2-a8a7-adc446ad29ba
-- title:
--   Definitions of Basic: Basic finite-dimensional matrix operators This module contains the elementary trace and matrix-algebra facts used by…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.Quantum.FiniteMatrix.Basic` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Basic finite-dimensional matrix operators. This module contains the elementary trace and matrix-algebra facts used by the finite-dimensional quantum layer. It introduces the local operator abbreviation `Op d = Matrix d d ℂ` and keeps the basic trace bookkeeping independent of the positive-semidefinite order and normalized-trace material.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (2): `MIPStarRE.Quantum.Op` (Square complex matrices as the finite-dimensional operator algebra.); `Matrix.submatrixLinearMap` (Taking a submatrix is linear in the ambient matrix.).
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `submatrixLinearMap_apply`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.Quantum.FiniteMatrix.Basic` (`MIPRE/Background/LIDT/MIPStarRE/Quantum/FiniteMatrix/Basic.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/Quantum/FiniteMatrix/Basic.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/Quantum/FiniteMatrix/Basic.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/Quantum/FiniteMatrix/Basic.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

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

open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.Elementwise
open WithLp

namespace Matrix

/-! ### Trace bookkeeping -/

-- vendoring compile fix (Lean v4.33): the previous step may close the goal

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
    try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal
  map_smul' := by
    intro c A
    ext i j
    try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal

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

end MIPStarRE.Quantum


