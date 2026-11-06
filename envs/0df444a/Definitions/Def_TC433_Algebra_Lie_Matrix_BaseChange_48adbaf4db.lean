-- Prove2me | Definitions.Def_TC433_Algebra_Lie_Matrix_BaseChange_48adbaf4db
-- name    : TC433_Algebra_Lie_Matrix_BaseChange_48adbaf4db
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:25:20.997297+00:00
-- url     : https://prove2.me/theorems/767b69a1-1151-437d-b57b-2ee0edbda8c5
-- title:
--   TauCeti: Algebra / Lie / Matrix / BaseChange
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.Algebra.Lie.Matrix.BaseChange for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/Algebra/Lie/Matrix/BaseChange.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import Definitions.Def_TC433_Compat4331_Tensor_6326550516

public import Mathlib.Algebra.Lie.BaseChange
public import Mathlib.Algebra.Lie.OfAssociative
public import Definitions.Def_TC433_Algebra_Matrix_BaseChange_38ae5477f3

/-!
# Scalar extension of matrix Lie algebras

The associative matrix-algebra base-change equivalence also identifies Mathlib's scalar extension
of the matrix Lie algebra with the matrix Lie algebra over the target ring. The explicit Lie
equivalence is needed because the scalar-extension bracket and the associative commutator bracket
are propositionally equal but come from different, non-definitionally-equal `LieRing` instances.

## Main definitions

* `TauCeti.matrixBaseChangeLieEquiv`: the Lie equivalence
  `A ⊗[R] Matrix n n R ≃ Matrix n n A`.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

namespace TauCeti

open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

variable (n R A : Type*) [Fintype n] [DecidableEq n]
  [CommRing R] [CommRing A] [Algebra R A]

/-- Scalar extension commutes with forming a matrix Lie algebra. The underlying linear
equivalence is `TauCeti.Algebra.matrixBaseChangeAlgEquiv`; the Lie proof bridges Mathlib's
scalar-extension bracket with the associative commutator bracket on matrices. -/
noncomputable def matrixBaseChangeLieEquiv :
    A ⊗[R] Matrix n n R ≃ₗ⁅A⁆ Matrix n n A where
  toFun := Algebra.matrixBaseChangeAlgEquiv R A n
  invFun := (Algebra.matrixBaseChangeAlgEquiv R A n).symm
  left_inv := (Algebra.matrixBaseChangeAlgEquiv R A n).left_inv
  right_inv := (Algebra.matrixBaseChangeAlgEquiv R A n).right_inv
  map_add' := map_add (Algebra.matrixBaseChangeAlgEquiv R A n)
  map_smul' := map_smul (Algebra.matrixBaseChangeAlgEquiv R A n)
  map_lie' {x y} := by
    induction x with
    | tmul a M =>
      induction y with
      | tmul b N =>
        simp only [LieAlgebra.ExtendScalars.bracket_tmul,
          Algebra.matrixBaseChangeAlgEquiv_tmul, LieRing.of_associative_ring_bracket]
        rw [Matrix.map_sub _ (map_sub (algebraMap R A)), Matrix.map_mul, Matrix.map_mul,
          smul_sub]
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm]
      | add y z hy hz => simp [hy, hz]
    | add x z hx hz => simp [hx, hz]

/-- The scalar-extension equivalence sends a pure tensor to the entrywise scalar extension. -/
@[simp]
theorem matrixBaseChangeLieEquiv_tmul (a : A) (M : Matrix n n R) :
    matrixBaseChangeLieEquiv n R A (a ⊗ₜ[R] M) = a • M.map (algebraMap R A) :=
  Algebra.matrixBaseChangeAlgEquiv_tmul R A n a M

end TauCeti


