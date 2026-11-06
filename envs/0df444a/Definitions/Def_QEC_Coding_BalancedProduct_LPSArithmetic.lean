-- Prove2me | Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
-- name    : QEC_Coding_BalancedProduct_LPSArithmetic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T20:41:19.596707+00:00
-- url     : https://prove2.me/theorems/f7f53803-b853-4917-89d1-2fb5ca1fe0e2
-- title:
--   LPSArithmetic
-- statement:
--   Definitions and structural lemmas for LPSArithmetic, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSArithmetic.lean

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.NumberTheory.LegendreSymbol.Basic
set_option autoImplicit false
open scoped MatrixGroups
namespace QEC.Coding.BalancedProduct.LPSArithmetic
open Matrix
variable {R : Type*} [CommRing R]
def upperUnipotentPGL : AddChar R PGL(2, R) :=
  Matrix.ProjGenLinGroup.mk.compAddChar
    (Matrix.GeneralLinearGroup.upperRightHom (R := R))
@[simp]
theorem upperUnipotentPGL_apply (x : R) :
    upperUnipotentPGL x =
      Matrix.ProjGenLinGroup.mk
        (Matrix.GeneralLinearGroup.upperRightHom x) :=
  rfl
@[simp]
theorem upperUnipotentPGL_zero : upperUnipotentPGL (0 : R) = 1 :=
  AddChar.map_zero_eq_one _
@[simp]
theorem upperUnipotentPGL_add (x y : R) :
    upperUnipotentPGL (x + y) =
      upperUnipotentPGL x * upperUnipotentPGL y :=
  AddChar.map_add_eq_mul _ _ _
theorem upperUnipotentPGL_injective :
    Function.Injective (upperUnipotentPGL (R := R)) := by
  intro x y hxy
  have hzero : upperUnipotentPGL (x - y) = 1 := by
    rw [sub_eq_add_neg, upperUnipotentPGL_add]
    rw [AddChar.map_neg_eq_inv, hxy, mul_inv_cancel]
  rw [upperUnipotentPGL_apply, Matrix.ProjGenLinGroup.mk_eq_one,
    Matrix.GeneralLinearGroup.center_eq_range_scalar] at hzero
  rcases hzero with ⟨u, hu⟩
  have h01 := congrArg (fun g : GL (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R) 0 1) hu
  exact sub_eq_zero.mp (by
    simpa [Matrix.GeneralLinearGroup.upperRightHom_apply] using h01.symm)
def upperUnipotentSubgroup : Subgroup PGL(2, R) :=
  AddSubgroup.toSubgroup
    ((upperUnipotentPGL (R := R)).toAddMonoidHom.range)
@[simp]
theorem mem_upperUnipotentSubgroup_iff (g : PGL(2, R)) :
    g ∈ upperUnipotentSubgroup (R := R) ↔
      ∃ x : R, upperUnipotentPGL x = g := by
  rfl
theorem upperUnipotentPGL_mem (x : R) :
    upperUnipotentPGL x ∈ upperUnipotentSubgroup (R := R) := by
  exact ⟨x, rfl⟩
noncomputable def upperUnipotentEquiv :
    R ≃ upperUnipotentSubgroup (R := R) where
  toFun x := ⟨upperUnipotentPGL x, upperUnipotentPGL_mem x⟩
  invFun g := Classical.choose (mem_upperUnipotentSubgroup_iff g |>.mp g.property)
  left_inv x := by
    have hx := Classical.choose_spec
      (mem_upperUnipotentSubgroup_iff (upperUnipotentPGL x) |>.mp
        (upperUnipotentPGL_mem x))
    apply upperUnipotentPGL_injective
    exact hx
  right_inv g := by
    apply Subtype.ext
    exact Classical.choose_spec
      (mem_upperUnipotentSubgroup_iff (g : PGL(2, R)) |>.mp g.property)
noncomputable instance upperUnipotentSubgroupFintype [Fintype R] :
    Fintype (upperUnipotentSubgroup (R := R)) :=
  Fintype.ofEquiv R (upperUnipotentEquiv (R := R))
section DeterminantSquareClass
def ProjectiveDetIsSquare (g : PGL(2, R)) : Prop :=
  ∃ A : GL (Fin 2) R,
    Matrix.ProjGenLinGroup.mk A = g ∧ IsSquare A.det
end DeterminantSquareClass
end QEC.Coding.BalancedProduct.LPSArithmetic


