-- Prove2me | Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
-- name    : LeanPool_LowWeightPauliDynamics_Pauli_Matrix
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:06:17.612817+00:00
-- url     : https://prove2.me/theorems/065677ee-6e30-44e0-a143-c83779b506d0
-- title:
--   Matrix
-- statement:
--   Definitions and structural lemmas for Matrix, from Jue Xu; LeanPool contributors's pinned Low-weight Pauli dynamics and truncation error development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean

module
public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.Module.Torsion.Field
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_eq_phaseMul_iff
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_eq_self_iff
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_phase
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_x
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_z
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_zero
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_mul_self_right
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_phaseMul_left
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_phaseMul_right
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_self
attribute [local simp] Lean4LPD.PauliString.phaseMul_eq_phaseMul_iff
attribute [local simp] Lean4LPD.PauliString.phaseMul_eq_self_iff
attribute [local simp] Lean4LPD.PauliString.phaseMul_phase
attribute [local simp] Lean4LPD.PauliString.phaseMul_x
attribute [local simp] Lean4LPD.PauliString.phaseMul_z
attribute [local simp] Lean4LPD.PauliString.phaseMul_zero
attribute [local simp] Lean4LPD.PauliString.sympForm_mul_self_right
attribute [local simp] Lean4LPD.PauliString.sympForm_phaseMul_left
attribute [local simp] Lean4LPD.PauliString.sympForm_phaseMul_right
attribute [local simp] Lean4LPD.PauliString.sympForm_self


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Lean4LPD
noncomputable def iPow (k : ZMod 4) : ℂ := Complex.I ^ k.val
noncomputable def negOnePow (a : ZMod 2) : ℂ := (-1 : ℂ) ^ a.val
@[simp] lemma iPow_zero : iPow 0 = 1 := by simp [iPow]
lemma iPow_one : iPow 1 = Complex.I := by simp [iPow, show (1 : ZMod 4).val = 1 from rfl]
abbrev Bits (n : ℕ) := Fin n → ZMod 2
namespace PauliString
variable {n : ℕ} {G s t : PauliString n}
noncomputable def toMatrix (s : PauliString n) : Matrix (Bits n) (Bits n) ℂ :=
  Matrix.of fun a b => if a = b + s.x then iPow s.phase * negOnePow (s.z ⬝ᵥ b) else 0
lemma toMatrix_apply (s : PauliString n) (a b : Bits n) :
    toMatrix s a b = if a = b + s.x then iPow s.phase * negOnePow (s.z ⬝ᵥ b) else 0 := rfl
example : toMatrix X1 0 0 = 0 ∧ toMatrix X1 0 1 = 1 ∧
    toMatrix X1 1 0 = 1 ∧ toMatrix X1 1 1 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [toMatrix_apply, if_neg (by decide : ¬ ((0 : Bits 1) = 0 + X1.x))]
  · rw [toMatrix_apply, if_pos (by decide : (0 : Bits 1) = 1 + X1.x)]; simp [X1, negOnePow]
  · rw [toMatrix_apply, if_pos (by decide : (1 : Bits 1) = 0 + X1.x)]; simp [X1, negOnePow]
  · rw [toMatrix_apply, if_neg (by decide : ¬ ((1 : Bits 1) = 1 + X1.x))]
example : toMatrix Z1 0 0 = 1 ∧ toMatrix Z1 0 1 = 0 ∧
    toMatrix Z1 1 0 = 0 ∧ toMatrix Z1 1 1 = -1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [toMatrix_apply, if_pos (by decide : (0 : Bits 1) = 0 + Z1.x)]; simp [Z1, negOnePow, show (1 : ZMod 2).val = 1 from rfl]
  · rw [toMatrix_apply, if_neg (by decide : ¬ ((0 : Bits 1) = 1 + Z1.x))]
  · rw [toMatrix_apply, if_neg (by decide : ¬ ((1 : Bits 1) = 0 + Z1.x))]
  · rw [toMatrix_apply, if_pos (by decide : (1 : Bits 1) = 1 + Z1.x)]; simp [Z1, negOnePow, show (1 : ZMod 2).val = 1 from rfl]
example : toMatrix Y1 0 0 = 0 ∧ toMatrix Y1 0 1 = -Complex.I ∧
    toMatrix Y1 1 0 = Complex.I ∧ toMatrix Y1 1 1 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [toMatrix_apply, if_neg (by decide : ¬ ((0 : Bits 1) = 0 + Y1.x))]
  · rw [toMatrix_apply, if_pos (by decide : (0 : Bits 1) = 1 + Y1.x)]
    simp [Y1, iPow_one, negOnePow, show (1 : ZMod 2).val = 1 from rfl]
  · rw [toMatrix_apply, if_pos (by decide : (1 : Bits 1) = 0 + Y1.x)]
    simp [Y1, iPow_one, negOnePow, show (1 : ZMod 2).val = 1 from rfl]
  · rw [toMatrix_apply, if_neg (by decide : ¬ ((1 : Bits 1) = 1 + Y1.x))]
end PauliString
end Lean4LPD


