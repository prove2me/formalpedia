-- Prove2me | Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Trace
-- name    : LeanPool_LowWeightPauliDynamics_Pauli_Trace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:14:05.835809+00:00
-- url     : https://prove2.me/theorems/1c16c301-27ef-460c-a653-187ecd1006e8
-- title:
--   Trace
-- statement:
--   Definitions and structural lemmas for Trace, from Jue Xu; LeanPool contributors's pinned Low-weight Pauli dynamics and truncation error development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Trace.lean

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
public import Mathlib.LinearAlgebra.Matrix.Trace
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
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_one
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_phaseMul
public import Theorems.Thm_Lean4LPD_conj_negOnePow
public import Theorems.Thm_Lean4LPD_iPow_signPhase
public import Theorems.Thm_Lean4LPD_iPow_two
public import Theorems.Thm_Lean4LPD_negOnePow_add
public import Theorems.Thm_Lean4LPD_negOnePow_mul_self
public import Theorems.Thm_Lean4LPD_negOnePow_one
public import Theorems.Thm_Lean4LPD_negOnePow_zero
public import Theorems.Thm_Lean4LPD_star_negOnePow
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
attribute [local simp] Lean4LPD.PauliString.toMatrix_one
attribute [local simp] Lean4LPD.PauliString.toMatrix_phaseMul
attribute [local simp] Lean4LPD.conj_negOnePow
attribute [local simp] Lean4LPD.iPow_signPhase
attribute [local simp] Lean4LPD.iPow_two
attribute [local simp] Lean4LPD.negOnePow_mul_self
attribute [local simp] Lean4LPD.negOnePow_one
attribute [local simp] Lean4LPD.negOnePow_zero
attribute [local simp] Lean4LPD.star_negOnePow


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Lean4LPD
namespace PauliString
variable {n : ℕ} {s t u : PauliString n}
lemma sum_zmod_two (f : ZMod 2 → ℂ) : ∑ c : ZMod 2, f c = f 0 + f 1 := by
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton]
lemma zmod_two_cases' (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide
lemma negOnePow_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    negOnePow (∑ i ∈ s, f i) = ∏ i ∈ s, negOnePow (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, negOnePow_add, ih]
lemma negOnePow_dotProduct (u b : Bits n) :
    negOnePow (u ⬝ᵥ b) = ∏ i, negOnePow (u i * b i) := by
  simp only [dotProduct]
  exact negOnePow_sum _ _
lemma sum_negOnePow_mul (a : ZMod 2) :
    (∑ c : ZMod 2, negOnePow (a * c)) = if a = 0 then (2 : ℂ) else 0 := by
  rw [sum_zmod_two]
  rcases zmod_two_cases' a with ha | ha <;> rw [ha] <;> norm_num
theorem char_sum (n : ℕ) (u : Bits n) :
    (∑ b : Bits n, negOnePow (u ⬝ᵥ b)) = if u = 0 then (2 : ℂ) ^ n else 0 := by
  rw [Finset.sum_congr rfl fun b _ => negOnePow_dotProduct u b,
    ← Fintype.prod_sum fun (i : Fin n) (c : ZMod 2) => negOnePow (u i * c),
    Finset.prod_congr rfl fun i _ => sum_negOnePow_mul (u i)]
  by_cases hu : u = 0
  · subst hu; simp
  · rw [if_neg hu]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hu
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
example : (∑ b : Bits 2, negOnePow ((0 : Bits 2) ⬝ᵥ b)) = 4 := by
  rw [char_sum, if_pos (rfl : (0 : Bits 2) = 0)]; norm_num
example : (∑ b : Bits 1, negOnePow ((1 : Bits 1) ⬝ᵥ b)) = 0 := by
  rw [char_sum, if_neg (by decide : ¬ ((1 : Bits 1) = 0))]
end PauliString
end Lean4LPD


