-- Prove2me | Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerError
-- name    : LeanPool_LowWeightPauliDynamics_Pauli_LayerError
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T08:01:28.875975+00:00
-- url     : https://prove2.me/theorems/9bf66b06-388b-4a53-aa6c-c707deaa2d0c
-- title:
--   Layer Error
-- statement:
--   Definitions and structural lemmas for Layer Error, from Jue Xu; LeanPool contributors's pinned Low-weight Pauli dynamics and truncation error development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerLadder
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TruncationError
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_AssemblyBound
public import Theorems.Thm_Lean4LPD_PauliString_blockEnd_apply
public import Theorems.Thm_Lean4LPD_PauliString_cls_fst
public import Theorems.Thm_Lean4LPD_PauliString_cls_herm
public import Theorems.Thm_Lean4LPD_PauliString_cls_snd
public import Theorems.Thm_Lean4LPD_PauliString_coeffVec_apply
public import Theorems.Thm_Lean4LPD_PauliString_cover_nil
public import Theorems.Thm_Lean4LPD_PauliString_herm_x
public import Theorems.Thm_Lean4LPD_PauliString_herm_z
public import Theorems.Thm_Lean4LPD_PauliString_jumpAct_apply
public import Theorems.Thm_Lean4LPD_PauliString_jumpAct_zero
public import Theorems.Thm_Lean4LPD_PauliString_mem_antiLayer
public import Theorems.Thm_Lean4LPD_PauliString_mem_antiSites
public import Theorems.Thm_Lean4LPD_PauliString_mem_highSet
public import Theorems.Thm_Lean4LPD_PauliString_mem_support
public import Theorems.Thm_Lean4LPD_PauliString_oneLayer_cons
public import Theorems.Thm_Lean4LPD_PauliString_oneLayer_nil
public import Theorems.Thm_Lean4LPD_PauliString_pauliNorm_sq
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_eq_phaseMul_iff
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_eq_self_iff
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_phase
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_x
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_z
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_zero
public import Theorems.Thm_Lean4LPD_PauliString_reachable_cons
public import Theorems.Thm_Lean4LPD_PauliString_reachable_nil
public import Theorems.Thm_Lean4LPD_PauliString_restr_apply
public import Theorems.Thm_Lean4LPD_PauliString_restr_univ
public import Theorems.Thm_Lean4LPD_PauliString_self_mem_branch
public import Theorems.Thm_Lean4LPD_PauliString_site_mul
public import Theorems.Thm_Lean4LPD_PauliString_site_one
public import Theorems.Thm_Lean4LPD_PauliString_site_phaseMul
public import Theorems.Thm_Lean4LPD_PauliString_stayAct_apply
public import Theorems.Thm_Lean4LPD_PauliString_stayAct_zero
public import Theorems.Thm_Lean4LPD_PauliString_support_phaseMul
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_mul_self_right
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_phaseMul_left
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_phaseMul_right
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_self
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_one
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_phaseMul
public import Theorems.Thm_Lean4LPD_PauliString_trotterStepTraj_zero
public import Theorems.Thm_Lean4LPD_PauliString_trotterTraj_zero
public import Theorems.Thm_Lean4LPD_PauliString_weight_one
public import Theorems.Thm_Lean4LPD_PauliString_weight_phaseMul
public import Theorems.Thm_Lean4LPD_PauliString_wt_cls
public import Theorems.Thm_Lean4LPD_chainWeight_zero
public import Theorems.Thm_Lean4LPD_conj_negOnePow
public import Theorems.Thm_Lean4LPD_iPow_signPhase
public import Theorems.Thm_Lean4LPD_iPow_two
public import Theorems.Thm_Lean4LPD_negOnePow_mul_self
public import Theorems.Thm_Lean4LPD_negOnePow_one
public import Theorems.Thm_Lean4LPD_negOnePow_zero
public import Theorems.Thm_Lean4LPD_norm_iPow
public import Theorems.Thm_Lean4LPD_rungWeight_one
public import Theorems.Thm_Lean4LPD_star_negOnePow
attribute [local simp] Lean4LPD.PauliString.blockEnd_apply
attribute [local simp] Lean4LPD.PauliString.cls_fst
attribute [local simp] Lean4LPD.PauliString.cls_herm
attribute [local simp] Lean4LPD.PauliString.cls_snd
attribute [local simp] Lean4LPD.PauliString.coeffVec_apply
attribute [local simp] Lean4LPD.PauliString.cover_nil
attribute [local simp] Lean4LPD.PauliString.herm_x
attribute [local simp] Lean4LPD.PauliString.herm_z
attribute [local simp] Lean4LPD.PauliString.jumpAct_apply
attribute [local simp] Lean4LPD.PauliString.jumpAct_zero
attribute [local simp] Lean4LPD.PauliString.mem_antiLayer
attribute [local simp] Lean4LPD.PauliString.mem_antiSites
attribute [local simp] Lean4LPD.PauliString.mem_highSet
attribute [local simp] Lean4LPD.PauliString.mem_support
attribute [local simp] Lean4LPD.PauliString.oneLayer_cons
attribute [local simp] Lean4LPD.PauliString.oneLayer_nil
attribute [local simp] Lean4LPD.PauliString.pauliNorm_sq
attribute [local simp] Lean4LPD.PauliString.phaseMul_eq_phaseMul_iff
attribute [local simp] Lean4LPD.PauliString.phaseMul_eq_self_iff
attribute [local simp] Lean4LPD.PauliString.phaseMul_phase
attribute [local simp] Lean4LPD.PauliString.phaseMul_x
attribute [local simp] Lean4LPD.PauliString.phaseMul_z
attribute [local simp] Lean4LPD.PauliString.phaseMul_zero
attribute [local simp] Lean4LPD.PauliString.reachable_cons
attribute [local simp] Lean4LPD.PauliString.reachable_nil
attribute [local simp] Lean4LPD.PauliString.restr_apply
attribute [local simp] Lean4LPD.PauliString.restr_univ
attribute [local simp] Lean4LPD.PauliString.self_mem_branch
attribute [local simp] Lean4LPD.PauliString.site_mul
attribute [local simp] Lean4LPD.PauliString.site_one
attribute [local simp] Lean4LPD.PauliString.site_phaseMul
attribute [local simp] Lean4LPD.PauliString.stayAct_apply
attribute [local simp] Lean4LPD.PauliString.stayAct_zero
attribute [local simp] Lean4LPD.PauliString.support_phaseMul
attribute [local simp] Lean4LPD.PauliString.sympForm_mul_self_right
attribute [local simp] Lean4LPD.PauliString.sympForm_phaseMul_left
attribute [local simp] Lean4LPD.PauliString.sympForm_phaseMul_right
attribute [local simp] Lean4LPD.PauliString.sympForm_self
attribute [local simp] Lean4LPD.PauliString.toMatrix_one
attribute [local simp] Lean4LPD.PauliString.toMatrix_phaseMul
attribute [local simp] Lean4LPD.PauliString.trotterStepTraj_zero
attribute [local simp] Lean4LPD.PauliString.trotterTraj_zero
attribute [local simp] Lean4LPD.PauliString.weight_one
attribute [local simp] Lean4LPD.PauliString.weight_phaseMul
attribute [local simp] Lean4LPD.PauliString.wt_cls
attribute [local simp] Lean4LPD.chainWeight_zero
attribute [local simp] Lean4LPD.conj_negOnePow
attribute [local simp] Lean4LPD.iPow_signPhase
attribute [local simp] Lean4LPD.iPow_two
attribute [local simp] Lean4LPD.negOnePow_mul_self
attribute [local simp] Lean4LPD.negOnePow_one
attribute [local simp] Lean4LPD.negOnePow_zero
attribute [local simp] Lean4LPD.norm_iPow
attribute [local simp] Lean4LPD.rungWeight_one
attribute [local simp] Lean4LPD.star_negOnePow


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Lean4LPD
end Lean4LPD
namespace Lean4LPD.PauliString
open Finset
variable {n : ℕ}
noncomputable def layerBlockTraj (layers : ℕ → List (PauliString n × ℝ))
    (O : Matrix (Bits n) (Bits n) ℂ) : ℕ → Matrix (Bits n) (Bits n) ℂ
  | 0 => O
  | i + 1 => layerConj (layers i) (layerBlockTraj layers O i)
@[simp] theorem layerBlockTraj_zero (layers : ℕ → List (PauliString n × ℝ))
    (O : Matrix (Bits n) (Bits n) ℂ) : layerBlockTraj layers O 0 = O := rfl
theorem layerBlockTraj_succ (layers : ℕ → List (PauliString n × ℝ))
    (O : Matrix (Bits n) (Bits n) ℂ) (i : ℕ) :
    layerBlockTraj layers O (i + 1) = layerConj (layers i) (layerBlockTraj layers O i) := rfl
noncomputable def layerStepTraj (layers : ℕ → List (PauliString n × ℝ))
    (Γ wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) : ℕ → Matrix (Bits n) (Bits n) ℂ
  | 0 => O
  | d + 1 => truncOp (highSet n wstar)ᶜ
      (layerBlockTraj layers (layerStepTraj layers Γ wstar O d) Γ)
@[simp] theorem layerStepTraj_zero (layers : ℕ → List (PauliString n × ℝ))
    (Γ wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) : layerStepTraj layers Γ wstar O 0 = O := rfl
noncomputable def layerScheduledTraj (layers : ℕ → List (PauliString n × ℝ))
    (Γ wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) : ℕ → Matrix (Bits n) (Bits n) ℂ :=
  layerTraj (fun T => layers (T % Γ)) (trotterSchedule Γ wstar) O
@[simp] theorem layerScheduledTraj_zero (layers : ℕ → List (PauliString n × ℝ))
    (Γ wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) :
    layerScheduledTraj layers Γ wstar O 0 = O := rfl
noncomputable def discardedLayerStep (layers : ℕ → List (PauliString n × ℝ))
    (Γ wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d : ℕ) : Matrix (Bits n) (Bits n) ℂ :=
  layerBlockTraj layers (layerStepTraj layers Γ wstar O d) Γ -
    layerStepTraj layers Γ wstar O (d + 1)
noncomputable def layerStepMass (layers : ℕ → List (PauliString n × ℝ))
    (Γ wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d i : ℕ) : ℝ :=
  highNorm wstar (layerBlockTraj layers (layerStepTraj layers Γ wstar O d) i)
theorem layerConj_add (L : List (PauliString n × ℝ)) (A B : Matrix (Bits n) (Bits n) ℂ) :
    layerConj L (A + B) = layerConj L A + layerConj L B := by
  induction L with
  | nil => rfl
  | cons g L ih =>
    rcases g with ⟨G, θ⟩
    simp only [layerConj, ih, Matrix.mul_add, Matrix.add_mul]
@[simp] theorem layerConj_zero (L : List (PauliString n × ℝ)) :
    layerConj L (0 : Matrix (Bits n) (Bits n) ℂ) = 0 := by
  induction L with
  | nil => rfl
  | cons g L ih => simp only [layerConj, ih, Matrix.mul_zero, Matrix.zero_mul]
theorem layerBlockTraj_add (layers : ℕ → List (PauliString n × ℝ))
    (A B : Matrix (Bits n) (Bits n) ℂ) (i : ℕ) :
    layerBlockTraj layers (A + B) i = layerBlockTraj layers A i + layerBlockTraj layers B i := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [layerBlockTraj_succ, ih, layerConj_add, layerBlockTraj_succ, layerBlockTraj_succ]
@[simp] theorem layerBlockTraj_zero_input (layers : ℕ → List (PauliString n × ℝ)) (i : ℕ) :
    layerBlockTraj layers (0 : Matrix (Bits n) (Bits n) ℂ) i = 0 := by
  induction i with
  | zero => rfl
  | succ i ih => rw [layerBlockTraj_succ, ih, layerConj_zero]
noncomputable def layerBlockEnd (layers : ℕ → List (PauliString n × ℝ)) (Γ : ℕ) :
    AddMonoid.End (Matrix (Bits n) (Bits n) ℂ) where
  toFun A := layerBlockTraj layers A Γ
  map_zero' := layerBlockTraj_zero_input layers Γ
  map_add' A B := layerBlockTraj_add layers A B Γ
end Lean4LPD.PauliString


