-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMulApplyLeOne
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMulApplyLeOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:37.2398+00:00
-- url     : https://prove2.me/theorems/565d7efc-a599-448e-9d05-77f64326e34d
-- title:
--   Norm Mul Apply Le One
-- statement:
--   Definitions and structural lemmas for Norm Mul Apply Le One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormMulApplyLeOne.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix
noncomputable section
namespace GlobalTheory.JR.GLift
theorem norm_mul_apply_le_one {F : Type} [NormedField F] [IsUltrametricDist F] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) F) (hA : ∀ i j, ‖A i j‖ ≤ 1) (hB : ∀ i j, ‖B i j‖ ≤ 1) (i j : Fin n) :
    ‖(A * B) i j‖ ≤ 1 := by
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hA i k) (norm_nonneg _) (hB k j)
theorem norm_one_apply_le_one {F : Type} [NormedField F] {n : ℕ} (i j : Fin n) :
    ‖(1 : Matrix (Fin n) (Fin n) F) i j‖ ≤ 1 := by
  rw [Matrix.one_apply]
  split_ifs <;> simp
def glOSub (n : ℕ) (F : Type) [NormedField F] [IsUltrametricDist F] : Subgroup (GL (Fin n) F) where
  carrier := glO n F
  mul_mem' {a b} ha hb := by
    intro i j
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]
      exact norm_mul_apply_le_one _ _ (fun i j => (ha i j).1) (fun i j => (hb i j).1) i j
    · rw [_root_.mul_inv_rev, Units.val_mul]
      exact norm_mul_apply_le_one _ _ (fun i j => (hb i j).2) (fun i j => (ha i j).2) i j
  one_mem' := by
    intro i j
    simp only [inv_one, Units.val_one]
    exact ⟨norm_one_apply_le_one i j, norm_one_apply_le_one i j⟩
  inv_mem' {a} ha := by
    intro i j
    rw [inv_inv]
    exact ⟨(ha i j).2, (ha i j).1⟩
end GlobalTheory.JR.GLift


