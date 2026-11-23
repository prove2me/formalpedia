-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumPosOfTensorPos
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumPosOfTensorPos
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:21.788017+00:00
-- url     : https://prove2.me/theorems/0534e6a0-fbc7-47b6-a0fb-3f2678d9d57e
-- title:
--   Sum Pos Of Tensor Pos
-- statement:
--   Definitions and structural lemmas for Sum Pos Of Tensor Pos, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumPosOfTensorPos.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PointStepCompare
open NumberField Matrix
open scoped MatrixOrder
section Evaluations
variable {Y : Type} [AddCommGroup Y] {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ Y)
def evalOn (B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) : (ι × ι → ℤ) →ₗ[ℤ] ℝ where
  toFun n := ∑ p, (n p : ℝ) * B (b p.1) (b p.2)
  map_add' n n' := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' k n := by simp [Finset.mul_sum, mul_assoc]
def tensorCoord : Y →ₗ[ℤ] Y →ₗ[ℤ] (ι × ι → ℤ) :=
  LinearMap.mk₂ ℤ (fun x y p => b.repr x p.1 * b.repr y p.2)
    (fun _ _ _ => by funext p; simp [add_mul]) (fun _ _ _ => by funext p; simp [mul_assoc])
    (fun _ _ _ => by funext p; simp [mul_add]) (fun _ _ _ => by funext p; simp [mul_left_comm])
end Evaluations
end GlobalTheory.PointStepCompare


