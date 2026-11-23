-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_AdelicDixmierMalliavinLie
-- name    : GroundTheory_AutomorphicForms_AdelicDixmierMalliavinLie
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:53.963078+00:00
-- url     : https://prove2.me/theorems/8517b449-b15a-4ecb-99b8-f642852f8aef
-- title:
--   Adelic Dixmier Malliavin Lie
-- statement:
--   Definitions and structural lemmas for Adelic Dixmier Malliavin Lie, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicDixmierMalliavinLie.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Automorphic
open scoped Manifold ContDiff Topology
open NormedSpace Set
set_option linter.unusedSectionVars false
noncomputable section
def RegNorm (𝔅 : Type*) : Type _ := 𝔅
namespace RegNorm
variable (𝔅 : Type*) [Ring 𝔅] [Algebra ℝ 𝔅] [FiniteDimensional ℝ 𝔅]
instance : Ring (RegNorm 𝔅) := inferInstanceAs (Ring 𝔅)
instance : Algebra ℝ (RegNorm 𝔅) := inferInstanceAs (Algebra ℝ 𝔅)
instance : FiniteDimensional ℝ (RegNorm 𝔅) := inferInstanceAs (FiniteDimensional ℝ 𝔅)
def toRegNorm : 𝔅 ≃ₐ[ℝ] RegNorm 𝔅 := AlgEquiv.refl
open scoped Matrix.Norms.L2Operator
def leftReg : RegNorm 𝔅 →ₐ[ℝ] Matrix (Fin (Module.finrank ℝ 𝔅)) (Fin (Module.finrank ℝ 𝔅)) ℝ :=
  Algebra.leftMulMatrix (Module.finBasis ℝ 𝔅)
theorem leftReg_injective : Function.Injective (leftReg 𝔅) :=
  Algebra.leftMulMatrix_injective _
instance : NormedRing (RegNorm 𝔅) :=
  NormedRing.induced (RegNorm 𝔅) _ (leftReg 𝔅) (leftReg_injective 𝔅)
instance : NormedAlgebra ℝ (RegNorm 𝔅) :=
  NormedAlgebra.induced ℝ (RegNorm 𝔅) _ (leftReg 𝔅)
instance : CompleteSpace (RegNorm 𝔅) := FiniteDimensional.complete ℝ _
variable [TopologicalSpace 𝔅] [IsTopologicalAddGroup 𝔅] [ContinuousSMul ℝ 𝔅]
end RegNorm
section FormGroup
variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [FiniteDimensional ℝ 𝔄]
  (σ : 𝔄 →ₗ[ℝ] 𝔄) (hσ1 : σ 1 = 1) (hσ : ∀ x y, σ (x * y) = σ y * σ x) (J : 𝔄ˣ)
def formGroup : Subgroup 𝔄ˣ where
  carrier := {g | σ g * J * g = J}
  one_mem' := by simp [hσ1]
  mul_mem' {a b} ha hb := by
    simp only [mem_ofPred_eq, Units.val_mul, hσ] at ha hb ⊢
    calc σ b * σ a * J * (a * b) = σ b * (σ a * J * a) * b := by simp only [mul_assoc]
      _ = J := by rw [ha, hb]
  inv_mem' {a} ha := by
    simp only [mem_ofPred_eq] at ha ⊢
    have h1 : σ (a⁻¹ : 𝔄ˣ) * σ a = 1 := by rw [← hσ, Units.mul_inv, hσ1]
    calc σ (a⁻¹ : 𝔄ˣ) * J * (a⁻¹ : 𝔄ˣ) = σ (a⁻¹ : 𝔄ˣ) * (σ a * J * a) * (a⁻¹ : 𝔄ˣ) := by rw [ha]
      _ = (σ (a⁻¹ : 𝔄ˣ) * σ a) * J * (a * (a⁻¹ : 𝔄ˣ)) := by simp only [mul_assoc]
      _ = J := by rw [h1, Units.mul_inv, one_mul, mul_one]
def formLie : Submodule ℝ 𝔄 where
  carrier := {X | σ X * J + J * X = 0}
  add_mem' {X Y} hX hY := by
    simp only [mem_ofPred_eq, map_add, add_mul, mul_add] at hX hY ⊢
    calc σ X * J + σ Y * J + (J * X + J * Y) = (σ X * J + J * X) + (σ Y * J + J * Y) := by abel
      _ = 0 := by rw [hX, hY, add_zero]
  zero_mem' := by simp
  smul_mem' r X hX := by
    simp only [mem_ofPred_eq, map_smul, smul_mul_assoc, mul_smul_comm] at hX ⊢
    rw [← smul_add, hX, smul_zero]
end FormGroup
end
end GroundTheory.Automorphic


