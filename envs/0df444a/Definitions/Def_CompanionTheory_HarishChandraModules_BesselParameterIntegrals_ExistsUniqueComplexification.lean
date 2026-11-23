-- Prove2me | Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ExistsUniqueComplexification
-- name    : CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ExistsUniqueComplexification
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:06:15.438235+00:00
-- url     : https://prove2.me/theorems/0475240f-05f8-4afe-bdc0-355573375846
-- title:
--   Exists Unique Complexification
-- statement:
--   Definitions and structural lemmas for Exists Unique Complexification, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ExistsUniqueComplexification.lean

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ContDiffOnExpPartialHomeomorphSymm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace CompanionTheory.D.Upq
open Matrix
set_option linter.unusedSectionVars false
attribute [local instance 100] LieRing.ofAssociativeRing
variable {n : Type*} [Fintype n] [DecidableEq n]
section Generic
variable (J : Matrix n n ℂ)
def lieJ : Submodule ℝ (Matrix n n ℂ) where
  carrier := {X | Xᴴ * J + J * X = 0}
  add_mem' {X Y} hX hY := by
    simp only [Set.mem_ofPred_eq, conjTranspose_add, Matrix.add_mul, Matrix.mul_add] at hX hY ⊢
    calc Xᴴ * J + Yᴴ * J + (J * X + J * Y) = (Xᴴ * J + J * X) + (Yᴴ * J + J * Y) := by abel
      _ = 0 := by rw [hX, hY, add_zero]
  zero_mem' := by simp
  smul_mem' r X hX := by
    simp only [Set.mem_ofPred_eq, conjTranspose_smul, star_trivial, Matrix.smul_mul,
      Matrix.mul_smul] at hX ⊢
    rw [← smul_add, hX, smul_zero]
variable {J}
theorem conjTranspose_mul_eq_of_mem {X : Matrix n n ℂ} (hX : X ∈ lieJ J) : Xᴴ * J = -(J * X) :=
  eq_neg_of_add_eq_zero_left hX
theorem commutator_mem_lieJ {X Y : Matrix n n ℂ} (hX : X ∈ lieJ J) (hY : Y ∈ lieJ J) :
    X * Y - Y * X ∈ lieJ J := by
  have hX' := conjTranspose_mul_eq_of_mem hX
  have hY' := conjTranspose_mul_eq_of_mem hY
  show (X * Y - Y * X)ᴴ * J + J * (X * Y - Y * X) = 0
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, Matrix.sub_mul,
    Matrix.mul_assoc Yᴴ Xᴴ J, hX', Matrix.mul_assoc Xᴴ Yᴴ J, hY', Matrix.mul_neg, Matrix.mul_neg,
    ← Matrix.mul_assoc Yᴴ J X, hY', ← Matrix.mul_assoc Xᴴ J Y, hX']
  simp only [Matrix.neg_mul, neg_neg, Matrix.mul_sub, Matrix.mul_assoc]
  abel
variable (J) in

def lieSubJ : LieSubalgebra ℝ (Matrix n n ℂ) :=
  { lieJ J with
    lie_mem' := fun {X Y} hX hY => by
      rw [Ring.lie_def]
      exact commutator_mem_lieJ hX hY }
@[simp] theorem mem_lieSubJ {X : Matrix n n ℂ} : X ∈ lieSubJ J ↔ X ∈ lieJ J := Iff.rfl
end Generic
section Involutive
variable {J : Matrix n n ℂ} (hJ : J * J = 1) (hJh : Jᴴ = J)
include hJ
end Involutive
section Cartan
variable (J : Matrix n n ℂ)
def kJ : Submodule ℝ (Matrix n n ℂ) where
  carrier := {X | X ∈ lieJ J ∧ X * J = J * X}
  add_mem' {X Y} hX hY := ⟨add_mem hX.1 hY.1, by rw [Matrix.add_mul, Matrix.mul_add, hX.2, hY.2]⟩
  zero_mem' := ⟨zero_mem _, by simp⟩
  smul_mem' c X hX := ⟨Submodule.smul_mem _ c hX.1, by
    rw [Matrix.smul_mul, Matrix.mul_smul, hX.2]⟩
def pJ : Submodule ℝ (Matrix n n ℂ) where
  carrier := {X | X ∈ lieJ J ∧ X * J = -(J * X)}
  add_mem' {X Y} hX hY := ⟨add_mem hX.1 hY.1, by
    rw [Matrix.add_mul, Matrix.mul_add, hX.2, hY.2, neg_add]⟩
  zero_mem' := ⟨zero_mem _, by simp⟩
  smul_mem' c X hX := ⟨Submodule.smul_mem _ c hX.1, by
    rw [Matrix.smul_mul, Matrix.mul_smul, hX.2, smul_neg]⟩
variable {J} (hJ : J * J = 1) (hJh : Jᴴ = J)
include hJ
end Cartan
section Complexification
variable (J : Matrix n n ℂ)
def thetaG (M : Matrix n n ℂ) : Matrix n n ℂ := -(J * Mᴴ * J)
noncomputable def reG (M : Matrix n n ℂ) : Matrix n n ℂ := (1 / 2 : ℂ) • (M + thetaG J M)
noncomputable def imG (M : Matrix n n ℂ) : Matrix n n ℂ := (-(Complex.I / 2)) • (M - thetaG J M)
variable {J}
variable (hJ : J * J = 1) (hJh : Jᴴ = J)
include hJ hJh
end Complexification
end CompanionTheory.D.Upq


