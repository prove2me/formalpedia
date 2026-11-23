-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_LaplaceFoundations_OneParameterSubgroups_ExpChart
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_LaplaceFoundations_OneParameterSubgroups_ExpChart
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:34:43.822374+00:00
-- url     : https://prove2.me/theorems/6ad610e7-42df-4021-9089-bb58e9ca2161
-- title:
--   Exp Chart
-- statement:
--   Definitions and structural lemmas for Exp Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/LaplaceFoundations/OneParameterSubgroups/ExpChart.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Finset
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
section Abstract
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
end Abstract
section Fil
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
structure IsFil (F : ℕ → Submodule ℝ A) (L : ℕ) : Prop where
  anti : ∀ i j, i ≤ j → F j ≤ F i
  mul : ∀ i j x y, x ∈ F i → y ∈ F j → x * y ∈ F (i + j + 1)
  bot : F L = ⊥
def IsShear (F : ℕ → Submodule ℝ A) (f : A → A) : Prop :=
  (∀ x ∈ F 0, f x ∈ F 0) ∧
    ∀ j, ∀ x ∈ F 0, ∀ y ∈ F 0, x - y ∈ F j → f x - f y - (x - y) ∈ F (j + 1)
def iter (f : A → A) : ℕ → A → A
  | 0, _ => 0
  | i + 1, z => iter f i z + (z - f (iter f i z))
variable {F : ℕ → Submodule ℝ A} {L : ℕ} {f g : A → A}
section Group
variable [FiniteDimensional ℝ A]
structure IsAdj (F : ℕ → Submodule ℝ A) (st : A →ₗ[ℝ] A) : Prop where
  mul : ∀ x y, st (x * y) = st y * st x
  one : st 1 = 1
  mem : ∀ x ∈ F 0, st x ∈ F 0
noncomputable def lieN (F : ℕ → Submodule ℝ A) (st : A →ₗ[ℝ] A) : Submodule ℝ A :=
  F 0 ⊓ LinearMap.ker (st + LinearMap.id)
def grpN (F : ℕ → Submodule ℝ A) (st : A →ₗ[ℝ] A) : Set A := {g | g - 1 ∈ F 0 ∧ st g * g = 1}
variable {st : A →ₗ[ℝ] A}
noncomputable def lg (L : ℕ) (g : A) : A := iter (fun x => NormedSpace.exp x - 1) L (g - 1)
end Group
section Haar
variable [FiniteDimensional ℝ A] {st : A →ₗ[ℝ] A} [MeasurableSpace A] [BorelSpace A]
end Haar
end Fil
section Matrices
open Matrix
open scoped Matrix.Norms.Operator
variable {n : ℕ}
def levF (lev : Fin n → ℕ) (j : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {X | ∀ a b, lev b < lev a + j + 1 → X a b = 0}
  add_mem' := fun hX hY a b h => by simp [hX a b h, hY a b h]
  zero_mem' := fun _ _ _ => rfl
  smul_mem' := fun c X hX a b h => by simp [hX a b h]
noncomputable def adjH (H : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun X := H * Xᴴ * H
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp
end Matrices
end ReciprocityTheory.ChartRestriction.DS.Lap.Base.N


