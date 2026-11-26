-- Prove2me | solution 1 for Auto.aux_integerDiscreteAverage_natToInt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:45:11.338048+00:00
-- url     : https://prove2.me/submissions/9f1a9946-f334-4e63-ad60-d0b9e85269ae

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
section
@[expose] public section
namespace Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
@[simp] private theorem aux_orbit_zero {X : Type*} (S : Fin 0 → X → X)
    (k : Fin 0 → ℕ) : aux_orbit S k = id :=
  rfl
@[simp] private theorem aux_orbit_succ {X : Type*} {n : ℕ}
    (S : Fin (n + 1) → X → X) (k : Fin (n + 1) → ℕ) :
    aux_orbit S k = (S 0)^[k 0] ∘
      aux_orbit (fun i ↦ S i.succ) (fun i ↦ k i.succ) :=
  rfl
section
universe v
end
namespace aux_CuboidNorm
variable {α κ : Type*} [MeasurableSpace α] [DecidableEq κ]
end aux_CuboidNorm
namespace aux_ErgodicBox
open MeasureTheory Set
open scoped ENNReal BigOperators
end aux_ErgodicBox
end
end Auto
end
end

set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace Auto
theorem _root_.solution {n : ℕ} (N : ℕ)
    (F : Fin n → (Fin n → ℕ) → ℝ) (k : Fin n → ℕ) :
    aux_integerDiscreteAverage N (fun i ↦ aux_natToInt (F i))
      (fun j ↦ (k j : ℤ)) = aux_discreteAverage N F k := by
  classical
  unfold aux_integerDiscreteAverage aux_discreteAverage
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.prod_congr rfl
  intro i _
  have hnonneg : ∀ j,
      0 ≤ aux_translateAxisInt (fun j ↦ (k j : ℤ)) i (m : ℤ) j := by
    intro j
    by_cases hji : j = i
    · subst j
      simp only [aux_translateAxisInt, if_true]
      positivity
    · simp [aux_translateAxisInt, hji]
  simp only [aux_natToInt, dif_pos hnonneg]
  congr 1
  funext j
  by_cases hji : j = i
  · subst j
    simp [aux_translateAxisInt, aux_coordinate]
    omega
  · simp [aux_translateAxisInt, aux_coordinate, hji]
end Auto
