-- Prove2me | solution 1 for Auto.aux_orbit_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:54:33.890125+00:00
-- url     : https://prove2.me/submissions/b37ea8f8-bce0-4160-8f77-cc6fcda4547f

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_orbit_zero_vector
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
theorem _root_.solution {X : Type*} : ∀ {n : ℕ}
    (S : Fin n → X → X) (i : Fin n) (r : ℕ),
    aux_orbit S (Pi.single i r) = (S i)^[r]
  | 0, S, i, r => Fin.elim0 i
  | n + 1, S, i, r => by
      refine Fin.cases ?_ ?_ i
      · rw [aux_orbit_succ]
        have htail : (fun j : Fin n ↦
            Pi.single (M := fun _ : Fin (n + 1) ↦ ℕ) (0 : Fin (n + 1)) r j.succ) = 0 := by
          ext j
          simp
        rw [htail, aux_orbit_zero_vector]
        simp
      · intro i
        rw [aux_orbit_succ]
        have htail : (fun j : Fin n ↦
            Pi.single (M := fun _ : Fin (n + 1) ↦ ℕ) i.succ r j.succ) =
            Pi.single (M := fun _ : Fin n ↦ ℕ) i r := by
          ext j
          rw [Pi.single_apply, Pi.single_apply]
          by_cases hji : j = i
          · subst j
            simp
          · have hsucc : j.succ ≠ i.succ := by
              intro h
              exact hji (Fin.succ_injective n h)
            simp [hji, hsucc]
        rw [htail, solution]
        have hne : (0 : Fin (n + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
        rw [Pi.single_apply, if_neg hne]
        simp
end Auto
