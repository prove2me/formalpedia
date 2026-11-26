-- Prove2me | solution 1 for Auto.aux_orbit_measurePreserving
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:36:31.324425+00:00
-- url     : https://prove2.me/submissions/dd895246-2f79-46fa-9a09-f25657843640

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
theorem _root_.solution {X : Type*} [MeasurableSpace X]
    {μ : Measure X} : ∀ {n : ℕ} (S : Fin n → X → X) (k : Fin n → ℕ),
      (∀ i, MeasurePreserving (S i) μ μ) →
      MeasurePreserving (aux_orbit S k) μ μ
  | 0, S, k, hS => by
      simpa using MeasurePreserving.id μ
  | n + 1, S, k, hS => by
      rw [aux_orbit_succ]
      apply MeasurePreserving.comp (μa := μ) (μb := μ) (μc := μ)
      · exact (hS 0).iterate (k 0)
      · apply solution
        intro i
        exact hS i.succ
end Auto
