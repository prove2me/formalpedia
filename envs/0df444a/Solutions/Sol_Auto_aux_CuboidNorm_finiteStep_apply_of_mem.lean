-- Prove2me | solution 1 for Auto.aux_CuboidNorm.finiteStep_apply_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:37:15.184843+00:00
-- url     : https://prove2.me/submissions/0e41cd6a-7f29-4a49-865c-01292332b9f3

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
open Auto.aux_CuboidNorm
variable {α κ : Type*} [MeasurableSpace α] [DecidableEq κ]
omit [MeasurableSpace α] [DecidableEq κ]
namespace Auto.aux_CuboidNorm
theorem _root_.solution (A : Finset κ) (s : κ → Set α)
    (a : κ → ℝ)
    (hdisj : ∀ ⦃k⦄, k ∈ A → ∀ ⦃l⦄, l ∈ A → k ≠ l → Disjoint (s k) (s l))
    {k : κ} (hk : k ∈ A) {x : α} (hx : x ∈ s k) :
    finiteStep A s a x = a k := by
  classical
  unfold finiteStep
  rw [Finset.sum_eq_single k]
  · simp [hx]
  · intro l hl hne
    have hxl : x ∉ s l := by
      intro hxl
      exact Set.disjoint_left.1 (hdisj hk hl hne.symm) hx hxl
    simp [hxl]
  · simp [hk]
end Auto.aux_CuboidNorm
