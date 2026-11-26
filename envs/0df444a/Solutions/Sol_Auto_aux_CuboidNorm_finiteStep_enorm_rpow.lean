-- Prove2me | solution 1 for Auto.aux_CuboidNorm.finiteStep_enorm_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:47:41.902341+00:00
-- url     : https://prove2.me/submissions/4e2052ab-49d5-42d9-95f8-4a79ccefc0f1

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_CuboidNorm_finiteStep_apply_of_mem
public import Theorems.Thm_Auto_aux_CuboidNorm_finiteStep_apply_eq_zero
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
    (a : κ → ℝ) (q : ℝ) (hq : 0 < q)
    (hdisj : ∀ ⦃k⦄, k ∈ A → ∀ ⦃l⦄, l ∈ A → k ≠ l → Disjoint (s k) (s l))
    (x : α) :
    ‖finiteStep A s a x‖ₑ ^ q =
      ∑ k ∈ A, (s k).indicator (fun _ ↦ ‖a k‖ₑ ^ q) x := by
  classical
  by_cases hx : ∃ k ∈ A, x ∈ s k
  · obtain ⟨k, hk, hxk⟩ := hx
    have hstep := finiteStep_apply_of_mem A s a hdisj hk hxk
    rw [hstep]
    rw [Finset.sum_eq_single k]
    · simp [hxk]
    · intro l hl hne
      have hxl : x ∉ s l := by
        intro hxl
        exact Set.disjoint_left.1 (hdisj hk hl hne.symm) hxk hxl
      simp [hxl]
    · simp [hk]
  · have hzero : finiteStep A s a x = 0 :=
      finiteStep_apply_eq_zero A s a (by
        simpa only [not_exists, not_and] using hx)
    rw [hzero]
    simp only [enorm_zero, ENNReal.zero_rpow_of_pos hq]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro k hk
    have hxk : x ∉ s k := by
      intro hxk
      exact hx ⟨k, hk, hxk⟩
    simp [hxk]
end Auto.aux_CuboidNorm
