-- Prove2me | solution 1 for Auto.aux_ErgodicBox.prod_rpow_eq_rpow_sum_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:52:44.077811+00:00
-- url     : https://prove2.me/submissions/f9c1477a-b814-47e8-b234-520a99c90ab1

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
open Auto.aux_ErgodicBox
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace Auto.aux_ErgodicBox
theorem _root_.solution
    {ι : Type*} (s : Finset ι) (B : ℝ≥0∞) (q : ι → ℝ)
    (hq : ∀ i ∈ s, 0 ≤ q i) :
    ∏ i ∈ s, B ^ q i = B ^ (∑ i ∈ s, q i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        ih (fun i hi ↦ hq i (Finset.mem_insert_of_mem hi))]
      exact (ENNReal.rpow_add_of_nonneg (q a) (∑ i ∈ s, q i)
        (hq a (Finset.mem_insert_self _ _))
        (Finset.sum_nonneg fun i hi ↦ hq i (Finset.mem_insert_of_mem hi))).symm
end Auto.aux_ErgodicBox
