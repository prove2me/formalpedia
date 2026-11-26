-- Prove2me | solution 1 for Auto.aux_overlapContribution_eq_indicator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:40:21.115632+00:00
-- url     : https://prove2.me/submissions/c4bd0f2c-e9c8-487c-b35b-c65a981eab53

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_mem_commonOverlapSet_iff
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
theorem _root_.solution {n : ℕ} (hn : 0 < n)
    (ε δ : ℝ) (a : Fin n → aux_ZVector n → ℝ) (k : aux_ZVector n)
    (u : aux_RVector n) (q : ℕ) (s : ℝ) :
    aux_overlapContribution ε δ a k u q s =
      (Ico (aux_overlapLower hn ε u q) (aux_overlapUpper hn ε δ u q)).indicator
        (fun _ ↦ ∏ i, a i (aux_translateAxisInt k i (q : ℤ))) s := by
  classical
  by_cases h : aux_commonOverlap ε δ u q s
  · rw [aux_overlapContribution]
    simp only [h, if_true]
    rw [Set.indicator_of_mem]
    exact (aux_mem_commonOverlapSet_iff hn u q).mp h
  · rw [aux_overlapContribution]
    simp only [h, if_false]
    rw [Set.indicator_of_notMem]
    intro hmem
    exact h ((aux_mem_commonOverlapSet_iff hn u q).mpr hmem)
end Auto
