-- Prove2me | solution 1 for Auto.aux_CuboidNorm.latticeCuboid_pairwise_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:41:43.802434+00:00
-- url     : https://prove2.me/submissions/99c99fb3-35c5-4cf2-a755-f2d2f41a838d

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_CuboidNorm_disjoint_Ico_int_shift
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
namespace Auto.aux_CuboidNorm
theorem _root_.solution {n : ℕ} {ε : ℝ} (hε : ε ≤ 1)
    {k l : ZVector n} (hkl : k ≠ l) :
    Disjoint (latticeCuboid ε k) (latticeCuboid ε l) := by
  apply Set.disjoint_left.2
  intro x hxk hxl
  have hcoordinate : ∃ j : Fin n, k j ≠ l j := by
    by_contra h
    push Not at h
    exact hkl (funext h)
  obtain ⟨j, hj⟩ := hcoordinate
  have hxkj : x j ∈ Ico ((k j : ℝ) + 0) ((k j : ℝ) + 0 + ε) := by
    simpa [latticeCuboid, cuboid, add_assoc] using hxk j (by simp)
  have hxlj : x j ∈ Ico ((l j : ℝ) + 0) ((l j : ℝ) + 0 + ε) := by
    simpa [latticeCuboid, cuboid, add_assoc] using hxl j (by simp)
  exact Set.disjoint_left.1 (disjoint_Ico_int_shift (c := 0) (w := ε) hε hj)
    hxkj hxlj
end Auto.aux_CuboidNorm
