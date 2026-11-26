-- Prove2me | solution 1 for Auto.aux_CuboidNorm.latticeAxisCuboid_pairwise_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:41:40.833364+00:00
-- url     : https://prove2.me/submissions/7411a6ea-69c4-464a-9ccd-878456ff1bdb

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
namespace Auto.aux_CuboidNorm
theorem _root_.solution {n : ℕ}
    {ε δ : ℝ} (hε : ε ≤ 1) (hδ : δ ≤ 1) (i : Fin n)
    {k l : ZVector n} (hkl : k ≠ l) :
    Disjoint (latticeAxisCuboid ε δ i k) (latticeAxisCuboid ε δ i l) := by
  apply Set.disjoint_left.2
  intro x hxk hxl
  have hcoordinate : ∃ j : Fin n, k j ≠ l j := by
    by_contra h
    push Not at h
    exact hkl (funext h)
  obtain ⟨j, hj⟩ := hcoordinate
  have hxkj : x j ∈ Ico ((k j : ℝ) + if j = i then ε else 0)
      ((k j : ℝ) + if j = i then ε + δ else ε) := by
    simpa [latticeAxisCuboid, axisCuboid, cuboid, axisLower, axisUpper]
      using hxk j (by simp)
  have hxlj : x j ∈ Ico ((l j : ℝ) + if j = i then ε else 0)
      ((l j : ℝ) + if j = i then ε + δ else ε) := by
    simpa [latticeAxisCuboid, axisCuboid, cuboid, axisLower, axisUpper]
      using hxl j (by simp)
  by_cases hji : j = i
  · subst j
    have h := disjoint_Ico_int_shift (c := ε) (w := δ) hδ hj
    have hxkj' : x i ∈ Ico ((k i : ℝ) + ε) ((k i : ℝ) + ε + δ) := by
      simpa [add_assoc] using hxkj
    have hxlj' : x i ∈ Ico ((l i : ℝ) + ε) ((l i : ℝ) + ε + δ) := by
      simpa [add_assoc] using hxlj
    exact Set.disjoint_left.1 h hxkj' hxlj'
  · have h := disjoint_Ico_int_shift (c := 0) (w := ε) hε hj
    have hxkj' : x j ∈ Ico ((k j : ℝ) + 0) ((k j : ℝ) + 0 + ε) := by
      simpa [hji, add_assoc] using hxkj
    have hxlj' : x j ∈ Ico ((l j : ℝ) + 0) ((l j : ℝ) + 0 + ε) := by
      simpa [hji, add_assoc] using hxlj
    exact Set.disjoint_left.1 h hxkj' hxlj'
end Auto.aux_CuboidNorm
