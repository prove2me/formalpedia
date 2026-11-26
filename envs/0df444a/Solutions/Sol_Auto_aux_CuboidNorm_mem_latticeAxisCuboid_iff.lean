-- Prove2me | solution 1 for Auto.aux_CuboidNorm.mem_latticeAxisCuboid_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:47:24.746802+00:00
-- url     : https://prove2.me/submissions/27a14808-85b6-4436-90b9-1cf38d252c7b

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_floor_intCast_add_of_mem_Ico
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
theorem _root_.solution {n : ℕ} {ε δ : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε < 1) (hεδ : ε + δ < 1)
    (i : Fin n) (k : ZVector n) (y : RVector n) :
    y ∈ latticeAxisCuboid ε δ i k ↔
      (∀ j,
        if j = i then
          ε ≤ y j - (⌊y j⌋ : ℝ) ∧ y j - (⌊y j⌋ : ℝ) < ε + δ
        else
          0 ≤ y j - (⌊y j⌋ : ℝ) ∧ y j - (⌊y j⌋ : ℝ) < ε) ∧
        (fun j ↦ ⌊y j⌋) = k := by
  constructor
  · intro hy
    have hfloor : ∀ j, ⌊y j⌋ = k j := by
      intro j
      have hyj : y j ∈ Ico ((k j : ℝ) + if j = i then ε else 0)
          ((k j : ℝ) + if j = i then ε + δ else ε) := by
        simpa [latticeAxisCuboid, axisCuboid, cuboid, axisLower, axisUpper]
          using hy j (by simp)
      rcases hyj with ⟨hlow, hupp⟩
      by_cases hji : j = i
      · subst j
        simp only [eq_self, if_true] at hlow hupp
        have hyrewrite : y i = (k i : ℝ) + (y i - (k i : ℝ)) := by ring
        rw [hyrewrite]
        exact aux_floor_intCast_add_of_mem_Ico (k i) (by linarith) (by linarith)
      · simp only [if_neg hji] at hlow hupp
        have hyrewrite : y j = (k j : ℝ) + (y j - (k j : ℝ)) := by ring
        rw [hyrewrite]
        exact aux_floor_intCast_add_of_mem_Ico (k j) (by linarith) (by linarith)
    refine ⟨?_, funext hfloor⟩
    intro j
    have hyj : y j ∈ Ico ((k j : ℝ) + if j = i then ε else 0)
        ((k j : ℝ) + if j = i then ε + δ else ε) := by
      simpa [latticeAxisCuboid, axisCuboid, cuboid, axisLower, axisUpper]
        using hy j (by simp)
    rcases hyj with ⟨hlow, hupp⟩
    by_cases hji : j = i
    · subst j
      simp only [eq_self, if_true] at hlow hupp
      simp only [eq_self, if_true]
      rw [hfloor i]
      constructor <;> linarith
    · simp only [if_neg hji] at hlow hupp ⊢
      rw [hfloor j]
      constructor <;> linarith
  · rintro ⟨hcond, hfloor⟩
    intro j _
    specialize hcond j
    by_cases hji : j = i
    · subst j
      simp only [axisLower, axisUpper, Set.mem_Ico, eq_self, if_true]
      rw [← congrFun hfloor i]
      simp only [eq_self, if_true] at hcond
      constructor <;> linarith
    · simp only [axisLower, axisUpper, Set.mem_Ico, if_neg hji]
      rw [← congrFun hfloor j]
      simp only [if_neg hji] at hcond
      constructor <;> linarith
end Auto.aux_CuboidNorm
