-- Prove2me | solution 1 for Auto.HeatData.pointwise_dissipation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:29:50.850565+00:00
-- url     : https://prove2.me/submissions/19caf09e-ce64-4651-a135-9d8f4b9d8a8c

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_HeatData_neighbor_cost_comparison
public import Theorems.Thm_Auto_HeatData_Z_le
public import Theorems.Thm_Auto_HeatData_sqrt_two_le

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open Auto.HeatData
variable (Hd : HeatData ι)
namespace Auto.HeatData
theorem _root_.solution (hh : 0 < Hd.h) {η : ℝ} (hη : 0 < η) (p σ : Fin 3 → ℝ)
    (hσ : ∀ k, 0 < σ k) {α : Fin 3 → ℝ} (hα : ∀ k, α k = 1 ∨ α k = 11 / 10)
    (hsum : α 0 + α 1 + α 2 = 16 / 5) :
    ∑ v, (33 / 20 * Hd.Z p σ η v - (α v * Hd.V p σ η v + α (v + 1) * Hd.Ynext p σ η v + α (v -
      1) * Hd.Yprev p σ η v) / 2) ≤ -(1 / 28) * ∑ v, Hd.V p σ η v := by
  have hN : ∀ w, Hd.Yprev p σ η (w + 1) + Hd.Ynext p σ η (w - 1) ≤ √2 * Hd.V p σ η w :=
    fun w => Hd.neighbor_cost_comparison p σ hh (hσ w) hη
  have hZ : ∀ v, Hd.Z p σ η v ≤ (Hd.Ynext p σ η v + Hd.Yprev p σ η v) / 2 :=
    fun v => Hd.Z_le p σ hη v
  have hV : ∀ v, 0 ≤ Hd.V p σ η v := fun v => ENNReal.toReal_nonneg
  have hYn : ∀ v, 0 ≤ Hd.Ynext p σ η v := fun v => ENNReal.toReal_nonneg
  have hYp : ∀ v, 0 ≤ Hd.Yprev p σ η v := fun v => ENNReal.toReal_nonneg
  have hs2 : ∀ v, √2 * Hd.V p σ η v ≤ 10 / 7 * Hd.V p σ η v := fun v =>
    mul_le_mul_of_nonneg_right sqrt_two_le (hV v)
  have e01 : (0 : Fin 3) + 1 = 1 := rfl
  have e02 : (0 : Fin 3) - 1 = 2 := rfl
  have e11 : (1 : Fin 3) + 1 = 2 := rfl
  have e12 : (1 : Fin 3) - 1 = 0 := rfl
  have e21 : (2 : Fin 3) + 1 = 0 := rfl
  have e22 : (2 : Fin 3) - 1 = 1 := rfl
  have hN0 := hN 0
  have hN1 := hN 1
  have hN2 := hN 2
  rw [e01, e02] at hN0
  rw [e11, e12] at hN1
  rw [e21, e22] at hN2
  rw [Fin.sum_univ_three, Fin.sum_univ_three, e01, e02, e11, e12, e21, e22]
  have hZ0 := hZ 0
  have hZ1 := hZ 1
  have hZ2 := hZ 2
  have := hs2 0
  have := hs2 1
  have := hs2 2
  have := hYn 0
  have := hYn 1
  have := hYn 2
  have := hYp 0
  have := hYp 1
  have := hYp 2
  have := hV 0
  have := hV 1
  have := hV 2
  rcases hα 0 with h0 | h0 <;> rcases hα 1 with h1 | h1 <;> rcases hα 2 with h2 | h2 <;>
    rw [h0, h1, h2] at hsum ⊢
  all_goals first | (norm_num at hsum; done) | linarith
end Auto.HeatData
