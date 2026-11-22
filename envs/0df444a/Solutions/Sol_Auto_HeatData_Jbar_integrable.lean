-- Prove2me | solution 1 for Auto.HeatData.Jbar_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:36:14.347361+00:00
-- url     : https://prove2.me/submissions/7119955f-51ad-4940-bf81-2c8a7537a246

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_good_integrable
public import Theorems.Thm_Auto_HeatData_family_good

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open Auto.HeatData
variable (Hd : HeatData ι) {kk : ι → ℤ}
namespace Auto.HeatData
theorem _root_.solution (hh : 0 < Hd.h) {η : ℝ} (hη : 0 < η) {α : Fin 3 → ℝ} (hα1 : ∀ k, 1 ≤ α k)
    (hα2 : ∀ k, α k ≤ 2) {s : ℝ} (hs : 0 < s) :
    Integrable (fun p => Gm (1 / 10) 0 s p * ∑ v, Hd.qE α η v s p) := by
  have e : (fun p => Gm (1 / 10) 0 s p * ∑ v, Hd.qE α η v s p) =
      fun p => ∑ v, Gm (1 / 10) 0 s p * Hd.qE α η v s p := by
    funext p; rw [Finset.mul_sum]
  rw [e]
  refine integrable_finsetSum _ fun v _ => ?_
  have G := Hd.family_good α η v hh hη hα1 hα2 hs (le_refl s)
  exact (good_integrable (Q := fun z => Hd.qE α η v z.1 z.2) hs (by positivity : (0 : ℝ) < 2 * s)
      (by norm_num : (0 : ℝ) < 1 / 10) v (G _ (by simp)).1 (G _ (by simp)).2 0).1 s
    ⟨le_rfl, le_rfl⟩
end Auto.HeatData
