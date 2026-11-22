-- Prove2me | solution 1 for Auto.HeatData.costDensity_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:35:23.6302+00:00
-- url     : https://prove2.me/submissions/9d8987a7-95d6-46b8-9189-619d0d478fc1

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
variable (Hd : HeatData ι)
namespace Auto.HeatData
theorem _root_.solution (hh : 0 < Hd.h) {η : ℝ} (hη : 0 < η) {α : Fin 3 → ℝ}
    (hα1 : ∀ k, 1 ≤ α k) (hα2 : ∀ k, α k ≤ 2) {ta tb : ℝ} (hta : 0 < ta) (hab : ta ≤ tb) :
    Integrable (Hd.costDensity α η) ((volume.restrict (Set.Ioc ta tb)).prod volume) := by
  have e : Hd.costDensity α η = fun z => ∑ v, Gm (1 / 10) 0 z.1 z.2 * Hd.qV α η v z.1 z.2 := by
    funext z; rw [costDensity, Finset.mul_sum]
  rw [e]
  refine integrable_finsetSum _ fun v _ => ?_
  have G := Hd.family_good α η v hh hη hα1 hα2 hta hab
  exact (good_integrable (Q := fun z => Hd.qV α η v z.1 z.2) hta (by linarith : (0 : ℝ) < 2 * tb)
    (by norm_num : (0 : ℝ) < 1 / 10) v (G _ (by simp)).1 (G _ (by simp)).2 0).2
end Auto.HeatData
