-- Prove2me | solution 1 for Auto.HeatData.integral_Vbar_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:37:14.991882+00:00
-- url     : https://prove2.me/submissions/328e2a3b-4bd3-4439-a731-6bafa85e8631

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_good_integrable
public import Theorems.Thm_Auto_HeatData_family_good
public import Theorems.Thm_Auto_HeatData_costDensity_integrable

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
theorem _root_.solution (hh : 0 < Hd.h) {η : ℝ} (hη : 0 < η) {α : Fin 3 → ℝ} (hα1 : ∀ k, 1 ≤ α k)
    (hα2 : ∀ k, α k ≤ 2) {ta tb : ℝ} (hta : 0 < ta) (hab : ta ≤ tb) :
    ∫ s in ta..tb, ∑ v, Hd.Vbar α η v s = ∫ z, Hd.costDensity α η z ∂((volume.restrict (Set.Ioc
      ta tb)).prod volume) := by
  rw [intervalIntegral.integral_of_le hab,
    integral_prod _ (Hd.costDensity_integrable hh hη hα1 hα2 hta hab)]
  refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
  have hs0 : 0 < s := hta.trans hs.1
  simp only [costDensity, Vbar]
  rw [← integral_finsetSum]
  · congr 1; funext p; rw [Finset.mul_sum]
  · intro v _
    have G := Hd.family_good α η v hh hη hα1 hα2 hta hab
    exact (good_integrable (Q := fun z => Hd.qV α η v z.1 z.2) hta
      (by linarith : (0 : ℝ) < 2 * tb) (by norm_num : (0 : ℝ) < 1 / 10) v (G _ (by simp)).1
      (G _ (by simp)).2 0).1 s ⟨hs.1.le, hs.2⟩
end Auto.HeatData
