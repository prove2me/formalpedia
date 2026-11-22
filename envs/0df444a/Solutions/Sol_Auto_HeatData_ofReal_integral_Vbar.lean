-- Prove2me | solution 1 for Auto.HeatData.ofReal_integral_Vbar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:38:54.338083+00:00
-- url     : https://prove2.me/submissions/21d707fb-9405-4e66-8b59-6c8ed25c864b

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_HeatData_costDensity_integrable
public import Theorems.Thm_Auto_HeatData_costDensity_nonneg
public import Theorems.Thm_Auto_HeatData_ofReal_costDensity
public import Theorems.Thm_Auto_HeatData_integral_Vbar_eq

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
    ENNReal.ofReal (∫ s in ta..tb, ∑ v, Hd.Vbar α η v s) = ∫⁻ z, ENNReal.ofReal (Gm (1 / 10) 0
      z.1 z.2) * ∑ v, matCost (Hd.T z.2 (sig α z.1) v + (η : ℂ) • 1) (Hd.Ui z.2 (sig α z.1) v)
      ∂((volume.restrict (Set.Ioc ta tb)).prod volume) := by
  rw [Hd.integral_Vbar_eq hh hη hα1 hα2 hta hab, ofReal_integral_eq_lintegral_ofReal
    (Hd.costDensity_integrable hh hη hα1 hα2 hta hab)
    (Eventually.of_forall (Hd.costDensity_nonneg α η))]
  exact lintegral_congr fun z => Hd.ofReal_costDensity hη α z
end Auto.HeatData
