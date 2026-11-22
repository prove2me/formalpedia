-- Prove2me | solution 1 for Auto.heatCost_aemeasurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:39:21.360741+00:00
-- url     : https://prove2.me/submissions/2dd0a20f-cd69-45c5-a48e-2ede94aae2f3

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_HeatData_costDensity_integrable
public import Theorems.Thm_Auto_heatCost_tendsto

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
public section
open scoped ENNReal NNReal
open MeasureTheory Filter Topology Real
public section
open Auto
open MeasureTheory Filter Topology Matrix Real
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
namespace Auto
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Hd : HeatData ι) (hh : 0 < Hd.h) {α : Fin 3 → ℝ}
    (hα1 : ∀ v, 1 ≤ α v) (hα2 : ∀ v, α v ≤ 2)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    AEMeasurable (heatCost Hd α) ((volume.restrict (Set.Ioc a b)).prod volume) := by
  apply ENNReal.aemeasurable_of_tendsto
    (f := fun m z => ENNReal.ofReal (Hd.costDensity α (1 / ((m : ℝ) + 1)) z))
  · intro m
    exact (Hd.costDensity_integrable hh (by positivity) hα1 hα2 ha
      hab).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  · exact Eventually.of_forall fun z => heatCost_tendsto Hd α z (fun m => by positivity)
      tendsto_one_div_add_atTop_nhds_zero_nat
end Auto
