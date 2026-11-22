-- Prove2me | solution 1 for Auto.heatCost_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:38:03.390316+00:00
-- url     : https://prove2.me/submissions/0dbd40a2-122b-4191-b228-fec73b02676e

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_HeatData_ofReal_costDensity
public import Theorems.Thm_Auto_matCost_tendsto_regularization

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
    (Hd : HeatData ι) (α : Fin 3 → ℝ) (z : ℝ × (Fin 3 → ℝ))
    {η : ℕ → ℝ} (hη0 : ∀ m, 0 < η m) (hη : Tendsto η atTop (𝓝 0)) :
    Tendsto (fun m => ENNReal.ofReal (Hd.costDensity α (η m) z)) atTop
      (𝓝 (heatCost Hd α z)) := by
  simp only [Hd.ofReal_costDensity (hη0 _), heatCost]
  apply ENNReal.Tendsto.const_mul _ (Or.inr ENNReal.ofReal_ne_top)
  apply tendsto_finsetSum
  intro v _
  exact matCost_tendsto_regularization (Matrix.posSemidef_conjTranspose_mul_self _)
    _ (fun m => (hη0 m).le) hη
end Auto
