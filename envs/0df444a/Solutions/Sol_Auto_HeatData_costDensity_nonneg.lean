-- Prove2me | solution 1 for Auto.HeatData.costDensity_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:31:45.513264+00:00
-- url     : https://prove2.me/submissions/a3660232-42ae-4fce-a07d-5cce7a1cd35d

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_HeatData_Gm_eq

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
theorem _root_.solution (α : Fin 3 → ℝ) (η : ℝ) (z : ℝ × (Fin 3 → ℝ)) :
    0 ≤ Hd.costDensity α η z := by
  refine mul_nonneg ?_ (Finset.sum_nonneg fun v _ => ENNReal.toReal_nonneg)
  rw [Gm_eq]; exact gaussian_nonneg' _ _
end Auto.HeatData
