-- Prove2me | solution 1 for Auto.HeatData.Jbar_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:31:41.271279+00:00
-- url     : https://prove2.me/submissions/2f692559-70ad-43da-8578-3c2f3d22bed0

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_energyReg_bounds
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
theorem _root_.solution (α : Fin 3 → ℝ) {η : ℝ} (hη : 0 ≤ η) (s : ℝ) : 0 ≤ Hd.Jbar α η s := by
  refine integral_nonneg fun p => mul_nonneg ?_ (Finset.sum_nonneg fun v _ =>
    (energyReg_bounds (Matrix.posSemidef_conjTranspose_mul_self _) hη).1)
  rw [Gm_eq]; exact gaussian_nonneg' _ _
end Auto.HeatData
