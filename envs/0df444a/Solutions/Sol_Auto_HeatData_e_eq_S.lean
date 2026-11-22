-- Prove2me | solution 1 for Auto.HeatData.e_eq_S
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:07:57.887742+00:00
-- url     : https://prove2.me/submissions/b37c6fb8-6928-479d-96c1-ccb645fff559

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_energyReg_conjTranspose_mul_self_eq

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
variable (Hd : HeatData ι) (p σ : Fin 3 → ℝ)
namespace Auto.HeatData
theorem _root_.solution (η : ℝ) (v : Fin 3) : Hd.e p σ η v = energyReg η (Hd.S p σ v) := by
  rw [e, T, S]
  exact energyReg_conjTranspose_mul_self_eq η (Hd.R p σ v)
end Auto.HeatData
