-- Prove2me | solution 1 for Auto.HeatData.T_eq_DXD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:18:33.324606+00:00
-- url     : https://prove2.me/submissions/20956836-a153-452f-8e4d-27208bb0c991

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_HeatData_rdiag_mul_rdiag
public import Theorems.Thm_Auto_HeatData_rdiag_conjTranspose
public import Theorems.Thm_Auto_HeatData_R_eq
public import Theorems.Thm_P2M_Auto_gweight_nonneg__bb3decd414c3
public import Theorems.Thm_Auto_HeatData_Dc_eq

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
theorem _root_.solution (hh : 0 ≤ Hd.h) (v : Fin 3) :
    Hd.T p σ v = rdiag (Hd.dv p σ v) * Hd.X p σ v * rdiag (Hd.dv p σ v) := by
  have hw : Hd.sqw p σ v * Hd.sqw p σ v = Hd.w p σ v := by
    funext i
    simp only [sqw, Pi.mul_apply]
    exact Real.mul_self_sqrt (gweight_nonneg' _ hh _ _ i)
  rw [T, R_eq, X, wGram, ← Dc_eq, ← hw, ← rdiag_mul_rdiag]
  have hD : (Hd.Dc p σ v)ᴴ = Hd.Dc p σ v := by
    rw [Dc_eq, rdiag_conjTranspose]
  simp only [Matrix.conjTranspose_mul, rdiag_conjTranspose, hD, Matrix.mul_assoc]
end Auto.HeatData
