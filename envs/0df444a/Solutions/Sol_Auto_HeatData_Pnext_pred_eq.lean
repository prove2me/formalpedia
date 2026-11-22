-- Prove2me | solution 1 for Auto.HeatData.Pnext_pred_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:17:00.974391+00:00
-- url     : https://prove2.me/submissions/d48b83f4-e909-43bd-947b-27dcd689bbef

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_HeatData_rdiag_conjTranspose
public import Theorems.Thm_Auto_HeatData_sqw_N_sqw

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
theorem _root_.solution (hh : 0 < Hd.h) {v : Fin 3} (hσ : 0 < σ v) :
    Hd.Pnext p σ (v - 1) = Hd.W p σ (v - 1) * Hd.N p σ v * (Hd.W p σ (v - 1))ᴴ := by
  have hv : v - 1 + 1 = v := by abel
  rw [Pnext, Bnext, hv, wGram, W, hv, ← Hd.sqw_N_sqw p σ hh hσ]
  simp only [Matrix.conjTranspose_mul, rdiag_conjTranspose, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc]
end Auto.HeatData
