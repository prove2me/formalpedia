-- Prove2me | solution 1 for Auto.HeatData.sqw_N_sqw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:47:26.9438+00:00
-- url     : https://prove2.me/submissions/71e6a8be-8b77-4c10-a27e-34d696abef32

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_HeatData_rdiag_mul_rdiag
public import Theorems.Thm_Auto_HeatData_w_pos

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
    rdiag (Hd.sqw p σ v) * Hd.N p σ v * rdiag (Hd.sqw p σ v) = rdiag (Hd.dw p σ v) := by
  rw [N, rdiag_mul_rdiag, rdiag_mul_rdiag]
  congr 1
  funext i
  have hw := Hd.w_pos p σ hh hσ i
  have hs : Hd.sqw p σ v i * Hd.sqw p σ v i = Hd.w p σ v i := Real.mul_self_sqrt hw.le
  simp only [Pi.mul_apply]
  rw [mul_comm (Hd.sqw p σ v i * _), ← mul_assoc, hs]
  field_simp
end Auto.HeatData
