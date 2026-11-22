-- Prove2me | solution 1 for Auto.HeatData.sq_mul_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:31:57.920005+00:00
-- url     : https://prove2.me/submissions/4528640d-17e4-40cf-8e45-e50a7799288b

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_gweight_nonneg

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
omit [Fintype ι] [DecidableEq ι]
namespace Auto.HeatData
theorem _root_.solution (hh : 0 ≤ Hd.h) {v : Fin 3} (hσ : 0 < σ v) :
    Hd.sqw p σ v * Hd.sqw p σ v = Hd.w p σ v := by
  funext i
  simp only [sqw, Pi.mul_apply]
  exact Real.mul_self_sqrt (gweight_nonneg _ hh hσ _ i)
end Auto.HeatData
