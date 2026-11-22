-- Prove2me | solution 1 for Auto.HeatData.T_update
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:14:26.183797+00:00
-- url     : https://prove2.me/submissions/fa580899-de25-4b22-9d91-3b12cc20ee3c

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_HeatData_T_eq_wGram
public import Theorems.Thm_Auto_HeatData_w_update_self
public import Theorems.Thm_Auto_HeatData_Brow_update

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
theorem _root_.solution (hh : 0 ≤ Hd.h) (hσ : ∀ k, 0 < σ k) (v : Fin 3) (q : ℝ) :
    Hd.T (Function.update p v q) σ v = 0 + wGram (Hd.Brow p σ v) (gweight Hd.u Hd.h (σ v) q) := by
  rw [T_eq_wGram Hd _ σ hh (hσ v), Brow_update, w_update_self, zero_add]
end Auto.HeatData
