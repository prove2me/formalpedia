-- Prove2me | solution 1 for Auto.HeatData.S_update_next
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:45:04.202838+00:00
-- url     : https://prove2.me/submissions/2d59f465-4e24-422f-9a05-921f23499f23

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_HeatData_S_eq_wGram
public import Theorems.Thm_Auto_HeatData_fin3_ne_succ
public import Theorems.Thm_Auto_HeatData_fin3_succ_ne_pred
public import Theorems.Thm_Auto_HeatData_w_update_ne
public import Theorems.Thm_Auto_HeatData_w_update_self
public import Theorems.Thm_Auto_HeatData_Bnext_update
public import Theorems.Thm_Auto_HeatData_Bprev_update

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
    Hd.S (Function.update p (v + 1) q) σ v = wGram (Hd.Bprev p σ v) (Hd.w p σ (v - 1)) + wGram
      (Hd.Bnext p σ v) (gweight Hd.u Hd.h (σ (v + 1)) q) := by
  rw [S_eq_wGram Hd _ σ hh (hσ _) (hσ _), Bnext_update Hd p σ (fin3_ne_succ v).symm,
    Bprev_update Hd p σ (fin3_ne_succ v).symm, w_update_self,
    w_update_ne Hd p σ (fin3_succ_ne_pred v).symm, add_comm]
end Auto.HeatData
