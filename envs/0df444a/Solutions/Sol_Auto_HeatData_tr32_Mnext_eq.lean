-- Prove2me | solution 1 for Auto.HeatData.tr32_Mnext_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:22:24.839815+00:00
-- url     : https://prove2.me/submissions/d0cd9986-96ac-4d03-a7a6-cd599e1e6bef

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_HeatData_fin3_ne_succ
public import Theorems.Thm_Auto_HeatData_fin3_succ_ne_pred
public import Theorems.Thm_Auto_HeatData_e_heat_next
public import Theorems.Thm_Auto_HeatData_hasDerivAt_e_curve
public import Theorems.Thm_Auto_HeatData_hasDerivAt_update_coord
public import Theorems.Thm_Auto_HeatData_update_pos

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
theorem _root_.solution (hh : 0 < Hd.h) {η : ℝ} (hη : 0 < η) (hσ : ∀ k, 0 < σ k) (v : Fin 3) :
    tr32 η (Hd.T p σ v) (Hd.Mnext p σ v) = tr32 η (Hd.S p σ v) (wGram (Hd.Bnext p σ v) (fun i =>
      Hd.ddw p σ (v + 1) i / 2)) := by
  have h1 := Hd.hasDerivAt_e_curve p hh hη (c := fun τ => Function.update σ (v + 1) τ) (c' :=
      (Pi.single (v + 1) (1 : ℝ) : Fin 3 → ℝ)) (θ₀ := σ (v + 1)) (fun j => hasDerivAt_update_coord σ
      (v + 1) j _) (update_pos hσ (v + 1)) v
  simp only [Function.update_eq_self, Pi.single_eq_same,
    Pi.single_eq_of_ne (fin3_ne_succ v), Pi.single_eq_of_ne (fin3_succ_ne_pred v).symm,
    zero_mul, one_mul, zero_add, add_zero] at h1
  exact h1.unique (Hd.e_heat_next p σ hh.le hη hσ v).2.2
end Auto.HeatData
