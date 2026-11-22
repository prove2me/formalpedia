-- Prove2me | solution 1 for Auto.HeatData.measurable_rowCost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:38:05.010813+00:00
-- url     : https://prove2.me/submissions/08e83d69-4cd0-491c-b47e-239fff87faca

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_matCost_ne_top
public import Theorems.Thm_Auto_posDef_add_smul_one
public import Theorems.Thm_Auto_HeatData_continuous_scalars
public import Theorems.Thm_Auto_matCost_eq_iSup

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
theorem _root_.solution (σ : Fin 3 → ℝ) (hσ : ∀ k, 0 < σ k) (v : Fin 3) :
    Measurable fun p : Fin 3 → ℝ => matCost (Hd.T p σ v) (Hd.Ui p σ v) := by
  have e : (fun p : Fin 3 → ℝ => matCost (Hd.T p σ v) (Hd.Ui p σ v)) = fun p =>
      ⨆ m : ℕ, ENNReal.ofReal (Hd.V p σ (1 / ((m : ℝ) + 1)) v) := by
    funext p
    rw [matCost_eq_iSup (P := Hd.T p σ v) (Matrix.posSemidef_conjTranspose_mul_self _)]
    congr 1; funext m
    exact (ENNReal.ofReal_toReal (matCost_ne_top (posDef_add_smul_one
      (Matrix.posSemidef_conjTranspose_mul_self (Hd.R p σ v))
        (one_div_pos.2 (by positivity : (0 : ℝ) < (m : ℝ) + 1))) (Hd.Ui p σ v))).symm
  rw [e]
  refine Measurable.iSup fun m => ENNReal.measurable_ofReal.comp ?_
  exact ((Hd.continuous_scalars continuous_id continuous_const (fun _ => hσ)
    (by positivity : (0 : ℝ) < 1 / ((m : ℝ) + 1)) v).2.2.2.2.2.2.2.1).measurable
end Auto.HeatData
