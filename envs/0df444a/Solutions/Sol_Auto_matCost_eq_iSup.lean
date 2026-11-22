-- Prove2me | solution 1 for Auto.matCost_eq_iSup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:36:23.920292+00:00
-- url     : https://prove2.me/submissions/e18c2387-fd50-43d7-8bc6-3b0a7c5988e3

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_posDef_add_smul_one
public import Theorems.Thm_Auto_matCost_anti
public import Theorems.Thm_Auto_matCost_le_liminf

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
namespace Auto
theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n] {P : Matrix n n ℂ}
    (hP : P.PosSemidef) (K : Matrix n n ℂ) :
    matCost P K = ⨆ m : ℕ, matCost (P + ((1 / ((m : ℝ) + 1) : ℝ) : ℂ) • 1) K := by
  refine le_antisymm ?_ (iSup_le fun m => ?_)
  · refine (matCost_le_liminf hP K (η := fun m : ℕ => 1 / ((m : ℝ) + 1)) (fun m => by positivity)
      tendsto_one_div_add_atTop_nhds_zero_nat).trans ?_
    exact (liminf_le_limsup (f := atTop)).trans limsup_le_iSup
  · refine matCost_anti (posDef_add_smul_one hP (by positivity)).posSemidef ?_ K
    rw [Matrix.le_iff, add_sub_cancel_left]
    exact Matrix.PosSemidef.one.smul (by exact_mod_cast (by positivity : (0 : ℝ) ≤ 1 / ((m : ℝ)
        + 1)))
end Auto
