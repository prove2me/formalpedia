-- Prove2me | solution 1 for Auto.HeatData.ofReal_costDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:14:04.53981+00:00
-- url     : https://prove2.me/submissions/d49c734a-fb5e-41b9-872d-27fef4a19650

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_matCost_ne_top
public import Theorems.Thm_Auto_posDef_add_smul_one
public import Theorems.Thm_Auto_HeatData_Gm_eq

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
theorem _root_.solution {η : ℝ} (hη : 0 < η) (α : Fin 3 → ℝ) (z : ℝ × (Fin 3 → ℝ)) :
    ENNReal.ofReal (Hd.costDensity α η z) = ENNReal.ofReal (Gm (1 / 10) 0 z.1 z.2) * ∑ v,
      matCost (Hd.T z.2 (sig α z.1) v + (η : ℂ) • 1) (Hd.Ui z.2 (sig α z.1) v) := by
  have hG : 0 ≤ Gm (1 / 10) 0 z.1 z.2 := by rw [Gm_eq]; exact gaussian_nonneg' _ _
  simp only [costDensity, qV, V]
  rw [ENNReal.ofReal_mul hG, ENNReal.ofReal_sum_of_nonneg
    (fun v _ => ENNReal.toReal_nonneg)]
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  exact ENNReal.ofReal_toReal (matCost_ne_top (posDef_add_smul_one
    (Matrix.posSemidef_conjTranspose_mul_self _) hη) _)
end Auto.HeatData
