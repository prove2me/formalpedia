-- Prove2me | solution 1 for Auto.tendsto_energyReg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:31:37.541812+00:00
-- url     : https://prove2.me/submissions/bfe69e42-2dca-47ac-b945-45db467f84fa

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_trF_eq_sum

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
variable {n : Type*} [Fintype n] [DecidableEq n]
namespace Auto
theorem _root_.solution {P : Matrix n n ℂ} (hP : P.IsHermitian) {η : ℕ → ℝ}
    (hη : Tendsto η atTop (𝓝 0)) :
    Tendsto (fun m => energyReg (η m) P) atTop (𝓝 (energyReg 0 P)) := by
  simp only [energyReg, trF_eq_sum _ hP]
  refine tendsto_finsetSum _ fun i _ => ?_
  have hc : Continuous fun e : ℝ => (hP.eigenvalues i + e) ^ (3 / 2 : ℝ) - e ^ (3 / 2 : ℝ) :=
    ((Real.continuous_rpow_const (by norm_num)).comp (continuous_const.add continuous_id)).sub
      (Real.continuous_rpow_const (by norm_num))
  exact (hc.tendsto 0).comp hη
end Auto
