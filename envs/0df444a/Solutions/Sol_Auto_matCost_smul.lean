-- Prove2me | solution 1 for Auto.matCost_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:10:33.439902+00:00
-- url     : https://prove2.me/submissions/ef0620c3-b452-4d29-b277-2d991c86da41

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_costInt_smul

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
open Auto
noncomputable section
attribute [local instance] Auto._p2m_local_instance_5846efa9ac_1611
attribute [local instance] Auto._p2m_local_instance_5846efa9ac_1612
variable {n : Type*} [Fintype n] [DecidableEq n]
namespace Auto
theorem _root_.solution (P K : Matrix n n ℂ) {c : ℝ} (hc : c ≠ 0) :
    matCost P (c • K) = ENNReal.ofReal (c ^ 2) * matCost P K := by
  rw [matCost, matCost, ENNReal.mul_iSup]
  apply le_antisymm
  · refine iSup_le fun X => ?_
    refine le_trans (le_of_eq ?_) (le_iSup _ (c⁻¹ • X))
    rw [← ENNReal.ofReal_mul (sq_nonneg c)]
    congr 1
    have := costInt_smul (CFC.sqrt P) K (c⁻¹ • X) c
    rw [smul_smul, mul_inv_cancel₀ hc, one_smul] at this
    rw [this]; ring
  · refine iSup_le fun X => ?_
    refine le_trans (le_of_eq ?_) (le_iSup _ (c • X))
    rw [← ENNReal.ofReal_mul (sq_nonneg c), costInt_smul]
    ring_nf
end Auto
