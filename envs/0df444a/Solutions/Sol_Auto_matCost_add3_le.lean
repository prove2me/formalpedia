-- Prove2me | solution 1 for Auto.matCost_add3_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:12:23.422986+00:00
-- url     : https://prove2.me/submissions/a86d6a40-92ab-46a2-a2e1-0ca89a6cfcd0

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_hsRe_smul_right
public import Theorems.Thm_Auto_matCost_smul

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
theorem _root_.solution (P K₁ K₂ K₃ : Matrix n n ℂ) :
    matCost P (K₁ + K₂ + K₃) ≤ 3 * (matCost P K₁ + matCost P K₂ + matCost P K₃) := by
  have h9 : ∀ K, matCost P ((3 : ℝ) • K) = 9 * matCost P K := by
    intro K; rw [matCost_smul P K (by norm_num : (3 : ℝ) ≠ 0)]; norm_num
  refine iSup_le fun X => ?_
  set A := CFC.sqrt P
  have e : (3 / 2) * costInt A (K₁ + K₂ + K₃) X = (1 / 3) * ((3 / 2) * costInt A ((3 : ℝ) • K₁) X +
      (3 / 2) * costInt A ((3 : ℝ) • K₂) X + (3 / 2) * costInt A ((3 : ℝ) • K₃) X) := by
    unfold costInt
    have hc : ∀ (K Y : Matrix n n ℂ), hsRe ((3 : ℝ) • K) Y = 3 * hsRe K Y := by
      intro K Y; rw [hsRe_comm, hsRe_smul_right, hsRe_comm]
    have hadd : ∀ (K L Y : Matrix n n ℂ), hsRe (K + L) Y = hsRe K Y + hsRe L Y := by
      intro K L Y; rw [hsRe_comm, hsRe_add_right, hsRe_comm, hsRe_comm Y]
    rw [hadd, hadd, hc, hc, hc]
    ring
  rw [e]
  have hle : ∀ K, ENNReal.ofReal ((3 / 2) * costInt A K X) ≤ matCost P K := fun K =>
    le_iSup (fun X => ENNReal.ofReal ((3 / 2) * costInt (CFC.sqrt P) K X)) X
  calc ENNReal.ofReal ((1 / 3) * ((3 / 2) * costInt A ((3 : ℝ) • K₁) X + (3 / 2) * costInt A ((3 :
      ℝ) • K₂) X + (3 / 2) * costInt A ((3 : ℝ) • K₃) X))
      ≤ ENNReal.ofReal (1 / 3) * (ENNReal.ofReal ((3 / 2) * costInt A ((3 : ℝ) • K₁) X) +
          ENNReal.ofReal ((3 / 2) * costInt A ((3 : ℝ) • K₂) X) +
          ENNReal.ofReal ((3 / 2) * costInt A ((3 : ℝ) • K₃) X)) := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        gcongr
        exact ENNReal.ofReal_add_le.trans (add_le_add ENNReal.ofReal_add_le le_rfl)
    _ ≤ ENNReal.ofReal (1 / 3) * (matCost P ((3 : ℝ) • K₁) + matCost P ((3 : ℝ) • K₂) +
          matCost P ((3 : ℝ) • K₃)) := by gcongr <;> exact hle _
    _ = 3 * (matCost P K₁ + matCost P K₂ + matCost P K₃) := by
        rw [h9, h9, h9, ← mul_add, ← mul_add, ← mul_assoc]
        congr 1
        rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num)]
        norm_num
end Auto
