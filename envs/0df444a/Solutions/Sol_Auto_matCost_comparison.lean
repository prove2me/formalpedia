-- Prove2me | solution 1 for Auto.matCost_comparison
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:08:00.689711+00:00
-- url     : https://prove2.me/submissions/4a7618f1-e770-4393-9d12-e3b10845090d

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_hsRe_smul_right
public import Theorems.Thm_Auto_sqrt_smul_eq
public import Theorems.Thm_Auto_quadForm_mono

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
open Auto
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]
namespace Auto
theorem _root_.solution {P Q : Matrix n n ℂ} (hQ : Q.PosSemidef) {a : ℝ} (ha : 0 < a)
    (hPQ : P ≤ (a : ℂ) • Q) (K : Matrix n n ℂ) :
    ENNReal.ofReal (√a)⁻¹ * matCost Q K ≤ matCost P K := by
  have hsa : 0 < √a := Real.sqrt_pos.2 ha
  have hsqrt : CFC.sqrt P ≤ ((√a : ℝ) : ℂ) • CFC.sqrt Q := by
    rw [← sqrt_smul_eq hQ ha.le]; exact CFC.sqrt_le_sqrt _ _ hPQ
  rw [matCost, matCost, ENNReal.mul_iSup]
  refine iSup_le fun Z => ?_
  refine le_trans ?_ (le_iSup _ ((√a)⁻¹ • Z))
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hmono := quadForm_mono (Matrix.le_iff.1 hsqrt) ((√a)⁻¹ • Z)
  unfold costInt
  have e1 : hsRe K ((√a)⁻¹ • Z) = (√a)⁻¹ * hsRe K Z := hsRe_smul_right _ _ _
  have e2 : hsRe ((√a)⁻¹ • Z) ((((√a : ℝ) : ℂ) • CFC.sqrt Q) * ((√a)⁻¹ • Z)) +
      hsRe ((√a)⁻¹ • Z) (((√a)⁻¹ • Z) * (((√a : ℝ) : ℂ) • CFC.sqrt Q)) =
      (√a)⁻¹ * (hsRe Z (CFC.sqrt Q * Z) + hsRe Z (Z * CFC.sqrt Q)) := by
    have hcs : ((√a : ℝ) : ℂ) • CFC.sqrt Q = (√a) • CFC.sqrt Q := Complex.coe_smul _ _
    have hsc : (√a)⁻¹ * √a = 1 := inv_mul_cancel₀ hsa.ne'
    have hsc' : √a * (√a)⁻¹ = 1 := mul_inv_cancel₀ hsa.ne'
    have hc : ∀ (c : ℝ) (X Y : Matrix n n ℂ), hsRe (c • X) Y = c * hsRe X Y := by
      intro c X Y; rw [hsRe_comm, hsRe_smul_right, hsRe_comm]
    rw [hcs]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hsc, hsc', one_smul, hc]
    ring
  rw [e1] at *
  nlinarith [hmono, e2]
end Auto
