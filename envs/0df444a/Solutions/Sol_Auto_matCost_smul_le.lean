-- Prove2me | solution 1 for Auto.matCost_smul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:33:08.745628+00:00
-- url     : https://prove2.me/submissions/129f1633-82a8-45df-93b7-7605cd942f43

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_matCost_smul

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
namespace Auto
theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n] (P K : Matrix n n ℂ) (c : ℝ) :
    matCost P ((c : ℂ) • K) ≤ ENNReal.ofReal (c ^ 2) * matCost P K := by
  by_cases hc : c = 0
  · subst hc
    simp only [Complex.ofReal_zero, zero_smul]
    refine le_trans (iSup_le fun X => ?_) (zero_le (a := ENNReal.ofReal (0 ^ 2) * matCost P K))
    refine (ENNReal.ofReal_eq_zero.2 ?_).le
    have hA : (CFC.sqrt P - ((0 : ℝ) : ℂ) • (1 : Matrix n n ℂ)).PosSemidef := by
      simpa using (CFC.sqrt_nonneg P).posSemidef
    have h := sylvester_lower hA hA X
    rw [hsRe_add_right] at h
    simp only [costInt, hsRe, Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.trace_zero,
      Complex.zero_re, mul_zero, zero_sub] at h ⊢
    nlinarith [hsSq_nonneg X]
  · have e : (c : ℂ) • K = c • K := by ext i j; simp [Complex.real_smul]
    rw [e, matCost_smul P K hc]
end Auto
