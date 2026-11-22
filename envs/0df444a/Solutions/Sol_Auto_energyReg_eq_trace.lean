-- Prove2me | solution 1 for Auto.energyReg_eq_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:42:29.300739+00:00
-- url     : https://prove2.me/submissions/9a99afb1-6ced-472c-a941-a0d27e6c8f33

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_trace_conj_unitary
public import Theorems.Thm_Auto_trF_eq_sum
public import Theorems.Thm_Auto_add_smul_one_eq_conj

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
theorem _root_.solution {P : Matrix n n ℂ} (hP : P.PosSemidef) {η : ℝ} (hη : 0 ≤ η) :
    energyReg η P = (((P + (η : ℂ) • 1) * CFC.sqrt (P + (η : ℂ) • 1)).trace).re - η ^ (3 / 2 :
      ℝ) * Fintype.card n := by
  set U := hP.1.eigenvectorUnitary
  set p := hP.1.eigenvalues
  have hUU : (U : Matrix n n ℂ) * star (U : Matrix n n ℂ) = 1 := Unitary.coe_mul_star_self U
  have hU'U : star (U : Matrix n n ℂ) * U = 1 := Unitary.coe_star_mul_self U
  have hp : ∀ i, 0 ≤ p i := hP.eigenvalues_nonneg
  have hPY : P + (η : ℂ) • 1 = (U : Matrix n n ℂ) *
      diagonal (fun i => ((p i + η : ℝ) : ℂ)) * star (U : Matrix n n ℂ) :=
    add_smul_one_eq_conj hP.1 η
  have hB : (diagonal (fun i => ((√(p i + η) : ℝ) : ℂ))).PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]
    intro i; exact_mod_cast Real.sqrt_nonneg _
  have hsq : CFC.sqrt (P + (η : ℂ) • 1) = (U : Matrix n n ℂ) *
      diagonal (fun i => ((√(p i + η) : ℝ) : ℂ)) * star (U : Matrix n n ℂ) := by
    have hnn : 0 ≤ (U : Matrix n n ℂ) * diagonal (fun i => ((√(p i + η) : ℝ) : ℂ)) *
        star (U : Matrix n n ℂ) := by
      have := hB.mul_mul_conjTranspose_same (U : Matrix n n ℂ)
      rw [← Matrix.star_eq_conjTranspose] at this
      exact this.nonneg
    refine CFC.sqrt_unique ?_ hnn
    rw [hPY]
    calc (U : Matrix n n ℂ) * diagonal (fun i => ((√(p i + η) : ℝ) : ℂ)) *
          star (U : Matrix n n ℂ) * ((U : Matrix n n ℂ) *
            diagonal (fun i => ((√(p i + η) : ℝ) : ℂ)) * star (U : Matrix n n ℂ))
        = (U : Matrix n n ℂ) * (diagonal (fun i => ((√(p i + η) : ℝ) : ℂ)) * (star (U : Matrix n n
            ℂ) * U) * diagonal (fun i => ((√(p i + η) : ℝ) : ℂ))) *
              star (U : Matrix n n ℂ) := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hU'U, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
        congr 3; funext i
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith [hp i])]
  rw [energyReg, trF_eq_sum _ hP.1, hsq, hPY]
  have : (U : Matrix n n ℂ) * diagonal (fun i => ((p i + η : ℝ) : ℂ)) * star (U : Matrix n n ℂ) *
      ((U : Matrix n n ℂ) * diagonal (fun i => ((√(p i + η) : ℝ) : ℂ)) *
        star (U : Matrix n n ℂ)) = (U : Matrix n n ℂ) *
          diagonal (fun i => (((p i + η) * √(p i + η) : ℝ) : ℂ)) * star (U : Matrix n n ℂ) := by
    calc _ = (U : Matrix n n ℂ) * (diagonal (fun i => ((p i + η : ℝ) : ℂ)) * (star (U : Matrix n n
        ℂ) * U) * diagonal (fun i => ((√(p i + η) : ℝ) : ℂ))) *
              star (U : Matrix n n ℂ) := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hU'U, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
        congr 3; funext i; push_cast; ring
  rw [this, trace_conj_unitary, Matrix.trace_diagonal, Complex.re_sum, Finset.sum_sub_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.ofReal_re, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add' (by linarith [hp i]) (by norm_num), Real.rpow_one, Real.sqrt_eq_rpow]
  · simp [mul_comm]
end Auto
