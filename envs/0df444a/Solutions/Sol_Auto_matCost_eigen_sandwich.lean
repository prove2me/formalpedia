-- Prove2me | solution 1 for Auto.matCost_eigen_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:15:03.963224+00:00
-- url     : https://prove2.me/submissions/adce0165-7445-461d-9c7e-b4a31b6adbf5

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_matCost_eq_sum_of_conj
public import Theorems.Thm_Auto_conj_unitary_mul

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (W0 W1 W2 D0 D1 D2 : Matrix ι ι ℂ)
namespace Auto
theorem _root_.solution {κ : Type*} [Fintype κ] [DecidableEq κ]
    (U : Matrix.unitaryGroup κ ℂ) (m : κ → ℝ) (D : Matrix κ κ ℂ) :
    matCost (((U : Matrix κ κ ℂ) * diagonal (fun i => (m i : ℂ)) * star (U : Matrix κ κ ℂ)) *
      ((U : Matrix κ κ ℂ) * diagonal (fun i => (m i : ℂ)) * star (U : Matrix κ κ ℂ))) (((U :
      Matrix κ κ ℂ) * diagonal (fun i => (m i : ℂ)) * star (U : Matrix κ κ ℂ)) * D * ((U : Matrix
      κ κ ℂ) * diagonal (fun i => (m i : ℂ)) * star (U : Matrix κ κ ℂ))) = ENNReal.ofReal ((3 / 2)
      * ∑ i, ∑ j, |m i| ^ 2 * |m j| ^ 2 * ‖(star (U : Matrix κ κ ℂ) * D * U) i j‖ ^ 2 / (|m i| +
      |m j|)) := by
  set M := (U : Matrix κ κ ℂ) * diagonal (fun i => (m i : ℂ)) * star (U : Matrix κ κ ℂ)
  have hU'U : star (U : Matrix κ κ ℂ) * U = 1 := Unitary.coe_star_mul_self U
  have hUMU : star (U : Matrix κ κ ℂ) * M * U = diagonal (fun i => (m i : ℂ)) := by
    simp only [M, Matrix.mul_assoc, hU'U, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hU'U, Matrix.one_mul]
  have hMM : M * M = (U : Matrix κ κ ℂ) * diagonal (fun i => ((m i ^ 2 : ℝ) : ℂ)) *
      star (U : Matrix κ κ ℂ) := by
    simp only [M, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star (U : Matrix κ κ ℂ)) (U : Matrix κ κ ℂ), hU'U, Matrix.one_mul,
      ← Matrix.mul_assoc (diagonal _) (diagonal _), Matrix.diagonal_mul_diagonal]
    congr 3; funext i; push_cast; ring
  have hent : star (U : Matrix κ κ ℂ) * (M * D * M) * U =
      diagonal (fun i => (m i : ℂ)) * (star (U : Matrix κ κ ℂ) * D * U) *
        diagonal (fun i => (m i : ℂ)) := by
    rw [conj_unitary_mul, conj_unitary_mul, hUMU]
  rw [hMM, matCost_eq_sum_of_conj U (fun i => m i ^ 2) (fun i => sq_nonneg _) rfl, hent]
  set Dt := star (U : Matrix κ κ ℂ) * D * U
  have hterm : ∀ i j, ENNReal.ofReal ((3 / 2) * ‖(diagonal (fun i => (m i : ℂ)) * Dt *
      diagonal (fun i => (m i : ℂ))) i j‖ ^ 2) / ENNReal.ofReal (√(m i ^ 2) + √(m j ^ 2)) =
      ENNReal.ofReal ((3 / 2) * (|m i| ^ 2 * |m j| ^ 2 * ‖Dt i j‖ ^ 2 / (|m i| + |m j|))) := by
    intro i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
    have hnorm : ‖(m i : ℂ) * Dt i j * (m j : ℂ)‖ ^ 2 = |m i| ^ 2 * |m j| ^ 2 * ‖Dt i j‖ ^ 2 := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs]; ring
    rw [hnorm]
    rcases (add_nonneg (abs_nonneg (m i)) (abs_nonneg (m j))).eq_or_lt with h | h
    · have hi : |m i| = 0 := by linarith [abs_nonneg (m i), abs_nonneg (m j)]
      rw [← h, hi]; simp
    · rw [← ENNReal.ofReal_div_of_pos h, mul_div_assoc]
  simp_rw [hterm]
  rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
end Auto
