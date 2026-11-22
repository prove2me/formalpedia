-- Prove2me | solution 1 for Auto.abs_matCostBil_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:15:13.428983+00:00
-- url     : https://prove2.me/submissions/e6f8ee2c-7a27-4a47-8692-423023f71a3e

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_sqrt_eigenvalues_pos
public import Theorems.Thm_Auto_matCost_toReal_eq
public import Theorems.Thm_Auto_matCostBil_eq

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
open Auto
noncomputable section
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
omit [Fintype m] [DecidableEq m]
namespace Auto
theorem _root_.solution {P : Matrix n n ℂ} (hP : P.PosDef) (K L : Matrix n n ℂ) :
    |matCostBil P K L| ≤ √(matCost P K).toReal * √(matCost P L).toReal := by
  rw [matCostBil_eq hP, (matCost_toReal_eq hP K).2, (matCost_toReal_eq hP L).2]
  set c : n → n → ℝ := fun i j => √(hP.1.eigenvalues i) + √(hP.1.eigenvalues j)
  have hc : ∀ i j, 0 < c i j := fun i j =>
    add_pos (sqrt_eigenvalues_pos hP i) (sqrt_eigenvalues_pos hP j)
  set a := eigCoord hP.1 K
  set b := eigCoord hP.1 L
  have key : |∑ i, ∑ j, (3 / 2) * ((starRingEnd ℂ) (a i j) * b i j).re / c i j| ≤
      ∑ i, ∑ j, (√(3 / 2) * ‖a i j‖ / √(c i j)) * (√(3 / 2) * ‖b i j‖ / √(c i j)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    have h1 : |((starRingEnd ℂ) (a i j) * b i j).re| ≤ ‖a i j‖ * ‖b i j‖ := by
      refine (Complex.abs_re_le_norm _).trans ?_; simp
    have hcij := hc i j
    rw [abs_div, abs_mul, abs_of_pos hcij, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    have : √(3 / 2) * ‖a i j‖ / √(c i j) * (√(3 / 2) * ‖b i j‖ / √(c i j)) = (3 / 2) * (‖a i j‖ * ‖b
        i j‖) / c i j := by
      rw [div_mul_div_comm, mul_mul_mul_comm, Real.mul_self_sqrt (by norm_num),
        Real.mul_self_sqrt hcij.le]
    rw [this]
    gcongr
  refine key.trans ?_
  have := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (n × n)) (fun p => √(3 / 2) * ‖a p.1
      p.2‖ / √(c p.1 p.2)) (fun p => √(3 / 2) * ‖b p.1 p.2‖ / √(c p.1 p.2))
  simp only [Fintype.sum_prod_type] at this
  refine this.trans (le_of_eq ?_)
  congr 2
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (hc i j).le]
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (hc i j).le]
end Auto
