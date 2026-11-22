-- Prove2me | solution 1 for Auto.energyReg_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:28:01.004803+00:00
-- url     : https://prove2.me/submissions/bcefebeb-b986-4ad1-b1d1-298aad658f07

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_trF_eq_sum
public import Theorems.Thm_Auto_three_halves_sub_le
public import Theorems.Thm_Auto_three_halves_sub_nonneg

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
namespace Auto
theorem _root_.solution {P : Matrix κ κ ℂ} (hP : P.PosSemidef) {η : ℝ} (hη : 0 ≤ η) :
    0 ≤ energyReg η P ∧ energyReg η P ≤ 2 * P.trace.re * √(P.trace.re + η) := by
  set L := P.trace.re
  have hL : L = ∑ i, hP.1.eigenvalues i := by
    simp only [L]
    rw [hP.1.trace_eq_sum_eigenvalues]
    simp [Complex.re_sum]
  have hev : ∀ i, 0 ≤ hP.1.eigenvalues i := hP.eigenvalues_nonneg
  have hevL : ∀ i, hP.1.eigenvalues i ≤ L := fun i => by
    rw [hL]; exact Finset.single_le_sum (fun j _ => hev j) (Finset.mem_univ i)
  rw [energyReg, trF_eq_sum _ hP.1]
  refine ⟨Finset.sum_nonneg fun i _ => three_halves_sub_nonneg (hev i) hη, ?_⟩
  calc ∑ i, ((hP.1.eigenvalues i + η) ^ (3 / 2 : ℝ) - η ^ (3 / 2 : ℝ))
      ≤ ∑ i, 2 * hP.1.eigenvalues i * √(L + η) := by
        refine Finset.sum_le_sum fun i _ => (three_halves_sub_le (hev i) hη).trans ?_
        gcongr
        · exact mul_nonneg zero_le_two (hev i)
        · exact hevL i
    _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum, ← hL]
end Auto
