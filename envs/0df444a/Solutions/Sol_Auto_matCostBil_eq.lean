-- Prove2me | solution 1 for Auto.matCostBil_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:13:08.8131+00:00
-- url     : https://prove2.me/submissions/73e01f38-ad68-4b3f-b0b0-3efc49eadfc2

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_eigCoord_add
public import Theorems.Thm_Auto_eigCoord_sub
public import Theorems.Thm_Auto_matCost_toReal_eq

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
    matCostBil P K L = ∑ i, ∑ j, (3 / 2) * ((starRingEnd ℂ) (eigCoord hP.1 K i j) * eigCoord
      hP.1 L i j).re / (√(hP.1.eigenvalues i) + √(hP.1.eigenvalues j)) := by
  rw [matCostBil, (matCost_toReal_eq hP _).2, (matCost_toReal_eq hP _).2, eigCoord_add,
    eigCoord_sub, ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.add_apply, Matrix.sub_apply]
  set a := eigCoord hP.1 K i j
  set b := eigCoord hP.1 L i j
  have hab : ‖a + b‖ ^ 2 - ‖a - b‖ ^ 2 = 4 * ((starRingEnd ℂ) a * b).re := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_add,
      Complex.normSq_sub]
    simp [Complex.mul_re]
    ring
  rw [div_sub_div_same, ← mul_sub, hab]
  ring
end Auto
