-- Prove2me | solution 1 for Auto.three_halves_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:26:31.188611+00:00
-- url     : https://prove2.me/submissions/5f1b6def-eae9-4e09-96eb-35e62a129cbe

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_rpow_three_halves

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
theorem _root_.solution {x η : ℝ} (hx : 0 ≤ x) (hη : 0 ≤ η) :
    (x + η) ^ (3 / 2 : ℝ) - η ^ (3 / 2 : ℝ) ≤ 2 * x * √(x + η) := by
  rw [rpow_three_halves (by positivity), rpow_three_halves hη]
  set a := √(x + η)
  set b := √η
  have ha : a ^ 2 = x + η := Real.sq_sqrt (by positivity)
  have hb : b ^ 2 = η := Real.sq_sqrt hη
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hab : b ≤ a := Real.sqrt_le_sqrt (by linarith)
  have hx' : x = a ^ 2 - b ^ 2 := by linarith
  rw [hx']
  nlinarith [mul_nonneg (sub_nonneg.2 hab) (mul_nonneg hb0 hb0),
    mul_nonneg (sub_nonneg.2 hab) (mul_nonneg hb0 (hb0.trans hab))]
end Auto
