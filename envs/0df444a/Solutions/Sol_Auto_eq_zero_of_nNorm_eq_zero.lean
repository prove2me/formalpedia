-- Prove2me | solution 1 for Auto.eq_zero_of_nNorm_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:37:49.482585+00:00
-- url     : https://prove2.me/submissions/b1662567-7a75-4e9f-8efc-82e432960cbe

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT

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
omit [DecidableEq ι]
namespace Auto
theorem _root_.solution {h : ℝ} (hh : 0 < h) {A : Matrix ι ι ℂ} (hA : nNorm h A = 0) :
    A = 0 := by
  unfold nNorm at hA
  have hS : 0 ≤ h ^ 2 * ∑ i, ∑ j, ‖A i j‖ ^ 3 := by positivity
  rw [Real.rpow_eq_zero hS (by norm_num)] at hA
  have hS0 : ∑ i, ∑ j, ‖A i j‖ ^ 3 = 0 := by
    rcases mul_eq_zero.1 hA with h1 | h1
    · exact absurd h1 (by positivity)
    · exact h1
  ext i j
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ =>
    by positivity)).1 hS0 i (Finset.mem_univ i)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).1 h1 j
    (Finset.mem_univ j)
  simpa using h2
end Auto
