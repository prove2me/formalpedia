-- Prove2me | solution 1 for Auto.integral_weight_line
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:29:53.843352+00:00
-- url     : https://prove2.me/submissions/5dad3c72-cd3f-45f4-b3b4-7753021cf51a

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
open Auto
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace Auto
theorem _root_.solution (u h σ : ℝ) (hσ : 0 < σ) : ∫ t, h * gaussian σ (u - t) = h := by
  rw [integral_const_mul, integral_sub_left_eq_self (fun t => gaussian σ t) volume u,
    integral_gaussian_eq_one hσ, mul_one]
end Auto
