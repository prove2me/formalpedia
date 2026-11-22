-- Prove2me | solution 1 for Auto.int_bounds_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:40:34.297797+00:00
-- url     : https://prove2.me/submissions/88b33410-5ab0-4d07-97f7-672026a6d2f2

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
public section
open scoped ENNReal NNReal
open MeasureTheory Filter Topology Real
public section
open Auto
open MeasureTheory Filter Topology Matrix Real
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
namespace Auto
theorem _root_.solution {F : ℝ × ℝ → ℂ} {ρ : ℝ}
    (hF : ∀ p, ρ < ‖p‖ → F p = 0) {N : ℕ} (hN : 0 < N)
    {a b : ℤ} (hp : F ((a : ℝ) / N, (b : ℝ) / N) ≠ 0) :
    (|a| : ℝ) ≤ ρ * N ∧ (|b| : ℝ) ≤ ρ * N := by
  have h : ‖((a : ℝ) / N, (b : ℝ) / N)‖ ≤ ρ :=
    not_lt.1 fun h => hp (hF _ h)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  simpa only [Prod.norm_def, max_le_iff, Real.norm_eq_abs, abs_div,
    abs_of_pos hN', div_le_iff₀ hN', Int.cast_abs] using h
end Auto
