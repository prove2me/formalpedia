-- Prove2me | solution 1 for Auto.triangular_gaussian_third
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:55:50.712921+00:00
-- url     : https://prove2.me/submissions/dddc14db-706a-4e6f-9c12-9e20a99d9ed8

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
theorem _root_.solution {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    gaussianD 3 σ t = (3 * t / σ ^ 2 - t ^ 3 / σ ^ 3) * gaussian σ t := by
  rw [gaussianD_eq_profile 3 hσ, gaussian_eq_profile hσ]
  rw [show 3 = 1 + 2 from rfl, gaussProfileD_succ_succ,
    show 1 + 1 = 0 + 2 from rfl, gaussProfileD_succ_succ]
  simp only [Nat.cast_zero, Nat.cast_one, zero_add, gaussProfileD_one, gaussProfileD_zero]
  have hs := Real.sq_sqrt hσ.le
  have hp := Real.sqrt_pos.mpr hσ
  generalize Real.sqrt σ = r at *; rw [← hs]
  generalize gaussProfile (r⁻¹ * t) = g; simp only [inv_pow]
  field_simp [ne_of_gt hp]; ring
end Auto
