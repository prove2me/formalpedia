-- Prove2me | solution 1 for Auto.lintegral_avgMeasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:32:14.890528+00:00
-- url     : https://prove2.me/submissions/905d213d-04d5-4866-9376-b847d4613669

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_measurable_gaussian_toNNReal

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
namespace Auto
theorem _root_.solution (s : ℝ) (F : ℝ → ℝ≥0∞) :
    ∫⁻ d, F d ∂(avgMeasure s) = ∫⁻ d, ENNReal.ofReal (gaussian (1 / 10 * s) d) * F d := by
  rw [avgMeasure, lintegral_withDensity_eq_lintegral_mul_non_measurable _
    (measurable_gaussian_toNNReal _).coe_nnreal_ennreal
    (Eventually.of_forall fun d => ENNReal.coe_lt_top)]
  rfl
end Auto
