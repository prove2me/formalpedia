-- Prove2me | solution 1 for Auto.integrable_avgMeasure_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:33:24.961266+00:00
-- url     : https://prove2.me/submissions/318f2563-2236-4513-abc4-0163e1f6dbd8

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
theorem _root_.solution (s : ℝ) {f : ℝ → ℝ}
    (hf : Integrable (fun d => gaussian (1 / 10 * s) d * f d)) :
    Integrable f (avgMeasure s) := by
  rw [avgMeasure, integrable_withDensity_iff_integrable_smul (measurable_gaussian_toNNReal _)]
  refine hf.congr (Eventually.of_forall fun d => ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (gaussian_nonneg' _ _), smul_eq_mul]
end Auto
