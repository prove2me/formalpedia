-- Prove2me | solution 1 for Auto.triangularGaussianPrimitive_tendsto_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:42:33.758597+00:00
-- url     : https://prove2.me/submissions/71f34629-9976-4c06-98df-39b7d1e77a1a

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_triangularGaussianPrimitive_eq_profile

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
theorem _root_.solution {c : ℝ} (hc : 0 < c) (t : ℝ) :
    Tendsto (fun s => triangularGaussianPrimitive c s t) atTop (𝓝 (2 / (c * Real.sqrt (2 *
      Real.pi * c) * t))) := by
  have hu : Tendsto (fun s : ℝ => t ^ 2 / (2 * c * s)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Tendsto.const_mul_atTop (by positivity) tendsto_id)
  have hp : Continuous triangularCutoffProfile := by unfold triangularCutoffProfile; fun_prop
  have h := (hp.continuousAt.tendsto.comp hu).const_mul
    (2 / (c * Real.sqrt (2 * Real.pi * c) * t))
  simpa [triangularGaussianPrimitive_eq_profile, triangularCutoffProfile] using h
end Auto
