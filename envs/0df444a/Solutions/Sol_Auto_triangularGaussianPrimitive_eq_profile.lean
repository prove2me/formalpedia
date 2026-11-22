-- Prove2me | solution 1 for Auto.triangularGaussianPrimitive_eq_profile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:37:09.011975+00:00
-- url     : https://prove2.me/submissions/ad91cac6-a499-4f0f-b190-f5907dcc7938

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
theorem _root_.solution (c s t : ℝ) :
    triangularGaussianPrimitive c s t = (2 / (c * Real.sqrt (2 * Real.pi * c) * t)) *
      triangularCutoffProfile (t ^ 2 / (2 * c * s)) := by
  unfold triangularGaussianPrimitive triangularCutoffProfile; ring_nf
end Auto
