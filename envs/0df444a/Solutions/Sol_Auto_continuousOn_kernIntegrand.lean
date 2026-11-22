-- Prove2me | solution 1 for Auto.continuousOn_kernIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:39:10.786838+00:00
-- url     : https://prove2.me/submissions/279c8292-f1d2-4676-a34d-9669fab3faa0

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_continuousOn_kernIntegrand_joint

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
theorem _root_.solution (m : ℕ) (t : ℝ) :
    ContinuousOn (fun s => kernIntegrand m s t) (Set.Ioi 0) :=
  (continuousOn_kernIntegrand_joint m).comp
    (continuous_id.prodMk continuous_const).continuousOn (fun _ hs => hs)
end Auto
