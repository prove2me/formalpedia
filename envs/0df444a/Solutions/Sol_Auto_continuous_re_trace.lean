-- Prove2me | solution 1 for Auto.continuous_re_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:28:19.522001+00:00
-- url     : https://prove2.me/submissions/3bfe4601-061a-4653-870f-a597fbbb7f32

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Type*} [TopologicalSpace X]
omit [Fintype ι] [DecidableEq ι]
namespace Auto
theorem _root_.solution {κ : Type*} [Fintype κ] {M : X → Matrix κ κ ℂ} (hM : Continuous M) :
    Continuous fun x => (M x).trace.re :=
  Complex.continuous_re.comp hM.matrix_trace
end Auto
