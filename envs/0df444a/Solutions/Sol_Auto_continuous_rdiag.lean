-- Prove2me | solution 1 for Auto.continuous_rdiag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:49:43.6968+00:00
-- url     : https://prove2.me/submissions/a74bc501-4c37-493e-a99e-52123fb17e72

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
omit [Fintype ι]
namespace Auto
theorem _root_.solution {f : X → ι → ℝ} (hf : ∀ i, Continuous fun x => f x i) :
    Continuous fun x => rdiag (f x) :=
  Continuous.matrix_diagonal (continuous_pi fun i => Complex.continuous_ofReal.comp (hf i))
end Auto
