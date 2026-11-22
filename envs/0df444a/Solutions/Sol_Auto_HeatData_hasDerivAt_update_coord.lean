-- Prove2me | solution 1 for Auto.HeatData.hasDerivAt_update_coord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:34:08.5729+00:00
-- url     : https://prove2.me/submissions/f81dbb5a-c1ed-4be5-8f8a-87d236b4023e

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
open Auto.HeatData
variable (Hd : HeatData ι) (p σ : Fin 3 → ℝ)
namespace Auto.HeatData
theorem _root_.solution (σ : Fin 3 → ℝ) (k j : Fin 3) (x : ℝ) :
    HasDerivAt (fun τ => Function.update σ k τ j) ((Pi.single k (1 : ℝ) : Fin 3 → ℝ) j) x := by
  by_cases hj : j = k
  · subst hj; simpa using hasDerivAt_id' x
  · simp only [Function.update_of_ne hj, Pi.single_apply, hj, ite_false]
    exact hasDerivAt_const _ _
end Auto.HeatData
