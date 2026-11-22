-- Prove2me | solution 1 for Auto.HeatData.continuous_sqw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:26:37.566097+00:00
-- url     : https://prove2.me/submissions/1af60a97-ee73-4c01-ab41-8f27d1e3be4a

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_HeatData_continuous_w

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
open Auto.HeatData
variable (Hd : HeatData ι) {p σ : X → Fin 3 → ℝ}
omit [Fintype ι] [DecidableEq ι]
namespace Auto.HeatData
theorem _root_.solution (hp : Continuous p) (hσ : Continuous σ) (hpos : ∀ x k, 0 < σ x k)
    (k : Fin 3) (i : ι) :
    Continuous fun x => Hd.sqw (p x) (σ x) k i :=
  Real.continuous_sqrt.comp (Hd.continuous_w hp hσ hpos k i)
end Auto.HeatData
