-- Prove2me | solution 1 for Auto.integrable_weight_line
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:30:29.96775+00:00
-- url     : https://prove2.me/submissions/da1daf0f-39e8-494f-8c51-9a10790ac206

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
namespace Auto
theorem _root_.solution (u h σ : ℝ) (hσ : 0 < σ) :
    Integrable (fun t => h * gaussian σ (u - t)) := ((integrable_gaussian' hσ).comp_sub_left
        u).const_mul h
end Auto
