-- Prove2me | solution 1 for Auto.shiftMat_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:34:53.91993+00:00
-- url     : https://prove2.me/submissions/f4ef7a5d-cfe4-463a-9e4b-8aa242277ba1

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
open Auto
noncomputable section
namespace Auto
theorem _root_.solution (v : Fin 3) (x : Fin 3 → ℝ) :
    shiftMat v *ᵥ x = Function.update (planePt ![x 0, x 1]) v (planePt ![x 0, x 1] v + x 2) := by
  ext r
  fin_cases v <;> fin_cases r <;>
    simp [shiftMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three, planePt] <;> ring
end Auto
