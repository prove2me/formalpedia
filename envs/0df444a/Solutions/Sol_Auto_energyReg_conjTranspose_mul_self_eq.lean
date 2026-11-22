-- Prove2me | solution 1 for Auto.energyReg_conjTranspose_mul_self_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:06:50.480798+00:00
-- url     : https://prove2.me/submissions/72abec19-c5da-4850-af86-c3fac4979ff7

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_trF_conjTranspose_mul_self_eq

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
open Auto
noncomputable section
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
namespace Auto
theorem _root_.solution (η : ℝ) (R : Matrix m n ℂ) :
    energyReg η (Rᴴ * R) = energyReg η (R * Rᴴ) :=
  trF_conjTranspose_mul_self_eq _ (by simp) R
end Auto
