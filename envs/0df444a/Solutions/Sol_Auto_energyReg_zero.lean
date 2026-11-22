-- Prove2me | solution 1 for Auto.energyReg_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:04:13.217731+00:00
-- url     : https://prove2.me/submissions/2ef8a361-980b-485b-812e-9820049cd5a9

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
open Auto
noncomputable section
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
namespace Auto
theorem _root_.solution (P : Matrix n n ℂ) :
    energyReg 0 P = energy P := by
  simp [energyReg, energy, Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0)]
end Auto
