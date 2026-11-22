-- Prove2me | solution 1 for Auto.add_smul_one_sub_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:24:01.307005+00:00
-- url     : https://prove2.me/submissions/7f354ea0-c5c5-40f9-b3c1-b06645433480

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
variable {n : Type*} [Fintype n] [DecidableEq n]
omit [Fintype n]
namespace Auto
theorem _root_.solution {P : Matrix n n ℂ} (hP : P.PosSemidef) (η : ℝ) :
    (P + (η : ℂ) • (1 : Matrix n n ℂ) - (η : ℂ) • (1 : Matrix n n ℂ)).PosSemidef := by
  simpa using hP
end Auto
