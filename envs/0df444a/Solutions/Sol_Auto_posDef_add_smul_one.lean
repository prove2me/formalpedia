-- Prove2me | solution 1 for Auto.posDef_add_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:22:44.672918+00:00
-- url     : https://prove2.me/submissions/c8d53276-c58d-4903-964f-25bab3253a2a

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
theorem _root_.solution {P : Matrix n n ℂ} (hP : P.PosSemidef) {η : ℝ} (hη : 0 < η) :
    (P + (η : ℂ) • (1 : Matrix n n ℂ)).PosDef :=
  Matrix.PosDef.posSemidef_add hP (Matrix.PosDef.one.smul (by exact_mod_cast hη))
end Auto
