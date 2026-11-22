-- Prove2me | solution 1 for Auto.blk3_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:31:04.211581+00:00
-- url     : https://prove2.me/submissions/786f820a-c08f-47f2-b640-fd4e02a60144

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
attribute [local instance] Auto._p2m_local_instance_5846efa9ac_1611
attribute [local instance] Auto._p2m_local_instance_5846efa9ac_1612
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι] [Fintype ι]
namespace Auto
theorem _root_.solution (a b c d e f g h i : Matrix ι ι ℂ) :
    (blk3 !![a, b, c; d, e, f; g, h, i])ᴴ = blk3 !![aᴴ, dᴴ, gᴴ; bᴴ, eᴴ, hᴴ; cᴴ, fᴴ, iᴴ] := by
  ext ⟨w, x⟩ ⟨w', y⟩
  fin_cases w <;> fin_cases w' <;> simp [blk3, Matrix.comp_apply, Matrix.conjTranspose_apply]
end Auto
