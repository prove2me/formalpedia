-- Prove2me | solution 1 for Auto.matIntegral_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:26:30.582809+00:00
-- url     : https://prove2.me/submissions/f351cae6-cb1c-4348-b386-b0a144fa3d10

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
variable {n : Type*} [Fintype n] [DecidableEq n] {Z : Type*} [MeasurableSpace Z] {ν : Measure Z}
omit [DecidableEq n] [Fintype n]
namespace Auto
theorem _root_.solution (M : Z → Matrix n n ℂ) (i j : n) :
    matIntegral ν M i j = ∫ z, M z i j ∂ν := rfl
end Auto
