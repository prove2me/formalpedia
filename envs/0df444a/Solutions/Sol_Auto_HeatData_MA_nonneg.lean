-- Prove2me | solution 1 for Auto.HeatData.MA_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:23:10.055608+00:00
-- url     : https://prove2.me/submissions/0adfb8b9-2c93-4ffb-980d-6e5a688301ab

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
variable (Hd : HeatData ι)
omit [DecidableEq ι]
namespace Auto.HeatData
theorem _root_.solution : 0 ≤ Hd.MA := by unfold MA; positivity
end Auto.HeatData
