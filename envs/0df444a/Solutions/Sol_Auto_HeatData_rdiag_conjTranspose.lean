-- Prove2me | solution 1 for Auto.HeatData.rdiag_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:32:38.709624+00:00
-- url     : https://prove2.me/submissions/a181df84-0d73-4ad9-a1a7-27361f780910

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_rdiag_isHermitian

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
variable (Hd : HeatData ι) (p σ : Fin 3 → ℝ)
omit [Fintype ι]
namespace Auto.HeatData
theorem _root_.solution (f : ι → ℝ) : (rdiag f)ᴴ = rdiag f := (rdiag_isHermitian f).eq
end Auto.HeatData
