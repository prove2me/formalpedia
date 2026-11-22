-- Prove2me | solution 1 for Auto.HeatData.phi_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:23:28.396345+00:00
-- url     : https://prove2.me/submissions/deb10b58-f043-41e1-9c3b-ca9bc8d5560d

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_edec_pos
public import Theorems.Thm_Auto_edec_le_one

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
omit [Fintype ι] [DecidableEq ι]
namespace Auto.HeatData
theorem _root_.solution {b : ℝ} (hb : 0 < b) (v : Fin 3) (p : Fin 3 → ℝ) : phi b v p ≤ 2 := by
  unfold phi
  have h0 := edec_le_one hb (p v)
  have h1 := edec_le_one hb (p (v + 1))
  have h2 := edec_le_one hb (p (v - 1))
  have := edec_pos b (p v)
  have := edec_pos b (p (v + 1))
  have := edec_pos b (p (v - 1))
  nlinarith
end Auto.HeatData
