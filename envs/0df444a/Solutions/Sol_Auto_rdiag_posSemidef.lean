-- Prove2me | solution 1 for Auto.rdiag_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:44:08.370917+00:00
-- url     : https://prove2.me/submissions/79bf2ea4-5251-408d-81ec-7f81fce269b7

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
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
omit [Fintype κ] [DecidableEq κ] [Fintype ι]
namespace Auto
theorem _root_.solution {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) : (rdiag f).PosSemidef := by
  rw [rdiag, Matrix.posSemidef_diagonal_iff]
  intro i; exact_mod_cast hf i
end Auto
