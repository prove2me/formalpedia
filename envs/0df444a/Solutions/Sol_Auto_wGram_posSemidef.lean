-- Prove2me | solution 1 for Auto.wGram_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:45:18.685475+00:00
-- url     : https://prove2.me/submissions/79080d41-2521-43ca-97d2-6ff41ade8682

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_rdiag_posSemidef

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
omit [DecidableEq κ] [Fintype κ]
namespace Auto
theorem _root_.solution [Finite κ] (B : Matrix ι κ ℂ) {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) :
    (wGram B f).PosSemidef := by
  exact (rdiag_posSemidef hf).conjTranspose_mul_mul_same B
end Auto
