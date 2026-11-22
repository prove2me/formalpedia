-- Prove2me | solution 1 for Auto.continuous_wGram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:50:54.093506+00:00
-- url     : https://prove2.me/submissions/d793866f-2a0c-4c50-a2ab-89f4bf9f6516

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_continuous_rdiag

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Type*} [TopologicalSpace X]
namespace Auto
theorem _root_.solution {κ : Type*} {B : X → Matrix ι κ ℂ} {f : X → ι → ℝ} (hB : Continuous B)
    (hf : ∀ i, Continuous fun x => f x i) :
    Continuous fun x => wGram (B x) (f x) := by
  exact (hB.matrix_conjTranspose.matrix_mul (continuous_rdiag hf)).matrix_mul hB
end Auto
