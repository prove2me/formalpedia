-- Prove2me | solution 1 for Auto.hasDerivAt_wGram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:33:10.88428+00:00
-- url     : https://prove2.me/submissions/f72d2258-283c-4b03-9c4f-565e3da20880

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_wGram_apply

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
theorem _root_.solution (B : Matrix ι κ ℂ) {f : ℝ → ι → ℝ} {f' : ι → ℝ} {θ₀ : ℝ}
    (hf : ∀ i, HasDerivAt (fun θ => f θ i) (f' i) θ₀) :
    ∀ a b, HasDerivAt (fun θ => wGram B (f θ) a b) (wGram B f' a b) θ₀ := by
  intro a b
  simp only [wGram_apply]
  refine HasDerivAt.fun_sum fun i _ => ?_
  exact ((hf i).ofReal_comp.const_mul _).mul_const _
end Auto
