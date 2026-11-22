-- Prove2me | solution 1 for Auto.hasDerivAt_re_trace_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:41:03.357477+00:00
-- url     : https://prove2.me/submissions/a5e50c46-3175-4c7f-8133-dfe31b6827c4

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
omit [DecidableEq n]
namespace Auto
theorem _root_.solution {F G : ℝ → Matrix n n ℂ} {F' G' : Matrix n n ℂ} {θ₀ : ℝ}
    (hF : ∀ i j, HasDerivAt (fun θ => F θ i j) (F' i j) θ₀)
    (hG : ∀ i j, HasDerivAt (fun θ => G θ i j) (G' i j) θ₀) :
    HasDerivAt (fun θ => ((F θ * G θ).trace).re) (((F' * G θ₀ + F θ₀ * G').trace).re) θ₀ := by
  have h : HasDerivAt (fun θ => (F θ * G θ).trace) ((F' * G θ₀ + F θ₀ * G').trace) θ₀ := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.add_apply,
      ← Finset.sum_add_distrib]
    refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun k _ => ?_
    exact (hF i k).mul (hG k i)
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt θ₀ h
end Auto
