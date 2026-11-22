-- Prove2me | solution 1 for Auto.matIntegral_wGram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:33:28.418099+00:00
-- url     : https://prove2.me/submissions/00b2158a-4de0-4fd0-8645-39de23e988fd

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_matIntegral_apply
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
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace Auto
theorem _root_.solution {κ : Type*} {ν : Measure ℝ} (B : Matrix ι κ ℂ) (f : ℝ → ι → ℝ)
    (hf : ∀ i, Integrable (fun d => f d i) ν) :
    (∀ a b, Integrable (fun d => wGram B (f d) a b) ν) ∧ matIntegral ν (fun d => wGram B (f d))
      = wGram B (fun i => ∫ d, f d i ∂ν) := by
  have hc : ∀ a b i, Integrable (fun d => star (B i a) * (f d i : ℂ) * B i b) ν := fun a b i =>
    (((hf i).ofReal).const_mul (star (B i a))).mul_const (B i b)
  refine ⟨fun a b => ?_, ?_⟩
  · simp_rw [wGram_apply]
    exact integrable_finsetSum _ fun i _ => hc a b i
  · ext a b
    rw [matIntegral_apply, wGram_apply]
    simp_rw [wGram_apply]
    rw [integral_finsetSum _ fun i _ => hc a b i]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_mul_const, integral_const_mul, integral_complex_ofReal]
end Auto
