-- Prove2me | Definitions.Def_BasicResults_Spectral_MultiplicationOperator
-- name    : BasicResults_Spectral_MultiplicationOperator
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:27:07.265262+00:00
-- url     : https://prove2.me/theorems/db799f17-8cc6-4223-a99d-6398722aae04
-- title:
--   Multiplication Operator
-- statement:
--   Definitions and structural lemmas for Multiplication Operator, from Mario Ullrich (mario-ullrich/Lean-SNumbers; see pinned Apache-2.0 LICENSE and source headers)'s pinned Pietsch axiomatic theory of s-numbers and maximal difference bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/MultiplicationOperator.lean

module
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.Holder
set_option autoImplicit true
@[expose] public section
@[expose] public section
open scoped ENNReal NNReal
open MeasureTheory
namespace MeasureTheory
variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
variable {𝕜 : Type*} [RCLike 𝕜]
noncomputable def mulL2 (f : α → 𝕜) (hf : MemLp f ⊤ μ) : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ :=
  (ContinuousLinearMap.mul 𝕜 𝕜).holderL μ ⊤ 2 2 (hf.toLp f)
theorem memLp_mul_top {f g : α → 𝕜} (hf : MemLp f ⊤ μ) (hg : MemLp g ⊤ μ) :
    MemLp (f * g) ⊤ μ :=
  MemLp.mul hg hf
end MeasureTheory


