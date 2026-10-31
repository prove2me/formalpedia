-- Prove2me | Definitions.Def_MarkovProcess_V3H_Kernel_Operator_8b41d3bf
-- name    : MarkovProcess_V3H_Kernel_Operator_8b41d3bf
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:36:01.088971+00:00
-- url     : https://prove2.me/theorems/e595084d-b682-4e80-9ad1-0cf00f438630
-- title:
--   MarkovProcess: MarkovProcess_V3H_Kernel_Operator_8b41d3bf
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Kernel_Integral_2b459584
import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Definitions.Def_MarkovProcess_V3H_Kernel_Lp_4fe2b873
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableIntegral

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Operators associated with a sub-Markov kernel semigroup

This file constructs the jointly measurable time-space kernel and the
canonical contractive operator families on real `Lᵖ`.  It deliberately makes
no claim here about the operator semigroup laws or strong continuity.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

namespace MarkovProcess

variable {α : Type*} [MeasurableSpace α]

namespace SubMarkovKernelSemigroup

variable (P : SubMarkovKernelSemigroup α)

/-- The time-space kernel obtained from the jointly measurable transition
measures of `P`. -/
def jointKernel : Kernel (NNReal × α) α where
  toFun p := P p.1 p.2
  measurable' := P.measurable_kernel







/-- A measure is subinvariant for `P` when it dominates its image under every
transition kernel. -/
def IsSubInvariant (μ : Measure α) : Prop :=
  ∀ t, P t ∘ₘ μ ≤ μ

private instance fact_one_le_coe_nnreal (p : NNReal) [Fact (1 ≤ p)] :
    Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast Fact.out⟩

/-- The canonical finite-exponent operator family associated with `P`. -/
noncomputable def operatorFinite (μ : Measure α) (hμ : P.IsSubInvariant μ)
    (p : NNReal) [Fact (1 ≤ p)] :
    NNReal → Lp ℝ (p : ℝ≥0∞) μ →L[ℝ] Lp ℝ (p : ℝ≥0∞) μ :=
  fun t ↦ kernelLpFinite μ (P t) (P.isSubMarkovKernel t) (hμ t) p

/-- The canonical infinite-exponent operator family associated with `P`. -/
noncomputable def operatorTop (μ : Measure α) (hμ : P.IsSubInvariant μ) :
    NNReal → Lp ℝ ∞ μ →L[ℝ] Lp ℝ ∞ μ :=
  fun t ↦ kernelLpTop μ (P t) (P.isSubMarkovKernel t) (hμ t)

/-- A finite-exponent operator family is associated with `P` when each output
is represented by the corresponding raw kernel integral. -/
def IsAssociatedFinite (μ : Measure α) (p : NNReal) [Fact (1 ≤ p)]
    (T : NNReal → Lp ℝ (p : ℝ≥0∞) μ →L[ℝ] Lp ℝ (p : ℝ≥0∞) μ) : Prop :=
  ∀ t f, T t f =ᵐ[μ] kernelIntegral (P t) f

/-- An infinite-exponent operator family is associated with `P` when each
output is represented by the corresponding raw kernel integral. -/
def IsAssociatedTop (μ : Measure α)
    (T : NNReal → Lp ℝ ∞ μ →L[ℝ] Lp ℝ ∞ μ) : Prop :=
  ∀ t f, T t f =ᵐ[μ] kernelIntegral (P t) f









end SubMarkovKernelSemigroup

end MarkovProcess


