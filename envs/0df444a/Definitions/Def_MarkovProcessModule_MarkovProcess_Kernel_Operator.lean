-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_Kernel_Operator
-- name    : MarkovProcessModule_MarkovProcess_Kernel_Operator
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T19:53:23.408547+00:00
-- url     : https://prove2.me/theorems/83aa8fb8-7f11-4f4d-b814-0f8c4707ac16
-- title:
--   MarkovProcess.Kernel.Operator
-- statement:
--   # Operators associated with a sub-Markov kernel semigroup
--
--   This file constructs the jointly measurable time-space kernel and the
--   canonical contractive operator families on real `Lᵖ`.  It deliberately makes
--   no claim here about the operator semigroup laws or strong continuity.
--
--   Complete pinned Lean module MarkovProcess.Kernel.Operator by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Kernel/Operator.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_Kernel_KernelSemigroup
import Definitions.Def_MarkovProcessModule_MarkovProcess_Kernel_Lp

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

@[simp]
theorem jointKernel_apply (p : NNReal × α) : P.jointKernel p = P p.1 p.2 :=
  rfl

/-- Joint strong measurability of the raw kernel integral. -/
theorem stronglyMeasurable_kernelIntegral {f : α → ℝ}
    (hf : StronglyMeasurable f) :
    StronglyMeasurable fun p : NNReal × α ↦ kernelIntegral (P p.1) f p.2 := by
  exact hf.integral_kernel (κ := P.jointKernel)

/-- Joint measurability of the raw kernel integral. -/
theorem measurable_kernelIntegral {f : α → ℝ} (hf : Measurable f) :
    Measurable fun p : NNReal × α ↦ kernelIntegral (P p.1) f p.2 :=
  (P.stronglyMeasurable_kernelIntegral hf.stronglyMeasurable).measurable

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

/-- The canonical finite-exponent family is associated with `P`. -/
theorem isAssociatedFinite_operatorFinite (μ : Measure α) (hμ : P.IsSubInvariant μ)
    (p : NNReal) [Fact (1 ≤ p)] :
    P.IsAssociatedFinite μ p (P.operatorFinite μ hμ p) := by
  intro t f
  exact coeFn_kernelLpFinite μ (P t) (P.isSubMarkovKernel t) (hμ t) p f

/-- The canonical infinite-exponent family is associated with `P`. -/
theorem isAssociatedTop_operatorTop (μ : Measure α) (hμ : P.IsSubInvariant μ) :
    P.IsAssociatedTop μ (P.operatorTop μ hμ) := by
  intro t f
  exact coeFn_kernelLpTop μ (P t) (P.isSubMarkovKernel t) (hμ t) f

/-- Every time slice of the canonical finite-exponent family has norm at most
one. -/
theorem norm_operatorFinite_le (μ : Measure α) (hμ : P.IsSubInvariant μ)
    (p : NNReal) [Fact (1 ≤ p)] (t : NNReal) :
    ‖P.operatorFinite μ hμ p t‖ ≤ 1 :=
  norm_kernelLpFinite_le μ (P t) (P.isSubMarkovKernel t) (hμ t) p

/-- Every time slice of the canonical infinite-exponent family has norm at
most one. -/
theorem norm_operatorTop_le (μ : Measure α) (hμ : P.IsSubInvariant μ)
    (t : NNReal) : ‖P.operatorTop μ hμ t‖ ≤ 1 :=
  norm_kernelLpTop_le μ (P t) (P.isSubMarkovKernel t) (hμ t)

end SubMarkovKernelSemigroup

end MarkovProcess


