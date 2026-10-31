-- Prove2me | Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
-- name    : MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:27:49.920204+00:00
-- url     : https://prove2.me/theorems/9bc3cdb2-65d3-4cdf-be51-380d5cc88413
-- title:
--   MarkovProcess: MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Kernel_Basic_264434f5
import Mathlib.Probability.Kernel.Composition.Comp

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Sub-Markov transition-kernel semigroups

This file packages jointly measurable, nonnegative-time transition kernels with
the Chapman--Kolmogorov law.  Mathlib writes `η.comp κ` for first applying `κ`
and then `η`; consequently the law below is `K (s + t) = (K t).comp (K s)`.

Conservativity is deliberately a separate predicate.  A killed transition
family has mass at most one, while a conservative family has mass exactly one.
-/

open Set
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace MarkovProcess

open MeasureTheory ProbabilityTheory

/-- A jointly measurable sub-Markov transition-kernel semigroup.

The measurability field is joint in time and starting point.  The composition
orientation agrees with the convention that the operator associated with a
kernel `K` sends `f` to `x ↦ ∫ y, f y ∂K x`.
-/
structure SubMarkovKernelSemigroup (α : Type*) [MeasurableSpace α] where
  /-- The transition kernel at a nonnegative time. -/
  kernel : NNReal → Kernel α α
  /-- Joint measurability in time and starting point. -/
  measurable_kernel : Measurable fun p : NNReal × α ↦ kernel p.1 p.2
  /-- At time zero the transition kernel is the identity kernel. -/
  kernel_zero : kernel 0 = Kernel.id
  /-- The Chapman--Kolmogorov law, in Mathlib's kernel-composition orientation. -/
  kernel_add : ∀ s t, kernel (s + t) = (kernel t).comp (kernel s)
  /-- Every transition measure has mass at most one. -/
  isSubMarkovKernel : ∀ t, IsSubMarkovKernel (kernel t)

namespace SubMarkovKernelSemigroup

variable {α : Type*} [MeasurableSpace α]

instance : CoeFun (SubMarkovKernelSemigroup α)
    (fun _ ↦ NNReal → Kernel α α) where
  coe P := P.kernel

@[ext]
theorem ext {P Q : SubMarkovKernelSemigroup α}
    (h : ∀ t, P t = Q t) : P = Q := by
  cases P with
  | mk P _ _ _ _ =>
    cases Q with
    | mk Q _ _ _ _ =>
      have hPQ : P = Q := funext h
      cases hPQ
      rfl

variable (P : SubMarkovKernelSemigroup α)

/-- The transition measures are jointly measurable in time and starting point. -/
theorem measurable_toMeasure : Measurable fun p : NNReal × α ↦ P p.1 p.2 :=
  P.measurable_kernel

/-- Evaluation on a measurable set is jointly measurable in time and start. -/
theorem measurable_measure {s : Set α} (hs : MeasurableSet s) :
    Measurable fun p : NNReal × α ↦ P p.1 p.2 s :=
  (Measure.measurable_coe hs).comp P.measurable_toMeasure

@[simp]
theorem zero : P 0 = Kernel.id :=
  P.kernel_zero

@[simp]
theorem add (s t : NNReal) : P (s + t) = (P t).comp (P s) :=
  P.kernel_add s t







/-- The tower form of Chapman--Kolmogorov for nonnegative measurable functions. -/
theorem lintegral_add (s t : NNReal) (x : α) {f : α → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ y, f y ∂P (s + t) x = ∫⁻ y, ∫⁻ z, f z ∂P t y ∂P s x := by
  rw [P.add, Kernel.lintegral_comp _ _ _ hf]

/-- Every transition measure has mass at most one. -/
theorem measure_univ_le_one (t : NNReal) (x : α) : P t x univ ≤ 1 :=
  P.isSubMarkovKernel t x



/-- A transition-kernel semigroup is conservative when no mass is lost. -/
def IsConservative : Prop :=
  ∀ t x, P t x univ = 1

namespace IsConservative

/-- At each time, a conservative transition family is a Mathlib Markov kernel. -/
theorem isMarkovKernel {P : SubMarkovKernelSemigroup α} (hP : P.IsConservative)
    (t : NNReal) : IsMarkovKernel (P t) where
  isProbabilityMeasure x := ⟨hP t x⟩

end IsConservative

end SubMarkovKernelSemigroup

end MarkovProcess


