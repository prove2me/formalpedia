-- Prove2me | Definitions.Def_MarkovProcess_Kernel_KernelSemigroup_SourceClosedV3
-- name    : MarkovProcess_Kernel_KernelSemigroup_SourceClosedV3
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-28T12:41:07.113189+00:00
-- url     : https://prove2.me/theorems/c9d6476b-53c6-4cae-bcf6-808e4e40a796
-- title:
--   MarkovProcess definitions: Kernel.KernelSemigroup
-- statement:
--   Scott Armstrong’s MarkovProcess library, module `MarkovProcess.Kernel.KernelSemigroup`. This source-preserving bundle supplies the non-theorem declarations and definition-embedded lemmas used in the main Markov process formalisation.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Kernel/KernelSemigroup.lean#L1-L127

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcess_Kernel_Basic_SourceClosedV3
import Mathlib.Probability.Kernel.Composition.Comp

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



variable (P : SubMarkovKernelSemigroup α)





@[simp]
theorem zero : P 0 = Kernel.id :=
  P.kernel_zero

@[simp]
theorem add (s t : NNReal) : P (s + t) = (P t).comp (P s) :=
  P.kernel_add s t













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


