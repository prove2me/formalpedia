-- Prove2me | Definitions.Def_MarkovProcess_V3H_Parameterized_Semigroup_5f8b28ce
-- name    : MarkovProcess_V3H_Parameterized_Semigroup_5f8b28ce
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:32:18.303032+00:00
-- url     : https://prove2.me/theorems/e715011b-3830-4d0c-b755-f9ae5c8fd238
-- title:
--   MarkovProcess: MarkovProcess_V3H_Parameterized_Semigroup_5f8b28ce
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Kernel_Basic_264434f5
import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Mathlib.Probability.Kernel.Composition.Comp

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Measurably parameterized sub-Markov kernel semigroups

This file packages sub-Markov kernel semigroups depending measurably on a parameter. The
measurability field is joint in parameter, time, and starting state, with carrier ordering
`Theta × (NNReal × alpha)`. Each fixed-parameter slice is an ordinary
`SubMarkovKernelSemigroup`.

No parameter family is selected here, and no concrete coefficient, domain, Feller, conservativity,
or stochastic-process assertion is made.
-/

open Set
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace MarkovProcess

open MeasureTheory ProbabilityTheory

/-- A jointly measurable parameter family of sub-Markov transition-kernel semigroups.

The kernel is jointly measurable on `Θ × (NNReal × α)`. Mathlib writes `η.comp κ` for
first applying `κ` and then `η`, so the Chapman--Kolmogorov field has the orientation
`K θ (s + t) = (K θ t).comp (K θ s)`.
-/
structure ParameterizedSubMarkovKernelSemigroup (Theta alpha : Type*)
    [MeasurableSpace Theta] [MeasurableSpace alpha] where
  /-- The transition kernel at a parameter and nonnegative time. -/
  kernel : Theta → NNReal → Kernel alpha alpha
  /-- Joint measurability in parameter, time, and starting state. -/
  measurable_kernel : Measurable fun q : Theta × (NNReal × alpha) ↦
    kernel q.1 q.2.1 q.2.2
  /-- At time zero every parameter slice is the identity kernel. -/
  kernel_zero : ∀ theta, kernel theta 0 = Kernel.id
  /-- The Chapman--Kolmogorov law, in Mathlib's kernel-composition orientation. -/
  kernel_add : ∀ theta s t, kernel theta (s + t) = (kernel theta t).comp (kernel theta s)
  /-- Every transition measure has mass at most one. -/
  isSubMarkovKernel : ∀ theta t, IsSubMarkovKernel (kernel theta t)

namespace ParameterizedSubMarkovKernelSemigroup

variable {Theta alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]

instance : CoeFun (ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (fun _ ↦ Theta → NNReal → Kernel alpha alpha) where
  coe P := P.kernel

/-- Two parameterized semigroups are equal when all their kernel slices are equal. -/
@[ext]
theorem ext {P Q : ParameterizedSubMarkovKernelSemigroup Theta alpha}
    (h : ∀ theta t, P theta t = Q theta t) : P = Q := by
  cases P with
  | mk P _ _ _ _ =>
    cases Q with
    | mk Q _ _ _ _ =>
      have hPQ : P = Q := funext fun theta ↦ funext fun t ↦ h theta t
      cases hPQ
      rfl

variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)

/-- The jointly measurable kernel with input ordered as parameter, then time and state. -/
def jointKernel : Kernel (Theta × (NNReal × alpha)) alpha where
  toFun q := P q.1 q.2.1 q.2.2
  measurable' := P.measurable_kernel

/-- Evaluation of the joint kernel is evaluation of the original parameter family. -/
@[simp]
theorem p2m_embedded_c956630c7a62aefd (q : Theta × (NNReal × alpha)) :
    P.jointKernel q = P q.1 q.2.1 q.2.2 :=
  rfl

/-- Evaluation of the joint kernel at an explicit parameter, time, and state. -/
@[simp]
theorem p2m_embedded_609018f0afa0f938 (theta : Theta) (t : NNReal) (x : alpha) :
    P.jointKernel (theta, (t, x)) = P theta t x :=
  rfl



/-- The ordinary sub-Markov kernel semigroup at one fixed parameter. -/
def toSubMarkovKernelSemigroup (theta : Theta) : SubMarkovKernelSemigroup alpha where
  kernel := P theta
  measurable_kernel := by
    have hPair : Measurable fun p : NNReal × alpha ↦ (theta, p) :=
      (measurable_const : Measurable fun _ : NNReal × alpha ↦ theta).prod measurable_id
    exact P.measurable_kernel.comp hPair
  kernel_zero := P.kernel_zero theta
  kernel_add := P.kernel_add theta
  isSubMarkovKernel := P.isSubMarkovKernel theta

/-- A fixed-parameter slice evaluates to the original parameterized kernel. -/
@[simp]
theorem p2m_embedded_9d7c469be6864e8e (theta : Theta) (t : NNReal) :
    toSubMarkovKernelSemigroup (P := P) theta t = P theta t :=
  rfl

/-- Every parameter slice is the identity kernel at time zero. -/
@[simp]
theorem zero (theta : Theta) : P theta 0 = Kernel.id :=
  P.kernel_zero theta

/-- The parameterwise Chapman--Kolmogorov law. -/
@[simp]
theorem add (theta : Theta) (s t : NNReal) :
    P theta (s + t) = (P theta t).comp (P theta s) :=
  P.kernel_add theta s t













end ParameterizedSubMarkovKernelSemigroup

end MarkovProcess


