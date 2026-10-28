-- Prove2me | Definitions.Def_MarkovProcess_KernelIntegral
-- name    : MarkovProcess_KernelIntegral
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T13:17:36.561911+00:00
-- url     : https://prove2.me/theorems/dec57481-88cd-4d2a-85de-225d5ce7b35c
-- title:
--   Real-valued integration against a transition kernel
-- statement:
--   Define kernelIntegral κ f x as the real integral of f with respect to the measure κ x. It is the basic operator used to study sub-Markov transition semigroups, killed processes, and their resolvents. Exact source definition from Scott Armstrong, MarkovProcess, Apache-2.0.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Kernel/Integral.lean#L1-L27

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcess_IsSubMarkovKernel
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# Integration against a kernel

This file defines the raw real-valued integral operator associated with a
kernel.  Subinvariance of a measure makes this operator independent, almost
everywhere, of the chosen representative of its input.
-/

open MeasureTheory
open ProbabilityTheory

namespace MarkovProcess

variable {α : Type*} [MeasurableSpace α]

/-- The raw real-valued integral of `f` against the measure `κ x`. -/
noncomputable def kernelIntegral (κ : Kernel α α) (f : α → ℝ) (x : α) : ℝ :=
  ∫ y, f y ∂κ x


end MarkovProcess


