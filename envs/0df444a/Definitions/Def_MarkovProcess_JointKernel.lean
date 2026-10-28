-- Prove2me | Definitions.Def_MarkovProcess_JointKernel
-- name    : MarkovProcess_JointKernel
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T14:39:21.045926+00:00
-- url     : https://prove2.me/theorems/ca9f4c0a-ff64-4be6-a710-fb67579d2a6b
-- title:
--   Jointly measurable time-space transition kernel
-- statement:
--   For a jointly measurable sub-Markov kernel semigroup P, its joint time-space transition kernel maps (t,x) to the transition measure P(t,x). The measurability proof is exactly the semigroup structure field. Source: Scott Armstrong MarkovProcess, Apache-2.0.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Kernel/Operator.lean#L1-L36

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcess_SubMarkovKernelSemigroup
import Mathlib.Probability.Kernel.Composition.Comp

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

end SubMarkovKernelSemigroup

end MarkovProcess


