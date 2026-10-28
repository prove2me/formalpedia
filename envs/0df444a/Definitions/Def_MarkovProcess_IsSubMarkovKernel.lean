-- Prove2me | Definitions.Def_MarkovProcess_IsSubMarkovKernel
-- name    : MarkovProcess_IsSubMarkovKernel
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T13:11:54.008111+00:00
-- url     : https://prove2.me/theorems/1931a999-8111-4fb9-916a-8481c4ec16ef
-- title:
--   Sub-Markov kernels: transition measures with mass at most one
-- statement:
--   For measurable spaces alpha and beta, define an alpha-to-beta Markov kernel to be sub-Markov when the total mass of its output measure is at most one at every starting state. This basic definition enables killed kernels and sub-Markov transition semigroups. Ported directly from Scott Armstrong's MarkovProcess (Apache-2.0) without altering the definition.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Kernel/Basic.lean#L1-L29

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Probability.Kernel.Composition.Comp

/-!
# Sub-Markov kernels

This file records the elementary mass algebra of sub-Markov kernels.  It does
not define transition families or connect kernels to operator semigroups or
stochastic processes.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace MarkovProcess

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- A kernel is sub-Markov if each of its measures has total mass at most one. -/
def IsSubMarkovKernel (κ : ProbabilityTheory.Kernel α β) : Prop :=
  ∀ x, κ x Set.univ ≤ 1


end MarkovProcess


