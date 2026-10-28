-- Prove2me | Definitions.Def_MarkovProcess_Kernel_Basic_SourceClosedV3
-- name    : MarkovProcess_Kernel_Basic_SourceClosedV3
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-28T12:37:16.334607+00:00
-- url     : https://prove2.me/theorems/e7f897b6-db8b-4aaf-9df3-de482c105746
-- title:
--   MarkovProcess definitions: Kernel.Basic
-- statement:
--   Scott Armstrong’s MarkovProcess library, module `MarkovProcess.Kernel.Basic`. This source-preserving bundle supplies the non-theorem declarations and definition-embedded lemmas used in the main Markov process formalisation.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Kernel/Basic.lean#L1-L75

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

namespace IsSubMarkovKernel

open ProbabilityTheory

variable {κ : Kernel α β} {η : Kernel β γ}





/-- A sub-Markov kernel is a finite kernel. -/
theorem isFiniteKernel (hκ : IsSubMarkovKernel κ) : IsFiniteKernel κ :=
  ⟨⟨1, ENNReal.one_lt_top, hκ⟩⟩









end IsSubMarkovKernel

end MarkovProcess


