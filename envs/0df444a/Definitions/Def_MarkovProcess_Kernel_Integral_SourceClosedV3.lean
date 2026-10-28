-- Prove2me | Definitions.Def_MarkovProcess_Kernel_Integral_SourceClosedV3
-- name    : MarkovProcess_Kernel_Integral_SourceClosedV3
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-28T12:41:11.743809+00:00
-- url     : https://prove2.me/theorems/9c13b7b9-5b31-4513-ad0b-a09fd958f2cd
-- title:
--   MarkovProcess definitions: Kernel.Integral
-- statement:
--   Scott Armstrong’s MarkovProcess library, module `MarkovProcess.Kernel.Integral`. This source-preserving bundle supplies the non-theorem declarations and definition-embedded lemmas used in the main Markov process formalisation.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Kernel/Integral.lean#L1-L59

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcess_Kernel_Basic_SourceClosedV3
import Mathlib.Probability.Kernel.Composition.Comp
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


