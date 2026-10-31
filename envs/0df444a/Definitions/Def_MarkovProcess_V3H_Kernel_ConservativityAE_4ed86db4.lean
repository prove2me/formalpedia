-- Prove2me | Definitions.Def_MarkovProcess_V3H_Kernel_ConservativityAE_4ed86db4
-- name    : MarkovProcess_V3H_Kernel_ConservativityAE_4ed86db4
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:36:38.739085+00:00
-- url     : https://prove2.me/theorems/493ad6c5-6c9c-4719-a900-d7c6da0a5de3
-- title:
--   MarkovProcess: MarkovProcess_V3H_Kernel_ConservativityAE_4ed86db4
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Definitions.Def_MarkovProcess_V3H_Kernel_Lp_4fe2b873
import Definitions.Def_MarkovProcess_V3H_Kernel_Operator_8b41d3bf
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
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
# Conservativity from preservation of constants

This file extracts the measure-theoretic conservativity consequence of an
associated `L∞` operator that preserves the constant-one class.  The conclusion
is initially almost everywhere in the starting point.  Continuity of the
transition mass and positivity of the reference measure on nonempty open sets
upgrade it to pointwise conservativity.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

namespace MarkovProcess

variable {α : Type*} [MeasurableSpace α]

/-- The constant-one class in `L∞`, available without a finiteness assumption
on the reference measure. -/
noncomputable def oneLpTop (μ : Measure α) : Lp ℝ ∞ μ :=
  (memLp_top_const (μ := μ) (1 : ℝ)).toLp (fun _ : α => (1 : ℝ))



namespace SubMarkovKernelSemigroup

variable (P : SubMarkovKernelSemigroup α)

/-- Conservativity almost everywhere in the starting point, relative to `μ`. -/
def IsConservativeAE (μ : Measure α) : Prop :=
  ∀ t, ∀ᵐ x ∂μ, P t x Set.univ = 1

/-- An `L∞` operator family preserves the constant-one equivalence class. -/
def PreservesOneTop (μ : Measure α)
    (T : NNReal → Lp ℝ ∞ μ →L[ℝ] Lp ℝ ∞ μ) : Prop :=
  ∀ t, T t (oneLpTop μ) = oneLpTop μ







end SubMarkovKernelSemigroup

end MarkovProcess


