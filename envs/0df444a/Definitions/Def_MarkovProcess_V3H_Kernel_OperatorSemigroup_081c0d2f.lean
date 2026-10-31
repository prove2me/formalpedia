-- Prove2me | Definitions.Def_MarkovProcess_V3H_Kernel_OperatorSemigroup_081c0d2f
-- name    : MarkovProcess_V3H_Kernel_OperatorSemigroup_081c0d2f
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:36:45.374486+00:00
-- url     : https://prove2.me/theorems/1c742481-59c3-4d5a-8820-feeaad467368
-- title:
--   MarkovProcess: MarkovProcess_V3H_Kernel_OperatorSemigroup_081c0d2f
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Kernel_Operator_8b41d3bf
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
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
# Semigroup laws for the canonical kernel operators

This file proves only the algebraic zero- and add-time laws for the canonical
real `Lᵖ` operator families.  It makes no strong-continuity claim.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

namespace MarkovProcess

variable {α : Type*} [MeasurableSpace α]

namespace SubMarkovKernelSemigroup

variable (P : SubMarkovKernelSemigroup α)

private instance fact_one_le_coe_nnreal (p : NNReal) [Fact (1 ≤ p)] :
    Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast Fact.out⟩



















end SubMarkovKernelSemigroup

end MarkovProcess


