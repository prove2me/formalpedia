-- Prove2me | Definitions.Def_MarkovProcess_V3H_Kernel_Resolvent_f63a7282
-- name    : MarkovProcess_V3H_Kernel_Resolvent_f63a7282
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:36:42.88274+00:00
-- url     : https://prove2.me/theorems/909a1f3a-ea6a-4ade-a026-5d0ff0928610
-- title:
--   MarkovProcess: MarkovProcess_V3H_Kernel_Resolvent_f63a7282
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Kernel_Integral_2b459584
import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Definitions.Def_MarkovProcess_V3H_Kernel_Operator_8b41d3bf
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.ExpDecay
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
# Resolvents of kernel semigroups

This file defines the resolvent of a sub-Markov kernel semigroup on nonnegative extended-real
observables by Laplace transformation of its transition kernels.

Main definitions: `SubMarkovKernelSemigroup.kernelResolvent` and
`SubMarkovKernelSemigroup.kernelResolventReal`.

No conservativity, topology, or finiteness of the resolvent is asserted.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MarkovProcess.SubMarkovKernelSemigroup

variable {alpha : Type*} [MeasurableSpace alpha]

/-- The kernel resolvent on nonnegative extended-real observables. -/
noncomputable def kernelResolvent (P : SubMarkovKernelSemigroup alpha) (lam : ℝ)
    (f : alpha → ℝ≥0∞) (x : alpha) : ℝ≥0∞ :=
  ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) *
    ∫⁻ y, f y ∂(P (Real.toNNReal t) x)

/-- The kernel resolvent on real-valued observables.  Finiteness is established separately for
bounded observables at positive shifts. -/
noncomputable def kernelResolventReal (P : SubMarkovKernelSemigroup alpha) (lam : ℝ)
    (f : alpha → ℝ) (x : alpha) : ℝ :=
  ∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) *
    kernelIntegral (P (Real.toNNReal t)) f x











end MarkovProcess.SubMarkovKernelSemigroup


