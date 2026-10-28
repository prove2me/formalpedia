-- Prove2me | Definitions.Def_MarkovProcess_KernelResolvents
-- name    : MarkovProcess_KernelResolvents
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T14:35:26.720238+00:00
-- url     : https://prove2.me/theorems/ebbe45a0-a17b-4919-b72e-cf1f38196b01
-- title:
--   Nonnegative and real kernel resolvents of a sub-Markov semigroup
-- statement:
--   The kernel resolvents are the Laplace transforms in nonnegative time of a sub-Markov kernel semigroup applied to an observable. Both extended-nonnegative and real-valued forms are defined without extra boundedness or finiteness claims. Source-faithful port from Scott Armstrong, MarkovProcess, Apache-2.0.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Kernel/Resolvent.lean#L1-L40

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.ExpDecay
import Definitions.Def_MarkovProcess_SubMarkovKernelSemigroup
import Definitions.Def_MarkovProcess_KernelIntegral

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


