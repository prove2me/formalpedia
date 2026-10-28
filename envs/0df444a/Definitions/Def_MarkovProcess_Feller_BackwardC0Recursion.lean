-- Prove2me | Definitions.Def_MarkovProcess_Feller_BackwardC0Recursion
-- name    : MarkovProcess_Feller_BackwardC0Recursion
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-28T12:56:35.195991+00:00
-- url     : https://prove2.me/theorems/7a4fc151-4382-4c86-a6c0-229e99140890
-- title:
--   MarkovProcess definitions: Feller.BackwardC0Recursion
-- statement:
--   Scott Armstrong’s MarkovProcess library, module `MarkovProcess.Feller.BackwardC0Recursion`. This source-preserving bundle supplies the non-theorem declarations and definition-embedded lemmas used in the main Markov process formalisation.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Feller/BackwardC0Recursion.lean#L1-L87

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcess_Feller_Semigroup
import Definitions.Def_MarkovProcess_FiniteTime_Kernel
import Definitions.Def_MarkovProcess_Kernel_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_C0_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_Integral_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_KernelSemigroup_SourceClosedV3
import Definitions.Def_MarkovProcess_Semigroup_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Time_FiniteOrderedTimes
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-!
# Backward `C₀` recursion for finite Feller transitions

An ordered nonempty family of one-coordinate `C₀` factors determines a backward semigroup
recursion: evolve the last factors relative to the first time, multiply by the first factor, and
then evolve from the starting state to the first time.  The recursion varies continuously in the
`C₀` norm when every ordered observation time converges.

This file contains only the analytic recursion and its continuity.  Its identification with an
integral against a finite-time kernel is in `Feller/BackwardC0Integral.lean`; no statement about
path space is proved here.
-/

open Filter Topology
open scoped NNReal ZeroAtInfty

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]

/-- Backward semigroup recursion for a nonempty ordered family of coordinatewise `C₀` factors. -/
noncomputable def IsFellerKernelSemigroup.backwardC0
    {P : SubMarkovKernelSemigroup alpha} (hP : P.IsFellerKernelSemigroup) :
    {n : ℕ} → FiniteOrderedTimes (n + 1) →
      (Fin (n + 1) → C₀(alpha, ℝ)) → C₀(alpha, ℝ)
  | 0, times, factors => hP.c0Semigroup (times 0) (factors 0)
  | _n + 1, times, factors =>
      hP.c0Semigroup (times 0)
        (factors 0 * hP.backwardC0 times.relativeTail (Fin.tail factors))







end SubMarkovKernelSemigroup
end MarkovProcess


