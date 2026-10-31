-- Prove2me | Definitions.Def_MarkovProcess_V3H_Feller_BackwardC0Recursion_bbf80ad3
-- name    : MarkovProcess_V3H_Feller_BackwardC0Recursion_bbf80ad3
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:36:32.759668+00:00
-- url     : https://prove2.me/theorems/01c9a87d-8eae-4092-9074-ec447d0c41f2
-- title:
--   MarkovProcess: MarkovProcess_V3H_Feller_BackwardC0Recursion_bbf80ad3
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Feller_FiniteTimeKernelContinuity_b2a7d2a7
import Definitions.Def_MarkovProcess_V3H_Feller_Semigroup_2cfe612a
import Definitions.Def_MarkovProcess_V3H_FiniteTime_Kernel_7ce8d73d
import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Definitions.Def_MarkovProcess_V3H_Semigroup_Basic_fec91841
import Definitions.Def_MarkovProcess_V3H_Time_FiniteOrderedTimes_717796dd
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

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

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

/-- The backward recursion for a singleton family is one Feller-semigroup application. -/
@[simp]
theorem IsFellerKernelSemigroup.backwardC0_zero
    {P : SubMarkovKernelSemigroup alpha} (hP : P.IsFellerKernelSemigroup)
    (times : FiniteOrderedTimes 1) (factors : Fin 1 → C₀(alpha, ℝ)) :
    hP.backwardC0 times factors = hP.c0Semigroup (times 0) (factors 0) :=
  rfl

/-- At a successor length, the backward recursion multiplies the first factor by the recursively
evolved relative tail before applying the first transition. -/
@[simp]
theorem IsFellerKernelSemigroup.backwardC0_succ
    {P : SubMarkovKernelSemigroup alpha} (hP : P.IsFellerKernelSemigroup)
    {n : ℕ} (times : FiniteOrderedTimes (n + 2))
    (factors : Fin (n + 2) → C₀(alpha, ℝ)) :
    hP.backwardC0 times factors = hP.c0Semigroup (times 0)
      (factors 0 * hP.backwardC0 times.relativeTail (Fin.tail factors)) :=
  rfl

/-- The backward recursion is continuous in the `C₀` norm under coordinatewise convergence of a
nonempty ordered time family. -/
theorem IsFellerKernelSemigroup.p2m_embedded_fd22dc65d7d96e91
    {P : SubMarkovKernelSemigroup alpha} (hP : P.IsFellerKernelSemigroup)
    {X : Type*} {l : Filter X} {n : ℕ}
    {times : X → FiniteOrderedTimes (n + 1)}
    {times0 : FiniteOrderedTimes (n + 1)}
    (ht : ∀ i, Tendsto (fun a ↦ times a i) l (nhds (times0 i)))
    (factors : Fin (n + 1) → C₀(alpha, ℝ)) :
    Tendsto (fun a ↦ hP.backwardC0 (times a) factors) l
      (nhds (hP.backwardC0 times0 factors)) := by
  induction n with
  | zero =>
      simp only [backwardC0_zero]
      exact hP.c0Semigroup.p2m_embedded_0957dd8f4e4395ee (ht 0) tendsto_const_nhds
  | succ n ih =>
      have htail : ∀ i, Tendsto (fun a ↦ (times a).relativeTail i) l
          (nhds (times0.relativeTail i)) := by
        intro i
        simpa only [FiniteOrderedTimes.relativeTail_apply] using
          (ht i.succ).sub (ht 0)
      have hinner := ih htail (Fin.tail factors)
      simp only [backwardC0_succ]
      exact hP.c0Semigroup.p2m_embedded_0957dd8f4e4395ee (ht 0)
        (tendsto_const_nhds.mul hinner)

end SubMarkovKernelSemigroup
end MarkovProcess


