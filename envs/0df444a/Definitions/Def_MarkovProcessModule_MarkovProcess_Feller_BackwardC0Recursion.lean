-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_Feller_BackwardC0Recursion
-- name    : MarkovProcessModule_MarkovProcess_Feller_BackwardC0Recursion
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T19:57:31.665313+00:00
-- url     : https://prove2.me/theorems/538d0f46-5445-43a0-9b18-15b24023797e
-- title:
--   MarkovProcess.Feller.BackwardC0Recursion
-- statement:
--   # Backward `C₀` recursion for finite Feller transitions
--
--   An ordered nonempty family of one-coordinate `C₀` factors determines a backward semigroup
--   recursion: evolve the last factors relative to the first time, multiply by the first factor, and
--   then evolve from the starting state to the first time.  The recursion varies continuously in the
--   `C₀` norm when every ordered observation time converges.
--
--   This file contains only the analytic recursion and its continuity.  Its identification with an
--   integral against a finite-time kernel is in `Feller/BackwardC0Integral.lean`; no statement about
--   path space is proved here.
--
--   Complete pinned Lean module MarkovProcess.Feller.BackwardC0Recursion by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Feller/BackwardC0Recursion.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_Feller_FiniteTimeKernelContinuity
import Definitions.Def_MarkovProcessModule_MarkovProcess_FiniteTime_Kernel

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
theorem IsFellerKernelSemigroup.tendsto_backwardC0
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
      exact hP.c0Semigroup.tendsto_apply_of_tendsto (ht 0) tendsto_const_nhds
  | succ n ih =>
      have htail : ∀ i, Tendsto (fun a ↦ (times a).relativeTail i) l
          (nhds (times0.relativeTail i)) := by
        intro i
        simpa only [FiniteOrderedTimes.relativeTail_apply] using
          (ht i.succ).sub (ht 0)
      have hinner := ih htail (Fin.tail factors)
      simp only [backwardC0_succ]
      exact hP.c0Semigroup.tendsto_apply_of_tendsto (ht 0)
        (tendsto_const_nhds.mul hinner)

end SubMarkovKernelSemigroup
end MarkovProcess


