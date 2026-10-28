-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_FiniteTime_KernelMixedPullback
-- name    : MarkovProcessModule_MarkovProcess_FiniteTime_KernelMixedPullback
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T20:05:55.734614+00:00
-- url     : https://prove2.me/theorems/b6f0abbf-333c-4718-8a1e-fe59e6f34676
-- title:
--   MarkovProcess.FiniteTime.KernelMixedPullback
-- statement:
--   # Pulling a finite-time concatenation back to mixed labels
--
--   This file records the reindexing step after an ordered finite-dimensional law has been split at
--   a designated cut.  A mixed label may select a past coordinate, a strict-future coordinate, or
--   the terminal past coordinate.  The last alternative permits a future-zero label to duplicate a
--   terminal past label without requiring either label to be present.
--
--   The result is pure finite-dimensional Chapman--Kolmogorov algebra.  In particular it has no
--   continuity, density, path-space, or Feller hypothesis.
--
--   Complete pinned Lean module MarkovProcess.FiniteTime.KernelMixedPullback by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/FiniteTime/KernelMixedPullback.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_FiniteTime_KernelConcatenation

/-!
# Pulling a finite-time concatenation back to mixed labels

This file records the reindexing step after an ordered finite-dimensional law has been split at
a designated cut.  A mixed label may select a past coordinate, a strict-future coordinate, or
the terminal past coordinate.  The last alternative permits a future-zero label to duplicate a
terminal past label without requiring either label to be present.

The result is pure finite-dimensional Chapman--Kolmogorov algebra.  In particular it has no
continuity, density, path-space, or Feller hypothesis.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

variable {alpha pastLabel futureLabel : Type*} [MeasurableSpace alpha]

/-- Pull a split finite path back to arbitrary past and future label types.  `none` selects the
terminal past coordinate; this is the coordinate used by a future label representing elapsed
time zero. -/
def pullbackSplitFinitePath {m n : ℕ}
    (pastIndex : pastLabel → Fin (m + 1))
    (futureIndex : futureLabel → Option (Fin n))
    (z : (Fin (m + 1) → alpha) × (Fin n → alpha)) :
    pastLabel ⊕ futureLabel → alpha
  | Sum.inl i => z.1 (pastIndex i)
  | Sum.inr j => (futureIndex j).elim (z.1 (Fin.last m)) z.2

/-- Pullback to mixed labels is measurable, including when either label type is empty and when
several labels select the terminal coordinate. -/
theorem measurable_pullbackSplitFinitePath {m n : ℕ}
    (pastIndex : pastLabel → Fin (m + 1))
    (futureIndex : futureLabel → Option (Fin n)) :
    Measurable
      (pullbackSplitFinitePath (alpha := alpha) pastIndex futureIndex) := by
  rw [measurable_pi_iff]
  rintro (i | j)
  · exact (measurable_pi_apply (pastIndex i)).comp measurable_fst
  · cases h : futureIndex j with
    | none =>
        simpa only [pullbackSplitFinitePath, h] using!
          ((measurable_pi_apply (Fin.last m)).comp measurable_fst)
    | some k =>
        simpa only [pullbackSplitFinitePath, h] using!
          ((measurable_pi_apply k).comp measurable_snd)

namespace IsConservative

/-- Concatenation at an ordered cut remains valid after pulling the two pieces back to arbitrary
mixed labels.  Mapping a future label to `none` reads the cut coordinate from the past, so the
theorem directly permits simultaneous terminal-past/future-zero observations. -/
theorem finiteTimeKernel_map_pullbackSplitFinitePath
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (m n : ℕ) (times : FiniteOrderedTimes (n + (m + 1)))
    (pastIndex : pastLabel → Fin (m + 1))
    (futureIndex : futureLabel → Option (Fin n)) :
    (finiteTimeKernel P times).map
        (pullbackSplitFinitePath (alpha := alpha) pastIndex futureIndex ∘
          splitFinitePath (alpha := alpha) (m := m) (n := n)) =
      (finiteTimeKernel P (FiniteOrderedTimes.initialSegment times) ⊗ₖ
        (finiteTimeKernel P (FiniteOrderedTimes.relativeFinalSegment times)).comap
          (splitPastTerminal (alpha := alpha) (m := m))
          measurable_splitPastTerminal).map
        (pullbackSplitFinitePath (alpha := alpha) pastIndex futureIndex) := by
  rw [Kernel.map_comp_right]
  · rw [hP.finiteTimeKernel_map_splitFinitePath P m n times]
  · exact measurable_splitFinitePath
  · exact measurable_pullbackSplitFinitePath pastIndex futureIndex

end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess


