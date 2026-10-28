-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_Trajectory_FellerCountableStoppingRestart
-- name    : MarkovProcessModule_MarkovProcess_Trajectory_FellerCountableStoppingRestart
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T21:16:33.872981+00:00
-- url     : https://prove2.me/theorems/bcc0c255-c4d8-4be3-a37e-d72a8d9ad3ee
-- title:
--   MarkovProcess.Trajectory.FellerCountableStoppingRestart
-- statement:
--   # Conditional restart of the Feller trajectory at countable-range stopping times
--
--   For a finite `NNReal`-valued stopping time with countable range, the conditional expectation of a
--   bounded strongly measurable functional of the canonical Feller trajectory shifted at that time,
--   given the stopped sigma-algebra, is the path-kernel expectation started from the state at that
--   time.  The proof feeds the all-time event-restricted deterministic restart identity into the
--   generic countable-range stopping-time bridge.
--
--   The stopping time here has countable range.  An arbitrary finite stopping time is covered in
--   `Trajectory/FellerStoppingConditional.lean`, and a `WithTop`-valued time that can be infinite in
--   `Trajectory/StoppingLtTop.lean`.
--
--   Complete pinned Lean module MarkovProcess.Trajectory.FellerCountableStoppingRestart by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Trajectory/FellerCountableStoppingRestart.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_Trajectory_FellerRestrictedRestart
import Definitions.Def_MarkovProcessModule_MarkovProcess_Restart_CountableStoppingRestart

/-!
# Conditional restart of the Feller trajectory at countable-range stopping times

For a finite `NNReal`-valued stopping time with countable range, the conditional expectation of a
bounded strongly measurable functional of the canonical Feller trajectory shifted at that time,
given the stopped sigma-algebra, is the path-kernel expectation started from the state at that
time.  The proof feeds the all-time event-restricted deterministic restart identity into the
generic countable-range stopping-time bridge.

The stopping time here has countable range.  An arbitrary finite stopping time is covered in
`Trajectory/FellerStoppingConditional.lean`, and a `WithTop`-valued time that can be infinite in
`Trajectory/StoppingLtTop.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess.SubMarkovKernelSemigroup
noncomputable section
open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]

/-- At a finite stopping time with countable range, the conditional expectation of a bounded
functional of the shifted Feller trajectory given the stopped sigma-algebra is its path-kernel
expectation started from the state at that time. -/
theorem IsFellerKernelSemigroup.continuousPathTrajectory_condExp_shift_countableStoppingTime
    (P : SubMarkovKernelSemigroup alpha) (hFeller : P.IsFellerKernelSemigroup)
    (hP : P.IsConservative) (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (x : alpha) (tau : ContinuousPath alpha → NNReal)
    (htau : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦ (tau omega : WithTop NNReal)))
    (htauRange : (Set.range tau).Countable)
    (F : ContinuousPath alpha → E) (hF : StronglyMeasurable F)
    (C : ℝ) (hFC : ∀ eta, ‖F eta‖ ≤ C) :
    ((continuousPathTrajectory P hP default) x)[fun omega ↦
        F (ContinuousPath.shift (tau omega) omega)|htau.measurableSpace] =ᵐ[
      (continuousPathTrajectory P hP default) x]
      fun omega ↦ ∫ eta, F eta ∂(continuousPathTrajectory P hP default)
        (omega (tau omega)) := by
  apply
    ContinuousPath.condExp_shift_stoppingTime_ae_eq_integral_pathKernel_of_restart_on_range
      (continuousPathTrajectory P hP default) x tau htau htauRange
  · intro S _
    exact hFeller.continuousPathTrajectory_restrict_map_shift
      P hP default hK x S
  · exact hF
  · exact hFC

end
end MarkovProcess.SubMarkovKernelSemigroup


