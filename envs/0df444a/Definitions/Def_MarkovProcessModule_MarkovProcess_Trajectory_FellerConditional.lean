-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_Trajectory_FellerConditional
-- name    : MarkovProcessModule_MarkovProcess_Trajectory_FellerConditional
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T21:16:54.343319+00:00
-- url     : https://prove2.me/theorems/52bd2ee6-9f43-4d0a-b793-9110a329df1e
-- title:
--   MarkovProcess.Trajectory.FellerConditional
-- statement:
--   # Deterministic-time conditional expectation for the Feller trajectory
--
--   At every physical time, the conditional expectation of a bounded strongly measurable functional
--   of the shifted canonical Feller trajectory, given the canonical filtration at that time, is the
--   path-kernel expectation started from the current state.  The proof passes the event-restricted
--   deterministic restart identity through the generic continuous-path conditional-expectation
--   bridge.
--
--   The time here is deterministic.  The corresponding statement at a finite stopping time is in
--   `Trajectory/FellerStoppingConditional.lean`, and at a stopping time that may be infinite in
--   `Trajectory/StoppingLtTop.lean`.
--
--   Complete pinned Lean module MarkovProcess.Trajectory.FellerConditional by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Trajectory/FellerConditional.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_Trajectory_FellerRestrictedRestart

/-!
# Deterministic-time conditional expectation for the Feller trajectory

At every physical time, the conditional expectation of a bounded strongly measurable functional
of the shifted canonical Feller trajectory, given the canonical filtration at that time, is the
path-kernel expectation started from the current state.  The proof passes the event-restricted
deterministic restart identity through the generic continuous-path conditional-expectation
bridge.

The time here is deterministic.  The corresponding statement at a finite stopping time is in
`Trajectory/FellerStoppingConditional.lean`, and at a stopping time that may be infinite in
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

/-- At every physical time, the conditional expectation of a bounded functional of the shifted
Feller trajectory given the canonical filtration is its path-kernel expectation started from the
current state. -/
theorem IsFellerKernelSemigroup.continuousPathTrajectory_condExp_shift
    (P : SubMarkovKernelSemigroup alpha) (hFeller : P.IsFellerKernelSemigroup)
    (hP : P.IsConservative) (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (x : alpha) (s : NNReal)
    (F : ContinuousPath alpha → E) (hF : StronglyMeasurable F)
    (C : ℝ) (hFC : ∀ eta, ‖F eta‖ ≤ C) :
    ((continuousPathTrajectory P hP default) x)[fun omega ↦
        F (ContinuousPath.shift s omega)|
      ContinuousPath.canonicalFiltration (alpha := alpha) s] =ᵐ[
        (continuousPathTrajectory P hP default) x]
      fun omega ↦ ∫ eta, F eta ∂(continuousPathTrajectory P hP default)
        (omega s) := by
  apply ContinuousPath.condExp_shift_ae_eq_integral_pathKernel_of_restrict_map
    (continuousPathTrajectory P hP default) x s
  · exact hFeller.continuousPathTrajectory_restrict_map_shift
      P hP default hK x s
  · exact hF
  · exact hFC

end
end MarkovProcess.SubMarkovKernelSemigroup


