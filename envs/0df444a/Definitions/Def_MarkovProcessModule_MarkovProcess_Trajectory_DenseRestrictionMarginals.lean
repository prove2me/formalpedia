-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_Trajectory_DenseRestrictionMarginals
-- name    : MarkovProcessModule_MarkovProcess_Trajectory_DenseRestrictionMarginals
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T20:51:27.276009+00:00
-- url     : https://prove2.me/theorems/1307dc7e-a5d7-4abf-917b-156a48337dd7
-- title:
--   MarkovProcess.Trajectory.DenseRestrictionMarginals
-- statement:
--   # Finite marginals of dense restrictions of continuous trajectories
--
--   The finite-coordinate laws of the dense-time restriction of the canonical continuous trajectory
--   are the existing finite-set kernels, reindexed from physical time back to rational labels.  This
--   file makes no shift, Markov, strong Markov, or Hunt-process assertion.
--
--   Complete pinned Lean module MarkovProcess.Trajectory.DenseRestrictionMarginals by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Trajectory/DenseRestrictionMarginals.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_DenseTime_PhysicalReindex

/-!
# Finite marginals of dense restrictions of continuous trajectories

The finite-coordinate laws of the dense-time restriction of the canonical continuous trajectory
are the existing finite-set kernels, reindexed from physical time back to rational labels.  This
file makes no shift, Markov, strong Markov, or Hunt-process assertion.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess
namespace SubMarkovKernelSemigroup
namespace IsConservative

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]

/-- Every finite restriction of the dense-time pushforward of the continuous trajectory has the
finite-set transition law at the corresponding physical times, reindexed by rational labels. -/
theorem continuousPathTrajectory_map_denseRestriction_map_restrict
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (I : Finset DenseTime) :
    ((continuousPathTrajectory P hP default).map
        ContinuousPath.denseRestriction).map I.restrict =
      (finiteSetKernel P (denseTimePhysicalSet I)).map
        (DenseTimePath.pullbackPhysicalSet I) := by
  let evaluatePhysical : ContinuousPath alpha → denseTimePhysicalSet I → alpha :=
    fun path t ↦ path t
  have hEvaluate : Measurable evaluatePhysical := by
    rw [measurable_pi_iff]
    intro t
    rw [BorelSpace.measurable_eq (α := alpha)]
    exact (ContinuousPath.continuous_eval (alpha := alpha) (t : NNReal)).borel_measurable
  have hfun :
      I.restrict ∘ ContinuousPath.denseRestriction =
        DenseTimePath.pullbackPhysicalSet I ∘ evaluatePhysical := by
    funext path
    exact (DenseTimePath.pullbackPhysicalSet_evaluation I path).symm
  rw [← Kernel.map_comp_right]
  · rw [hfun, Kernel.map_comp_right]
    · change
        ((continuousPathTrajectory P hP default).map
          (fun path (t : denseTimePhysicalSet I) ↦ path t)).map
            (DenseTimePath.pullbackPhysicalSet I) = _
      rw [continuousPathTrajectory_map_finiteDenseTimeSet P hP default hK I]
    · exact hEvaluate
    · exact DenseTimePath.measurable_pullbackPhysicalSet I
  · exact ContinuousPath.measurable_denseRestriction
  · exact Finset.measurable_restrict I

end
end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess


