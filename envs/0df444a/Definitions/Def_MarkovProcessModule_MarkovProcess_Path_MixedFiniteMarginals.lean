-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_Path_MixedFiniteMarginals
-- name    : MarkovProcessModule_MarkovProcess_Path_MixedFiniteMarginals
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T20:55:57.993074+00:00
-- url     : https://prove2.me/theorems/9cb756b8-d057-4ffe-a279-fe7c75fefa34
-- title:
--   MarkovProcess.Path.MixedFiniteMarginals
-- statement:
--   # Finite mixed past/future marginals of continuous trajectories
--
--   Every finite collection of rational coordinates drawn from the past through `S` and the shifted
--   future has the finite transition law on the corresponding union of absolute physical times,
--   followed by the canonical possibly noninjective coordinate pullback.  In particular, a terminal
--   past coordinate and a future coordinate at zero are both retained even though they observe the
--   same absolute time.
--
--   This is a finite-dimensional law identity.  The conditional factorization of that law through
--   the state at `S` is in `Restart/RationalRestart.lean`.
--
--   Complete pinned Lean module MarkovProcess.Path.MixedFiniteMarginals by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Path/MixedFiniteMarginals.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_Trajectory_FiniteMarginals
import Definitions.Def_MarkovProcessModule_MarkovProcess_Restart_MixedPastFuture

/-!
# Finite mixed past/future marginals of continuous trajectories

Every finite collection of rational coordinates drawn from the past through `S` and the shifted
future has the finite transition law on the corresponding union of absolute physical times,
followed by the canonical possibly noninjective coordinate pullback.  In particular, a terminal
past coordinate and a future coordinate at zero are both retained even though they observe the
same absolute time.

This is a finite-dimensional law identity.  The conditional factorization of that law through
the state at `S` is in `Restart/RationalRestart.lean`.
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

/-- A finite mixed rational past/shifted-future marginal is the finite transition law on its
absolute physical times, pulled back to the original mixed labels. -/
theorem continuousPathTrajectory_map_mixedPastShiftedCoordinates_restrict
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) :
    (continuousPathTrajectory P hP default).map
        (I.restrict ∘ ContinuousPath.mixedPastShiftedCoordinates S) =
      (finiteSetKernel P (MixedPastFuture.absolutePhysicalFinset S I)).map
        (MixedPastFuture.pullbackAbsolutePhysical S I) := by
  let evaluateAbsolute : ContinuousPath alpha →
      MixedPastFuture.absolutePhysicalFinset S I → alpha :=
    fun path t ↦ path t
  have hEvaluateAbsolute : Measurable evaluateAbsolute := by
    rw [measurable_pi_iff]
    intro t
    exact ContinuousPath.measurable_coordinateProcess (alpha := alpha) t
  have hcoordinates :
      I.restrict ∘ ContinuousPath.mixedPastShiftedCoordinates S =
        MixedPastFuture.pullbackAbsolutePhysical S I ∘ evaluateAbsolute := by
    funext omega
    exact ContinuousPath.restrict_mixedPastShiftedCoordinates S I omega
  rw [hcoordinates, Kernel.map_comp_right]
  · change
      ((continuousPathTrajectory P hP default).map
        (fun path (t : denseTimePhysicalSet (MixedPastFuture.absoluteFinset S I)) ↦
          path t)).map (MixedPastFuture.pullbackAbsolutePhysical S I) = _
    rw [continuousPathTrajectory_map_finiteDenseTimeSet P hP default hK]
    rfl
  · exact hEvaluateAbsolute
  · exact MixedPastFuture.measurable_pullbackAbsolutePhysical S I

end
end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess


