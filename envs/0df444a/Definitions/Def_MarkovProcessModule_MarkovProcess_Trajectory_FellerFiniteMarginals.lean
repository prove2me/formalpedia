-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_Trajectory_FellerFiniteMarginals
-- name    : MarkovProcessModule_MarkovProcess_Trajectory_FellerFiniteMarginals
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T21:01:38.748512+00:00
-- url     : https://prove2.me/theorems/dc26744d-04c1-454f-83eb-1819d3bb792c
-- title:
--   MarkovProcess.Trajectory.FellerFiniteMarginals
-- statement:
--   # Arbitrary-time finite marginals of Feller trajectories
--
--   This file removes the compact-test convergence premise from the earlier arbitrary-time
--   finite-marginal reduction. For a conservative Feller kernel semigroup whose dense trajectory has
--   the stated Kolmogorov control, every finite family of continuous-path coordinates has exactly the
--   finite-set-kernel law.
--
--   The theorem is stated for an arbitrary such semigroup; no particular semigroup is singled out,
--   and no Hunt-process property is asserted.
--
--   Complete pinned Lean module MarkovProcess.Trajectory.FellerFiniteMarginals by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Trajectory/FellerFiniteMarginals.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_Feller_FiniteDenseApproximationContinuity

/-!
# Arbitrary-time finite marginals of Feller trajectories

This file removes the compact-test convergence premise from the earlier arbitrary-time
finite-marginal reduction. For a conservative Feller kernel semigroup whose dense trajectory has
the stated Kolmogorov control, every finite family of continuous-path coordinates has exactly the
finite-set-kernel law.

The theorem is stated for an arbitrary such semigroup; no particular semigroup is singled out,
and no Hunt-process property is asserted.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal

namespace MarkovProcess

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [LocallyCompactSpace alpha]

namespace SubMarkovKernelSemigroup

open IsConservative

variable [CompleteSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]

/-- A conservative Feller trajectory with the required Kolmogorov control has the prescribed
finite-dimensional law at every finite set of nonnegative-real times. -/
theorem IsFellerKernelSemigroup.continuousPathTrajectory_map_finiteTimeSet
    (P : SubMarkovKernelSemigroup alpha) (hFeller : P.IsFellerKernelSemigroup)
    (hP : P.IsConservative) (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (I : Finset NNReal) :
    (continuousPathTrajectory P hP default).map
        (ContinuousPath.finiteEvaluation (fun t : I ↦ (t : NNReal))) =
      finiteSetKernel P I := by
  obtain ⟨q, hq⟩ := exists_denseTime_finset_seq_tendsto I
  apply IsConservative.continuousPathTrajectory_map_finiteTimeSet_of_integral_tendsto
    P hP default hK I q hq
  intro x f
  exact hFeller.tendsto_integral_compactlySupported_finiteDenseApproximationKernel
    hP q hq f x

end SubMarkovKernelSemigroup

end

end MarkovProcess


