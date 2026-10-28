-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_Parameterized_CemeteryDenseTimeMarginals
-- name    : MarkovProcessModule_MarkovProcess_Parameterized_CemeteryDenseTimeMarginals
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T20:36:24.999609+00:00
-- url     : https://prove2.me/theorems/8d8ba6d2-42dd-4599-8bff-20a2af4586a6
-- title:
--   MarkovProcess.Parameterized.CemeteryDenseTimeMarginals
-- statement:
--   # Cemetery marginals of parameterized dense-time trajectories
--
--   This file proves a one-time marginal identity.  It makes no simultaneous path-support or
--   lifetime claim.
--
--   Complete pinned Lean module MarkovProcess.Parameterized.CemeteryDenseTimeMarginals by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Parameterized/CemeteryDenseTimeMarginals.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_Parameterized_CemeterySemigroup
import Definitions.Def_MarkovProcessModule_MarkovProcess_Parameterized_DenseTimeTrajectoryMarginals

/-!
# Cemetery marginals of parameterized dense-time trajectories

This file proves a one-time marginal identity.  It makes no simultaneous path-support or
lifetime claim.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace ParameterizedSubMarkovKernelSemigroup

noncomputable section

variable {Theta D alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]
  [StandardBorelSpace (Cemetery alpha)]

/-- From a live starting state, every coordinate of the parameterized cemetery trajectory has
zero cemetery mass when the original parameter slices are conservative. -/
theorem parameterizedCemeteryDenseTimeTrajectory_map_eval_singleton_delta
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (e : ℕ ≃ D) (iota : D ↪ NNReal) (theta : Theta) (x : alpha) (d : D) :
    ((P.cemeterySemigroup.parameterizedDenseTimeTrajectory
        P.isConservative_cemeterySemigroup e iota).map
      (fun path ↦ path d)) (theta, Cemetery.alive x) {Cemetery.delta} = 0 := by
  rw [parameterizedDenseTimeTrajectory_map_eval, parameterStateKernel_apply,
    cemeterySemigroup_apply, Kernel.cemeteryExtension_alive_singleton_delta]
  have hmass := hP theta (iota d) x
  change P theta (iota d) x Set.univ = 1 at hmass
  rw [hmass]
  exact tsub_self 1

end
end ParameterizedSubMarkovKernelSemigroup
end MarkovProcess


