-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_DenseTime_CemeteryDenseTimeMarginals
-- name    : MarkovProcessModule_MarkovProcess_DenseTime_CemeteryDenseTimeMarginals
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T20:35:17.457233+00:00
-- url     : https://prove2.me/theorems/f44f1a70-d0d8-4b66-b67c-9dd12542b484
-- title:
--   MarkovProcess.DenseTime.CemeteryDenseTimeMarginals
-- statement:
--   # Cemetery marginals of dense-time trajectories
--
--   For a conservative live semigroup, the trajectory of its cemetery extension has no cemetery mass
--   at any dense-time coordinate when started from a live state.  This is a finite-coordinate statement;
--   it does not assert that a dense-time path has a continuous lifetime-path extension.
--
--   Complete pinned Lean module MarkovProcess.DenseTime.CemeteryDenseTimeMarginals by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/DenseTime/CemeteryDenseTimeMarginals.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_DenseTime_CemeterySemigroup
import Definitions.Def_MarkovProcessModule_MarkovProcess_DenseTime_TrajectoryMarginals

/-!
# Cemetery marginals of dense-time trajectories

For a conservative live semigroup, the trajectory of its cemetery extension has no cemetery mass
at any dense-time coordinate when started from a live state.  This is a finite-coordinate statement;
it does not assert that a dense-time path has a continuous lifetime-path extension.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MarkovProcess
namespace SubMarkovKernelSemigroup
namespace IsConservative

noncomputable section

variable {D alpha : Type*} [MeasurableSpace alpha] [StandardBorelSpace (Cemetery alpha)]

/-- Every dense-time coordinate of the cemetery trajectory started from a live state has zero
cemetery mass when the original semigroup is conservative. -/
theorem cemeteryDenseTimeTrajectory_map_eval_alive_delta
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (e : ℕ ≃ D) (iota : D ↪ NNReal) (d : D) (x : alpha) :
    ((denseTimeTrajectory P.cemeterySemigroup P.isConservative_cemeterySemigroup e iota).map
        (fun path ↦ path d)) (Cemetery.alive x) {Cemetery.delta} = 0 := by
  rw [denseTimeTrajectory_map_eval]
  rw [cemeterySemigroup_apply, Kernel.cemeteryExtension_alive_singleton_delta]
  rw [hP (iota d) x, tsub_self]

end
end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess


