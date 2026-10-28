-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_Path_Polish
-- name    : MarkovProcessModule_MarkovProcess_Path_Polish
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T19:33:31.658915+00:00
-- url     : https://prove2.me/theorems/ad7c6dea-001f-4058-866a-4de7cf3ed4e4
-- title:
--   MarkovProcess.Path.Polish
-- statement:
--   # Polish structure of continuous-path space
--
--   For a complete separable metric state space, the compact-open topology on continuous paths is
--   Polish: it is second countable, and it is induced by the compact-convergence uniformity, which is
--   complete and countably generated because nonnegative time is locally compact and sigma-compact.
--   With the Borel sigma-algebra the path space is therefore a standard Borel space.
--
--   This is ordinary topological infrastructure.  It proves no probabilistic statement.
--
--   Complete pinned Lean module MarkovProcess.Path.Polish by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Path/Polish.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_Path_Basic
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Polish structure of continuous-path space

For a complete separable metric state space, the compact-open topology on continuous paths is
Polish: it is second countable, and it is induced by the compact-convergence uniformity, which is
complete and countably generated because nonnegative time is locally compact and sigma-compact.
With the Borel sigma-algebra the path space is therefore a standard Borel space.

This is ordinary topological infrastructure.  It proves no probabilistic statement.
-/

namespace MarkovProcess
namespace ContinuousPath

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha] [SecondCountableTopology alpha]

/-- Continuous-path space over a complete separable metric space is Polish. -/
instance instPolishSpace : PolishSpace (ContinuousPath alpha) := inferInstance

/-- With the Borel sigma-algebra, continuous-path space is a standard Borel space. -/
theorem standardBorelSpace_borel :
    @StandardBorelSpace (ContinuousPath alpha) (borel (ContinuousPath alpha)) := by
  let : MeasurableSpace (ContinuousPath alpha) := borel (ContinuousPath alpha)
  have : BorelSpace (ContinuousPath alpha) := ⟨rfl⟩
  infer_instance

end ContinuousPath
end MarkovProcess


