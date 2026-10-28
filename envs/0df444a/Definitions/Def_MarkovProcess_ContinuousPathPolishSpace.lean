-- Prove2me | Definitions.Def_MarkovProcess_ContinuousPathPolishSpace
-- name    : MarkovProcess_ContinuousPathPolishSpace
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T17:26:03.081496+00:00
-- url     : https://prove2.me/theorems/87a96541-1e4b-4fa8-911c-90ec2b01b36e
-- title:
--   Polish and standard Borel structures on continuous-path space
-- statement:
--   If the state space is a complete, second-countable metric space, the space of continuous paths on nonnegative time with the compact-open topology is Polish. With its Borel measurable structure this path space is standard Borel. The complete original source proof and typeclass instance are retained, replacing only the upstream module import by the published Prove2Me ContinuousPath foundation import.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Path/Polish.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcess_ContinuousPath
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


