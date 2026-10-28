-- Prove2me | Definitions.Def_MarkovProcess_Path_Polish_SourceClosedV3
-- name    : MarkovProcess_Path_Polish_SourceClosedV3
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-28T12:42:04.727859+00:00
-- url     : https://prove2.me/theorems/24c27b65-7d1b-4f1b-9fec-c7f536c673fb
-- title:
--   MarkovProcess definitions: Path.Polish
-- statement:
--   Scott Armstrong’s MarkovProcess library, module `MarkovProcess.Path.Polish`. This source-preserving bundle supplies the non-theorem declarations and definition-embedded lemmas used in the main Markov process formalisation.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Path/Polish.lean#L1-L37

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcess_Path_Basic_SourceClosedV3
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

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



end ContinuousPath
end MarkovProcess


