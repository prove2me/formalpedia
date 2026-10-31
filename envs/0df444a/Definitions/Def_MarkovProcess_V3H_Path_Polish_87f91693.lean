-- Prove2me | Definitions.Def_MarkovProcess_V3H_Path_Polish_87f91693
-- name    : MarkovProcess_V3H_Path_Polish_87f91693
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:27:52.86693+00:00
-- url     : https://prove2.me/theorems/09581ec3-5222-4f3d-8282-ac4666bb3487
-- title:
--   MarkovProcess: MarkovProcess_V3H_Path_Polish_87f91693
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

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


