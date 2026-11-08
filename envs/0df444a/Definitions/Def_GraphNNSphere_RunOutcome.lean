-- Prove2me | Definitions.Def_GraphNNSphere_RunOutcome
-- name    : GraphNNSphere_RunOutcome
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:10.778138+00:00
-- url     : https://prove2.me/theorems/e13a0d57-33f9-40a6-a7f3-ed0f7cec9704
-- title:
--   Outcome of a navigation run
-- statement:
--   The outcome of a navigation run: success, recorded with the number of moves, the number of completed expansions and the number of distinct evaluated points; or failure, when the run stops without evaluating a target.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §1.2, p.3

import Mathlib

namespace GraphNNSphere

/-- The outcome of a navigation run (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on
the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §1.2, p.3): success with the number
of moves, of completed expansions and of distinct evaluated points, or failure. -/
inductive RunOutcome where
  | success (moves expansions evals : ℕ)
  | fail

end GraphNNSphere


