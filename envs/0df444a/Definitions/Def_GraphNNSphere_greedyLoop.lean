-- Prove2me | Definitions.Def_GraphNNSphere_greedyLoop
-- name    : GraphNNSphere_greedyLoop
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:41:02.999207+00:00
-- url     : https://prove2.me/theorems/3b71a7a5-4b4d-4439-a1b7-f2fe16ef98d1
-- title:
--   One visit of the navigation run
-- statement:
--   One visit of a navigation run at the current point $x$. It expands $x$ by scanning the entire list $G(x)$ and evaluating each point not already evaluated. Success is recorded after the completed expansion if the evaluated points include a member of $\mathrm{Top}_k(q)$, even when the entry itself is a target. Otherwise the run moves to the listed point closest to $q$ if it is strictly closer than $x$, and it stops if no listed point is closer.
--
--   **Formalization Note** The recursion is bounded by a fuel argument, and exhausted fuel is reported as failure. This branch is unreachable from the initial fuel $n+1$: distances to $q$ strictly decrease, so a run visits at most $n$ labels.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §1.2, p.3

import Mathlib
import Definitions.Def_GraphNNSphere_IsTarget
import Definitions.Def_GraphNNSphere_successor
import Definitions.Def_GraphNNSphere_RunOutcome

namespace GraphNNSphere

open Classical in
/-- One visit of the navigation run from the current point `cur`, with evaluated set `ev` and the
counts of moves and expansions so far (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on
the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §1.2, p.3). It expands `cur` by
adding its entire list to the evaluated set. Success is recorded if the evaluated set then includes
a target. Otherwise the run moves to the successor if it is strictly closer to `q`, and stops
unsuccessfully if not.

**Formalization Note** The recursion is bounded by `fuel`. Fuel exhaustion is reported as `fail` and
is unreachable from `greedyRun`, which starts with fuel `n + 1`: distances to `q` strictly decrease,
so a run visits at most `n` distinct labels. -/
noncomputable def greedyLoop {n d : ℕ} (G : NavGraph n) (X : Fin n → Sph d) (q : Sph d) (k : ℕ) :
    ℕ → Fin n → Finset (Fin n) → ℕ → ℕ → RunOutcome
  | 0, _, _, _, _ => .fail
  | fuel + 1, cur, ev, moves, expansions =>
    if ∃ j ∈ ev ∪ G cur, IsTarget k X q j then
      .success moves (expansions + 1) (ev ∪ G cur).card
    else
      match successor G X q cur with
      | some y =>
        if geo q (X y) < geo q (X cur) then
          greedyLoop G X q k fuel y (ev ∪ G cur) (moves + 1) (expansions + 1)
        else .fail
      | none => .fail

end GraphNNSphere


