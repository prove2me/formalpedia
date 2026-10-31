-- Prove2me | Definitions.Def_FASTournament_IsDirCycle
-- name    : FASTournament_IsDirCycle
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:31:21.138363+00:00
-- url     : https://prove2.me/theorems/98567408-bbcd-4c22-af31-c1c20d355e7e
-- title:
--   Directed cycle (as a set of arcs)
-- statement:
--   A **directed cycle** of a digraph $G$ is a closed walk $c_0\to c_1\to\cdots\to c_{k-1}\to c_0$ through $k\ge 2$ distinct vertices. It is identified with its arc set $\{c_0c_1,\dots,c_{k-2}c_{k-1},c_{k-1}c_0\}$, which is how it appears as a row of the cycle-arc incidence matrix $M$.
--
--   **Formalization Note** The cyclic successor of index $i$ is `finRotate k i`. Loops are not cycles; tournaments have no loops.
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, p.2 ("cycles (directed)")

import Mathlib
import Definitions.Def_FASTournament_Arc

namespace FASTournament

/-- **Directed cycle, as a set of arcs.**
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, p.2 ("cycles (directed)").

`C` is (the arc set of) a directed cycle of `G` if there are `k ≥ 2` distinct vertices
`c 0, …, c (k-1)` with arcs `c 0 → c 1 → ⋯ → c (k-1) → c 0`, and `C` is exactly the set of these
`k` arcs.

**Formalization Note.** `finRotate k` sends `i` to `i + 1 mod k`. Cycles have length at least
`2`, so a loop is not a cycle (the paper's digraphs are loopless, and tournaments have no loops).
Cycles are identified with their arc sets, as rows of the cycle-arc incidence matrix are. -/
def IsDirCycle {V : Type*} (G : Digraph V) (C : Finset (Arc G)) : Prop :=
  ∃ (k : ℕ) (c : Fin k → V), 2 ≤ k ∧ Function.Injective c ∧
    (∀ i, G.Adj (c i) (c (finRotate k i))) ∧
    ∀ e : Arc G, e ∈ C ↔ ∃ i, e.1 = (c i, c (finRotate k i))

end FASTournament


