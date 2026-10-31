-- Prove2me | Definitions.Def_ArcFlowBPP_IsArcFlowGraph
-- name    : ArcFlowBPP_IsArcFlowGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:07:36.969985+00:00
-- url     : https://prove2.me/theorems/ef148970-f04f-4665-b1a8-c7069916a88d
-- title:
--   Standing assumptions on the arc-flow graph: acyclic, no walk from $t$ to $s$
-- statement:
--   The **standing assumptions** on the graph of the arc-flow model (17)–(22):
--
--   1. $G$ is acyclic;
--   2. there is no directed walk from the target $t$ to the source $s$.
--
--   The paper requires a directed acyclic graph with source $s$ and target $t$, and uses that $s$ is "the only excess node" and $t$ "the only deficit node" of a flow. The second clause is that reading: it holds when no arc enters $s$, when no arc leaves $t$, and, in an acyclic graph, as soon as there is some path from $s$ to $t$. Since the empty walk is a walk from $t$ to $t$, it also gives $s \ne t$.
--
--   **Formalization Note** Without the second clause, an arc $t \to s$ lets the linear relaxation of (17)–(22) send flow from $t$ to $s$ with $z < 0$.
-- source:
--   Brandão, Pedroso, Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression, arXiv:1310.6887v1, §3, p.7 (directed acyclic graph, source s, target t) and p.8 ("the only excess node (node s) … the only deficit node (node t)")

import Mathlib
import Definitions.Def_ArcFlowBPP_LabelledGraph
import Definitions.Def_ArcFlowBPP_IsWalk
import Definitions.Def_ArcFlowBPP_IsAcyclic

namespace ArcFlowBPP

/-- Brandão, Pedroso, *Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression*, arXiv:1310.6887v1, §3, pp.7–8: the standing assumptions on the graph of model (17)–(22). The graph is a
directed acyclic graph ("we always need to ensure that it is a directed acyclic graph", p.7),
`s` is the source and `t` the target (p.7), so that `s` is "the only excess node" and `t` "the
only deficit node" of a flow (p.8). The second clause states this as: there is no directed walk
from `t` to `s`.

**Formalization Note.** No walk from `t` to `s` includes the empty walk, so `s ≠ t` follows.
The clause holds when no arc enters `s` (a source), when no arc leaves `t` (a target), and, in
an acyclic graph, as soon as some `s`–`t` path exists (some valid packing pattern is
represented). Without it the linear relaxation of (17)–(22) can send flow from `t` to `s` with
`z < 0` (an arc `t → s` and no `s`–`t` path makes it unbounded below while Gilmore–Gomory has
value `0` for `b = 0`). -/
def IsArcFlowGraph {m : ℕ} {V A : Type*} (G : LabelledGraph m V A) : Prop :=
  IsAcyclic G ∧ ∀ π : List A, ¬ IsWalk G G.t π G.s

end ArcFlowBPP


