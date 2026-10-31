-- Prove2me | Definitions.Def_ArcFlowBPP_LabelledGraph
-- name    : ArcFlowBPP_LabelledGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:05:08.148999+00:00
-- url     : https://prove2.me/theorems/9f538033-e8ee-4113-b667-87b4fe43e7ee
-- title:
--   Labelled multigraph $(V, A, s, t)$ of the arc-flow model
-- statement:
--   A **labelled multigraph** for the arc-flow model consists of a set of vertices $V$, a set of arcs $A$, and for every arc $a$ a tail $u$, a head $v$ and a label $i$; the paper writes the arc as $(u, v, i)$. The label $i \in \{1, \dots, m\}$ means that the arc contributes to the demand of item $i$, and the label $i = 0$ marks a **loss arc**. Two distinguished vertices are the **source** $s$ and the **target** $t$. Several arcs may join the same pair of vertices, also with the same label (a multigraph).
--
--   This is the graph on which the general arc-flow model (17)–(22) is posed: each path from $s$ to $t$ represents a packing pattern.
--
--   **Formalization Note** Items are `Fin m` and a label is an `Option (Fin m)`: `some i` for item $i$, `none` for a loss arc. The arcs are the elements of a type `A`, so parallel arcs are distinct elements. Finiteness of `A` and the standing assumptions are separate hypotheses.
-- source:
--   Brandão, Pedroso, Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression, arXiv:1310.6887v1, §3, pp.6–7 (the arc $(u,v,i)$, loss arcs $i=0$, source s and target t, multigraph)

import Mathlib

namespace ArcFlowBPP

/-- Brandão, Pedroso, *Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression*, arXiv:1310.6887v1, §3, p.7 (the paragraph under (17)–(22)) and p.6.
A labelled directed multigraph for the arc-flow model: `V` is the set of vertices, `A` the set
of arcs, and an arc `a : A` is the paper's arc `(u, v, i)` with `tail a = u`, `head a = v` and
label `i`. The source is `s` and the target `t`. Parallel arcs are allowed, since two distinct
elements of `A` may have the same tail, head and label ("there may be more than one arc
between two vertices (multigraph)", p.7).

**Formalization Note.** The items are `Fin m` (the paper's `1, …, m`), and the label of an arc
is `some i` for an arc that contributes to item `i`, and `none` for a loss arc (the paper's
`i = 0`). Finiteness of `A` and the standing assumptions (acyclic, `s` a source and `t` a
target) are separate hypotheses (`ArcFlowBPP.IsArcFlowGraph`). -/
structure LabelledGraph (m : ℕ) (V : Type*) (A : Type*) where
  /-- The tail `u` of an arc `(u, v, i)`. -/
  tail : A → V
  /-- The head `v` of an arc `(u, v, i)`. -/
  head : A → V
  /-- The label `i` of an arc `(u, v, i)`: `some i` for item `i`, `none` for a loss arc. -/
  label : A → Option (Fin m)
  /-- The source vertex `s`. -/
  s : V
  /-- The target vertex `t`. -/
  t : V

end ArcFlowBPP


