-- Prove2me | Definitions.Def_ArcFlowBPP_pathPatterns
-- name    : ArcFlowBPP_pathPatterns
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:07:06.47605+00:00
-- url     : https://prove2.me/theorems/21da208e-7f44-42ca-ba47-2c86c9ea37d5
-- title:
--   Patterns obtained from paths from $s$ to $t$
-- statement:
--   The set $P(G) \subseteq \mathbb N^m$ of **path patterns** of $G$ is the set of packing patterns of all directed walks from $s$ to $t$.
--
--   Property 1 compares the arc-flow model with the Gilmore–Gomory model over "the same patterns as the ones obtained from paths in the graph", that is, over $P(G)$. A walk made only of loss arcs gives the zero pattern, which then belongs to $P(G)$.
--
--   **Formalization Note** $P(G)$ is a `Set (Fin m → ℕ)`. It is finite for a finite acyclic graph, but no statement needs this, because Gilmore–Gomory solutions are finitely supported.
-- source:
--   Brandão, Pedroso, Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression, arXiv:1310.6887v1, Property 1, p.7 ("the patterns obtained from paths in the graph")

import Mathlib
import Definitions.Def_ArcFlowBPP_LabelledGraph
import Definitions.Def_ArcFlowBPP_IsWalk
import Definitions.Def_ArcFlowBPP_pattern

namespace ArcFlowBPP

/-- Brandão, Pedroso, *Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression*, arXiv:1310.6887v1, Property 1, p.7: "the patterns obtained from paths in the graph".
`pathPatterns G` is the set of packing patterns of the directed walks from `s` to `t` in `G`.

**Formalization Note.** It is a `Set (Fin m → ℕ)`; for a finite acyclic graph it is finite, but
nothing below needs this, since Gilmore–Gomory solutions are finitely supported (`Finsupp`).
A walk consisting only of loss arcs gives the zero pattern, which is then a member. -/
def pathPatterns {m : ℕ} {V A : Type*} (G : LabelledGraph m V A) : Set (Fin m → ℕ) :=
  {p | ∃ π : List A, IsWalk G G.s π G.t ∧ pattern G π = p}

end ArcFlowBPP


