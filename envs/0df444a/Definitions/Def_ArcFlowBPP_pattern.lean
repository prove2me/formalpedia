-- Prove2me | Definitions.Def_ArcFlowBPP_pattern
-- name    : ArcFlowBPP_pattern
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:06:15.825542+00:00
-- url     : https://prove2.me/theorems/989fc102-125c-41dc-bc40-5789950a5a72
-- title:
--   Packing pattern of a list of arcs
-- statement:
--   For a list of arcs $\pi$, its **packing pattern** is the vector $a = (a_1, \dots, a_m) \in \mathbb N^m$ where $a_i$ is the number of arcs of $\pi$ labelled with item $i$. Loss arcs count for no item.
--
--   This is how a path from $s$ to $t$ "corresponds to a valid packing pattern" (p.6), the pattern $a^j$ of the Gilmore–Gomory model (p.4).
-- source:
--   Brandão, Pedroso, Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression, arXiv:1310.6887v1, §3, p.6 ("each path between s and t in this graph corresponds to a valid packing pattern"); §2.2, p.4 (pattern $a^j$)

import Mathlib
import Definitions.Def_ArcFlowBPP_LabelledGraph

namespace ArcFlowBPP

/-- Brandão, Pedroso, *Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression*, arXiv:1310.6887v1, §3, p.6 ("each path between s and t in this graph corresponds to a valid packing
pattern") and §2.2, p.4 (a pattern is the vector `aʲ = (aʲ₁, …, aʲₘ)` of item counts).
The packing pattern of a list of arcs `π`: its `i`-th entry is the number of arcs of `π` labelled
with item `i`. Loss arcs (label `none`) count for no item. -/
def pattern {m : ℕ} {V A : Type*} (G : LabelledGraph m V A) (π : List A) : Fin m → ℕ :=
  fun i => π.countP (fun a => G.label a = some i)

end ArcFlowBPP


