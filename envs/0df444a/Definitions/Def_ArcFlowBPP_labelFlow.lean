-- Prove2me | Definitions.Def_ArcFlowBPP_labelFlow
-- name    : ArcFlowBPP_labelFlow
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:05:54.139988+00:00
-- url     : https://prove2.me/theorems/a547fe16-a87e-455f-a68a-3df041830922
-- title:
--   Total flow on the arcs of item $i$
-- statement:
--   For a flow $f$ and an item $i$, the **total flow of item $i$** is $\sum_{(u,v,j)\in A:\, j=i} f_{uvj}$, the sum of the flow on all arcs labelled with item $i$. It is the left-hand side of the demand constraints (19) and (20).
-- source:
--   Brandão, Pedroso, Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression, arXiv:1310.6887v1, eqs. (19)–(20), p.7

import Mathlib
import Definitions.Def_ArcFlowBPP_LabelledGraph

namespace ArcFlowBPP

/-- Brandão, Pedroso, *Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression*, arXiv:1310.6887v1, eqs. (19)–(20), p.7: the left-hand side `∑_{(u,v,j)∈A : j=i} f_{uvj}`, the total
flow on the arcs labelled with item `i`. -/
def labelFlow {m : ℕ} {V A : Type*} [Fintype A] {R : Type*} [AddCommMonoid R]
    (G : LabelledGraph m V A) (f : A → R) (i : Fin m) : R :=
  ∑ a ∈ Finset.univ.filter (fun a => G.label a = some i), f a

end ArcFlowBPP


